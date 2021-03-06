
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1gTerm := L1g.compile.Term.
Definition L1gTerms := L1g.compile.Terms.
Definition L1gBrs := L1g.compile.Brs.
Definition L1gDefs := L1g.compile.Defs.
Definition L1gPgm := Program L1gTerm.
Definition L1gEC := envClass L1gTerm.
Definition L1gEnv := environ L1gTerm.


Inductive Term : Type :=
| TRel       : nat -> Term
| TProof     : Term
| TLambda    : name -> Term -> Term
| TLetIn     : name -> Term -> Term -> Term
| TApp       : Term -> Term (* first arg must exist *) -> Terms -> Term
| TConst     : string -> Term
| TConstruct : inductive -> nat (* cnstr no *) ->
               nat (* # pars *) -> nat (* # args *) -> Term
                                  (* use Defs to code branches *)
| TCase      : (inductive * nat) (* # of pars *) ->
               Term (* discriminee *) -> Brs (* # args, branch *) -> Term
| TFix       : Defs -> nat -> Term
| TWrong     : string -> Term
| TDummy     : string -> Term   (* residual of Sorts, inductives, Products *)
with Terms : Type :=
| tnil : Terms
| tcons : Term -> Terms -> Terms
with Brs : Type :=
| bnil : Brs
| bcons : nat -> Term -> Brs -> Brs
with Defs : Type :=
| dnil : Defs
| dcons : name -> Term -> nat -> Defs -> Defs.
Hint Constructors Term Terms Brs Defs.
Scheme Trm_ind' := Induction for Term Sort Prop
  with Trms_ind' := Induction for Terms Sort Prop
  with Brs_ind' := Induction for Brs Sort Prop
  with Defs_ind' := Induction for Defs Sort Prop.
Combined Scheme TrmTrmsBrsDefs_ind
         from Trm_ind', Trms_ind', Brs_ind', Defs_ind'.
Notation prop := (TSort SProp).
Notation set_ := (TSort SSet).
Notation type_ := (TSort SType).
Notation tunit t := (tcons t tnil).
Notation dunit nm t m := (dcons nm t m dnil).

Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

(** syntactic control of "TApp": no nested apps, app must have an argument **)
Function mkApp (t:Term) (args:Terms) {struct t} : Term :=
  match t with
  | TApp fn b bs => TApp fn b (tappend bs args)
  | fn => match args with
          | tnil => fn
          | tcons c cs => TApp fn c cs
          end
  end.

Function strip (t:L1gTerm) : Term :=
  match t with
    | L1g.compile.TRel n => TRel n
    | L1g.compile.TSort s => TDummy "Srt"
    | L1g.compile.TProof => TProof
    | L1g.compile.TProd nm _ _ => TDummy ("Prod:"++ print_name nm)
    | L1g.compile.TLambda nm _ bod => TLambda nm (strip bod)
    | L1g.compile.TLetIn nm dfn _ bod => TLetIn nm (strip dfn) (strip bod)
    | L1g.compile.TApp fn arg args =>
      mkApp (strip fn) (tcons (strip arg) (strips args))
    | L1g.compile.TConst nm => TConst nm
    | L1g.compile.TInd i => TDummy ("Ind:"++ print_inductive i)
    | L1g.compile.TConstruct i m np na => TConstruct i m np na
    | L1g.compile.TCase n _ mch brs => TCase n (strip mch) (stripBs brs)
    | L1g.compile.TFix ds n => TFix (stripDs ds) n
    | L1g.compile.TWrong str => TWrong str
  end
with strips (ts:L1gTerms) : Terms := 
  match ts with
    | L1g.compile.tnil => tnil
    | L1g.compile.tcons t ts => tcons (strip t) (strips ts)
  end
with stripBs (bs:L1gBrs) : Brs := 
  match bs with
    | L1g.compile.bnil => bnil
    | L1g.compile.bcons n t ts => bcons n (strip t) (stripBs ts)
  end
with stripDs (ts:L1gDefs) : Defs := 
  match ts with
    | L1g.compile.dnil => dnil
    | L1g.compile.dcons nm _ t m ds => dcons nm (strip t) m (stripDs ds)
  end.

Lemma strips_tcons:
  forall t ts,
    strips (L1g.compile.tcons t ts) = tcons (strip t) (strips ts).
Proof.
  reflexivity.
Qed.

Lemma not_isApp_strip_App_App:
  forall fn arg args,
    ~ L1g.term.isApp fn ->
    strip (L1g.compile.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
Proof.
  destruct fn; intros; try reflexivity.
  - elim H. auto.
Qed.

(*************
Lemma TLambda_strip_inv:
  forall nm bod t, TLambda nm bod = strip t ->
                   exists bod' ty, t = L1g.compile.TLambda nm ty bod'.
Proof.
  induction t; intros; cbn in *; try discriminate. myInjection H.
  exists t2, t1. reflexivity.
Qed.
Lemma strip_TCast_TCast:
  forall t, ~ L1g.term.isCastProp t ->
            forall u, strip (L1g.compile.TCast u t) = TCast (strip u).
Proof.
  intros t ht u. unfold isCastProp in ht.
  assert (j: forall prp, t <> L1g.compile.TCast prp L1g.compile.prop).
  { intros prp j. elim ht. exists prp. assumption. }
  destruct t; cbn; try reflexivity.
  destruct t2; cbn; try reflexivity.
  destruct s; cbn; try reflexivity.
  specialize (j t1). destruct j. reflexivity.
Qed.

Lemma strip_TCast_TCast':
  forall u t, ~ L1g.term.isProofCast (L1g.compile.TCast u t) ->
            strip (L1g.compile.TCast u t) = TCast (strip u).
Proof.
  intros u t h. unfold isProofCast in h.
  assert (j: forall prf prp,
            L1g.compile.TCast u t <>
            L1g.compile.TCast prf (L1g.compile.TCast prp L1g.compile.prop)).
  { intros prf prp k. apply h. exists prf, prp. assumption. }
  destruct t; cbn; try reflexivity.
  destruct t2; cbn; try reflexivity.
  destruct s; cbn; try reflexivity.
  specialize (j u t1). destruct j. reflexivity.
Qed.
*******************)

(** environments and programs **)
Function stripEC (ec:L1gEC) : AstCommon.envClass Term :=
  match ec with
    | ecTrm t => ecTrm (strip t)
    | ecTyp _ n itp => ecTyp Term n itp
  end.

Definition  stripEnv : L1gEnv -> AstCommon.environ Term :=
  List.map (fun nmec : string * L1gEC => (fst nmec, stripEC (snd nmec))).

Lemma stripEcTrm_hom:
  forall t, stripEC (ecTrm t) = ecTrm (strip t).
Proof.
  intros. reflexivity.
Qed.

Lemma stripEnv_pres_fresh:
  forall nm p, fresh nm p -> fresh nm (stripEnv p).
Proof.
  induction 1.
  - constructor; assumption.
  - constructor.
Qed.

Lemma stripEnv_inv:
  forall gp s ec p, stripEnv gp = (s, ec) :: p ->
                    exists ec2 p2, ec =stripEC ec2 /\ p = stripEnv p2.
Proof.
  intros. destruct gp. discriminate. cbn in H. injection H; intros. subst.
  exists (snd p0), gp. intuition.
Qed.
  
Definition stripProgram (p:L1gPgm) : Program Term :=
  {| env:= stripEnv (env p);
     main:= strip (main p) |}.

(*** from L1 to L2 ***) 
Definition program_Program (p:program) : Program Term :=
  stripProgram (L1g.compile.program_Program_ext p).

Definition term_Term (e:AstCommon.environ L1gTerm) (t:term) : Term :=
  strip (L1g.compile.term_Term e t).
