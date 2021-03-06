(* Continuation-Passing Style language for the CertiCoq project.
 *   Initial design, Andrew W. Appel, June 2014
 *)
From Coq Require Import ZArith.ZArith Lists.List.
From CertiCoq.L6 Require Import List_util.
From compcert.lib Require Import Maps.
From Template Require Import BasicAst. (* For identifier names *)

Import ListNotations.

(* We will use several maps from identifiers to types, values, etc.
 * For now we'll use Xavier Leroy's efficient polymorphic maps from 
 * positive numbers to _. When the MMaps module of the Coq stdlib is
 * created, we'll use that. *)

Module M := Maps.PTree.

Fixpoint getlist {A} (xs: list M.elt) (rho: M.t A) : option (list A) :=
  match xs with 
  | x :: xs' => match M.get x rho, getlist xs' rho with
               | Some v, Some vs => Some (v::vs)
               | _, _ => None
               end
  | nil => Some nil
  end.

Fixpoint setlist {A} (xs: list M.elt) (vs: list A) (rho: M.t A) : option (M.t A) :=
  match xs, vs with
  | x::xs', v::vs' => match setlist xs' vs' rho with
                     | Some rho' => Some (M.set x v rho')
                     | None => None
                     end
  | nil, nil => Some rho
  | _, _ => None
  end.

Definition var := M.elt.   (* value variables *)
Definition fTag := M.elt.   (* discrimination tags for functions *)
Definition iTag := M.elt.   (* discrimination tags for inductive types *)
Definition cTag := M.elt.   (* discrimination tags for constructors *)
Definition prim := M.elt. (* primitive operators *)


(* Remark.  It sure would be nice if we could use abstraction here,
   so that M was instantiated differently for vars, types, and tags,
   such that [var] was not beta-eta equal to [type].  But then the
   type of maps [M.t] would have to be abstract, and that in turn
   would mean that Coq could not determine that [M.t(A)] is covariant
   in A.  Which, in turn, would make impossible the inductive definition
   of [val], below. 
 *)


(* To describe the [i]th field of a record, we use type BinNat,
   that is, [N].  This has a more efficient representation than [nat],
   which is a consideration for programs that process large
   abstract syntax trees.
 *)


(* Given a list of tagged variants, return the one with the matching tag. *)
Fixpoint findtag {A} (cl: list (cTag * A)) (c: cTag) : option A :=
  match cl with
  | (c',a)::cl' => if M.elt_eq c' c then Some a else findtag cl' c
  | nil => None
  end.

(** * CPS Expressions *)

(* Expressions [exp] of the CPS language. *)
Inductive exp : Type :=
| Econstr: var -> cTag -> list var -> exp -> exp
| Ecase: var -> list (cTag * exp) -> exp
| Eproj: var -> cTag -> N -> var -> exp -> exp
| Efun: fundefs -> exp -> exp
| Eapp: var -> fTag -> list var -> exp
| Eprim: var -> prim -> list var -> exp -> exp (* where prim is id *)
| Ehalt : var -> exp
with fundefs : Type :=
     | Fcons: var -> fTag -> list var -> exp -> fundefs -> fundefs
     | Fnil: fundefs.


(* [Econstr x t c ys e] applies a data constructor with tag [c] to
           a list of values denoted by variables [ys].   The resulting
           value is bound to variable [x] of type [t], and then execution
           continues with expression [e].  Static typing requires that
           the typeinfo bound to [t] has a variant consistent with [c]
           and the types of [ys].
    [Ecase v cl] does case-discrimination on value [v], which
           must be a [Vconstr t c vs] value. One of the elements of 
           [cl] must be the pair [(c,e)], where [e] a expression 
           that uses [v] (and makes necessary projections). 
    [Eproj v t n y e] projects the record value [y] by selecting
           the [n]th element of the record.   This is bound to [v] of type [t]
           and execution continues with [e].  Typechecking requires
           that the type of [y] be a Tdata with a single variant, whose 
           data list has length at least n.
    [Efun fl e]  binds the set of mutually recursive functions [fl]
           into the environment, and continues with [e].
    [Eapp f ys]   applies the function [f] to arguments [ys]
    [Eprim x t f ys e] applies primop [f] to arguments [ys]
            and binds the result to [x] of type [t], continues with [e].
            The primop [f] is a primitive operator, whose type is equivalent to
            the CPS transform of [ts->t], where [ts] are the type of the [ys].

   [Fdef f t ys e]   defines a function [f] of type [t] with parameters [ys]
             and body [e].  We do not syntactically distinguish continuations 
             from other functions, as Andrew Kennedy does [Compiling with 
             Continuations, Continued, 2007].  Instead, we rely on the type 
             system to do it; see below.  This mechanism also permits
             classifying functions into different calling conventions, even 
             if they have the same source-language type.
 *)

(* Remark.  It is conventional in CPS representations to guarantee
   that no two binding occurrences bind the same variable-name.
   However, neither the static (typing) semantics nor the dynamic
   (small-step) semantics requires this.  Some of the transformation
   (optimization, rewrite) algorithms may require it.
 *)


(** Induction principles for exp anf fundefs *)

Lemma exp_ind' :
  forall P : exp -> Type,
    (forall (v : var) (t : cTag) (l : list var) (e : exp),
        P e -> P (Econstr v t l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (cTag * exp)) (c : cTag) (e : exp),
        P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
        P e -> P (Eproj v t n v0 e)) ->
    (forall (f2 : fundefs) (e : exp), P e -> P (Efun f2 e)) ->
    (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
    (forall (v : var)  (p : prim) (l : list var) (e : exp),
        P e -> P (Eprim v p l e)) ->
    (forall (v : var), P (Ehalt v)) ->
    forall e : exp, P e.
Proof.
  intros P H1 H2 H3 H4 H5 H6 H7 H8. fix 1.
  destruct e; try (now clear exp_ind'; eauto).
  - eapply H1. eapply exp_ind'; eauto.
  - induction l as [ | [c e] xs IHxs].
    + eapply H2.
    + eapply H3. apply exp_ind'. eauto.
  - eapply H4. eapply exp_ind'; eauto.
  - eapply H5. eapply exp_ind'; eauto.
  - eapply H7. eapply exp_ind'; eauto.
Qed.

(** Mutual induction scheme for exp and fundefs *)
Lemma exp_mut :
  forall (P : exp -> Type) (P0 : fundefs -> Type),
    (forall (v : var) (t : cTag) (l : list var) (e : exp),
        P e -> P (Econstr v t l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (cTag * exp)) (c : cTag) (e : exp),
        P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
        P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
    (forall (v : var) (p : prim) (l : list var) (e : exp),
        P e -> P (Eprim v p l e)) ->
    (forall (v : var), P (Ehalt v)) ->
    (forall (v : var) (t : fTag) (l : list var) (e : exp),
        P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> forall e : exp, P e                                 
with fundefs_mut :
       forall (P : exp -> Type) (P0 : fundefs -> Type),
         (forall (v : var) (t : cTag) (l : list var) (e : exp),
             P e -> P (Econstr v t l e)) ->
         (forall (v : var), P (Ecase v nil)) ->
         (forall (v : var) (l : list (cTag * exp)) (c : cTag) (e : exp),
             P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
         (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
             P e -> P (Eproj v t n v0 e)) ->
         (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
         (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
         (forall (v : var) (p : prim) (l : list var) (e : exp),
             P e -> P (Eprim v p l e)) ->
         (forall (v : var), P (Ehalt v)) ->
         (forall (v : var) (t : fTag) (l : list var) (e : exp),
             P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
         P0 Fnil -> forall f7 : fundefs, P0 f7.
Proof.
  - intros P1 P2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. 
    destruct e; eauto.
    + eapply H1. eapply exp_mut; eauto.
    + induction l as [ | [c e] xs IHxs].
      * eapply H2.
      * eapply H3; eauto. eapply exp_mut; eauto.
    + eapply H4. eapply exp_mut; eauto.
    + eapply H5. eapply fundefs_mut; eauto.
      eapply exp_mut; eauto.
    + eapply H7. eapply exp_mut; eauto.
  - intros P1 P2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 defs. 
    destruct defs; eauto.
    eapply H9. eapply exp_mut; eauto.
    eapply fundefs_mut; eauto.
Qed.


Lemma exp_mut_alt :
  forall (P : exp -> Prop) (P0 : fundefs -> Prop),
    (forall (v : var) (t : cTag) (l : list var) (e : exp),
        P e -> P (Econstr v t l e)) ->
    (forall (v : var) (l : list (cTag * exp)),
       Forall (fun x => P (snd x)) l -> P (Ecase v l)) ->
    (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
        P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
    (forall (v : var) (p : prim) (l : list var) (e : exp),
        P e -> P (Eprim v p l e)) ->
    (forall (v : var), P (Ehalt v)) ->
    (forall (v : var) (t : fTag) (l : list var) (e : exp),
        P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> forall e : exp, P e                                 
with fundefs_mut_alt :
       forall (P : exp -> Prop) (P0 : fundefs -> Prop),
         (forall (v : var) (t : cTag) (l : list var) (e : exp),
             P e -> P (Econstr v t l e)) ->
         (forall (v : var) (l : list (cTag * exp)),
             Forall (fun x => P (snd x)) l -> P (Ecase v l)) ->
         (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
             P e -> P (Eproj v t n v0 e)) ->
         (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
         (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
         (forall (v : var) (p : prim) (l : list var) (e : exp),
             P e -> P (Eprim v p l e)) ->
         (forall (v : var), P (Ehalt v)) ->
         (forall (v : var) (t : fTag) (l : list var) (e : exp),
             P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
         P0 Fnil -> forall f7 : fundefs, P0 f7.
Proof.
  - intros P1 P2 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
    destruct e; eauto.
    + eapply H1. eapply exp_mut_alt; eauto.
    + eapply H2. induction l as [ | [c e] xs IHxs].
      now constructor.
      constructor; [| eassumption ]. eapply exp_mut_alt; eauto.
    + eapply H3. eapply exp_mut_alt; eauto.
    + eapply H4. eapply fundefs_mut_alt; eauto.
      eapply exp_mut_alt; eauto.
    + eapply H6. eapply exp_mut_alt; eauto.
  - intros P1 P2 H1 H2 H3 H4 H5 H6 H7 H8 H9 defs. 
    destruct defs; eauto.
    eapply H8. eapply exp_mut_alt; eauto.
    eapply fundefs_mut_alt; eauto.
Qed.

(* to do proofs simultaneously. *)
Lemma exp_def_mutual_ind :
  forall (P : exp -> Prop) (P0 : fundefs -> Prop),
    (forall (v : var) (t : cTag) (l : list var) (e : exp),
        P e -> P (Econstr v t l e)) ->
    (forall (v : var), P (Ecase v nil)) ->
    (forall (v : var) (l : list (cTag * exp)) (c : cTag) (e : exp),
        P e -> P (Ecase v l) -> P (Ecase v ((c, e) :: l))) ->
    (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
        P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
    (forall (v : var) (p : prim) (l : list var) (e : exp),
        P e -> P (Eprim v p l e)) ->
    (forall (v : var), P (Ehalt v)) ->
    (forall (v : var) (t : fTag) (l : list var) (e : exp),
        P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> (forall e : exp, P e) /\ (forall f : fundefs, P0 f).
Proof.
  intros. split.
  apply (exp_mut P P0); assumption.
  apply (fundefs_mut P P0); assumption.
Qed.

Lemma exp_def_mutual_ind' :
  forall (P : exp -> Prop) (P0 : fundefs -> Prop),
    (forall (v : var) (t : cTag) (l : list var) (e : exp),
        P e -> P (Econstr v t l e)) ->
    (forall (v : var) (l : list (cTag * exp)),
        Forall (fun x => P (snd x)) l -> P (Ecase v l)) ->
    (forall (v : var) (t : cTag) (n : N) (v0 : var) (e : exp),
        P e -> P (Eproj v t n v0 e)) ->
    (forall f2 : fundefs, P0 f2 -> forall e : exp, P e -> P (Efun f2 e)) ->
    (forall (v : var) (t : fTag) (l : list var), P (Eapp v t l)) ->
    (forall (v : var) (p : prim) (l : list var) (e : exp),
        P e -> P (Eprim v p l e)) ->
    (forall (v : var), P (Ehalt v)) ->
    (forall (v : var) (t : fTag) (l : list var) (e : exp),
        P e -> forall f5 : fundefs, P0 f5 -> P0 (Fcons v t l e f5)) ->
    P0 Fnil -> (forall e : exp, P e) /\ (forall f : fundefs, P0 f).
Proof.
  intros. split.
  apply (exp_mut_alt P P0); assumption.
  apply (fundefs_mut_alt P P0); assumption.
Qed.


(** name the induction hypotheses only *)
Ltac exp_defs_induction IH1 IHl IH2 :=
  apply exp_def_mutual_ind;
  [ intros ? ? ? ? IH1 
  | intros ?
  | intros ? ? ? ? IH1 IHl 
  | intros ? ? ? ? ? IH1
  | intros ? IH2 ? IH1 
  | intros ? ? ?
  | intros ? ? ? ? IH1
  | intros ?
  | intros ? ? ? ? IH1 ? IH2
  | ].

(** * CPS Values *)

Inductive val : Type :=
| Vconstr: cTag -> list val -> val
| Vfun: M.t val -> fundefs -> var -> val
(* [Vfun env fds f]
     where env is the environment at the function binding site
     fds is the list of mutually recursive functions including f *)
| Vint: Z -> val.


(** Induction principle for values. *)
Lemma val_ind' :
  forall P : val -> Prop,
    (forall (t : cTag), P (Vconstr t nil)) ->
    (forall (t : cTag) (v : val) (l : list val),
        P v -> P (Vconstr t l) -> P (Vconstr t (v :: l))) ->
    (forall (t : M.t val) (f0 : fundefs) (v : var), P (Vfun t f0 v)) ->
    (forall z : Z, P (Vint z)) ->
    forall v : val, P v.
Proof.
  intros P H1 H2 H3 H4.
  fix 1.
  destruct v; try (now clear val_ind'; eauto).
  - induction l as [ | x xs IHxs].
    eapply H1. eapply H2. apply val_ind'. eauto.
Qed.

Fixpoint def_funs (fl0 fl: fundefs) (rho0 rho: M.t val) : M.t val :=
  match fl with
  | Fcons f t xs e fl' => M.set f (Vfun rho0 fl0 f) (def_funs fl0 fl' rho0 rho)
  | Fnil => rho
  end.

Fixpoint find_def (f: var) (fl:  fundefs) :=
  match fl with
  | Fcons f' t ys e fl' => if M.elt_eq f f' then Some (t,ys,e)
                          else find_def f fl'
  | Fnil => None
  end.

(** * Information associated with identifiers Identifier info **)

(** The info of a constructor. Includes: the name of the constructor
                                         the name of its inductive type
                                         iTag of corresponding inductive type
                                         the constructor's arity
                                         the cTags ordinal in inductive defn starting at zero *)

Definition cTyInfo : Type := name * name * iTag * N * N.

(* The info of an inductive type is list of the ctags of its constructors *)
Definition iTyInfo : Type := list (cTag * N). 

Definition unkown_cTyInfo : cTyInfo := (nAnon, nAnon, 1%positive, 0%N, 0%N).

Definition unkown_iTyInfo : iTyInfo := nil.

Definition cEnv := M.t cTyInfo.  (* An constructor environment maps [cTag]s to their information *)

Definition iEnv := M.t iTyInfo. (* An inductive type environment maps [iTag]s to their constructors with their arities *)

Definition fTyInfo : Type := N * list N. (* every calling convention requires knowing how many
                                            arguments in which slots of the arg array *)

Definition fEnv: Type := M.t fTyInfo.

(** Register the tag used for closures **)
Definition add_cloTag (c i : positive) (cenv : cEnv) : cEnv :=
  M.set c (nAnon, nAnon, i, 2%N, 0%N) cenv.

