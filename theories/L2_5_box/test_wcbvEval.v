
Require Import Recdef.
Require Import omega.Omega.
Require Import Template.Template.
Require Import Common.Common.
Require Import L2_5.compile.
Require Import L2_5.term.
Require Import L2_5.wcbvEval.
Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.


Notation NN := (mkInd "Coq.Init.Datatypes.nat" 0).
Notation SS := (TConstruct NN 1 1).
Notation ZZ := (TConstruct NN 0 0).
Notation LL := (mkInd "Coq.Init.Datatypes.list" 0).
Notation CONS := (TConstruct LL 1).
Notation NIL := (TConstruct LL 0).
Notation VSR := (mkInd "Benchmarks.vs.VeriStar.veristar_result" 0).
Notation VSR_Val := (TConstruct VSR 0).
Notation VSR_Modl := (TConstruct VSR 1).
Notation VSR_Abrt := (TConstruct VSR 2).
Notation Lam := (TLambda).
Notation tLam := (tLambda).
Notation tPi := (tProd).
Notation tPROP := (tSort sProp).
Notation AND := (mkInd "Coq.Init.Logic.and" 0).
Notation CONJ := (TConstruct AND 0 4).
Notation TRUE := (mkInd "Coq.Init.Logic.True" 0).
Notation II := (TConstruct TRUE 0 0).
Notation EQ := (mkInd "Coq.Init.Logic.eq" 0).
Notation RFL := (TConstruct EQ 0 2).
Notation PROD := (mkInd "Coq.Init.Datatypes.prod" 0).
Notation PAIR := (TConstruct PROD 0 4).
Notation "^ x" := (nNamed x)  (at level 85).
Notation "^" := (nAnon).
Infix ":t:" := tcons  (at level 87, right associativity).
Notation "fn [| arg @ args |]" :=
  (TApp fn arg args)  (at level 90, left associativity).


(********* is my ascii_eq_bool really better?  *************
Require Import String.
Definition str1:= "poiiopoiuypiuyouytitrytyuyreutrsyeagafdsvcdsfbdsgfdjhgfkjhgjhgllkhjgljhghjgljkhlhjfkghfjfgshxfcmnbvnbcmbncxnvdshgjf,hmb,mjb,jhfjdf,mnbzxc,mvnblaksdjhfgldiygdlgdlsahjcghjgclygfdljchbdlskcgewljdhglkadjsghdljqwegdlqwjdghalsjcglqgdlsajhcglsacjhgsalcjhgalcjhgdslcjhgdslcjhdglchjdglcjhdgcldjhcgldjhcgdlchg".
Definition str2:= "piuwe;kjh;kjhfsdkjh;diufg;sdkfg;dskcgleytoewiuryepqwoifwoiweofhwe;fuhwe;fkuhf;kehf;khdsa;kjdashf;kdsjhfd;skjfhd;kfjdhflkdjfhdlueifduefiewhf;kjhasdkuhgdpiqwugdkqwjhdglsajch;skcjhqweudyewpiqufy;kvcjb.jb.mxzcncbcxz.mcnbadsljhfglqjhdgasmcjbsa,mcnbscmnb,cmnbc,mxzhcgasljhdgsaljhglasjhdglashdgsajhgsahjgsl".
Time Eval cbv in String.string_dec str1 str1.
Time Eval cbv in String.string_dec str1 str2.
Time Eval cbv in String.string_dec str2 str1.
Time Eval cbv in String.string_dec str2 str2.
Time Eval cbv in string_eq_bool str1 str1.
Time Eval cbv in string_eq_bool str1 str2.
Time Eval cbv in string_eq_bool str2 str1.
Time Eval cbv in string_eq_bool str2 str2.
******************  yes *****************************)

Set Implicit Arguments.
Set Template Cast Propositions. 
Set Printing Width 80.
Set Printing Depth 1000.

Quote Recursively Definition p_Type := Type.
Print p_Type.
Definition P_Type := Eval cbv in (program_Program p_Type).
Print P_Type.

Definition PropInType (b:bool) : Type :=
  if b then True else nat.
Definition aPropInType (b:bool) : PropInType b :=
  match b with
    | true => I 
    | false => 0
  end.
Recursive Extraction aPropInType.

Quote Recursively Definition p_aPropInType := aPropInType.
Definition P_aPropInType := Eval cbv in (program_Program p_aPropInType).
Print P_aPropInType.
Quote Recursively Definition p_aPropInType_t := (aPropInType true).
Quote Recursively Definition p_aPropInType_f := (aPropInType false).
Definition P_aPropInType_t := Eval cbv in (program_Program p_aPropInType_t).
Print P_aPropInType_t.
Definition P_aPropInType_f := Eval cbv in (program_Program p_aPropInType_f).
Definition P_env_aPropInType_t := Eval vm_compute in (env P_aPropInType_t).
Definition P_env_aPropInType_f := Eval vm_compute in (env P_aPropInType_f).
Definition P_main_aPropInType_t := Eval vm_compute in (main P_aPropInType_t).
Definition P_main_aPropInType_f := Eval vm_compute in (main P_aPropInType_f).
Eval vm_compute in
    wcbvEval P_env_aPropInType_t 10 P_main_aPropInType_t.
Eval vm_compute in (aPropInType true).
Eval vm_compute in
    wcbvEval P_env_aPropInType_f 10 P_main_aPropInType_f.
Eval vm_compute in (aPropInType false).


Definition listn (A:Type) (n:nat) := {l:list A | length l = n }.
Definition anEmptyList : listn nat 0 := exist _ nil eq_refl.
Eval vm_compute in anEmptyList.
(****
     = exist (fun l : list nat => length l = 0) nil eq_refl
     : listn nat 0
********)
Quote Recursively Definition p_anEmptyList := anEmptyList.
Definition P_anEmptyList :=
  Eval vm_compute in (program_Program p_anEmptyList).
Print P_anEmptyList.
Eval vm_compute in (wcbvEval (env P_anEmptyList) 20 (main P_anEmptyList)).

(**********
Inductive bar: Prop := Bar1 | Bar2.
Definition foo (p:and bar bar) : bool -> (bar /\ bar) :=
  match p with
      conj a b => fun (_:bool) => conj a a
  end.
Quote Recursively Definition p_foo := foo.
Print p_foo.
Eval cbv in (program_Program p_foo).
Print list.
Check cons.
Print eq.
Check eq_refl.
Print eq_rect.

Inductive oa (b:bool): Prop -> Prop :=  OA: forall x:Prop, oa b x.
Print oa.
Definition prop_match_1_args (b:bool) (x:Prop) (p:oa b x) : Prop :=
  match p with OA _ y => y end.
Quote Recursively Definition p_prop_match_1_args := prop_match_1_args.
Print p_prop_match_1_args.
Eval cbv in (program_Program p_prop_match_1_args).
Quote Recursively Definition p_prop_match_1_args_x :=
  (prop_match_1_args (OA true)).
Definition P_prop_match_1_args_x :=
  Eval cbv in (program_Program p_prop_match_1_args_x).
Print P_prop_match_1_args_x.
Definition P_env_prop_match_1_args_x :=
  Eval vm_compute in (env P_prop_match_1_args_x).
Definition P_main_prop_match_1_args_x :=
  Eval vm_compute in (main P_prop_match_1_args_x).
Eval vm_compute in
    wcbvEval P_env_prop_match_1_args_x 10 P_main_prop_match_1_args_x.
*********************)


Inductive P0: Prop := p0.
Inductive P1: Prop := p1.
Notation PP0 := (mkInd "P0" 0).
Notation pp0 := (TConstruct PP0 0 0).
Notation PP1 := (mkInd "P1" 0).
Notation pp1 := (TConstruct PP1 0 0).

(** works with [my_and_rect] **)
Definition my_and_rect := 
  fun (A B : Prop) (P : Type) (f : A -> B -> P) (a : A /\ B) =>
    match a with conj x x0 => f x x0 end.
Quote Recursively Definition p_my_and_rect := my_and_rect.
Print p_my_and_rect.
Eval cbv in (program_Program p_my_and_rect).
Definition my_and_rectx :=
  my_and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1).
Eval cbv in my_and_rectx.
Quote Recursively Definition p_my_and_rectx := my_and_rectx.
Print p_my_and_rectx.
Definition P_my_and_rectx := Eval cbv in (program_Program p_my_and_rectx).
Print P_my_and_rectx.
Quote Recursively Definition ans_my_and_rectx := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in my_and_rectx) in exact t).
Definition Ans_my_and_rectx :=
  Eval cbv in (wcbvEval (env (program_Program ans_my_and_rectx)) 1000
                        (main (program_Program ans_my_and_rectx))).
Print Ans_my_and_rectx.
Definition P_my_envx := env P_my_and_rectx.
Definition P_my_mainx := main P_my_and_rectx.
Eval cbv in (wcbvEval P_my_envx 100 P_my_mainx).
Goal wcbvEval P_my_envx 1000 P_my_mainx = Ans_my_and_rectx.
  vm_compute. reflexivity.
Qed.


(** now succeeds with library [and_rect] having eta-contracted branch **)
Quote Recursively Definition p_and_rect := and_rect.
Print p_and_rect.
Eval cbv in (program_Program p_and_rect).
Definition and_rectx :=
  and_rect (fun (x0:P0) (x1:P1) => pair (conj x1 x0) 0) (conj p0 p1).
Eval cbv in and_rectx.
Quote Recursively Definition ans_and_rectx := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in and_rectx) in exact t).
Definition Ans_and_rectx :=
  Eval cbv in (wcbvEval (env (program_Program ans_and_rectx)) 1000
                        (main (program_Program ans_and_rectx))).
Print Ans_and_rectx.
Quote Recursively Definition p_and_rectx := and_rectx.
Print p_and_rectx.
Definition P_and_rectx := Eval cbv in (program_Program p_and_rectx).
Print P_and_rectx.
Definition P_envx := env P_and_rectx.
Definition P_mainx := main P_and_rectx.
Eval cbv in (wcbvEval P_envx 100 P_mainx).
Goal wcbvEval P_envx 1000 P_mainx = Ans_and_rectx.
  vm_compute. reflexivity.
Qed.


Function Plus1 (n : nat) {wf lt n} : nat :=
  match n with
    | 0 => 1
    | S p => S (Plus1 p)
  end.
- intros. omega.
- apply lt_wf.
Defined.
Definition x:nat := 0.
Definition Plus1x := Plus1 x.
Eval vm_compute in Plus1x.

(** evaluation of [Function]s defined with measure or wf **
Time Quote Recursively Definition p_Plus1x := Plus1x.
Time Definition P_Plus1x : Program Term :=
  Eval vm_compute in program_Program p_Plus1x.
Time Definition P_env := Eval vm_compute in (env P_Plus1x).
Time Definition P_main := Eval vm_compute in (main P_Plus1x).
Time Definition P_ans := Eval vm_compute in (wcbvEval P_env 1000 P_main).
Print P_ans.
******************)

Unset Implicit Arguments.
(** Abhishek's example of looping in L1 **)
Inductive lt (n:nat) : nat -> Prop := lt_n: lt n (S n).
Inductive Acc (y: nat) : Prop :=
  Acc_intro : (forall x: nat, lt y x -> Acc x) -> Acc y.
Definition Acc_inv: forall (x:nat) (H:Acc x) (y:nat), lt x y -> Acc y.
  intros. destruct H. apply H. apply H0.
  Defined.
Fixpoint loop (n:nat) (a:Acc n) {struct a} : nat :=
  match n with
    | _ => loop (S n) (Acc_inv _ a (S n) (lt_n n))
  end.
Axiom Acc0Ax : Acc 0.
Eval vm_compute in (loop O Acc0Ax) .
Quote Recursively Definition p_loop0 := (loop 0 Acc0Ax).
Print p_loop0.


Set Implicit Arguments.


Definition Ll := list.
Quote Recursively Definition q_Ll := Ll.
Print  q_Ll.
Quote Definition q_eLl := Eval cbv in Ll.
Print  q_eLl.


(** non-recursive fixpoint has non-null Defs **)
Fixpoint tst (b:bool) : bool := true.
Print tst.
Quote Recursively Definition p_tst := tst.
Print p_tst.



Inductive foo (A:Set) : Set :=
| nilf: foo A
| consf: (fun (Y W:Set) => Y -> foo Y -> foo ((fun X Z => X) A nat)) A bool.
Quote Recursively Definition foo_nat_cons := (@consf nat 0 (nilf nat)).
Print foo_nat_cons.

Fixpoint foo_list (A:Set) (fs:foo A) : list A :=
  match fs with
    | nilf _ => nil
    | consf b bs => cons b (foo_list bs)
  end.
Fixpoint list_foo (A:Set) (fs:list A) : foo A :=
  match fs with
    | nil => nilf A
    | cons b bs => consf b (list_foo bs)
  end.
Goal forall (A:Set) (fs:list A), foo_list (list_foo fs) = fs.
induction fs; try reflexivity.
- simpl. rewrite IHfs. reflexivity.
Qed.
Goal forall (A:Set) (fs:foo A), list_foo (foo_list fs) = fs.
induction fs; try reflexivity.
- simpl. rewrite IHfs. reflexivity.
Qed.

(** indexed datatypes **)
Inductive fin : nat -> Set :=
| f0: fin 0
| fS: forall (n:nat) (f:fin n), fin (S n).

Definition fiszero (n:nat) (f:fin n) : bool :=
  match f with
    | f0 => true
    | fS _ => false
  end.
Quote Recursively Definition p_fiszero := fiszero.
Print p_fiszero.

Definition blist := (@list ((fun x:Set => x) bool)).
Quote Recursively Definition clist := blist.
Print clist.
Quote Recursively Definition bcons := (@cons bool).
Print bcons.

Definition xlist := (@list (list bool)).
Quote Definition qlist := Eval cbv in xlist.
Print qlist.
Quote Recursively Definition qcons :=
  (@cons (list bool): (list bool) -> xlist -> xlist).
Print qcons.

(** vector addition **)
Require Coq.Vectors.Vector.
Print Fin.t.
Print Vector.t.

Definition vplus (n:nat) :
  Vector.t nat n -> Vector.t nat n -> Vector.t nat n := (Vector.map2 plus).
Definition v01 : Vector.t nat 2 :=
  (Vector.cons nat 0 1 (Vector.cons nat 1 0 (Vector.nil nat))).
Definition v23 : Vector.t nat 2 :=
  (Vector.cons nat 2 1 (Vector.cons nat 3 0 (Vector.nil nat))).
Definition vplus0123 := (vplus v01 v23).
Quote Recursively Definition cbv_vplus0123 := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (vplus0123)) in exact t).
Print cbv_vplus0123.
(* [Term] of Coq's answer *)
Definition ans_vplus0123 := Eval cbv in (main (program_Program cbv_vplus0123)).
(* [program] of the program *)
Quote Recursively Definition p_vplus0123 := vplus0123.
Print p_vplus0123.
Definition P_vplus0123 := Eval cbv in (program_Program p_vplus0123).
Print P_vplus0123.
Goal
  let env := (env P_vplus0123) in
  let main := (main P_vplus0123) in
  wcbvEval (env) 100 (main) = Ret ans_vplus0123.
  vm_compute. reflexivity.
Qed.

(***
Inductive pack (A:Prop) : Prop := Pack: A -> A -> A -> A -> pack A.
Axiom packax: forall A, pack A -> pack A.
Definition pack_nat (A:Prop) (a:pack A) : nat :=
  match packax a with
    | Pack b1 b2 b3 b4 => 0
  end.
Quote Recursively Definition p_pack_nat := (pack_nat (Pack I I I I)).
Check p_pack_nat.
Definition P_pack_nat := Eval cbv in (program_Program p_pack_nat).
Print P_pack_nat.
 ***********)

Inductive xxxx : Prop :=
| xxxxl: forall n:nat, n = 0 -> xxxx
| xxxxr: forall n:nat, n = 1 -> xxxx.
Print xxxx.
Axiom Xxxx : xxxx.
Definition yyyy (f:xxxx) :=
  match f with xxxxl q => f | xxxxr q => f end.
Definition yyyyX := (yyyy Xxxx).
Print yyyyX.
Quote Recursively Definition cbv_yyyyX := (* [program] of Coq's answer *)
  ltac:(let t:=(eval cbv in (yyyyX)) in exact t).
Print cbv_yyyyX.
(* [Term] of Coq's answer *)
Definition ans_yyyyX := Eval cbv in (main (program_Program cbv_yyyyX)).
(* [program] of the program *)
Quote Recursively Definition p_yyyyX := yyyyX.
Print p_yyyyX.
Definition P_yyyyX := Eval cbv in (program_Program p_yyyyX).
Print P_yyyyX.
Goal
    let env := (env P_yyyyX) in
    let main := (main P_yyyyX) in
    wcbvEval (env) 100 (main) = Ret ans_yyyyX.
  vm_compute. reflexivity.
Qed.

(** mutual recursion **)
Set Implicit Arguments.
Inductive tree (A:Set) : Set :=
  node : A -> forest A -> tree A
with forest (A:Set) : Set :=
     | leaf : A -> forest A
     | fcons : tree A -> forest A -> forest A.

Fixpoint tree_size (t:tree bool) : nat :=
  match t with
    | node a f => S (forest_size f)
  end
with forest_size (f:forest bool) : nat :=
       match f with
         | leaf b => 1
         | fcons t f1 => (tree_size t + forest_size f1)
       end.
Quote Recursively Definition p_tree_size := tree_size.
Print p_tree_size.
Definition atree: tree bool := (node true (fcons (node true (leaf false)) (leaf true))).
Definition arden: forest bool :=
  fcons atree (fcons (node true (fcons (node true (leaf false)) (leaf true)))
                     (leaf false)).
Definition arden_size := (forest_size arden).
Quote Recursively Definition cbv_arden_size :=
  ltac:(let t:=(eval cbv in arden_size) in exact t).
Definition ans_arden_size :=
  Eval cbv in (main (program_Program cbv_arden_size)).
(* [program] of the program *)
Quote Recursively Definition p_arden_size := arden_size.
Print p_arden_size.
Quote Recursively Definition p_arden_tree_size := (tree_size atree).
Print p_arden_tree_size.
Definition P_arden_size := Eval cbv in (program_Program p_arden_size).
Print P_arden_size.
Goal
  let env := (env P_arden_size) in
  let main := (main P_arden_size) in
  wcbvEval (env) 100 (main) = Ret ans_arden_size.
  vm_compute. reflexivity.
Qed.


(** Ackermann **)
Fixpoint ack (n m:nat) {struct n} : nat :=
  match n with
    | 0 => S m
    | S p => let fix ackn (m:nat) {struct m} :=
                 match m with
                   | 0 => ack p 1
                   | S q => ack p (ackn q)
                 end
             in ackn m
  end.
Definition ack35 := (ack 3 5).
Quote Recursively Definition cbv_ack35 :=
  ltac:(let t:=(eval cbv in ack35) in exact t).
Print cbv_ack35.
Definition ans_ack35 :=
  Eval cbv in (main (program_Program cbv_ack35)).
Print ans_ack35.
(* [program] of the program *)
Quote Recursively Definition p_ack35 := ack35.
Print p_ack35.
Definition P_ack35 := Eval cbv in (program_Program p_ack35).
Print P_ack35.
Goal
  let env := (env P_ack35) in
  let main := (main P_ack35) in
  wcbvEval (env) 2000 (main) = Ret ans_ack35.
  vm_compute. reflexivity.
Qed.


(** SASL tautology function: variable arity **)
Fixpoint tautArg (n:nat) : Type :=
  match n with
    | 0 => bool
    | S n => bool -> tautArg n
  end.
Fixpoint taut (n:nat) : tautArg n -> bool :=
  match n with
    | 0 => (fun x => x)
    | S n => fun x => taut n (x true) && taut n (x false)
  end.
(* Pierce *)
Definition pierce := taut 2 (fun x y => implb (implb (implb x y) x) x).
Quote Recursively Definition cbv_pierce :=
  ltac:(let t:=(eval cbv in pierce) in exact t).
Print cbv_pierce.
Definition ans_pierce :=
  Eval cbv in (main (program_Program cbv_pierce)).
Print ans_pierce.
(* [program] of the program *)
Quote Recursively Definition p_pierce := pierce.
Print p_pierce.
Definition P_pierce := Eval cbv in (program_Program p_pierce).
Print P_pierce.
Goal
  let env := (env P_pierce) in
  let main := (main P_pierce) in
  wcbvEval (env) 2000 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.
(* S combinator *)
Definition Scomb := taut 3
         (fun x y z => implb (implb x (implb y z))
                             (implb (implb x y) (implb x z))).
Quote Recursively Definition cbv_Scomb :=
  ltac:(let t:=(eval cbv in Scomb) in exact t).
Print cbv_Scomb.
Definition ans_Scomb :=
  Eval cbv in (main (program_Program cbv_Scomb)).
Print ans_Scomb.
(* [program] of the program *)
Quote Recursively Definition p_Scomb := Scomb.
Print p_Scomb.
Definition P_Scomb := Eval cbv in (program_Program p_Scomb).
Print P_Scomb.
Goal
  let env := (env P_Scomb) in
  let main := (main P_Scomb) in
  wcbvEval (env) 2000 (main) = Ret ans_pierce.
  vm_compute. reflexivity.
Qed.

Inductive uuyy: Set := uu | yy.
Inductive wwzz: Set := ww (_:uuyy)| zz (_:nat) (_:uuyy) (_:bool).
Definition Foo : nat -> bool -> wwzz -> wwzz := 
  fun (n:nat) (b:bool) (x:wwzz) =>
    match n,x,b with
      | 0, _, true => ww uu
      | 0, _, false => ww yy
      | S m, ww x, b => zz m x b
      | S m, zz n x c, b => zz m x b
    end.
Definition Foo0ty := (Foo 0 true (ww uu)).
Quote Recursively Definition cbv_Foo0ty :=
  ltac:(let t:=(eval cbv in Foo0ty) in exact t).
Definition ans_Foo0ty :=
  Eval cbv in (main (program_Program cbv_Foo0ty)).
(* [program] of the program *)
Quote Recursively Definition p_Foo0ty := Foo0ty.
Definition P_Foo0ty := Eval cbv in (program_Program p_Foo0ty).
Goal
  let env := (env P_Foo0ty) in
  let main := (main P_Foo0ty) in
  wcbvEval (env) 30 (main) = Ret ans_Foo0ty.
  vm_compute. reflexivity.
Qed.

(** Fibonacci **)
Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Definition slowFib3 := (slowFib 3).
Quote Recursively Definition cbv_slowFib3 :=
  ltac:(let t:=(eval cbv in slowFib3) in exact t).
Definition ans_slowFib3 :=
  Eval cbv in (main (program_Program cbv_slowFib3)).
(* [program] of the program *)
Quote Recursively Definition p_slowFib3 := slowFib3.
Definition P_slowFib3 := Eval cbv in (program_Program p_slowFib3).
Goal
  let env := (env P_slowFib3) in
  let main := (main P_slowFib3) in
  wcbvEval (env) 30 (main) = Ret ans_slowFib3.
  vm_compute. reflexivity.
Qed.

(* fast Fib *)
Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).
Definition fib9 := fib 9.
Quote Recursively Definition cbv_fib9 :=
  ltac:(let t:=(eval cbv in fib9) in exact t).
Definition ans_fib9 :=
  Eval cbv in (main (program_Program cbv_fib9)).
(* [program] of the program *)
Quote Recursively Definition p_fib9 := fib9.
Definition P_fib9 := Eval cbv in (program_Program p_fib9).
Goal
  let env := (env P_fib9) in
  let main := (main P_fib9) in
  wcbvEval (env) 1000 (main) = Ret ans_fib9.
  vm_compute. reflexivity.
Qed.

(** Heterogenous datatypes, a la Matthes **)
Inductive PList : Set->Type:=  (* powerlists *)
| zero : forall A:Set, A -> PList A
| succ : forall A:Set, PList (A * A)%type -> PList A.

Definition myPList : PList nat :=
  succ (succ (succ (zero (((1,2),(3,4)),((5,6),(7,8)))))).

Fixpoint unzip (A:Set) (l:list (A*A)) {struct l} : list A :=
  match l return list A with
    | nil => nil
    | cons (a1,a2) l' => cons a1 (cons a2 (unzip l'))
  end.
Fixpoint PListToList (A:Set) (l:PList A) {struct l} : list A :=
  match l in PList A return list A with
    | zero a => cons a (nil )
    | succ l' => unzip (PListToList l')
  end.

Eval compute in PListToList myPList.

Fixpoint gen_sumPList (A:Set) (l:PList A) {struct l} : (A->nat)->nat :=
  match l in PList A return (A->nat)->nat with
    | zero a => fun f => f a
    | succ l' =>
      fun f => gen_sumPList l' (fun a => let (a1,a2) := a in f a1 + f a2)
  end.
Definition sumPList l := gen_sumPList l (fun x => x).
Definition sumPL_myPL := (sumPList myPList).
Quote Recursively Definition cbv_sumPL_myPL :=
  ltac:(let t:=(eval cbv in sumPL_myPL) in exact t).
Definition ans_sumPL_myPL :=
  Eval cbv in (main (program_Program cbv_sumPL_myPL)).
(* [program] of the program *)
Quote Recursively Definition p_sumPL_myPL := sumPL_myPL.
Definition P_sumPL_myPL := Eval cbv in (program_Program p_sumPL_myPL).
Goal
  let env := (env P_sumPL_myPL) in
  let main := (main P_sumPL_myPL) in
  wcbvEval (env) 1000 (main) = Ret ans_sumPL_myPL.
  vm_compute. reflexivity.
Qed.

Set Implicit Arguments.
Section List.
Variables X Y : Type.
Variable f : X -> Y -> Y.
Fixpoint fold (y : Y) (xs : list X) : Y :=
  match xs with
    | nil => y
    | cons x xr => fold (f x y) xr
  end.
End List.
Inductive Tree := T : list Tree -> Tree.
Fixpoint size (t : Tree) : nat :=
  match t with
    | T ts => S (fold (fun t a => size t + a) 0 ts)
  end.
Definition myTree := (T (cons (T (unit (T nil))) (cons (T (unit (T nil))) nil))).
Eval cbv in size myTree.
Definition size_myTree := size myTree.
Quote Recursively Definition cbv_size_myTree :=
  ltac:(let t:=(eval cbv in size_myTree) in exact t).
Definition ans_size_myTree :=
  Eval cbv in (main (program_Program cbv_size_myTree)).
(* [program] of the program *)
Quote Recursively Definition p_size_myTree := size_myTree.
Definition P_size_myTree := Eval cbv in (program_Program p_size_myTree).
Goal
  let env := (env P_size_myTree) in
  let main := (main P_size_myTree) in
  wcbvEval (env) 1000 (main) = Ret ans_size_myTree.
  vm_compute. reflexivity.
Qed.


Function Gcd (a b : nat) {wf Coq.Init.Peano.lt a} : nat :=
match a with
 | O => b 
 | S k =>  Gcd (b mod S k)  (S k)
end.
Proof.
  - intros m n k Heq. subst. apply Nat.mod_upper_bound.
    intros h. discriminate.
  - exact lt_wf.
Defined.
Definition Gcdx := (Gcd 4 2).
Eval vm_compute in Gcdx.
(*** works, quickly ***)
Time Quote Recursively Definition pGcdx := Gcdx.
Time Definition PGcdx := Eval cbv in (L2_5.compile.program_Program pGcdx).
Time Definition Penv_Gcdx := env PGcdx.
Time Definition Pmain_Gcdx := main PGcdx.
Time Definition ans_Gcdx :=
 Eval vm_compute in (wcbvEval Penv_Gcdx 1000 Pmain_Gcdx).
Print ans_Gcdx.


Require Import Benchmarks.vs.

(********************)
Time Quote Recursively Definition p_myMain := vs.myMain.
Time Definition P_myMain :=
  Eval vm_compute in (L2_5.compile.program_Program p_myMain).
Definition P_env_myMain := env P_myMain.
Definition P_main_myMain := AstCommon.main P_myMain.
Time Definition eval_myMain :=
  Eval vm_compute in (wcbvEval P_env_myMain 4000 P_main_myMain).
Set Printing Width 80.
Print eval_myMain.

(****** works, quickly *****
Time Quote Recursively Definition p_ce_example_myent := vs.ce_example_myent.
Time Definition P_ce_example_myent :=
  Eval vm_compute in (L2_5.compile.program_Program p_ce_example_myent).
Definition P_env_ce_example_myent := env P_ce_example_myent.
Definition P_main_ce_example_myent := AstCommon.main P_ce_example_myent.
Time Definition eval_ce_example_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example_myent 4000 P_main_ce_example_myent).
Print eval_ce_example_myent.
 ****************)
(****** works, quickly **********
Time Quote Recursively Definition p_ce_example1_myent := vs.ce_example1_myent.
Time Definition P_ce_example1_myent :=
  Eval vm_compute in (L2_5.compile.program_Program p_ce_example1_myent).
Definition P_env_ce_example1_myent := env P_ce_example1_myent.
Definition P_main_ce_example1_myent := AstCommon.main P_ce_example1_myent.
Time Definition eval_ce_example1_myent :=
  Eval vm_compute in
    (wcbvEval P_env_ce_example1_myent 4000 P_main_ce_example1_myent).
Print eval_ce_example1_myent.
 ****************)
(**** succeeds ***
Time Quote Recursively Definition p_ce_example_ent := vs.ce_example_ent.
Time Definition P_ce_example_ent: Program Term :=
  Eval vm_compute in (L2_5.compile.program_Program p_ce_example_ent).
Time Definition P_env_ce_example_ent := env P_ce_example_ent.
Time Definition P_main_ce_example_ent := AstCommon.main P_ce_example_ent.
Time Definition eval_ce_example_ent :=
  Eval vm_compute in (wcbvEval P_env_ce_example_ent 3000 P_main_ce_example_ent).
Print eval_ce_example_ent.

Require Import Ascii String ExtrOcamlString.
Require Import extraction.ExtrOcamlNatInt.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Definition cee := (wcbvEval P_env_ce_example_ent 10000 P_main_ce_example_ent).
Extraction "ce_example_ent" cee.

Print Assumptions vs.main.
Time Quote Recursively Definition p_vs := vs.main.
Time Definition P_vs := Eval cbv in (program_Program p_vs).
Time Definition P_env_vs := env P_vs.
Time Definition P_main_vs := AstCommon.main P_vs.
Time Definition eval_vs := Eval cbv in (wcbvEval P_env_vs 200 P_main_vs).
Set Printing Width 150.
Print eval_vs.
**********************)
