Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Import RelationClasses.


Require compcert.lib.Maps.
Require Import ExtLib.Data.Bool.
Require Coq.funind.Recdef.
Require Import compcert.lib.Coqlib.
Import Nnat.
Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec.
Require Import Libraries.CpdtTactics Coq.Sorting.Permutation.
Require Import Libraries.HashMap.
Require Import Libraries.maps_util.
Require Import L6.Ensembles_util.

Require Import L6.cps.
Require Import L6.ctx L6.logical_relations.
Require Import L6.cps_util L6.List_util L6.shrink_cps L6.eval L6.set_util L6.identifiers L6.stemctx L6.alpha_conv L6.functions.

Open Scope ctx_scope.

Ltac pi0 :=
  repeat match goal with
         | [ H: _ + _ = 0 |- _ ] =>
           apply plus_is_O in H; destruct H; subst
         | [ H: 0 = _ + _ |- _ ] =>
           symmetry in H
         | [ H: (if cps_util.var_dec ?X ?Y then _ else _) = 0 |- _] =>
           destruct (cps_util.var_dec X Y); try inversion H; pi0
         | [ H: ?X <> ?X |- _] =>
           exfalso; apply H; auto
         end.

(* TODO move *)
Theorem find_def_rename: forall f t xs e sigma fds,
    find_def f fds = Some (t, xs, e) ->
    find_def f (rename_all_fun sigma fds) = Some (t, xs, rename_all (remove_all sigma xs) e).
Proof.
  induction fds; intros.
  - simpl in *. destruct (M.elt_eq f v).
    + subst; inversion H; reflexivity.
    + apply IHfds; auto.
  -   inversion H.
Qed.


Theorem split_fds_nil:
  (forall fds fds',
      split_fds Fnil fds fds' -> fds = fds') /\
  (forall fds fds',
      split_fds fds Fnil fds' -> fds = fds').
Proof.
  split; induction fds; intros; inversion H; subst.
  erewrite IHfds; eauto.
  reflexivity.
  erewrite IHfds; eauto.
  reflexivity.
Qed.

(** general rewrite rules that preserves semantics
    - Fun_inline replaces one occurence on f by its definition
    - Fun_dead removes the definition of a set of functions if none of them occur free in the rest of the program
    - Fun_rm removes a function if it doesn't occur anywhere in its mutual bundle or in the rest of the term
    -  Constr_dead removes the binding of a datatype when it doesn't occur free in the rest of the program
    -  Constr_proj replaces a binding by the nth projection of a datatype when the datatype is known (in ctx)
    -  Constr_case reduces a pattern match into an application of the right continuation on the datatype when the
        datatype is known
 *)

Inductive rw (S : Ensemble var) : relation exp :=
(* Rules about dead var elimination *)
| Constr_dead:
    forall x t ys e,
      ~ occurs_free e x ->
      rw S (Econstr x t ys e) e
| Prim_dead:
    forall x p ys e,
      ~ occurs_free e x ->
      rw S (Eprim x p ys e) e
| Proj_dead:
    forall x t n y e,
      ~ occurs_free e x ->
      rw S (Eproj x t n y e) e
| Fun_dead:
    forall e fds,
      Forall (fun v => ~ occurs_free e v) (all_fun_name fds) ->
      rw S (Efun fds e) e
| Fun_rem:
    forall f t xs fb B1 B2 e,
      unique_functions (fundefs_append B1 (Fcons f t xs fb B2)) ->
      (* Zoe : This will not delete unused rec. functions. *)
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      rw S (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)
(* Rules about inlining/constant-folding *)
| Constr_case:
    forall x c cl co n e ys,
      find_tag_nth cl co e n ->
      (* x isn't shadowed on the way to the case statement *)
      ~ bound_stem_ctx c x ->
      rw S (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))

| Constr_proj:
    forall v t t' n x e k ys c,
      (* nothing shadows constructor x or var k in c *)
      ~ bound_stem_ctx c x ->
      ~ bound_stem_ctx c k ->
      (* nothing rebinds k in e *)
      ~ bound_var e k ->
      x <> k ->
      v <> k ->
      nthN ys n = Some k ->
      rw S (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename k v e]|))
| Fun_inline:
    forall c vs f t xs fb  fds,
      find_def f fds = Some (t, xs, fb) ->
      (* nothing rebinds vs in \xs.fb *)
      Disjoint _ (FromList xs :|: bound_var fb) (FromList vs) ->
      unique_functions fds ->
      (* nothing shadows the names and FV of fds in cμ   *)
      Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
      Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->
      List.NoDup xs ->
      rw S (Efun fds (c |[ Eapp f t vs ]|)) (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|))
| Fun_inline_letapp:
    forall c vs x f t xs e1 fb fds z z' C',
      find_def f fds = Some (t, xs, fb) ->
      (* nothing rebinds vs in \xs.fb *)
      Disjoint _ (FromList xs :|: bound_var fb) (FromList vs) ->
      unique_functions fds ->
      (* nothing shadows the names and FV of fds in cμ   *)
      Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
      Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->
      List.NoDup xs ->

      z \in S ->
            inline_letapp (rename_all (set_list (combine xs vs) (M.empty var)) fb) z = Some (C', z') ->

            rw S (Efun fds (c |[ Eletapp x f t vs e1]|)) (Efun fds (c |[ C' |[ e1 ]| ]|)).


Fixpoint collect_funvals (fds:fundefs)  : list (var * svalue) :=
  match fds with
  | Fnil => []
  | Fcons v t ys e fds' => ( v, (SVfun t ys e))::(collect_funvals fds')
  end.

Inductive gen_rw S : relation exp :=
| Ctx_rw :
    forall c e e', rw S e e' -> gen_rw S (c |[ e ]|) (c |[ e' ]|).

Definition gr_clos S := clos_refl_trans exp (gen_rw S).

Section Shrink_correct.

  Variable pr : prims.
  Variable cenv : ctor_env.

  Variable (P1 :  PostT) (PG : PostGT)
           (HPost_con : post_constr_compat P1 P1)
           (HPost_proj : post_proj_compat P1 P1)
           (HPost_fun : post_fun_compat P1 P1)
           (HPost_case_hd : post_case_compat_hd P1 P1)
           (HPost_case_tl : post_case_compat_tl P1 P1)
           (HPost_app : post_app_compat P1 PG)
           (HPost_letapp : post_letapp_compat cenv P1 P1 PG)
           (HPost_letapp_OOT : post_letapp_compat_OOT P1 PG)
           (HPost_OOT : post_OOT P1)
           (Hpost_base : post_base P1)
           (HGPost : inclusion _ P1 PG)

           (HPost_conG : post_constr_compat PG PG)
           (HPost_projG : post_proj_compat PG PG)
           (HPost_funG : post_fun_compat PG PG)
           (HPost_case_hdG : post_case_compat_hd PG PG)
           (HPost_case_tlG : post_case_compat_tl PG PG)
           (HPost_appG : post_app_compat PG PG)
           (HPost_letappG : post_letapp_compat cenv PG PG PG)
           (HPost_letapp_OOTG : post_letapp_compat_OOT PG PG)
           (HPost_OOTG : post_OOT PG)
           (Hpost_baseG : post_base PG).

  (* TODO move *)
  Lemma preord_val_constr :
    forall k t vl x,
      preord_val cenv PG k (cps.Vconstr t vl) x  ->
      exists vl', x = cps.Vconstr t vl' /\ Forall2_asym (preord_val cenv PG k) vl vl'.
  Proof.
    intros. eapply preord_val_eq in H.
    destruct x. simpl in H.
    destructAll. eauto.
    destruct H. destruct H.
  Qed.

  (* TODO move *)
  Lemma not_occur_list_not_in:
    forall v l, num_occur_list l v = 0 <-> ~ List.In  v l.
  Proof.
    induction l; split; intros.
    - intro. inversion H0.
    - auto.
    - intro. inversion H0.
      + subst. simpl in H.
        unfold cps_util.var_dec in *.
        destruct (M.elt_eq v v).
        inversion H. apply n; auto.
      + inversion H.
        apply IHl. destruct (cps_util.var_dec v a).
        inversion H3. auto. auto.
    - simpl.
      destruct (cps_util.var_dec v a).
      exfalso. apply H. constructor. auto.
      apply IHl. intro. apply H. constructor 2. auto.
  Qed.

  Lemma not_occurs_not_free:
    forall v, (forall e, num_occur e v 0 -> ~ occurs_free e v ) /\
         (forall f, num_occur_fds f v 0 -> ~ occurs_free_fundefs f v ).
  Proof.
    intro v.
    exp_defs_induction IHe IHl IHB; intros Hnum Hc; try (inv Hc; inv Hnum; pi0);
      (try now eapply not_occur_list_not_in; eauto);
      (try now eapply IHe; eauto).
    - inv H2; eauto. pi0. eapply IHe; eauto.
    - inv H. inv H2; eauto. pi0. eapply IHl; eauto.
      replace 0 with (num_occur_list [v0] v + 0).
      now constructor.
      simpl. destruct (cps_util.var_dec v v0). exfalso; auto. auto.
    - inv H5; eauto. eapply not_occur_list_not_in; eauto.
    - eapply IHB; eauto.
    - eapply IHB; eauto.
  Qed.


  Lemma preord_env_P_set_not_in_P_l':
    forall (pr : prims) (cenv : ctor_env) (x : var) (v : val)
      (P : Ensemble var) (k : nat) (rho1 rho2 : env),
      preord_env_P cenv P1 P k (M.set x v rho1) rho2 ->
      Disjoint var P (Singleton var x) ->
      preord_env_P cenv P1 P k rho1 rho2.
  Proof.
    intros; intro; intro; intro; intros.
    apply H. auto.
    rewrite M.gso; auto.
    intro.
    subst.
    inv H0.
    specialize (H3 x).
    apply H3. auto.
  Qed.

  Lemma preord_env_P_set_not_in_P_r':
    forall (pr : prims) (cenv : ctor_env) (x : var) (v : val)
      (P : Ensemble var) (k : nat) (rho1 rho2 : env),
      preord_env_P cenv P1 P k rho1 (M.set x v rho2) ->
      Disjoint var P (Singleton var x) ->
      preord_env_P cenv P1 P k rho1 rho2.
  Proof.
    intros; intro; intro; intro; intros.
    apply H in H2; auto.
    destructAll. exists x1. split; auto.
    rewrite M.gso in H2; auto.
    intro.
    subst.
    inv H0.
    specialize (H4 x).
    apply H4. auto.
  Qed.

  Theorem preord_env_P_def_funs_not_in_P_l':
    forall (pr : prims) (cenv : ctor_env) (B B' : fundefs)
      (P : Ensemble var) (k : nat) (rho : M.t val) (rho1 rho2 : env),
      preord_env_P cenv P1 P k (def_funs B' B rho rho1) rho2 ->
      Disjoint var P (name_in_fundefs B) ->
      preord_env_P cenv P1 P k rho1 rho2.
  Proof.
    intros; intro; intro; intro; intros.
    apply H; auto.
    rewrite def_funs_neq; auto.
    inv H0.
    specialize (H3 x).
    intro. apply H3; auto.
  Qed.

  Context (Hless_steps :
             forall C e1 rho1 (rho1' : env) (e2 : exp) (rho2 : env) (c1 c2 : nat),
               ctx_to_rho C rho1 rho1' ->
               len_exp_ctx C = 1 ->
               P1 (e1, rho1', c1) (e2, rho2, c2) ->
               P1 (C |[ e1 ]|, rho1, c1 + cost (C |[ e1 ]|)) (e2, rho2, c2))
          (Hpost_zero : forall e rho, post_zero e rho P1).

  Require Import L6.tactics.

  Lemma rm_constr k rho rho' e' v t l :
    ~ occurs_free e' v ->
    preord_env_P cenv PG (occurs_free e' \\ [set v]) k rho rho' ->
    preord_exp cenv P1 PG k (Econstr v t l e', rho) (e', rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Econstr_c v t l Hole_c) (P1 := P1).
    - intros; eapply Hless_steps; eauto.
    - simpl. eapply Hpost_zero.
    - reflexivity.
    - intros. inv H. inv H7.
      eapply preord_exp_refl; eauto.
      eapply preord_env_P_set_not_in_P_l in Henv; eauto with Ensembles_DB.
      rewrite Setminus_Disjoint in Henv. eassumption. eauto with Ensembles_DB.
  Qed.

  Lemma rm_prim k rho rho' e x p l :
    ~occurs_free e x ->
    preord_env_P cenv PG (occurs_free e \\ [set x]) k rho rho' ->
    preord_exp cenv P1 PG k (Eprim x p l e, rho) (e, rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Eprim_c x p l Hole_c) (P1 := P1).
    - intros; eapply Hless_steps; eauto.
    - simpl. eapply Hpost_zero.
    - reflexivity.
    - intros. inv H.
  Qed.


  Lemma rm_proj k rho rho' e x t n y :
    ~occurs_free e x ->
    preord_env_P cenv PG (occurs_free e \\ [set x]) k rho rho' ->
    preord_exp cenv P1 PG k (Eproj x t n y e, rho) (e, rho').
  Proof.
    intros Hnin Henv.
    eapply ctx_to_rho_preord_exp_l with (C := Eproj_c x t n y Hole_c) (P1 := P1).
    - intros; eapply Hless_steps; eauto.
    - simpl. eapply Hpost_zero.
    - reflexivity.
    - intros. inv H. inv H9.
      eapply preord_exp_refl; eauto.
      eapply preord_env_P_set_not_in_P_l in Henv; sets.
      rewrite Setminus_Disjoint in Henv. eassumption. sets.
  Qed.

  Lemma get_preord_env: forall rho rho' k,
      map_get_r _ rho rho' ->
      preord_env cenv PG k rho rho'.
  Proof.
    intros; intro; intros; intro; intros.
    rewrite H in H1.
    exists v1. split; auto.
    apply preord_val_refl; eauto.
  Qed.



  Definition fundefs_suffix fd fds:= (exists fd', fundefs_append fd' fd = fds).

  Lemma fundefs_append_assoc: forall F1 F2 F3,
      fundefs_append F1 (fundefs_append F2 F3) =
      fundefs_append (fundefs_append F1 F2) F3.
  Proof.
    induction F1; intros.
    - simpl. rewrite IHF1. auto.
    -     simpl. reflexivity.
  Qed.


  Lemma fundefs_suffix_cons: forall v f l e fds fds',
      fundefs_suffix (Fcons v f l e fds) fds' ->
      fundefs_suffix fds fds'.
  Proof.
    induction fds'; intros.
    - unfold fundefs_suffix in *. destructAll.
      destruct x.
      + inversion H; subst. exists ( Fcons v0 f0 l0 e0 (fundefs_append x (Fcons v f l e Fnil))).
        simpl.  rewrite <- fundefs_append_assoc. reflexivity.
      + inversion H; subst.
        exists (Fcons v0 f0 l0 e0 Fnil). auto.
    - unfold fundefs_suffix in H; destructAll.
      destruct x; inversion H.
  Qed.


  Lemma fundefs_suffix_in: forall v f l e fds fds',
      fundefs_suffix (Fcons v f l e fds) fds' ->
      List.In v (all_fun_name fds').
  Proof.
    induction fds'.
    - intro. inversion H. destruct x.
      + inversion H0. assert (fundefs_suffix (Fcons v f l e fds) fds'). exists x. auto.
        apply IHfds' in H1. subst.
        simpl. right. auto.
      + inversion H0. simpl. left; reflexivity.
    - intro. inversion H. destruct x; inversion H0.
  Qed.

  Lemma forall_name_fundefs: forall x P fds,
      Forall P (all_fun_name fds) ->
      name_in_fundefs fds x ->
      P x.
  Proof.
    induction fds; intros.
    - inversion H0; inversion H; subst.
      + inversion H1; subst. auto.
      + apply IHfds; auto.
    - inversion H0.
  Qed.

  Lemma all_name_fundefs: forall fds x,
      List.In x (all_fun_name fds) <-> name_in_fundefs fds x.
  Proof.
    induction fds; simpl; intros; split; intros.
    - destruct H. subst. left; auto.
      right. apply IHfds; auto.
    - inversion H; subst. inversion H0; auto.
      right. apply IHfds; auto.
    - inversion H.
    - inversion H.
  Qed.


  Lemma disjoint_not_occurs_fun: forall e fds,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      Disjoint var (occurs_free e) (name_in_fundefs fds).
  Proof.
    intros.
    apply Disjoint_intro; intros.
    intro.
    inversion H0; subst.
    assert (Hof := (not_occurs_not_free x)).
    destruct Hof.
    specialize (H3 e).
    apply H3; auto.
    rewrite Forall_forall in H.
    apply H.
    apply all_name_fundefs; auto.
  Qed.


  Lemma disjoint_occurs_free_fun: forall e fds,
      Forall (fun v => ~occurs_free e v) (all_fun_name fds) ->
      Disjoint var (occurs_free e) (name_in_fundefs fds).
  Proof.
    intros.
    apply Disjoint_intro; intros.
    intro.
    inversion H0; subst.
    rewrite Forall_forall in H.
    specialize (H x).
    apply H.
    apply all_name_fundefs; auto. auto.
  Qed.


  Lemma in_fun_name_suffix: forall fds fds' x,
      List.In x (all_fun_name fds) ->
      fundefs_suffix fds fds' ->
      List.In x (all_fun_name fds').
  Proof.
    induction fds. intros.
    simpl in H. destruct H.
    subst.
    eapply fundefs_suffix_in. eauto.
    apply fundefs_suffix_cons in H0. apply IHfds; eauto.
    intros. inversion H.
  Qed.


  Lemma forall_all_fun_name_suffix: forall P fds fds',
      Forall P (all_fun_name fds') ->
      fundefs_suffix fds fds' ->
      Forall P (all_fun_name fds).
  Proof.
    intros; rewrite Forall_forall.
    rewrite Forall_forall in H.
    intros.
    apply H.
    eapply in_fun_name_suffix; eauto.
  Qed.


  (* corrolary of preord_env_P_def_funs_not_in_P_l *)
  Lemma rm_fundefs_env: forall fds' fds e  k rho,
      Forall (fun v => num_occur e v 0) (all_fun_name fds') ->
      fundefs_suffix fds fds' ->
      preord_env_P cenv PG (occurs_free e) k (def_funs fds' fds rho rho) rho.
  Proof.
    intros.
    eapply preord_env_P_def_funs_not_in_P_l.
    apply preord_env_P_refl; eauto.
    apply disjoint_not_occurs_fun.
    eapply forall_all_fun_name_suffix; eauto.
  Qed.

  (* corrolary of preord_env_P_def_funs_not_in_P_r *)
  Lemma rm_fundefs_env' fds' fds e  k rho :
      Forall (fun v => num_occur e v 0) (all_fun_name fds') ->
      fundefs_suffix fds fds' ->
      preord_env_P cenv PG (occurs_free e) k rho (def_funs fds' fds rho rho).
  Proof.
    intros Hall Hsuff.
    eapply preord_env_P_def_funs_not_in_P_r.
    apply preord_env_P_refl; eauto.
    apply disjoint_not_occurs_fun.
    eapply forall_all_fun_name_suffix; eauto.
  Qed.


  Lemma rm_fundefs_env_of: forall fds' fds e  k rho,
      Forall (fun v => ~occurs_free e v) (all_fun_name fds') ->
      fundefs_suffix fds fds' ->
      preord_env_P cenv PG (occurs_free e) k (def_funs fds' fds rho rho) rho.
  Proof.
    intros.
    eapply preord_env_P_def_funs_not_in_P_l.
    apply preord_env_P_refl; eauto.
    apply disjoint_occurs_free_fun.
    eapply forall_all_fun_name_suffix in H; eauto.
  Qed.

  Lemma rm_fundefs_env_of': forall fds' fds e  k rho,
      Forall (fun v => ~occurs_free e v) (all_fun_name fds') ->
      fundefs_suffix fds fds' ->
      preord_env_P cenv PG (occurs_free e) k rho (def_funs fds' fds rho rho).
  Proof.
    intros.
    eapply preord_env_P_def_funs_not_in_P_r.
    apply preord_env_P_refl; eauto.
    apply disjoint_occurs_free_fun.
    eapply forall_all_fun_name_suffix in H; eauto.
  Qed.

  Lemma unique_bind_has_unique_name fds:
      unique_bindings_fundefs fds -> unique_functions fds.
  Proof.
    induction fds; intros H; auto.
    - inversion H; subst.
      constructor; eauto.
      intros Hc; apply H6.
      now apply name_in_fundefs_bound_var_fundefs.
    - constructor.
  Qed.

  Lemma split_fds_to_nil f1 f2:
    split_fds f1 f2 Fnil -> f1 = Fnil /\ f2 = Fnil.
  Proof.
    intros; destruct f1; destruct f2; inversion H. auto.
  Qed.

  Lemma split_fds_unique_name_l: forall fds,
      unique_functions fds ->
      forall fds' fds'',
        split_fds fds' fds'' fds ->
        unique_functions fds' /\ unique_functions fds'' /\
        Disjoint var (name_in_fundefs fds') (name_in_fundefs fds'').
  Proof.
    induction fds; intros H fds' fds'' Hsplit.
    - inversion H; subst.
      specialize (IHfds H6).
      inversion Hsplit; subst.
      + specialize (IHfds _ _ H4).
        destruct IHfds.
        split. constructor; [| eassumption ].
        intro; apply H2.
        now eapply split_fds_name_in_fundefs; eauto.
        destruct H1; split; auto.
        simpl. apply split_fds_name_in_fundefs in H4.
        apply Union_Disjoint_l; eauto.
        eapply Disjoint_Singleton_l. rewrite H4 in H2. eauto.
      + specialize (IHfds _ _ H4). destruct IHfds.
        destruct H1. split; [| split ]; eauto.
        simpl; constructor; eauto.
        intros Hc. apply H2.
        now eapply split_fds_name_in_fundefs; eauto.
        simpl; apply Union_Disjoint_r; eauto.
        apply split_fds_name_in_fundefs in H4.
        eapply Disjoint_Singleton_r. rewrite H4 in H2; eauto.
    - apply split_fds_to_nil in Hsplit. inv Hsplit; eauto.
      split; constructor; eauto. sets.
  Qed.

  Lemma split_fds_unique_functions_r B1 B2 B3 :
    unique_functions B1 -> unique_functions B2 ->
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
    split_fds B1 B2 B3 ->
    unique_functions B3.
  Proof with eauto with Ensembles_DB.
    intros Hun1 Hun2 HD Hspl. induction Hspl; simpl; repeat normalize_bound_var_in_ctx.
    - inv Hun1. constructor; eauto.
      + intros Hc.
        eapply split_fds_name_in_fundefs in Hc; [| eauto].
        inv Hc; auto.
        inv HD. specialize (H0 v). apply H0; split; auto.
        constructor. auto.
      + eapply IHHspl...
    - inv Hun2. constructor; eauto.
      + intros Hc.
        eapply split_fds_name_in_fundefs in Hc; [| eauto].
        inv Hc; auto.
        inv HD. specialize (H0 v). apply H0; split; auto.
        constructor. auto.
      + eapply IHHspl...
    - constructor.
  Qed.



  Lemma fundefs_append_unique_name_l B1 B2 B3 :
    unique_functions B3 ->
    fundefs_append B1 B2 = B3 ->
    unique_functions B1 /\
    unique_functions B2 /\
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2).
  Proof.
    intros. edestruct split_fds_unique_name_l; eauto.
    apply fundefs_append_split_fds; eauto.
  Qed.


  Lemma fundefs_append_unique_name_r B1 B2 B3 :
    fundefs_append B1 B2 = B3 ->
    unique_functions B1 ->
    unique_functions B2  ->
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
    unique_functions B3.
  Proof.
    intros.
    eapply split_fds_unique_functions_r;
      [ apply H0 | | | ]; eauto.
    apply fundefs_append_split_fds; eauto.
  Qed.

  (* XXX unused *)
  Lemma fundefs_swap_fun_order2:
    forall k x y tx ty xs ys ex ey rho1  B B12 B11',
      x <> y ->
      preord_env cenv PG k (def_funs B (fundefs_append B11' (Fcons x tx xs ex (Fcons y ty ys ey  B12))) rho1 rho1)
                 (def_funs B (fundefs_append B11' (Fcons y ty ys ey (Fcons  x tx xs ex B12))) rho1 rho1).
  Proof.
    induction B11'; intros.
    - simpl.
      apply preord_env_extend; auto.
      apply preord_val_refl; eauto.
    - simpl.
      intro. intro. intro. intro.
      rewrite set_permut in H1; auto. exists v1. split; auto.
      apply preord_val_refl; eauto.
  Qed.


  Lemma  find_def_fundefs_append_none:
    forall (f : var) (B1 B2 : fundefs) (v : fun_tag * list var * exp),
      find_def f B1 = None -> find_def f (fundefs_append B1 B2) = find_def f B2.
  Proof.
    induction B1; intros.
    simpl in *.
    destruct (M.elt_eq f v); eauto. inv H.
    simpl. auto.
  Qed.


  Lemma rm_fundefs_of' k rho e fds :
    Forall (fun v => ~occurs_free e v) (all_fun_name fds) ->
    preord_exp cenv P1 PG k (Efun fds e, rho) (e, rho).
  Proof.
    intros Hall. eapply ctx_to_rho_preord_exp_l with (C := Efun1_c fds Hole_c) (P1 := P1).
    - intros; eapply Hless_steps; eauto.
    - intros; eapply Hpost_zero.
    - reflexivity.
    - intros rho1 Henv. inv Henv. inv H3.
      eapply preord_exp_refl; eauto.
      eapply rm_fundefs_env_of; eauto.
      exists Fnil. simpl. auto.
  Qed.


  Lemma rm_fundefs_of k rho rho' e fds :
      Forall (fun v => ~ occurs_free e v) (all_fun_name fds) ->
      preord_env_P cenv PG (occurs_free e \\ name_in_fundefs fds)  k rho rho' ->
      preord_exp cenv P1 PG k (Efun fds e, rho) (e, rho').
  Proof.
    intros Hall Hpre. eapply ctx_to_rho_preord_exp_l with (C := Efun1_c fds Hole_c) (P1 := P1).
    - intros; eapply Hless_steps; eauto.
    - intros; eapply Hpost_zero.
    - reflexivity.
    - intros rho1 Henv. inv Henv. inv H3.
      eapply preord_exp_refl; eauto.
      eapply disjoint_occurs_free_fun in Hall.
      eapply preord_env_P_def_funs_not_in_P_l; eauto.
      rewrite Setminus_Disjoint in Hpre; eauto.
  Qed.

  Lemma rm_fundefs': forall k rho e fds,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      preord_exp cenv P1 PG k (Efun fds e, rho) (e, rho).
  Proof.
    intros; intro; intros.
    eapply Forall_impl in H.
    eapply rm_fundefs_of'; eauto.
    intros.
    simpl. apply not_occurs_not_free; auto.
  Qed.


  Lemma rm_fundefs: forall k rho rho' e fds,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      preord_env_P cenv PG (occurs_free e \\ name_in_fundefs fds)  k rho rho' ->
      preord_exp cenv P1 PG k (Efun fds e, rho) (e, rho').
  Proof.
    intros. eapply rm_fundefs_of; eauto.
    eapply Forall_impl; [| eassumption ]. intros.
    apply not_occurs_not_free; auto.
  Qed.


  Lemma preord_env_dead_fun: forall f t xs fb k fds' e rho1,
      ~(occurs_free (Efun fds' e)) f->
      ~ name_in_fundefs fds' f ->
      preord_env_P cenv PG (Union _ (occurs_free (Efun fds' e)) (name_in_fundefs fds')) k
                   (def_funs (Fcons f t xs fb fds') (Fcons f t xs fb fds') rho1 rho1) (def_funs fds' fds' rho1 rho1).
  Proof.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros. simpl. intro. intros.
    assert (Hxf: x <> f).
    {
      intro; subst.
      inv H1; auto.
    }
    intro. intros. rewrite M.gso in H2; auto.
    apply Union_Setminus in H1.
    inv H1.
    - inv H3.  rewrite def_funs_neq; auto.
      rewrite def_funs_neq in H2; auto.
      exists v1; split; auto.
      apply preord_val_refl; eauto.
    - erewrite def_funs_eq in H2; auto.
      inv H2.
      erewrite def_funs_eq; auto.
      exists  (Vfun rho1 fds' x).
      split; auto.
      rewrite preord_val_eq. intro. intros.
      assert (fundefs_append Fnil (Fcons f t xs fb fds') = (Fcons f t xs fb fds')) by auto.
      rewrite <- H5 in H2.
      rewrite find_def_fundefs_append_Fcons_neq in H2; auto. simpl in H2.
      clear H5.
      symmetry in H4.
      assert (Hsl:= set_lists_length _ (def_funs fds' fds' rho1 rho1) _ _ _  _ H1 H4).
      destruct Hsl.
      exists xs1, e1, x0.
      split; auto. split; auto.
      intros.
      eapply preord_exp_refl; eauto. clear; now firstorder.
      eapply preord_env_P_set_lists_l; eauto.  intros.
      apply find_def_correct in H2.
      eapply occurs_free_in_fun in H9; eauto.
      inv H9.
      exfalso; apply H8; auto.
      inv H10.
      right; auto.
      left.
      rewrite occurs_free_Efun. left.
      auto.
    - apply Decidable_name_in_fundefs.
  Qed.

  Lemma find_def_append_not_cons:
    forall B2 f t xs fb x B1,
      x <> f ->
      find_def x (fundefs_append B1 (Fcons f t xs fb B2)) = find_def x (fundefs_append B1 B2).
  Proof.
    induction B1; intros.
    - simpl. destruct (M.elt_eq x v); auto.
    - simpl. destruct (M.elt_eq x f).
      exfalso; auto.
      auto.
  Qed.

  (* adapted from identifiers.fun_in_fundefs_unique_fundefs_split *)
  Lemma fun_in_fundefs_unique_name_split f tau xs e B :
    fun_in_fundefs B (f, tau, xs, e) ->
    unique_functions B ->
    exists B1 B2,
      B = fundefs_append B1 (Fcons f tau xs e B2) /\
      ~ name_in_fundefs B1 f /\
      Same_set _ (Union _ (fun_in_fundefs B1) (fun_in_fundefs B2))
               (Setminus _ (fun_in_fundefs B) (Singleton _ (f, tau, xs, e))) /\
      unique_functions (fundefs_append B1 B2).
  Proof with eauto with Ensembles_DB.
    intros H Hun. induction B.
    - simpl in H.
      destruct (var_dec v f); subst.
      + inv H. inv H0.
        * exists Fnil. eexists. split; simpl; eauto.
          split; try (now intros Hc; inv Hc). split; try (now inv Hun; eauto).
          rewrite Union_Empty_set_neut_l, Setminus_Union_distr,
          Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          symmetry. eapply Setminus_Disjoint.
          apply Disjoint_Singleton_r. intros Hc.
          apply fun_in_fundefs_name_in_fundefs in Hc.
          inv Hun; auto.
        * exfalso. inv Hun. apply H2. eapply fun_in_fundefs_name_in_fundefs. eauto.
      + inv H. inv H0. congruence. inv Hun; eauto.
        edestruct IHB as [B1 [B2 [Heq [Hn [Hs Hun']]]]]; eauto.
        edestruct fundefs_append_unique_name_l as [H1 [H2s H3]];
          [ apply Hun' | | ]; eauto.
        exists (Fcons v f0 l e0 B1), B2. rewrite Heq. split; eauto.
        split; [| split ].
        * intros H. apply Hn. inv H; eauto. inv H4. congruence.
        * simpl. rewrite Setminus_Union_distr, <- Union_assoc.
          apply Same_set_Union_compat.
          apply Same_set_sym. eapply Setminus_Disjoint.
          apply Disjoint_Singleton_r. intros Hc. inv Hc. congruence.
          apply Same_set_sym.
          rewrite fundefs_append_fun_in_fundefs; eauto. simpl.
          rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set,
          Union_Empty_set_neut_l, <- Setminus_Union_distr.
          eapply Setminus_Disjoint. apply Union_Disjoint_l.
          eapply Disjoint_Singleton_r. intros Hc.
          apply Hn.
          eapply fun_in_fundefs_name_in_fundefs; eauto.
          eapply Disjoint_Singleton_r. intro.
          assert (In _ (Union (var * fun_tag * list var * exp) (fun_in_fundefs B1) (fun_in_fundefs B2)) (f, tau, xs, e)). right; auto. rewrite Hs in H4. inv H4. apply H7. auto.
        * simpl. constructor; eauto.
          intros H. apply H2.
          eapply fundefs_append_name_in_fundefs.
          symmetry. apply Heq.
          eapply fundefs_append_name_in_fundefs in H; [|reflexivity].
          inv H; auto.
          right. constructor 2. auto.
    - inv H.
  Qed.

  Lemma find_def_Included_name_in_fundefs f B B' :
    unique_functions B ->
    unique_functions B' ->
    Included _ (fun_in_fundefs B) (fun_in_fundefs B') ->
    name_in_fundefs B f ->
    find_def f B = find_def f B'.
  Proof with eauto with Ensembles_DB.
    revert B'. induction B; simpl; intros B' Hun Hun' H Hn.
    - edestruct fun_in_fundefs_unique_name_split
        as [B1 [B1' [Heq [Hn' [HS' Hun1]]]]]; eauto.
      eapply H. left. eauto.
      rewrite Heq. destruct (M.elt_eq f v); subst.
      + erewrite find_def_fundefs_append_r.
        simpl; destruct (M.elt_eq v v); try congruence.
        simpl; destruct (M.elt_eq v v); try congruence. eauto.
        apply name_not_in_fundefs_find_def_None.
        intros Hc. apply Hn'; eauto.
      + rewrite find_def_fundefs_append_Fcons_neq; eauto. eapply IHB; eauto.
        inv Hun; eauto.
        rewrite (fundefs_append_fun_in_fundefs B1 B1' (fundefs_append B1 B1')); eauto.
        eapply Included_trans; [| inv HS'; eauto].
        rewrite <- (Setminus_Disjoint (fun_in_fundefs B) (Singleton _ (v, f0, l, e))).
        eapply Included_Setminus_compat...
        eapply Included_trans; [| eassumption ]...
        eapply Disjoint_Singleton_r. inv Hun; eauto. intros Hc. apply H2.
        now eapply fun_in_fundefs_name_in_fundefs; eauto.
        inv Hn. inv H0; try congruence. eauto.
    - destruct B'; eauto. inv Hn.
  Qed.


  Lemma find_def_Same_set_name_in_fundefs f B B' :
    unique_functions B ->
    unique_functions B' ->
    Same_set _ (fun_in_fundefs B) (fun_in_fundefs B') ->
    find_def f B = find_def f B'.
  Proof.
    intros Hun1 Hun2 HS.
    destruct (@Dec _ _ (Decidable_name_in_fundefs B) f) as [Hin | Hnin].
    - inv HS. eapply find_def_Included_name_in_fundefs; eauto.
    - rewrite !name_not_in_fundefs_find_def_None; eauto.
      intros Hn. apply Hnin.
      apply name_in_fundefs_big_cup_fun_in_fundefs in Hn.
      destruct Hn as [[[[f' t] xs] e] [H1 H2]]. inv H2.
      eapply fun_in_fundefs_name_in_fundefs. now eapply HS; eauto.
  Qed.

  (* stronger version of preord_env_P_Same_set_fun_in_fundefs *)
  Lemma preord_env_P_Same_set_name_in_fundefs k S1 B1 B1' B2 B2' rho1 rho1' :
    Same_set _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
    Same_set _ (fun_in_fundefs B1') (fun_in_fundefs B2') ->
    unique_functions B1'->
    unique_functions B1 ->
    unique_functions B2'->
    unique_functions B2 ->
    preord_env_P cenv PG S1 k (def_funs B1' B1 rho1 rho1') (def_funs B2' B2 rho1 rho1').
  Proof.
    revert B1 S1 B1' B2 B2' rho1 rho1'.
    induction k using lt_wf_rec1; intros B1 S1 B1' B2 B2' rho1 rho1' HS1 HS2 Hun1' Hun1 Hun2' Hun2.
    intros x Hin v Hget. destruct (Decidable_name_in_fundefs B1) as [Hdec].
    destruct (Hdec x).
    - rewrite def_funs_eq in Hget; eauto. inv Hget.
      eexists. rewrite def_funs_eq; eauto. split; eauto.
      + rewrite preord_val_eq. intros vs1 vs2 i t xs1 e1 rho1'' Hlen Hf1 Hset1.
        edestruct (set_lists_length3 (def_funs B2' B2' rho1 rho1) xs1 vs2).
        rewrite <- Hlen. eapply set_lists_length_eq. now eauto.
        do 3 eexists. split; [| split ].
        erewrite find_def_Same_set_fun_in_fundefs; [ eassumption | | | ]; eauto.
        symmetry; eassumption. now eauto.
        intros Hlt Hall. eapply preord_exp_refl; eauto. clear; now firstorder.
        eapply preord_env_P_set_lists_l; eauto.
      + edestruct name_in_fundefs_find_def_is_Some as [? [? [? ?]]]. eassumption.
        eapply find_def_correct in H0. eapply HS1 in H0.
        eapply fun_in_fundefs_name_in_fundefs. eassumption.
    - rewrite def_funs_neq in *; eauto. eexists; split; eauto.
      eapply preord_val_refl; eauto.
      intros Hc; eapply n.
      edestruct name_in_fundefs_find_def_is_Some as [? [? [? ?]]]. eassumption.
      eapply find_def_correct in H0. eapply HS1 in H0.
      eapply fun_in_fundefs_name_in_fundefs. eassumption.
  Qed.


  Lemma rm1_fundefs: forall k rho1 rho2 fb e fds xs t f ,
      ~ (name_in_fundefs fds f) ->
      num_occur (Efun fds e) f 0 ->
      preord_env_P cenv PG (occurs_free (Efun fds e)) k rho1 rho2 ->
      preord_exp cenv P1 PG k (Efun (Fcons f t xs fb fds) e, rho1) ((Efun fds e), rho2).
  Proof.
    intros k rho1 rho2 fb e fds xs t f Hnin Hub H H0.
    eapply preord_exp_fun_compat; eauto.
    simpl. eapply preord_exp_refl; eauto.
    assert (Hin : ~ f \in (occurs_free (Efun fds e))).
    { intros Hin. eapply not_occurs_not_free in Hin; eauto. } repeat normalize_occurs_free_in_ctx.
    revert Hin H. generalize (occurs_free e) as S. revert k rho1 rho2 fb e fds xs t f Hnin Hub.
    induction k as [k' IHk'] using lt_wf_rec1; intros rho1 rho2 fb e fds xs t f Hnin Hub S H Henv.
    intros x Hin v Hget. destruct (peq x f); subst.
    - exfalso. eapply H. right. constructor; eauto.
    - rewrite M.gso in Hget; eauto.
      destruct (Decidable_name_in_fundefs fds) as [Hdec].
      destruct (Hdec x).
      + rewrite def_funs_eq in Hget; eauto. inv Hget.
        eexists. rewrite def_funs_eq; eauto. split; eauto.
        * rewrite preord_val_eq. intros vs1 vs2 i t' xs1 e1 rho1'' Hlen Hf1 Hset1.
          simpl in Hf1. rewrite peq_false in Hf1; eauto.
          edestruct (set_lists_length3 (def_funs fds fds rho2 rho2) xs1 vs2).
          rewrite <- Hlen. eapply set_lists_length_eq. now eauto.
          do 3 eexists. split; [| split ]; eauto.
          intros Hlt Hall.
          eapply preord_exp_refl; eauto. clear; now firstorder.
          eapply preord_env_P_set_lists_l with (P1 := occurs_free e1 \\ FromList xs1); eauto.
          replace i with (i + 1 - 1) by omega.
          eapply IHk'. omega. eassumption. eassumption.
          intros Hc. inv Hc.
          -- eapply not_occurs_not_free in H2; eauto. inv Hub. pi0. eassumption.
          -- inv Hub. pi0. eapply not_occurs_not_free in H8; eauto.
             eapply H8. eapply find_def_correct in Hf1.
             eapply occurs_free_in_fun in Hf1. inv H2. inv H3. eapply Hf1 in H2.
             inv H2; eauto. contradiction. inv H3; eauto. contradiction.
          -- eapply preord_env_P_monotonic; [| eapply preord_env_P_antimon; try eassumption ].
             omega. eapply Union_Included. now sets.
             do 2 eapply Setminus_Included_Included_Union. eapply Included_trans.
             eapply occurs_free_in_fun. eapply find_def_correct. eassumption. now sets.
          -- intros y Hnin' Hfv. constructor; eauto.
      + rewrite def_funs_neq in *; eauto. eapply preord_env_P_monotonic in Henv.
        eapply Henv. right; constructor; eauto. eassumption. omega.
  Qed.


  Lemma split_fds_unique_bindings_lr:
    forall B1 B11 B12 B2 ,
      unique_bindings_fundefs B1 ->
      split_fds B11 B12 B1 ->
      split_fds B11 B12 B2 ->
      unique_bindings_fundefs B2.
  Proof.
    intros.
    assert (HB1112 := split_fds_unique_bindings_fundefs_l _ _ _ H H0).
    destructAll.
    eapply split_fds_unique_bindings_fundefs_r.
    apply H2. apply H3. apply H4. auto.
  Qed.

  Lemma fundefs_append_num_occur:
    forall B1 B2 B,
      fundefs_append B1 B2 = B ->
      forall x n m,
        num_occur_fds B1 x n ->
        num_occur_fds B2 x m ->
        num_occur_fds B x (n+m).
  Proof.
    induction B1; intros.
    - simpl in H. destruct B. inversion H.
      specialize (IHB1 _ _ H7).
      subst.
      inv H0.
      specialize (IHB1 _ _ _ H10 H1).
      replace (n0 + m0 + m) with (n0 + (m0 + m)) by omega.
      constructor; auto.
      inv H.
    - simpl in H. inv H0. auto.
  Qed.

  Lemma fundefs_append_num_occur':
    forall B1 B2 nm x,
      num_occur_fds (fundefs_append B1 B2) x nm ->
      exists n m,
        num_occur_fds B1 x n /\ num_occur_fds B2 x m /\ n + m = nm.
  Proof.
    induction B1; intros.
    - simpl in H. inv H.
      apply IHB1 in H8. destructAll. exists (n + x0), x1. split.
      constructor; auto. split; auto. omega.
    - simpl in H. exists 0, nm. split; auto. constructor.
  Qed.

  Lemma rm_any_fundefs: forall k rho1 rho2 fb e B1 B2 xs t f ,
      unique_functions (fundefs_append B1 (Fcons f t xs fb B2)) ->
      num_occur (Efun (fundefs_append B1 B2) e) f 0 ->
      preord_env_P cenv PG (occurs_free (Efun (fundefs_append B1 B2) e)) k rho1 rho2 ->
      preord_exp cenv P1 PG k (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e, rho1)
                 ((Efun (fundefs_append B1 B2) e), rho2).
  Proof.
    intros k rho1 rho2 fb e B1 B2 xs t f Hnin Hub H H0.
    eapply preord_exp_fun_compat; eauto.
    simpl. eapply preord_exp_refl; eauto.
    assert (Hin : ~ f \in (occurs_free (Efun (fundefs_append B1 B2) e))).
    { intros Hin. eapply not_occurs_not_free in Hin; eauto. } repeat normalize_occurs_free_in_ctx.
    revert Hin H. generalize (occurs_free e) as S.

    revert rho1 rho2 fb e B1 B2 xs t f Hnin Hub.
    induction k as [k' IHk'] using lt_wf_rec1; intros rho1 rho2 fb e B1 B2 xs t f Hnin Hub S H Henv.
    intros x Hin v Hget. simpl.
    destruct (peq x f); subst.
    - exfalso. eapply H. right. constructor; eauto.
      intros Hc. eapply fundefs_append_unique_name_l in Hnin; eauto.
      destruct Hnin as [Hun1 [Hun2 Hdis]]. inv Hun2. simpl in Hdis.
      rewrite fundefs_append_name_in_fundefs in Hc; [| reflexivity ]. inv Hc; eauto.
      eapply Hdis. constructor; eauto.
    -  destruct (Decidable_name_in_fundefs (fundefs_append B1 B2)) as [Hdec].
       destruct (Hdec x).
       + rewrite def_funs_eq in Hget. inv Hget.
         eexists. rewrite def_funs_eq; eauto. split; eauto.
         * rewrite preord_val_eq. intros vs1 vs2 i t' xs1 e1 rho1'' Hlen Hf1 Hset1.
           edestruct (set_lists_length3 (def_funs (fundefs_append B1 B2) (fundefs_append B1 B2) rho2 rho2) xs1 vs2).
           rewrite <- Hlen. eapply set_lists_length_eq. now eauto.
           do 3 eexists. split; [| split ]; eauto.
           erewrite <- find_def_fundefs_append_Fcons_neq; eassumption.
           intros Hlt Hall.
           eapply preord_exp_refl; eauto. clear; now firstorder.
           eapply preord_env_P_set_lists_l with (P1 := occurs_free e1 \\ FromList xs1); eauto.
           replace i with (i + 1 - 1) by omega.
           erewrite find_def_fundefs_append_Fcons_neq in Hf1; try eassumption.
           eapply IHk'. omega. eassumption. eassumption.
           intros Hc. inv Hc.
           -- eapply not_occurs_not_free in H2; eauto. inv Hub. pi0. eassumption.
           -- inv Hub. pi0. eapply not_occurs_not_free in H8; eauto.
              eapply find_def_correct in Hf1.
              eapply occurs_free_in_fun in Hf1. inv H2. inv H3. eapply Hf1 in H2.
              inv H2; eauto. inv H3; eauto.
           -- eapply preord_env_P_monotonic; [| eapply preord_env_P_antimon; try eassumption ].
              omega. eapply Union_Included. now sets.
              do 2 eapply Setminus_Included_Included_Union. eapply Included_trans.
              eapply occurs_free_in_fun. eapply find_def_correct. eassumption. now sets.
           -- intros y Hnin' Hfv. constructor; eauto.
         * eapply fundefs_append_name_in_fundefs in n0; [| reflexivity ].
           eapply fundefs_append_name_in_fundefs. reflexivity. inv n0; eauto.
           right; right; eauto.
       + rewrite def_funs_neq in *; eauto. eapply preord_env_P_monotonic in Henv.
         eapply Henv. right; constructor; eauto. eassumption. omega.
         intros Hc. eapply n0. eapply fundefs_append_name_in_fundefs in Hc; [| reflexivity ].
         eapply fundefs_append_name_in_fundefs. reflexivity. inv Hc; eauto. inv H1; eauto.
         inv H2; eauto. contradiction.
  Qed.


  Lemma proper_get_list: forall A rho rho',
      map_get_r A rho rho' ->
      forall vs, get_list vs rho = get_list vs rho'.
  Proof.
    intros A rho rho' Hp.
    induction vs; auto.
    simpl. rewrite IHvs. rewrite Hp. reflexivity.
  Qed.

  Definition context_size (rho:env) := 1.

  Definition measure_map: forall A, (A -> nat) -> M.t A -> nat :=
    fun A f rho =>
      M.fold1 (fun n a => n + (f a)) rho 0.



  Context (Hless_steps' :
             forall x cl t e n rho1 c1,
               find_tag_nth cl t e n ->
               P1 (Ecase x cl, rho1, c1 + 1) (e, rho1, c1)).



  Lemma exp_case_equiv (vs:list val) e rho k cl (x :var) t n :
      M.get x rho = Some (Vconstr t vs) ->
      find_tag_nth cl t e n ->
      preord_exp cenv P1 PG k (Ecase x cl, rho) (e, rho).
  Proof.
    intros Hget Hf v1 c1 Hleq Hs. inv Hs.
    + exists OOT, 0. split; [| split ]. constructor; eauto. eapply cost_gt_0.
      eapply Hpost_zero; eauto. now simpl; eauto.
    + inv H0; repeat subst_exp.
      eapply find_tag_nth_deterministic in H6; [| clear H6; eassumption ]. inv H6.
      do 2 eexists.
      split; eauto. split; eauto. simpl in H9. simpl.
      rewrite <- (NPeano.Nat.sub_add 1 c1).
      replace (c1 - 1 + 1 - 1) with (c1 - 1) by (simpl in *; omega).
      simpl; eapply Hless_steps'; eauto. eassumption.
      apply preord_res_refl; eauto.
  Qed.


  Lemma caseConsistent_app: forall cenv t0 l0 l,
      caseConsistent cenv (l ++ l0) t0 ->
      caseConsistent cenv l t0 /\ caseConsistent cenv l0 t0.
  Proof.
    induction l; intros.
    split. apply CCnil.
    simpl in H. auto.
    inversion H; subst.
    apply IHl in H6.
    destruct H6.
    split; auto.
    eapply CCcons; eauto.
  Qed.

  (* XXX unused *)
  Lemma findtag_app_in: forall l0 t (e:exp) l,
      List.In (t, e) l ->
      findtag (l++l0) t = Some e ->
      findtag l t = Some e.
  Proof.
    induction l; intros.
    inversion H.
    simpl in H0. destruct a. simpl. destruct (M.elt_eq c t).
    auto. apply IHl; auto. inversion H.
    inversion H1; exfalso; auto.
    auto.
  Qed.

  Lemma get_fundefs_ctx :
    forall e (y : M.elt) (v : val) B (B' : fundefs) (rho : M.t val),
      M.get y rho = Some v ->
      ~ bound_var_fundefs_ctx B y -> M.get y (def_funs B' (B<[e]>) rho rho) = Some v.
  Proof.
    induction B; intros.
    - simpl. assert (y <> v0).
      intro; apply H0; subst; constructor.
      rewrite M.gso; auto.
      eapply get_fundefs; auto.
      intro; apply H0.
      constructor 4.
      apply name_in_fundefs_bound_var_fundefs.
      apply H2.
    - assert (y <> v0).
      intro; apply H0; subst; constructor.
      simpl. rewrite M.gso; auto.
  Qed.

  Lemma bv_in_find_def: forall x f t1 xs1 c B,
      find_def f B = Some (t1, xs1, c) ->
      bound_var c x -> bound_var_fundefs B x.
  Proof.
    induction B; intros.
    - simpl in H. destruct (M.elt_eq f v).
      + inversion H; subst. constructor 3. auto.
      + apply IHB in H; eauto.
    - inversion H.
  Qed.

  Lemma bv_in_find_def_ctx: forall x f t1 e xs1 c B,
      find_def f B = Some (t1, xs1, c |[ e ]|) ->
      bound_var_ctx c x -> bound_var_fundefs B x.
  Proof.
    induction B; intros.
    - simpl in H. destruct (M.elt_eq f v).
      + inversion H; subst. constructor 3.  apply bound_var_app_ctx. left. assumption.
      + apply IHB in H; eauto.
    - inversion H.
  Qed.


  Fixpoint ctx_size (c:exp_ctx): nat :=
    match c with
    | Hole_c => 0
    | Econstr_c v t vs c' => 1 + ctx_size c'
    | Eproj_c v t i r c' => 1 + ctx_size c'
    | Eletapp_c _ _ _ _  c' => 1 + ctx_size c'
    | Eprim_c v p vs c' => 1 + ctx_size c'
    | Ecase_c v l t c' l0 => 1 + fold_right
                                  (fun (p : ctor_tag * exp) (n : nat) => let (_, e1) := p in n + term_size e1)
                                  0 (l ++ l0) + ctx_size c'

    | Efun1_c fds c' => 1 + ctx_size c' + funs_size fds
    | Efun2_c cfds e => 1 + fundefs_ctx_size cfds + term_size e
    end
  with fundefs_ctx_size (cfds:fundefs_ctx): nat :=
         match cfds with
         | Fcons1_c v t ys c fds => 1 + ctx_size c + funs_size fds
         | Fcons2_c v t ys e cfds => 1 + term_size e + fundefs_ctx_size cfds
         end.


  Lemma app_ctx_size: (forall c e,
                          term_size (c |[e]|) = ctx_size c + term_size e) /\
                      (forall cfds e,
                          funs_size (cfds <[ e ]>) = fundefs_ctx_size cfds + term_size e).
  Proof.
    exp_fundefs_ctx_induction IHe IHf; intros; auto; try (simpl; rewrite IHe; reflexivity).
    - simpl.
      apply eq_S.
      induction l. simpl. rewrite IHe. omega.
      simpl. destruct a.
      rewrite IHl. omega.
    - simpl. rewrite IHe. omega.
    - simpl. rewrite IHf. omega.
    - simpl. rewrite IHe. omega.
    - simpl. rewrite IHf. omega.
  Qed.

  Lemma ctx_circular:
    forall c e,
      c |[e]| = e  -> c = Hole_c.
  Proof.
    intros.
    assert (term_size(c |[e]|) = ctx_size c + term_size e) by apply app_ctx_size.
    rewrite H in H0.
    destruct c; auto; exfalso; simpl in H0; omega.
  Qed.


  Lemma bv_in_ctx: (forall c e x c',
                       c' |[ e ]| = c |[ e ]| -> bound_var_ctx c x -> bound_var_ctx c' x) /\
                   (forall f e x  c',
                       c' <[ e ]> = f <[e]> -> bound_var_fundefs_ctx f x -> bound_var_fundefs_ctx c' x).
  Proof.
    exp_fundefs_ctx_induction IHe IHf; intros; destruct c'; try (inversion H; inversion H0; contradiction).
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    -  inversion H; subst.
       inversion H0; auto; subst. constructor.
       eapply IHe; eauto.
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    -  inversion H; subst.
       inversion H0; auto; subst.
       constructor.
       eapply IHe; eauto.
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    - inversion H; subst.
      inversion H0; auto.
      subst. constructor; eapply IHe; eauto.
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    - inversion H; subst.
      inversion H0; auto.
      subst. constructor; eapply IHe; eauto.
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    - inversion H; subst.
      revert H0; revert H3; revert H.
      revert l1; revert l.
      induction l; induction l1; intros; simpl in *.
      + inversion H3; subst.
        apply bound_var_Case_c in H0. inv H0.
        inv H1. inv H7.
        inv H1.
        apply bound_var_Case_c. right. left. eapply IHe; eauto.
        apply bound_var_Case_c; auto.
      + destruct a. inversion H3; subst.
        apply bound_var_Case_c in H0.
        inv H0.
        inversion H1; subst. inversion H6.
        inv H1. apply bound_var_Case_c.
        left. apply bound_var_Ecase_cons. left. apply bound_var_app_ctx; auto.
        apply bound_var_Ecase_app in H0. inv H0.
        apply bound_var_Case_c. left. apply bound_var_Ecase_cons. auto.
        apply bound_var_Ecase_cons in H1. inv H1.
        apply bound_var_app_ctx in H0. inv H0.
        apply bound_var_Case_c. auto.
        apply bound_var_Case_c.  left. apply bound_var_Ecase_cons.
        left. apply bound_var_app_ctx; auto.
        apply bound_var_Case_c. auto.
      + destruct a; inversion H3; subst.
        apply bound_var_Case_cons1_c in H0. inversion H0; subst.
        * apply bound_var_app_ctx in H1. inversion H1; auto.
          subst.
          simpl. apply bound_var_Case_c. right. right. apply bound_var_Ecase_app. right. apply bound_var_Ecase_cons. left.
          apply bound_var_app_ctx. auto.
        * apply bound_var_Case_c in H1. destruct H1.
          apply bound_var_Case_c. right. right. apply bound_var_Ecase_app. auto.
          inv H1.
          apply bound_var_Case_c. right; right.
          apply bound_var_Ecase_app. right.
          apply bound_var_Ecase_cons. left. apply bound_var_app_ctx. auto.
          apply bound_var_Case_c. right. right.
          apply bound_var_Ecase_app. right. apply bound_var_Ecase_cons. auto.
      + destruct a0; destruct a.
        inversion H3; subst.
        apply bound_var_Case_cons1_c in H0.
        inversion H0.
        * subst.
          apply bound_var_Case_cons1_c. auto.
        * subst. apply bound_var_Case_cons1_c. right.
          apply IHl; eauto.
          inversion H; subst.
          reflexivity.
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    - inversion H; subst.
      inversion H0; auto.
      subst.
      apply Bound_Fun12_c. eapply IHe; eauto.
    - inversion H.
      inversion H0; subst.
      + apply bound_var_app_f_ctx in H6.
        destruct H6.
        * constructor. auto.
        * apply Bound_Fun22_c.
          apply bound_var_app_ctx. right. auto.
      + apply bound_var_Fun2_c.
        right.
        apply bound_var_app_ctx. left; auto.
    - symmetry in H. exfalso. apply ctx_circular in H. inversion H.
    - inversion H.
      rewrite <- H3 in H0.
      apply bound_var_Fun2_c in H0.
      apply  bound_var_Fun1_c.
      inversion H0; subst.
      left. apply bound_var_app_f_ctx. left; auto.
      apply bound_var_app_ctx in H1.
      inversion H1.
      subst. right; auto.
      left.
      apply bound_var_app_f_ctx. right; auto.
    - inversion H.
      inversion H0; subst.
      + constructor.
        eapply IHf; eauto.
      + apply Bound_Fun22_c. auto.
    - inversion H; subst. apply bound_var_Fcons1_c in H0.
      apply bound_var_Fcons1_c.
      destruct H0. auto.
      destruct H0.
      auto.
      destruct H0.
      right. right. left.
      eapply IHe; eauto.
      auto.
    - inversion H; subst.
      apply bound_var_Fcons2_c.
      apply bound_var_Fcons1_c in H0.
      inv H0.
      auto.
      inv H1.
      auto.
      inv H0.
      right; right. left.
      apply bound_var_app_ctx. auto.
      apply bound_var_app_f_ctx in H1.
      inv H1; auto.
      right; right. left.
      apply bound_var_app_ctx. auto.
    - inversion H; subst.
      apply bound_var_Fcons1_c.
      apply bound_var_Fcons2_c in H0.
      inv H0; auto.
      inv H1; auto.
      inv H0; auto.
      apply bound_var_app_ctx in H1.
      inv H1; auto.
      right; right; right.
      apply bound_var_app_f_ctx. auto.
      right; right; right.
      apply bound_var_app_f_ctx. auto.
    - inversion H; subst.
      apply bound_var_Fcons2_c.
      apply bound_var_Fcons2_c in H0.
      inv H0; auto.
      inv H1; auto.
      inv H0; auto.
      right. right.
      right. eapply IHf; eauto.
  Qed.

  Lemma bv_in_find_def_ctx2 x f t1 e xs1 c B :
    find_def f (B<[e]>) = Some (t1, xs1, c |[ e ]|) ->
    bound_var_ctx c x -> bound_var_fundefs_ctx B x.
  Proof.
    induction B; intros; simpl in H; destruct (M.elt_eq f v); subst.
    - inversion H; subst.
      constructor 3.
      eapply bv_in_ctx; eauto.
    - constructor 4.
      eapply bv_in_find_def_ctx; eauto.
    -     inversion H; subst.
          constructor 7. apply bound_var_app_ctx. left. auto.
    - apply IHB in H; auto.
  Qed.

  Lemma name_boundvar_ctx: forall  x B' e1,
      name_in_fundefs (B' <[ e1 ]>) x -> bound_var_fundefs_ctx B' x.
  Proof.
    intros.
    induction B'; intros.
    - inversion H; subst. inversion H0; subst.
      constructor.
      constructor 4.
      apply name_in_fundefs_bound_var_fundefs; auto.
    - inversion H; subst. inversion H0; subst. constructor.
      apply Bound_Fcons24_c.
      apply IHB'; auto.
  Qed.

  Lemma name_boundvar_arg: forall x xs1 f c t1 f0,
      List.In x xs1 ->
      find_def f f0 = Some (t1, xs1, c) -> bound_var_fundefs f0 x.
  Proof.
    induction f0; intros.
    - simpl in H0.
      destruct (M.elt_eq f v).
      inversion H0; subst.
      constructor. right. apply H.
      constructor 2. apply IHf0; auto.
    - inversion H0.
  Qed.

  Lemma name_boundvar_arg_ctx: forall x xs1 t1 c e2 f B',
      List.In x xs1 ->
      find_def f (B' <[ e2 ]>) = Some (t1, xs1, c) -> bound_var_fundefs_ctx B' x.
  Proof.
    induction B'; intros.
    - simpl in H0. destruct (M.elt_eq f v).
      + subst. inversion H0; subst.
        constructor 2. auto.
      + constructor 4. eapply name_boundvar_arg; eauto.
    - simpl in H0. destruct (M.elt_eq f v).
      + subst. inversion H0; subst.
        constructor. auto.
      + constructor 8. apply IHB'; auto.
  Qed.

  Lemma included_bound_var_arg_ctx: forall  xs1 t1 c e2 f B',
      find_def f (B' <[ e2 ]>) = Some (t1, xs1, c) ->
      Included var (FromList xs1) (bound_var_fundefs_ctx B').
  Proof.
    intros. intro. intros.
    eapply name_boundvar_arg_ctx; eauto.
  Qed.

  Lemma included_name_fundefs_ctx: forall B e,
      Included var (name_in_fundefs (B <[ e ]>)) (bound_var_fundefs_ctx B).
  Proof.
    intros. intro. eapply name_boundvar_ctx.
  Qed.

  Lemma var_dec_eq: decidable_eq var.
  Proof.
    intro. intros. unfold decidable.
    destruct (var_dec x y); auto.
  Qed.


  Lemma fundefs_append_fnil_r: forall B, fundefs_append B Fnil = B.
  Proof.
    induction B.
    simpl. rewrite IHB. auto.
    auto.
  Qed.


  Lemma eq_P_apply_r:
    forall x sub sub',
      eq_env_P (Singleton _ x) sub sub' ->
      apply_r sub x = apply_r sub' x.
  Proof.
    intros.
    unfold apply_r.
    rewrite H.
    auto.
    constructor.
  Qed.

  Lemma eq_P_apply_r_list:
    forall sub sub' l,
      eq_env_P (FromList l) sub sub' ->
      apply_r_list sub l = apply_r_list sub' l.
  Proof.
    induction l.
    auto.
    simpl.
    intros.
    erewrite eq_P_apply_r.
    erewrite IHl. auto.
    intro. intro. apply H.
    constructor 2; auto.
    intro. intro; apply H.
    constructor.
    inv H0. auto.
  Qed.

  Lemma eq_env_P_def_funs: forall fl rho,
      eq_env_P (name_in_fundefs fl) (def_funs fl fl rho rho) rho
      -> eq_env_P (fun v => True) (def_funs fl fl rho rho) rho.
  Proof.
    intros.
    assert (Hv := Decidable_name_in_fundefs fl).
    destruct Hv.
    intro; intro.
    clear H0.
    specialize (Dec x).
    destruct Dec as [Hin | Hnin].
    + apply H in Hin. auto.
    + apply def_funs_neq.
      auto.
  Qed.

  Lemma eq_env_preord:
    forall S r1 r2,
      eq_env_P S r1 r2 ->
      (forall q, preord_env_P cenv PG S q r1 r2).
  Proof.
    intros. intro.
    intro.
    apply H in H0.
    unfold preord_var_env. intros.
    rewrite H0 in H1.
    eexists.
    split; eauto.
    apply preord_val_refl; eauto.
  Qed.

  Lemma preord_env_P_eq_r: forall S S' k rho1 rho2 rho3,
      preord_env_P cenv PG S k rho1 rho2 ->
      eq_env_P S' rho2 rho3 ->
      preord_env_P cenv PG (Intersection _ S  S') k rho1 rho3.
  Proof.
    intros. intro. intro. intro. intros.
    inv H1.
    apply H in H2; auto.
    destructAll.
    rewrite H0 in H1; auto.
    exists x0; split; eauto.
  Qed.

  Lemma preord_env_P_eq_l: forall S S' k rho1 rho2 rho3,
      preord_env_P cenv PG S k rho1 rho2 ->
      eq_env_P S' rho1 rho3 ->
      preord_env_P cenv PG (Intersection _ S  S') k rho3 rho2.
  Proof.
    intros. intro. intro. intro. intros.
    inv H1.
    rewrite <- H0 in H2; auto.
    apply H in H2; auto.
  Qed.



  Lemma eq_env_P_def_funs_not_in_P_l':
    forall (B B' : fundefs)
      (P : Ensemble var) (rho : M.t val) (rho1 rho2 : env),
      eq_env_P P (def_funs B' B rho rho1) rho2 ->
      Disjoint var P (name_in_fundefs B) ->
      eq_env_P P rho1 rho2.
  Proof.
    intros. intro; intros.
    specialize (H x H1).
    rewrite def_funs_neq in H; auto.
    inv H0.
    specialize (H2 x).
    intro. apply H2; auto.
  Qed.



  Lemma eq_env_P_def_funs_not_in_P_r:
    forall B B' P rho rho1 rho2,
      eq_env_P P rho1 rho2 ->
      Disjoint _ P (name_in_fundefs B) ->
      eq_env_P P rho1 (def_funs B' B rho rho2).
  Proof.
    intros. intro. intro.
    specialize (H x H1).
    rewrite def_funs_neq.
    auto.
    intro. inv H0.
    specialize (H3 x).
    apply H3. auto.
  Qed.

  Lemma eq_env_P_set_lists_not_in_P_r :
    forall (xs : list M.elt)
      (vs : list val) (P : Ensemble var) (rho1 rho2 : env)
      (rho2' : M.t val),
      eq_env_P P rho1 rho2 ->
      Some rho2' = set_lists xs vs rho2 ->
      Disjoint var P (FromList xs) -> eq_env_P P rho1 rho2'.
  Proof.
    intros. intro. intros.
    specialize (H x H2).
    erewrite <- set_lists_not_In with (rho' := rho2'); eauto.
    intro.
    inv H1. specialize (H4 x).
    apply H4; auto.
  Qed.

  Lemma eq_env_P_get_list: forall {A} S (rho:M.t A) rho',
      eq_env_P S rho rho' -> forall xs,
        Included _ (FromList xs) S ->
        get_list xs rho = get_list xs rho'.
  Proof.
    induction xs; intros. auto.
    simpl. destruct (M.get a rho) eqn:gar.
    + assert (S a).
      apply H0.
      constructor. reflexivity.
      apply H in H1.
      rewrite <- H1. rewrite gar.
      rewrite IHxs. reflexivity.
      intro. intros.
      apply H0.
      constructor 2. auto.
    + assert (S a).
      apply H0.
      constructor; reflexivity.
      apply H in H1.
      rewrite <- H1.
      rewrite gar.
      auto.
  Qed.


  (* More precise statement of find_def_def_funs_ctx *)
  Lemma find_def_def_funs_ctx' B f e1 tau xs e' :
    find_def f (B <[ e1 ]>) = Some (tau, xs, e') ->
    (forall e2, (find_def f (B <[ e2 ]>) = Some (tau, xs, e'))) \/
    (exists c, e' = c |[ e1 ]| /\
                          (forall e2, find_def f (B <[ e2 ]>) = Some (tau, xs, c |[ e2 ]|)) /\ (exists fd fd', B = (app_fundefs_ctx fd (Fcons1_c f tau xs c fd')))).
  Proof.
    revert tau xs e'. induction B; simpl; intros tau xs e' Heq.
    - destruct (M.elt_eq f v).
      + inv Heq. right. eexists e.
        split; eauto.
        split; eauto. exists Fnil, f0; auto.
      + left; eauto.
    - destruct (M.elt_eq f v).
      + inv Heq. left; eauto.
      + apply IHB in Heq. inv Heq. left; auto.
        inv H. destruct H0.
        inv H0. right.  exists x. split; auto. split; auto. destruct H2. destruct H.
        exists (Fcons v c l e x0), (x1).
        simpl. rewrite H. auto.
  Qed.


  Lemma preord_env_P_def_funs_compat_pre_vals_stem_set S k B  rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1' rho2' : env),
        m <  k ->
        Disjoint var (bound_stem_ctx c) S ->
        eq_env_P S rho1 rho1' ->
        eq_env_P S rho2 rho2' ->
        preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) m rho1' rho2' ->
        preord_exp cenv P1 PG m (c |[ e1 ]|, rho1') (c |[ e2 ]|, rho2')) ->
    preord_env_P cenv PG (occurs_free_fundefs (B' <[ e1 ]>) :|: S1) k rho1 rho2 ->
    Disjoint var (Union var (names_in_fundefs_ctx B) (bound_stem_fundefs_ctx B)) S ->
    Disjoint var (Union var (names_in_fundefs_ctx B') (bound_stem_fundefs_ctx B')) S ->
    preord_env_P cenv PG (S1 :|: (occurs_free_fundefs (B' <[ e1 ]>)) :|: (name_in_fundefs (B <[ e1 ]>)))
                 k (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv Hbv Hbv'.
    assert (Hval : forall f, preord_val cenv PG k (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx' as [H1 | [c [H1 H2]]]; eauto.

      + edestruct (@set_lists_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl; eauto. clear; now firstorder.
        eapply preord_env_P_set_lists_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega.
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x0 H Hfv.
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. eapply Union_assoc. right. eapply Ensembles_util.Union_commut. eauto.
      + destruct H2. inv H0. inv H2.
        edestruct (@set_lists_length cps.val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto.
        split; eauto.
        intros Hleq Hall.
        eapply preord_exp_post_monotonic. eassumption.
        eapply Hpre; eauto.
        {
          split; intro; intro. rewrite bound_stem_app_fundefs_ctx in Hbv'.
          inv Hbv'. specialize (H1 x1). apply H1. inv H0; auto.
        }
        eapply eq_env_P_set_lists_not_in_P_r; eauto.


        apply eq_env_P_def_funs_not_in_P_r. apply eq_env_P_refl.

        rewrite <- name_in_fundefs_ctx_ctx.
        eauto with Ensembles_DB.
        rewrite bound_stem_app_fundefs_ctx in Hbv'.
        eauto with Ensembles_DB.

        symmetry in Hs'.
        intro; eapply eq_env_P_set_lists_not_in_P_r; eauto.
        apply eq_env_P_def_funs_not_in_P_r.
        apply eq_env_P_refl.
        rewrite <- name_in_fundefs_ctx_ctx.
        eauto with Ensembles_DB.
        rewrite bound_stem_app_fundefs_ctx in Hbv'.
        eauto with Ensembles_DB.

        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega.
        repeat normalize_sets. 
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. omega. sets.
        intros x1 Hv Hfv.
        eapply find_def_correct in Hf; eauto. inv Hfv; eauto.
        eapply occurs_free_in_fun in H0; eauto. inv H0. now exfalso; eauto.
        eapply Union_assoc. 
        right. eapply Ensembles_util.Union_commut. eauto. left; eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + clear Hbv. induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite !Setminus_Union_distr. eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            rewrite Setminus_Union. rewrite (Union_commut [set v] [set v0]).
            rewrite <- Setminus_Union.
            rewrite Setminus_Same_set_Empty_set.
            now eauto with Ensembles_DB.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. apply IHB.
        eapply Disjoint_Included_l.
        2: apply Hbv.
        apply Included_Union_compat.
        simpl. right; auto.
        rewrite bound_stem_Fcons2_c. reflexivity.
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.

  (* This means that only bound variables on the applicative context c will modify the evaluation context rho *)
  Lemma preord_exp_compat_vals_stem_set S1 S k rho1 rho2 c e1 e2 :
    (forall k' rho1' rho2', k' <= k ->
                       preord_env_P cenv PG (occurs_free e1 :|: S1) k' rho1' rho2' ->

                       eq_env_P S rho1 rho1' ->
                       eq_env_P S rho2 rho2' ->
                       preord_exp cenv P1 PG k' (e1, rho1') (e2, rho2')) ->
    Disjoint var (bound_stem_ctx c) S ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv P1 PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    revert c S1 S rho1 rho2 e1 e2. induction k as [ k IH' ] using lt_wf_rec1.
    induction c; intros S1 S rho1 rho2 e1 e2 Hyp Hbv Hpre; eauto.
    - simpl. apply Hyp. auto.
      simpl in Hpre. apply Hpre.
      apply eq_env_P_refl.
      apply eq_env_P_refl.
    - rewrite bound_stem_Econstr_c in Hbv. simpl.
      eapply preord_exp_const_compat; eauto; intros.
      * eapply Forall2_same. intros x0 HIn. apply Hpre. left. constructor. auto.
      * assert (Disjoint _ S (Singleton _ v)).
         { eauto 10 with Ensembles_DB. }
         eapply preord_exp_monotonic. eapply IH'; eauto.
         {
           intros.
           apply Hyp; eauto. omega.
           eapply eq_env_P_set_not_in_P_l'; eauto.
           eapply eq_env_P_set_not_in_P_l'; eauto.
         }
         eapply Disjoint_Included_l; eauto.
         left; auto.
         apply preord_env_P_extend.
         eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. omega.
         simpl.
         rewrite occurs_free_Econstr.
         rewrite Setminus_Union_distr. now sets.
         rewrite preord_val_eq. constructor. reflexivity.
         apply Forall2_Forall2_asym_included; auto. omega.
    - simpl app_ctx_f.
      rewrite bound_stem_Eproj_c in Hbv.
      eapply preord_exp_proj_compat; eauto.
      + eapply Hpre. left. constructor; eauto.
      + intros m vs1 vs2 Hall Hpre'.
        assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IH'; eauto.
        {
          intros.
          apply Hyp; eauto. omega.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
        eauto with Ensembles_DB.
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]; omega.
        simpl. rewrite Setminus_Union_distr. rewrite occurs_free_Eproj. sets.
    - simpl.
      rewrite bound_stem_Eprim_c in Hbv.
      eapply preord_exp_prim_compat; eauto.
      + eapply Forall2_same. intros x0 Hin. eapply Hpre. left. constructor; eauto.
    (*    + intros vs1 vs2 Hall.
        assert (Disjoint _ S (Singleton _ v)).
        {
          eauto 10 with Ensembles_DB.
        }
        eapply IHc; eauto.
        {
          intros.
          apply Hyp; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
        eauto with Ensembles_DB.
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto.
        simpl. rewrite occurs_free_Eprim.
        eauto with Ensembles_DB. *)
    - rewrite bound_stem_Eletapp_c in Hbv. simpl.
      eapply preord_exp_letapp_compat; eauto; intros.
      * eapply Hpre. simpl. left. eapply occurs_free_Eletapp. sets.
      * eapply Forall2_same. intros x0 HIn. apply Hpre. left.
        constructor. auto. now right.
      * assert (Disjoint _ S (Singleton _ v)).
        { eauto 10 with Ensembles_DB. }
        eapply preord_exp_monotonic. eapply IH'; eauto.
        {
          intros.
          apply Hyp; eauto. omega.
          eapply eq_env_P_set_not_in_P_l'; eauto.
          eapply eq_env_P_set_not_in_P_l'; eauto.
        }
        eapply Disjoint_Included_l; eauto.
        left; auto.
        apply preord_env_P_extend.
        eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. omega.
        simpl.
        rewrite occurs_free_Eletapp. rewrite Setminus_Union_distr. 
        eauto 10 with Ensembles_DB. eassumption. omega.
    - simpl; eapply preord_exp_case_compat; eauto.
      eapply preord_env_P_antimon. eassumption. simpl. now sets.
      intros m Hlt.
      eapply IH'; auto.
      {
        intros.
        apply Hyp; eauto. omega.
      }
      rewrite bound_stem_Case_c in Hbv.
      eapply Disjoint_Included_l; eauto.
      reflexivity.
      eapply preord_env_P_antimon; eauto. eapply preord_env_P_monotonic; [| eassumption ]. omega.
      simpl. intros x0 H.
      inv H; eauto. left. eapply occurs_free_Ecase_Included; eauto.
      eapply in_or_app. right. left; eauto.
    - simpl.
      rewrite bound_stem_Fun1_c in Hbv.
      eapply preord_exp_fun_compat; eauto.
      assert (Disjoint _ S (name_in_fundefs f)).
      {
        eapply Disjoint_Included_l in Hbv.
        apply Disjoint_sym. apply Hbv.
        left.
        auto.
      }
      eapply preord_exp_monotonic.
      eapply IHc; eauto.
      {
        intros.
        apply Hyp; eauto.
        eapply eq_env_P_def_funs_not_in_P_l'; eauto.
        eapply eq_env_P_def_funs_not_in_P_l'; eauto.
      }
      eauto with Ensembles_DB.
      eapply preord_env_P_def_funs_cor; eauto.
      eapply preord_env_P_antimon; [ eassumption |].
      simpl. rewrite occurs_free_Efun.
      rewrite Setminus_Union_distr. eauto with Ensembles_DB. omega.
    - simpl. eapply preord_exp_fun_compat; eauto.
      eapply preord_exp_refl; eauto.
      eapply preord_env_P_antimon.
      simpl in Hpre.
      erewrite occurs_free_Efun in Hpre. 
      eapply preord_env_P_def_funs_compat_pre_vals_stem_set with (S1 := S1 :|: (occurs_free e \\ name_in_fundefs (f <[ e1 ]>))); eauto.
      { intros. eapply IH' with (S1 := S1 :|: (occurs_free e \\ name_in_fundefs (f <[ e1 ]>))); eauto.
        omega.
        intros.
        eapply Hyp; eauto. omega. eapply preord_env_P_antimon. eassumption.
        now sets.
        eapply eq_env_P_trans.
        apply H1. auto.
        eapply eq_env_P_trans; eauto. }
      + eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. omega.
        sets.
      + rewrite bound_stem_Fun2_c in Hbv. eassumption.
      + rewrite bound_stem_Fun2_c in Hbv. eassumption.
      + rewrite <- !Union_assoc.
        rewrite <- Union_Included_Union_Setminus; sets. tci.
  Qed.


  Corollary preord_exp_compat_stem_vals_le S1 xs vs vs' k rho1 rho2 c e1 e2 :
    (forall k' rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k' rho1 rho2 ->
                     k' <= k ->
                     get_list xs rho1 = Some vs ->
                     get_list xs rho2 = Some vs' ->
                     preord_exp cenv P1 PG k' (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_stem_ctx c) (FromList xs) ->
    get_list xs rho1 = Some vs ->
    get_list xs rho2 = Some vs' ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv P1 PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_stem_set with (S := FromList xs); eauto.
    intros. apply H; eauto.
    erewrite <- eq_env_P_get_list.
    eauto.
    eauto. intro; auto.
    erewrite <- eq_env_P_get_list.
    eauto.
    eauto. intro; auto.
  Qed.

  Corollary preord_exp_compat_vals_le S1 xs vs vs' k rho1 rho2 c e1 e2 :
    (forall k' rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k' rho1 rho2 ->
                     k' <= k ->
                     get_list xs rho1 = Some vs ->
                     get_list xs rho2 = Some vs' ->
                     preord_exp cenv P1 PG k' (e1, rho1) (e2, rho2)) ->
    Disjoint var (bound_var_ctx c) (FromList xs) ->
    get_list xs rho1 = Some vs ->
    get_list xs rho2 = Some vs' ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv P1 PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_stem_vals_le; eauto.
    eapply Disjoint_Included_l; eauto.
    apply bound_stem_var.
  Qed.

  Corollary preord_exp_compat_stem_val S1 x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->
                         preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)) ->
    ~ bound_stem_ctx c x ->
    M.get x rho1 = Some val ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv P1 PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros.
    eapply preord_exp_compat_vals_stem_set with (S := Singleton _ x); auto.
    intros.
    apply H. eauto. specialize (H5 x). rewrite <- H1.
    symmetry. apply H5.
    constructor.
    split. intro. intro. apply H0.
    inv H3. inv H5. eauto. eassumption.
  Qed.

  Corollary preord_exp_compat_val S1 x k val rho1 rho2 c e1 e2 :
    (forall k rho1 rho2, preord_env_P cenv PG (occurs_free e1 :|: S1) k rho1 rho2 ->
                         M.get x rho1 = Some val ->
                         preord_exp cenv P1 PG k (e1, rho1) (e2, rho2)) ->
    ~ bound_var_ctx c x ->
    M.get x rho1 = Some val ->
    preord_env_P cenv PG (occurs_free (c |[ e1 ]|) :|: S1) k rho1 rho2 ->
    preord_exp cenv P1 PG k (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    intros. eapply preord_exp_compat_stem_val; eauto.
    intro; apply H0.
    apply bound_stem_var. auto.
  Qed.

  Lemma  name_fds_same: forall x fds,
      name_in_fundefs fds x <->
      List.In x (all_fun_name fds).
  Proof.
    induction fds; split; intros.
    - simpl in H. inversion H; subst.
      inversion H0; subst.
      constructor; auto.
      rewrite IHfds in H0.
      constructor 2. auto.
    - simpl.
      simpl in H.
      inversion H.
      subst; left; auto.
      right.
      apply IHfds. auto.
    - inversion H.
    - inversion H.
  Qed.

  Lemma same_name_in_fun: forall f,
      Same_set _ (name_in_fundefs f) (FromList (all_fun_name f)).
  Proof.
    intro.
    split; intro; intro; apply name_fds_same; auto.
  Qed.


  Context (Hless_steps'' :
             forall x cl t e n rho1 rho2 c1 c2,
               find_tag_nth cl t e n ->
               P1 (e, rho1, c1) (e, rho2, c2) ->
               P1 (Ecase x cl, rho1, c1 + 1) (e, rho2, c2)).



  Lemma rw_case_local (k0 : nat) c0 vs e cl x n (rho0 rho3 : env) :
      preord_env_P cenv PG (occurs_free (Ecase x cl)) k0 rho0 rho3 ->
      find_tag_nth cl c0 e n ->
      M.get x rho0 = Some (Vconstr c0 vs) ->
      preord_exp cenv P1 PG k0 (Ecase x cl, rho0) (e, rho3).
  Proof.
    intros Hcc Hf Hget v1 c1 Hleq Hs. inv Hs.
    + exists OOT, 0. split; [| split ].
      constructor; eauto. eapply cost_gt_0.
      eapply Hpost_zero; eauto. now simpl; eauto.
    + inv H0; repeat subst_exp.
      eapply find_tag_nth_deterministic in H6; [| clear H6; eassumption ]. inv H6.
      edestruct (preord_exp_refl cenv P1 PG)
        with (k := k0) (e := e0) (rho := rho0) (rho' := rho3) (cin := (c1 - cost (Ecase x cl)))
        as [v2 [c2 [Hs2 [Hp2 Hr2]]]]; eauto.
      eapply preord_env_P_antimon. apply Hcc.
      eapply occurs_free_Ecase_Included. eapply find_tag_nth_In_patterns; eassumption.
      simpl; omega.

      do 2 eexists. split; [| split ]; eauto.
      simpl in *; replace c1 with (c1 - 1 + 1) by omega.
      eapply Hless_steps''; eauto.
      eapply preord_res_monotonic. eassumption. omega.
  Qed.



  Lemma rw_case_equiv  cl c0 e n x c ys rho1 rho2 k :
    find_tag_nth cl c0 e n ->
    ~bound_stem_ctx c x ->
    preord_env_P cenv PG (occurs_free (Econstr x c0 ys (c |[ Ecase x cl ]|))) k rho1 rho2 ->
    preord_exp cenv P1 PG k (Econstr x c0 ys (c |[ Ecase x cl ]|), rho1) (Econstr x c0 ys (c |[ e ]|), rho2).
  Proof.
    intros Hf Hb Henv.
    eapply preord_exp_const_compat; eauto.
    eapply Forall2_same. intros y Hin. eapply Henv. now constructor; eauto.
    intros m vs1 vs2 Hlt Hall.
    eapply preord_exp_compat_stem_val with (S1 := Empty_set _); eauto.
    2:{ rewrite M.gss; reflexivity. }
    - intros k' rho1' rho2' Hpre Hget1.
      rewrite Union_Empty_set_neut_r in Hpre. eapply rw_case_local; eassumption.
    - eapply preord_env_P_extend.
      eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. omega.
      normalize_occurs_free; now sets.
      rewrite preord_val_eq. simpl. split; auto. apply Forall2_Forall2_asym_included; auto.
  Qed.


  Lemma image_apply_r v m S :
    image (apply_r (M.remove v m)) S \subset v |: image (apply_r m) (S \\ [set v]).
  Proof.
    intros z [y [Hin Heq]]; subst.
    destruct (peq y v); subst.
    - left. unfold In. unfold apply_r. rewrite M.grs. reflexivity.
    - right. eexists; split; eauto.
      constructor; eauto. intros Hc; inv Hc; eauto.
      unfold apply_r. rewrite M.gro; eauto.
  Qed.

  Lemma image'_get_not_In {A} v (m : M.t A) S :
    image' (fun x : positive => M.get x (M.remove v m)) S \subset
    image' (fun x : positive => M.get x m) (S \\ [set v]).
  Proof.
    intros z [y [Hin Heq]]; subst.
    destruct (peq y v); subst.
    - rewrite M.grs in Heq. congruence.
    - rewrite M.gro in Heq; eauto. eexists; split; eauto.
      constructor; eauto. intros Hc; inv Hc. eauto.
  Qed.

  Lemma remove_all_none: forall x l sigma,
      M.get x sigma = None ->
      M.get x (remove_all sigma l) = None.
  Proof.
    induction l.
    - intros. simpl. auto.
    - intros. simpl. apply gr_none. eapply IHl. eassumption.
  Qed.

  (* todo: move *)
  Lemma in_remove_all: forall x l sigma,
      FromList l x ->
      M.get x (remove_all sigma l) = None.
  Proof.
    induction l; intros; simpl.
    - inv H.
    - destruct (peq x a); inv H; eauto; subst.
      + rewrite M.grs. reflexivity.
      + rewrite M.grs. reflexivity.
      + rewrite M.grs. reflexivity.
      + rewrite M.gro; eauto.
  Qed.

  Lemma not_in_remove_all: forall x l sigma,
      ~ (FromList l x) ->
      M.get x sigma = M.get x (remove_all sigma l).
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl.
      assert (Hin : ~ (a = x) /\ ~ (FromList l x)).
      { split; intro. apply H. constructor; auto.
        apply H. constructor 2; auto. }
      destruct Hin.
      rewrite M.gro; auto.
  Qed.

  Lemma image'_get_remove_all (m : M.t var) S l :
    image' (fun x : positive => M.get x (remove_all m l)) S \subset
    image' (fun x : positive => M.get x m) (S \\ FromList l).
  Proof.
    revert m S; induction l; intros m S.
    - simpl. repeat normalize_sets. reflexivity.
    - simpl. eapply Included_trans.
      eapply image'_get_not_In.
      eapply Included_trans. eapply IHl.
      repeat normalize_sets. rewrite Setminus_Union. reflexivity.
  Qed.



  Lemma preord_env_P_inj_remove (S : Ensemble var) (rho1 rho2 : env)
        (k : nat) m (x  : var) (v1 v2 : val) :
    ~ x \in (image' (fun x => M.get x m) (S \\ [set x])) ->
    preord_env_P_inj cenv PG (S \\ [set x]) k (apply_r m) rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    preord_env_P_inj cenv PG S k (apply_r (M.remove x m)) (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Hnin Henv Hv z HP. unfold extend.
    destruct (peq z x) as [| Hneq].
    - subst. intros z Hget.
      rewrite M.gss in Hget. inv Hget. eexists.
      split; eauto. unfold apply_r. rewrite M.grs. rewrite M.gss; eauto.
    - intros z' Hget. rewrite M.gso in Hget; eauto.
      unfold apply_r. rewrite M.gro; eauto. rewrite M.gso; eauto.
      eapply Henv. constructor; eauto. intros Hc; inv Hc; eauto. eassumption.
      destruct (M.get z m) eqn:Hget'; eauto.
      intros Hc; subst. eapply Hnin. eexists. split; eauto. constructor; eauto.
      intros Hc; inv Hc; eauto.
  Qed.

  Lemma preord_env_P_inj_set_lists_remove_all (S : var -> Prop) (rho1 rho2 rho1' rho2' : env)
        (k : nat) (xs1 : list var) (vs1 vs2 : list val) m :
    Disjoint _ (image' (fun x => M.get x m) (S \\ FromList xs1)) (FromList xs1) ->
    preord_env_P_inj cenv PG (S \\ (FromList xs1)) k (apply_r m) rho1 rho2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->
    set_lists xs1 vs1 rho1 = Some rho1' ->
    set_lists xs1 vs2 rho2 = Some rho2' ->
    preord_env_P_inj cenv PG S k (apply_r (remove_all m xs1))  rho1' rho2'.
  Proof with now eauto with Ensembles_DB.
    revert S rho1 rho2 rho1' rho2' vs1 vs2 m.
    induction xs1; intros S rho1 rho2 rho1' rho2' vs1 vs2 m Hd Hpre Hall Hs1 Hs2.
    - simpl in *. destruct vs1; destruct vs2; try congruence. inv Hs1; inv Hs2.
      eapply preord_env_P_inj_antimon. eassumption. do 2 normalize_sets. now sets.
    - simpl in *. destruct vs1; destruct vs2; try congruence.
      destruct (set_lists xs1 vs1 rho1) eqn:Hs1'; try congruence.
      destruct (set_lists xs1 vs2 rho2) eqn:Hs2'; try congruence.
      inv Hs1; inv Hs2.
      eapply preord_env_P_inj_remove.
      + intros Hc. eapply Hd. constructor; [| now left ].
        eapply image'_get_remove_all in Hc. normalize_sets. rewrite <- Setminus_Union.
        eassumption.
      + inv Hall. eapply IHxs1; [ | | | eassumption | eassumption ]; eauto.
        eapply Disjoint_Included; [| | eassumption ].
        now normalize_sets; sets.
        normalize_sets. rewrite Setminus_Union. sets.

        eapply preord_env_P_inj_antimon. eassumption.
        normalize_sets. sets.
      + inv Hall ; eauto.
  Qed.

  Lemma rename_all_correct k (m : M.t var) e1 rho1 rho2 :
    Disjoint _ (image' (fun x => M.get x m) (occurs_free e1)) (bound_var e1) ->
    preord_env_P_inj cenv PG (occurs_free e1) k (apply_r m) rho1 rho2 ->
    preord_exp cenv P1 PG k (e1, rho1) (rename_all m e1, rho2).
  Proof.
    revert e1 m rho1 rho2. induction k as [k IHk] using lt_wf_rec1.
    intros e1. revert k IHk; induction e1 using exp_ind'; intros k IHk m rho1 rho2 Hdis Hpre.
    - (* Econstr *)
      simpl; eapply preord_exp_const_compat; eauto; intros.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free. sets.
      + eapply IHk; [ eassumption | | ].
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite image'_Union.
          eapply Included_trans. eapply image'_get_not_In. now sets.
        * eapply preord_env_P_inj_remove.
          -- intros Hc. eapply Hdis. normalize_occurs_free.
             constructor; eauto. rewrite image'_Union. right; eauto.
          -- eapply preord_env_P_inj_antimon.
             eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free; sets.
          -- rewrite preord_val_eq. simpl; split; eauto.
             eapply Forall2_Forall2_asym_included. eassumption.
    - (* Ecase nil *)
      simpl; eapply preord_exp_case_nil_compat; eauto; intros.
    - (* Ecase cons *)
      simpl; eapply preord_exp_case_cons_compat; eauto; intros.
      + clear. induction l. now constructor.
        constructor; eauto. destruct a; reflexivity.
      + eapply IHk; [ eassumption | | ].
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite !image'_Union. now sets.
        * eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption ].
          omega. normalize_occurs_free; sets.
      + eapply IHe0.
        * eauto.
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite !image'_Union. now sets.
        * eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption ].
          omega. normalize_occurs_free; sets.
    - (* Eproj *)
      simpl; eapply preord_exp_proj_compat; eauto; intros.
      eapply IHk; [ eassumption | | ].
      * eapply Disjoint_Included; [| | eassumption ].
        normalize_bound_var. now sets.
        normalize_occurs_free. rewrite image'_Union.
        eapply Included_trans. eapply image'_get_not_In. now sets.
      * eapply preord_env_P_inj_remove.
        -- intros Hc. eapply Hdis. normalize_occurs_free.
           constructor; eauto. rewrite image'_Union. right; eauto.
        -- eapply preord_env_P_inj_antimon.
           eapply preord_env_P_inj_monotonic; [| eassumption ].
           omega. normalize_occurs_free; sets.
        -- eassumption.
    - (* Eletapp *)
      simpl; eapply preord_exp_letapp_compat; eauto; intros.
      + eapply Hpre. constructor. now left.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free. sets.
      + eapply IHk; [ eassumption | | ].
        * eapply Disjoint_Included; [| | eassumption ].
          normalize_bound_var. now sets.
          normalize_occurs_free. rewrite image'_Union.
          eapply Included_trans. eapply image'_get_not_In. now sets.
        * eapply preord_env_P_inj_remove.
          -- intros Hc. eapply Hdis. normalize_occurs_free.
             constructor; eauto. rewrite image'_Union. right; eauto.
          -- eapply preord_env_P_inj_antimon.
             eapply preord_env_P_inj_monotonic; [| eassumption ].
             omega. normalize_occurs_free; sets.
          -- eassumption.
    - (* Efun *)
      simpl; eapply preord_exp_fun_compat; eauto.
      eapply preord_exp_monotonic.
      eapply IHe1.
      + eauto.
      + eapply Disjoint_Included; [| | eassumption ].
        normalize_bound_var. now sets.
        normalize_occurs_free. rewrite image'_Union.
        eapply Included_trans. eapply image'_get_remove_all.
        rewrite same_name_in_fun. now sets.
      + eapply preord_env_P_inj_antimon with (S2 := (occurs_free (Efun f2 e1)) :|: name_in_fundefs f2).
        2:{ normalize_occurs_free; sets. rewrite <- Union_assoc, <- Union_Setminus. sets. tci. }
        induction k as [h IHk'] using lt_wf_rec1.
        intros z Hget v1 Hgetz1.
        destruct (Decidable_name_in_fundefs f2) as [Hdec]. destruct (Hdec z).
        * rewrite def_funs_eq in Hgetz1. inv Hgetz1.
          eexists. split.
          -- rewrite def_funs_eq. reflexivity.
             eapply rename_all_fun_name. unfold apply_r. rewrite in_remove_all.
             eassumption. eapply same_name_in_fun. eassumption.
          -- rewrite preord_val_eq. intros vs1 vs2 j t xs1 e rho Hlen Hf Hset.
             edestruct (set_lists_length3 (def_funs (rename_all_fun (remove_all m (all_fun_name f2)) f2)
                                                    (rename_all_fun (remove_all m (all_fun_name f2)) f2) rho2 rho2)
                                          xs1 vs2).
             rewrite <- Hlen; eapply set_lists_length_eq. now eauto.
             do 3 eexists; split; [| split ].
             ++ eapply find_def_rename. unfold apply_r.
                rewrite in_remove_all. eassumption. eapply same_name_in_fun. eassumption.
             ++ now eauto.
             ++ eapply find_def_correct in Hf.
                intros Hlt Hall.
                eapply preord_exp_post_monotonic. eassumption. eapply IHk.
                ** eassumption.
                ** eapply Disjoint_Included_l. eapply Included_trans.
                   eapply image'_get_remove_all. eapply image'_get_remove_all.
                   eapply Disjoint_Included; [ | | eassumption ].
                   normalize_bound_var. eapply Included_Union_preserv_l.
                   eapply Included_trans; [| now eapply fun_in_fundefs_bound_var_fundefs; eauto ].

                   now sets.
                   normalize_occurs_free. eapply image'_monotonic. do 2 eapply Setminus_Included_Included_Union.
                   eapply Included_trans. eapply occurs_free_in_fun; eauto. rewrite <- same_name_in_fun.
                   sets.
                ** eapply preord_env_P_inj_set_lists_remove_all; [ | | | now eauto | now eauto ].
                   --- eapply Disjoint_Included; [| | eassumption ].
                       normalize_bound_var. eapply Included_Union_preserv_l.
                       eapply Included_trans; [| now eapply fun_in_fundefs_bound_var_fundefs; eauto ].
                       now sets.
                       eapply Included_trans. eapply image'_get_remove_all.
                       eapply image'_monotonic. do 2 eapply Setminus_Included_Included_Union.
                       eapply Included_trans. eapply occurs_free_in_fun; eauto. rewrite <- same_name_in_fun.
                       normalize_occurs_free. sets.
                   --- eapply preord_env_P_inj_antimon. eapply IHk'; [ eassumption | | ].
                       +++ intros. eapply IHk; eauto. omega.
                       +++ eapply preord_env_P_inj_monotonic; [| eassumption ]. omega.
                       +++ eapply Setminus_Included_Included_Union. eapply Included_trans.
                           eapply occurs_free_in_fun. eassumption. normalize_occurs_free. sets.
                   --- eassumption.
          -- eassumption.
        * inv Hget; try contradiction.
          rewrite def_funs_neq in *; eauto. unfold apply_r. rewrite <- not_in_remove_all.
          eapply Hpre. eassumption. eassumption.
          intros Hc. eapply n. eapply same_name_in_fun. eassumption.
          intros Hc. edestruct rename_all_fun_name as [Hl Hr]. eapply Hl in Hc. clear Hr Hl.
          unfold apply_r in Hc. rewrite <- not_in_remove_all in Hc.
          destruct (M.get z m) eqn:Heq; eauto. eapply Hdis. constructor.
          now eexists; split; eauto.
          constructor; eauto. eapply name_in_fundefs_bound_var_fundefs. eassumption.
          intros Hc'. eapply n. eapply same_name_in_fun. eassumption.
      + omega.
    - (* Eapp *)
      simpl; eapply preord_exp_app_compat; eauto; intros.
      + eapply Forall2_preord_var_env_map. eassumption.
        normalize_occurs_free. sets.
    - (* Eprim *)
      simpl; eapply preord_exp_prim_compat; eauto; intros.
      eapply Forall2_preord_var_env_map. eassumption.
      normalize_occurs_free. sets.
    - (* Ehalt *)
      simpl; eapply preord_exp_halt_compat; eauto.
  Qed.




  Lemma apply_r_none:
    forall v sigma,
      M.get v sigma = None ->
      apply_r sigma v = v.
  Proof.
    intros. unfold apply_r.
    unfold M.get in H. unfold M.get. rewrite H.
    reflexivity.
  Qed.

  Lemma apply_r_some: forall v y sigma,
      M.get v sigma = Some y ->
      apply_r sigma v = y.
  Proof.
    intros. unfold apply_r.
    unfold M.get in *. rewrite H. reflexivity.
  Qed.

  Lemma apply_r_set2: forall x v y sigma,
      x <> v ->
      apply_r (M.set x y sigma) v = apply_r sigma v.
  Proof.
    intros. unfold apply_r. rewrite M.gso by auto. auto.
  Qed.

  Lemma num_occur_arl:
    forall x y l,
      x <> y ->
      num_occur_list (apply_r_list (M.set x y (M.empty var)) l) x = 0.
  Proof.
    induction l; intros.
    auto.
    simpl. rewrite IHl; auto.
    destruct (var_dec x a).
    + subst. erewrite apply_r_some by apply M.gss.
      destruct (cps_util.var_dec a y). exfalso; auto. auto.
    + rewrite apply_r_none.
      destruct (cps_util.var_dec x a). exfalso; auto. auto.
      rewrite M.gso by auto. apply M.gempty.
  Qed.


  Lemma not_in_sig_rem: forall sigma (x v:var),
      ~ (exists z, M.get z sigma = Some x) ->
      ~ (exists z, M.get z (M.remove v sigma) = Some x).
  Proof.
    intros. intro. destruct H0.
    destruct (var_dec x0 v).
    subst. rewrite M.grs in H0. inversion H0.
    rewrite M.gro in H0; auto. apply H. exists x0; auto.
  Qed.

  Lemma not_in_sig_list_rem:
    forall  x l sigma,
      ~ (exists z, M.get z sigma = Some x) ->
      ~ (exists z : M.elt, M.get z (remove_all sigma l) = Some x).
  Proof.
    induction l; intros.
    - simpl. auto.
    - simpl.
      apply not_in_sig_rem.
      apply IHl. auto.
  Qed.

  Lemma apply_r_not_in_sig: forall x v sigma,
      ~ (exists z : M.elt, M.get z sigma = Some x) ->
      x <> v -> x <> apply_r sigma v.
  Proof.
    intros. unfold apply_r.
    destruct (M.get v sigma) eqn:gvs.
    intro; subst. apply H. exists v; auto.
    auto.
  Qed.

  Lemma one_rename_all_ar: forall x y v sigma,
      ~ (exists z, M.get z sigma = Some x) ->
      (M.get x sigma = None) ->
      apply_r (M.set x y sigma) v =   (apply_r (M.set x y (M.empty var)) (apply_r sigma v)).
  Proof.
    intros.
    destruct (var_dec x v).
    + subst. erewrite apply_r_some by apply M.gss.
      rewrite apply_r_none with (v := v); auto.
      erewrite apply_r_some by apply M.gss.
      auto.
    + rewrite apply_r_set2; auto.
      rewrite apply_r_set2; auto.
      rewrite apply_r_empty; auto.
      apply apply_r_not_in_sig; auto.
  Qed.

  Lemma one_rename_all_list: forall y x l sigma,
      ~ (exists z, M.get z sigma = Some x) ->
      (M.get x sigma = None) ->
      apply_r_list (M.set x y sigma) l =  (apply_r_list (M.set x y (M.empty var)) (apply_r_list sigma l)).
  Proof.
    induction l; intros.
    reflexivity.
    simpl.
    rewrite IHl; auto.
    destruct (var_dec x a).
    - subst.
      erewrite apply_r_some by apply M.gss.
      erewrite apply_r_none with (v := a); auto.
      erewrite apply_r_some by apply M.gss.
      reflexivity.
    - rewrite apply_r_set2; auto.
      rewrite apply_r_set2; auto. rewrite apply_r_empty.
      auto.
      apply apply_r_not_in_sig; auto.
  Qed.

  Lemma one_rename_all_ar': forall x y v sigma,
      (M.get y sigma = None) ->
      apply_r (M.set x y sigma) v = apply_r sigma (apply_r (M.set x y (M.empty var)) v).
  Proof.
    intros.
    destruct (var_dec x v).
    + subst. erewrite apply_r_some by apply M.gss.
      erewrite apply_r_some with (v := v) by apply M.gss.
      rewrite apply_r_none with (v := y); auto.
    + rewrite apply_r_set2; auto.
      rewrite apply_r_set2; auto.
      rewrite apply_r_empty; auto.
  Qed.

  Lemma one_rename_all_list': forall y x l sigma,
      (M.get y sigma = None) ->
      apply_r_list (M.set x y sigma) l =  apply_r_list sigma (apply_r_list (M.set x y (M.empty var))  l).
  Proof.
    induction l; intros.
    reflexivity.
    simpl.
    rewrite IHl; auto.
    rewrite one_rename_all_ar'; auto.
  Qed.

  Lemma Disjoint_Singletons:
    forall v x,
      Disjoint var (Singleton var x) (Singleton var v) ->
      x <> v.
  Proof.
    intros. intro; subst. inv H.
    specialize (H0 v).
    apply H0. split; auto.
  Qed.

  (* todo: move *)
  Lemma remove_all_some:
    forall x y l sigma,
      M.get x (remove_all sigma l) = Some y ->
      ~ (FromList l x).
  Proof.
    induction l.
    - intros. intro. inv H0.
    - simpl. intros s Hget Hc. destruct (peq a x); subst; inv Hc; try contradiction.
      rewrite M.grs in Hget. congruence.
      rewrite M.grs in Hget. congruence.
      rewrite M.gro in Hget. eapply IHl; eauto.
      eauto.
  Qed.

  Lemma apply_r_list_refl m xs :
    (forall x, x \in FromList xs -> apply_r m x = x) ->
    apply_r_list m xs = xs.
  Proof.
    induction xs; eauto.
    - simpl; intros Hyp. f_equal. eapply Hyp.
      now left. eapply IHxs. 
      intros. eapply Hyp. now right.
  Qed.

  Lemma remove_apply_r_eq m v :
    (forall x, apply_r m x = x) ->
    (forall x, apply_r (M.remove v m) x =x).
  Proof.
    intros Hyp x. unfold apply_r. destruct (peq x v); subst.
    - rewrite M.grs. reflexivity.  
    - rewrite M.gro; eauto.
  Qed.

  Lemma remove_all_apply_r_eq m l :
    (forall x, apply_r m x = x) ->
    (forall x, apply_r (remove_all m l) x =x).
  Proof.
    induction l; intros Hyp x; eauto.
    simpl. rewrite remove_apply_r_eq; eauto.
  Qed.

  Lemma rename_all_refl_mut :
    (forall e m (Hyp : forall x, apply_r m x = x),
        rename_all m e = e) /\
    (forall B m (Hyp : forall x, apply_r m x = x),
        rename_all_fun m B = B).
  Proof.
    exp_defs_induction IHe IHl IHB; intros. 
    - simpl. rewrite apply_r_list_refl; eauto. rewrite IHe. reflexivity.
      eapply remove_apply_r_eq. eassumption.
    - simpl. rewrite Hyp; eauto.
    - simpl. rewrite Hyp; eauto.
      rewrite IHe; eauto. eapply IHl in Hyp. simpl in Hyp.
      do 2 f_equal. inversion Hyp. rewrite H1. eassumption. 
    - simpl. rewrite Hyp, IHe; eauto.
      eapply remove_apply_r_eq. eassumption.
    - simpl. rewrite Hyp, apply_r_list_refl, IHe; eauto.
      eapply remove_apply_r_eq. eassumption.
    - simpl. rewrite IHe, IHB; eauto.
      eapply remove_all_apply_r_eq; eauto.
      eapply remove_all_apply_r_eq; eauto.
    - simpl. rewrite Hyp, apply_r_list_refl; auto.
    - simpl. rewrite apply_r_list_refl; eauto. rewrite IHe. reflexivity.
      eapply remove_apply_r_eq. eassumption.
    - simpl. rewrite Hyp; eauto.
    - simpl. rewrite IHe, IHB; eauto. 
      eapply remove_all_apply_r_eq; eauto.
    - reflexivity. 
  Qed.

  Corollary rename_all_refl :
    forall e m (Hyp : forall x, apply_r m x = x),
      rename_all m e = e.
  Proof.
    eapply rename_all_refl_mut. 
  Qed.

  Lemma preord_env_P_inj_set_l S k rho1 rho2 m x y v v' : 
    preord_env_P_inj cenv PG (S \\ [set x]) k (apply_r m) rho1 rho2 ->
    M.get y rho2 = Some v' ->
    preord_val cenv PG k v v' ->
    preord_env_P_inj cenv PG S k (apply_r (M.set x y m)) (map_util.M.set x v rho1) rho2.
  Proof.
    intros Henv Hg1 Hval z Hin v1 Hgetz.
    destruct (peq z x); subst.
    - eexists. unfold apply_r. rewrite M.gss in *. inv Hgetz. split; eauto.
    - unfold apply_r. rewrite M.gso in *; eauto.
      eapply Henv; eauto. constructor; eauto.
      intros Hc; inv Hc; eauto.
  Qed.

  Lemma preord_env_P_inj_id S k rho1 rho2 : 
    preord_env_P cenv PG S k rho1 rho2 ->
    preord_env_P_inj cenv PG S k id rho1 rho2.
  Proof.
    intros Henv z Hin v1 Hgetz. eapply Henv; eauto. 
  Qed.

  Lemma preord_env_P_inj_map_id S k rho1 rho2 : 
    preord_env_P cenv PG S k rho1 rho2 ->
    preord_env_P_inj cenv PG S k (apply_r (M.empty _)) rho1 rho2.
  Proof.
    intros Henv z Hin v1 Hgetz. unfold apply_r. rewrite M.gempty.
    eapply Henv; eauto. 
  Qed.
  
  
  
  Lemma image'_get_Singleton {A} S x (y : A) :  
    image' (fun z : positive => M.get z (M.set x y (M.empty _))) S \subset [set y].
  Proof.
    intros m [z [Hin Heq]]. destruct (peq z x); subst.
    - rewrite M.gss in Heq. inv Heq. reflexivity. 
    - rewrite M.gso, M.gempty in Heq; eauto. inv Heq.
  Qed. 
                         
  (* rw rule for proj *)
  Lemma rw_proj_equiv x x' t t' ys  y e c n k rho1 rho2 :
      ~ bound_stem_ctx c x ->
      ~ bound_stem_ctx c y ->
      ~ bound_var e y  ->
      x <> y ->
      x' <> y ->
      nthN ys n = Some y ->
      preord_env_P cenv PG (occurs_free (Econstr x t ys (c |[ Eproj x' t' n x e ]|))) k rho1 rho2 ->
      preord_exp cenv P1 PG k (Econstr x t ys (c |[ Eproj x' t' n x e ]|) , rho1 )
                 (Econstr x t ys (c |[ rename y x' e ]|), rho2).
  Proof.
    intros Hn1 Hn2 Hn3 Hleq Hneq Hnth Henv.
    eapply preord_exp_const_compat_alt; eauto.
    + eapply Forall2_same. intros. eapply Henv. now constructor.
    + intros m vs1 vs2 Hlt Hg1 Hg2.
      edestruct (@get_list_nth_get val ys vs2) as [v2 [Hnth2 Hget2]]; eauto.
      edestruct (@get_list_nth_get val ys vs1) as [v1 [Hnth1 Hget1]]; eauto.
      
      assert (Hval : preord_val cenv PG k v1 v2).
      { edestruct preord_env_P_get_list_l as [vs2' [Hg2' Hvs]]; [| | eapply Hg1 |].
        eassumption. normalize_occurs_free; sets. subst_exp. eapply Forall2_nthN'; eassumption. }
      
      eapply preord_exp_compat_stem_vals_le with (xs := [x ; y]) (S1 := Empty_set _);
        [ | | simpl; rewrite M.gss, M.gso, Hget1; eauto | simpl; rewrite M.gss, M.gso, Hget2; eauto | ].
      * intros k1 rho1' rho2' Hpre Hleq1 Hgetl1 Hgetl2.
        eapply ctx_to_rho_preord_exp_l with (C := Eproj_c x' t' n x Hole_c) (P1 := P1).
        
        -- intros; eapply Hless_steps; eauto.
        -- eapply Hpost_zero.
        -- reflexivity.
        -- intros rho1'' Hrho1'; inv Hrho1'. inv H8.
           eapply rename_all_correct.
           ++ eapply Disjoint_Included_l.
              eapply image'_get_Singleton. eapply Disjoint_Singleton_l. eassumption.
           ++ simpl in Hgetl1, Hgetl2.
              destruct (M.get x rho1') eqn:Hgetx1; try congruence. 
              destruct (M.get y rho1') eqn:Hgety1; try congruence. 
              destruct (M.get x rho2') eqn:Hgetx2; try congruence. 
              destruct (M.get y rho2') eqn:Hgety2; try congruence. 
              inv Hgetl2. inv Hgetl1. inv H6.
              eapply preord_env_P_inj_set_l; eauto. eapply preord_env_P_inj_map_id. 
              eapply preord_env_P_antimon. eassumption. normalize_occurs_free; sets.
              subst_exp. eapply preord_val_monotonic; eauto. omega.
      * repeat normalize_sets.
        eapply Union_Disjoint_r; eapply Disjoint_Singleton_r; eauto.
      * eapply preord_env_P_extend.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. omega.
        normalize_occurs_free. now sets.
        rewrite preord_val_eq.  split; eauto.
        edestruct preord_env_P_get_list_l as [vs2' [Hg2' Hvs]]; [| | eapply Hg1 |]. eassumption.
        normalize_occurs_free; sets. eapply Forall2_Forall2_asym_included.
        subst_exp. eapply Forall2_monotonic; [ | eassumption ].
        intros. eapply preord_val_monotonic. eassumption. omega.
  Qed.
  

  (* TODO move  *)
  Lemma preord_var_env_monotonic: forall k rho1 rho2 j z x ,
      preord_var_env cenv PG k rho1 rho2 x z ->
      j <= k ->
      preord_var_env cenv PG j rho1 rho2 x z.
  Proof.
    intros. intro. intros. apply H in H1. destructAll. exists x0; split; auto.
    eapply preord_val_monotonic; eauto.
  Qed.

  (* 
  Lemma fun_inline_compat_clos: forall k fl e rho1 rho2 c e',
      (forall (k' : nat) (rho1' rho2' : env),
          k' <= k ->
          preord_env_P pr cenv (occurs_free e) k' rho1' rho2' ->
          eq_env_P (Union _ (occurs_free_fundefs fl) (name_in_fundefs fl)) (def_funs fl fl rho1 rho1) rho1' ->
          eq_env_P (Union _ (occurs_free_fundefs fl) (name_in_fundefs fl)) (def_funs fl fl rho2 rho2) rho2' ->
          preord_exp pr cenv k' (e, rho1') (e', rho2')) ->
      preord_env_P pr cenv (occurs_free (Efun fl (c|[e]|))) k rho1 rho2 ->
      Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fl)  ->
      Disjoint var (bound_stem_ctx c) (name_in_fundefs fl)  ->
      preord_exp pr cenv k (Efun fl (c |[ e ]|) , rho1) (Efun fl (c|[ e' ]|), rho2).
  Proof.
    intros. intro. intros.
    inv H4.
    eapply preord_exp_compat_vals_stem_set in H10; eauto.
    destructAll.
    eexists. eexists.
    split.
    constructor. eauto. auto.
    - apply Union_Disjoint_r; auto.
    -
      eapply preord_env_P_def_funs_cor.
      rewrite occurs_free_Efun in H0.
      rewrite Union_commut in H0.
      apply H0.
  Qed.
   *)
  
  (* TODO move *)
  Lemma Disjoint_FromList_r A S l x :
      Disjoint A S (FromList l) ->
      List.In x l -> ~ x \in S.
  Proof.
    intros HD Hin Hin'.
    eapply HD; eauto.
  Qed.

  Lemma Disjoint_FromList_cons A S a xs :
      Disjoint A S (FromList (a :: xs)) ->
      Disjoint A S (FromList xs).
  Proof.
    normalize_sets. intros HD. sets.
  Qed.


  Lemma set_list_eqn: forall l,
      set_list l (M.empty var)  =
      fold_right
        (fun (xv : M.elt * M.elt) (cmap : M.t M.elt) =>
           M.set (fst xv) (snd xv) cmap) (M.empty var) l.
  Proof.
    induction l. simpl. auto.
    destruct a. simpl. reflexivity.
  Qed.


  Lemma set_lists_empty_not_in:
    forall a xs ys,
      ~ List.In a xs ->
      M.get a  (fold_right
                  (fun (xv : M.elt * var) (cmap : M.t var) =>
                     M.set (fst xv) (snd xv) cmap) (M.empty var)
                  (combine xs ys)) = None.
  Proof.
    induction xs; intros.
    -  simpl. apply M.gempty.
    - simpl.
      assert (H' := H).
      apply not_in_cons in H.
      destruct H.
      destruct ys.
      simpl. apply M.gempty.
      simpl. rewrite M.gso by auto.
      specialize (IHxs ys H0).
      apply IHxs.
  Qed.

  
  Lemma Disjoint_bindings_find_def: forall f t xs fb fds,
      unique_bindings_fundefs fds ->
      find_def f fds = Some (t, xs, fb) ->
      Disjoint var (bound_var fb) (FromList xs).
  Proof.
    induction fds; intros.
    simpl in H0. destruct (M.elt_eq f v).
    - inv H0.
      inv H. auto.
    - inv H.
      apply IHfds; eauto.
    - inv H0.
  Qed.

  Lemma find_def_free_included:
    forall f t xs fb fds,
      find_def f fds = Some (t, xs, fb) ->
      Included  _
                (Setminus var (Setminus var (occurs_free fb) (FromList xs))
                          (name_in_fundefs fds))
                (occurs_free_fundefs fds).
  Proof.
    induction fds.
    - intros.
      simpl in H.
      rewrite occurs_free_fundefs_Fcons.
      destruct (M.elt_eq f v).
      + subst. inv H.
        simpl.
        eauto 20 with Ensembles_DB.
      + apply IHfds in H.
        simpl.
        intro. intros.
        right.

        assert (In var (occurs_free_fundefs fds) x).
        apply H. inv H0.
        constructor. auto. intro. apply H2. right; auto.
        constructor. auto.
        inv H0. intro.
        apply H3. left. auto.
    -   intros. inv H.
  Qed.



  Context (Hless_steps_app :
             forall (rho1 rho2 rhoc rho' : env) (f f' : var) (ft : fun_tag) 
                    (ys xs : list var) e1 e2 B vs c1 c2,
               M.get f rho1 = Some (Vfun rhoc B f') ->
               get_list ys rho1 = Some vs ->
               find_def f' B = Some (ft, xs, e1) ->
               set_lists xs vs (def_funs B B rhoc rhoc) = Some rho' ->       
               P1 (e1, rho', c1) (e2, rho2, c2) ->
               P1 (Eapp f ft ys, rho1, c1 + cost (Eapp f ft ys)) (e2, rho2, c2)).


  (* TODO move *)
  Lemma preord_exp_app_l
        (k : nat) (rho1 rho2 : env) (f : var) (ft : fun_tag)
        (ys : list var) e2 :
    (* post_Eapp_r P1 P2 e1 rho1 f ft ys rho2 -> *)
    (forall rhoc rho' e1 vs f' xs B,
        get_list ys rho1 = Some vs ->
        M.get f rho1 = Some (Vfun rhoc B f') ->
        find_def f' B = Some (ft, xs, e1) ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rho' ->
        preord_exp cenv P1 PG k (e1, rho') (e2, rho2)) ->
    preord_exp cenv P1 PG k (Eapp f ft ys, rho1) (e2, rho2).
  Proof.
    intros Hyp v c1 Hleq Hstep.
    inv Hstep.
    - eexists OOT, 0. split; [| split ].
      econstructor; eauto. eapply cost_gt_0.
      + eapply Hpost_zero. eassumption.
      + simpl; eauto.
    - inv H0. repeat subst_exp. 
      edestruct Hyp as (v2 & c2 & Hstep' & Hpost & Hval); [ | | | | | eassumption |]; eauto.
      omega.
      eexists. exists c2. split; [ eassumption | split ].
      replace c1 with (c1 - cost (Eapp f ft ys) + cost (Eapp f ft ys)) by omega.
      eapply Hless_steps_app; eauto.
      
      eapply preord_res_monotonic. eassumption. omega.
  Qed. 


  Lemma preord_env_eq_env k S rho1 rho2 rho1' rho2' :
    preord_env_P cenv PG S k rho1 rho2 ->
    eq_env_P S rho1 rho1' ->
    eq_env_P S rho2 rho2' ->
    preord_env_P cenv PG S k rho1' rho2'.
  Proof. 
    intros Henv Heq1 Heq2.
    rewrite <- (Intersection_idempotent S).
    eapply preord_env_P_eq_r; eauto.
    rewrite <- (Intersection_idempotent S).
    eapply preord_env_P_eq_l; eauto.
  Qed.
    
  
  Lemma preord_env_P_inj_set_lists_l S k rho1 rho1' rho2 xs ys vs1 vs2 : 
    preord_env_P cenv PG (S \\ FromList xs) k rho1 rho2 ->

    set_lists xs vs1 rho1 = Some rho1'  ->
    get_list ys rho2 = Some vs2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->      

    preord_env_P_inj cenv PG S k (apply_r (set_list (combine xs ys) (M.empty var))) rho1' rho2.
  Proof.
    revert S k rho1 rho1' rho2 ys vs1 vs2; induction xs;
      intros S k rho1 rho1' rho2 ys vs1 vs2 Henv Hset Hget Hvall.
    - simpl in Hset. destruct vs1; try congruence. inv Hset.
      inv Hvall. destruct ys; simpl in Hget; try congruence.
      intros z Hin v1 Hgetz. unfold apply_r. rewrite M.gempty. eapply Henv.
      constructor; eauto. eassumption.

      destruct (M.get e rho2); try congruence.
      destruct (get_list ys rho2); try congruence.
    - simpl in Hset. destruct vs1; try congruence.
      destruct vs2 as [|v' vs2]; inv Hvall.
      destruct (set_lists xs vs1 rho1) eqn:Hset1'; try congruence. inv Hset.
      destruct ys as [| y ys]; simpl in Hget; try congruence. 
      destruct (M.get y rho2) eqn:Hgety; try congruence.
      destruct (get_list ys rho2) eqn:Hgetys; try congruence.
      inv Hget. simpl. 

      eapply preord_env_P_inj_set_l; [| eassumption | eassumption ]. 

      eapply IHxs. eapply preord_env_P_antimon. eassumption.
      normalize_sets. rewrite Setminus_Union. sets.
      eassumption. eassumption. eassumption. 
  Qed.

  Lemma image'_get_set_list S xs1 vs1 :
    image' (fun x : positive => M.get x (set_list (combine xs1 vs1) (M.empty var))) S \subset (FromList vs1).
  Proof.
    revert vs1; induction xs1; intros vs1. simpl.
    - intros m [z [Hin Heq]]. rewrite M.gempty in Heq. inv Heq.
    - destruct vs1; simpl.
      + intros m [z [Hin Heq]]. rewrite M.gempty in Heq. inv Heq.
      + intros m [z [Hin Heq]].
        destruct (peq z a); subst. rewrite M.gss in Heq. inv Heq.
        now left.
        right. eapply IHxs1. eexists; split; eauto.
        rewrite M.gso in Heq. eassumption. eassumption. 
  Qed. 
  
  
  (* Main lemma for function inlining *)
  Lemma rw_fun_corr f fds t xs fb vs c rho1 rho2 k : 
    find_def f fds = Some (t, xs, fb) ->
    
    Disjoint _ (FromList xs :|: bound_var fb) (FromList vs) ->
    unique_functions fds ->
    Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
    Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->
    
    preord_env_P cenv PG (occurs_free (Efun fds (c |[ Eapp f t vs ]|))) k rho1 rho2 ->
    preord_exp cenv P1 PG k
               (Efun fds (c |[ Eapp f t vs ]|), rho1)
               (Efun fds (c |[ (rename_all (set_list (combine xs vs) (M.empty var)) fb)]|), rho2).
  Proof.
    intros Hf1 Hd1 Hun1 Hd2 Hd3 Hpre.
    eapply preord_exp_fun_compat; eauto.
    assert (Hget1 : M.get f (def_funs fds fds rho1 rho1) = Some (Vfun rho1 fds f)). 
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }
    assert (Hget2 : M.get f (def_funs fds fds rho2 rho2) = Some (Vfun rho2 fds f)). 
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }

    eapply preord_exp_compat_vals_stem_set with (S1 := name_in_fundefs fds :|: occurs_free_fundefs fds) (S :=  name_in_fundefs fds :|: occurs_free_fundefs fds). 
    
    (* eapply preord_exp_compat_stem_vals_le with (xs := [f]) *)
    (*                                            (S1 := name_in_fundefs fds :|: occurs_free_fundefs fds); *)
    (*   [ | | simpl; rewrite Hget1; reflexivity | simpl; rewrite Hget2; reflexivity | ]. *)
    * intros k1 rho1' rho2' Hleq1 Hpre' Heq1 Heq2. 
      
      (*        Hgetl1 Hgetl2. *)
      (* simpl in Hgetl1, Hgetl2. *)
      (* destruct (M.get f rho1') eqn:Hgetx1; try congruence.  *)
      (* destruct (M.get f rho2') eqn:Hgetx2; try congruence.        *)
      (* inv Hgetl1; inv Hgetl2. *)

      assert (Hf1' := Hf1).
      eapply find_def_correct in Hf1; eapply fun_in_fundefs_name_in_fundefs in Hf1.      
      eapply preord_exp_app_l. intros rhoc rho' e1 vs1 f' xs1 B Hgetl Hget Hf Hset.
      rewrite def_funs_eq in Hget1, Hget2; eauto.
      inv Hget1; inv Hget2.
       
      
      (* eapply preord_env_eq_env.  *)
      (* eapply preord_exp_compat_vals_stem_set. in Hleq1.  *)
      (* repeat subst_exp. *)
      
      (* edestruct preord_env_P_get_list_l as [vs2 [Hget' Hvall]]; [ | | eassumption | ]. eapply Hpre'. *)
      (* normalize_occurs_free. now sets. *)
      (* do 2 subst_exp. *) 
      rewrite <- Heq1 in Hget. rewrite def_funs_eq in Hget; eauto. inv Hget. repeat subst_exp.
       
      eapply rename_all_correct.
      ++ eapply Disjoint_Included_l. eapply image'_get_set_list. 
         eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
         now sets.

      ++ edestruct preord_env_P_get_list_l as [vs2 [Hget' Hvall]]; [ | | eassumption | ]. eassumption.
         normalize_occurs_free. sets. 
         (* erewrite <- get_list_def_funs_Disjoint in Hget'.         *)
         eapply preord_env_P_inj_set_lists_l; [ | | | ]; eauto.
 
         eapply preord_env_eq_env.
         ** eapply preord_env_P_antimon. 
            eapply preord_env_P_def_funs_pre. eassumption.
            { intros. eapply preord_exp_refl; eauto. }
            eapply preord_env_P_monotonic; [| eassumption ]. omega.
            eapply Setminus_Included_Included_Union.
            eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct; eauto.
            normalize_occurs_free. sets.
         ** eapply eq_env_P_refl.
         ** intros x Hin. eapply Heq2. inv Hin. eapply occurs_free_in_fun in H; [| eapply find_def_correct; eassumption ].
            inv H; eauto. contradiction. 
      ++ now left.
    * sets.
    * eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_pre with (e := c |[ Eapp f t vs ]|); eauto.
      { intros. eapply preord_exp_refl; eauto. }
      eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. omega. reflexivity.
      normalize_occurs_free. rewrite <- Union_assoc, <- Union_Setminus; tci. sets.
  Qed.

  Lemma eq_env_P_set_not_in_P_l (A : Type) (x : map_util.M.elt) (v : A)
        (P : Ensemble map_util.M.elt) (rho1 rho2 : map_util.M.t A) : 
    eq_env_P P rho1 rho2 ->
    ~ x \in P ->
    eq_env_P P (map_util.M.set x v rho1) rho2.
  Proof.
    intros Heq Hnin z Hin.
    rewrite M.gso; eauto.
    intros Hc; subst; contradiction. 
  Qed.


  Lemma interpret_ctx_eq_env_P S C rho rho' n :
    interpret_ctx_fuel cenv C rho (Res rho') n ->
    Disjoint _ (bound_var_ctx C) S ->
    eq_env_P S rho rho'.
  Proof.
    revert rho rho' n; induction C; intros rho rho' cost Hin Hd; inv Hin.
    - inv H0. eapply eq_env_P_refl.
    - inv H0. rewrite bound_var_Econstr_c in *.      
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. sets.
    - inv H0. rewrite bound_var_Eproj_c in *.      
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. sets.
    - inv H0.
    - inv H0. rewrite bound_var_Eletapp_c in *.      
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_sym. eapply eq_env_P_set_not_in_P_l; eauto.
      eapply eq_env_P_refl. eapply Disjoint_In_l. sets. sets.
    - inv H0.
    - inv H0. rewrite bound_var_Fun1_c in *.      
      eapply eq_env_P_trans; [| eapply IHC; [ eassumption | now sets ] ].
      eapply eq_env_P_def_funs_not_in_P_r. eapply eq_env_P_refl.
      eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs. sets.
    - inv H0.
  Qed.

  Lemma preord_env_P_inj_eq_r S S' sig k rho1 rho2 rho3 :
      preord_env_P_inj cenv PG S k sig rho1 rho2 ->
      eq_env_P (image sig S') rho2 rho3 ->
      preord_env_P_inj cenv PG (Intersection _ S  S') k sig rho1 rho3.
  Proof.
    intros Henv Heq x Hin v Hget. inv Hin.
    rewrite <- Heq; eauto. eapply Henv; eauto.
    eapply In_image. eassumption.
  Qed.

  Lemma preord_env_P_inj_eq_l S S' sig k rho1 rho2 rho3 :
      preord_env_P_inj cenv PG S k sig rho1 rho2 ->
      eq_env_P S' rho1 rho3 ->
      preord_env_P_inj cenv PG (Intersection _ S  S') k sig rho3 rho2.
  Proof.
    intros Henv Heq x Hin v Hget. inv Hin.
    rewrite <- Heq in Hget; eauto. eapply Henv; eauto.
  Qed.  

  Lemma preord_env_P_inj_eq_env_P S sig k rho1 rho2 rho3 rho4 :
    preord_env_P_inj cenv PG S k sig rho1 rho2 ->
    eq_env_P S rho1 rho3 ->
    eq_env_P (image sig S) rho2 rho4 ->
    preord_env_P_inj cenv PG S k sig rho3 rho4.
  Proof.
    intros Henv Heq1 Heq2.
    rewrite <- (Intersection_idempotent S). 
    eapply preord_env_P_inj_eq_l; eauto.
    rewrite <- (Intersection_idempotent S). 
    eapply preord_env_P_inj_eq_r; eauto.
  Qed.  

  
  Lemma inline_letapp_correct k x sig f t ys e1 e2 e' C C' x' rho1 rho2 : 
    (forall m rhoc rhoc' B f' xs vs e,
        m < k -> 
        M.get f rho1 = Some (Vfun rhoc B f') ->
        find_def f' B = Some (t, xs, e) ->
        get_list ys rho1 = Some vs ->
        set_lists xs vs (def_funs B B rhoc rhoc) = Some rhoc' ->
        preord_exp cenv P1 PG m (e, rhoc') (C' |[ e' ]|, rho2)) ->

    (forall m rho1 rho2 sig,
        m < k ->
        preord_env_P_inj cenv PG (occurs_free e1) m sig rho1 rho2 ->
        preord_exp cenv P1 PG m (e1, rho1) (e2, rho2)) ->

    preord_env_P_inj cenv PG (occurs_free (Eletapp x f t ys e1)) k sig rho1 rho2 ->
    
    Disjoint _ (bound_var_ctx C' :|: bound_var_ctx C) (image sig (occurs_free e1 \\ [set x])) ->    
    ~ x' \in (image sig (occurs_free e1 \\ [set x])) ->
    interprable C' = true ->
    inline_letapp e' x = Some (C, x') ->
    
    preord_exp cenv P1 PG k (Eletapp x f t ys e1, rho1) (C' |[ C |[ e2 ]| ]|, rho2).
  Proof.
    revert C' k x sig f t ys e1 e2 C x' rho1 rho2; induction e';
      intros C' k x sig f' t ys e1 e2 C x' rho1 rho2 Hyp1 Hyp2 Hpre Hdis Him Hint Hin; simpl in Hin;
        try match goal with
        | [ _ : context [inline_letapp ?E ?X] |- _ ] =>
          (destruct (inline_letapp E X) as [ [C'' u] | ] eqn:Hin'; simpl in Hin; inv Hin)
        end.
    - intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        eapply Hpost_zero; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Econstr_c v c l Hole_c)) k) with (C := C'') as [r2 [c2' [Hs2 [Hp2 Hv2]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * admit.
        * eassumption. 
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption. 
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 2 eexists. 
          split; [| split ]. eassumption. eassumption. eassumption.
    - inv Hin.
    - intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        now eapply Hpost_zero; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Eproj_c v c n v0 Hole_c)) k) with (C := C'') as [r2 [c2' [Hs2 [Hp2 Hv2]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * admit.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption. 
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 2 eexists.
          split; [| split ]. eassumption. eassumption. eassumption. 
    - intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        now eapply Hpost_zero; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Eletapp_c v v0 f l Hole_c)) k) with (C := C'') as [r2 [c2' [Hs2 [Hp2 Hv2]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * admit.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption. 
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 2 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        now eapply Hpost_zero; eauto. now simpl; eauto.
      + edestruct (IHe' (comp_ctx_f C' (Efun1_c f  Hole_c)) k) with (C := C'') as [r2 [c2' [Hs2 [Hp2 Hv2]]]].
        9:{ econstructor 2; eauto. }
        * rewrite <- app_ctx_f_fuse. simpl ( _ |[ _ ]|). eapply Hyp1.
        * eapply Hyp2.
        * eassumption.
        * admit.
        * eassumption.
        * eapply interprable_comp_f_l; eauto.
        * eassumption.
        * eassumption. 
        * rewrite <- app_ctx_f_fuse in *. simpl in *. do 2 eexists.
          split; [| split ]. eassumption. eassumption. eassumption.
    - inv Hin. simpl (_ |[ _ ]|).
      intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        now eapply Hpost_zero; eauto. now simpl; eauto.
      + inv H0. 

        * edestruct (Hyp1 (k -1)) as [r2 [c2' [Hs2 [Hp2 Hv2]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          simpl in *; omega. simpl in *; omega.
          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ].
          destruct Hs2 as (rho2' & n1 & n2 & Hadd & Hctx & Heval); subst.
          inv Heval.
          edestruct (Hyp2 (k - 1 - cin1)) with (rho2 := M.set x' v1 rho2') as [r3 [c3 [Hs3 [Hp3 Hv3]]]];
            [ | | | now eapply H14 | ]; eauto.
          simpl in *; omega.

          { eapply preord_env_P_inj_set_alt; [| eassumption | eassumption ].
            eapply preord_env_P_inj_eq_env_P; [| eapply eq_env_P_refl | ].
            2:{ eapply interpret_ctx_eq_env_P. eassumption. sets. }
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. omega. normalize_occurs_free. sets. } 
            
          simpl in *; omega.
          inv H1. 
          exists r3, (n1 + (n2 + c3)).
          split. eapply interpret_ctx_bstep_r. eassumption.
          constructor 2.
          2:{ simpl; replace (n2 + c3 - S (Datatypes.length l))
                      with (n2 - cost (Eapp v f l) + c3) by (simpl in *; omega).
              econstructor; eauto. } simpl in *; omega.
          split. 
          admit. (* post *)
          eapply preord_res_monotonic. eassumption. simpl in *; omega.
        * edestruct (Hyp1 (k -1)) as [r2 [c2' [Hs2 [Hp2 Hv2]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          simpl in *; omega. simpl in *; omega.
          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, c2'. split; [| split ]. 
          
          admit. (* lemma *)
          admit. (* post *)
          simpl; eauto. 
    - intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        now eapply Hpost_zero; eauto. now simpl; eauto.
      + inv H0.
        
        * edestruct (Hyp1 (k -1)) as [r2 [c2' [Hs2 [Hp2 Hv2]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          simpl in *; omega. simpl in *; omega.
          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ].
          destruct Hs2 as (rho2' & n1 & n2 & Hadd & Hctx & Heval); subst.
          inv Heval. inv H1.
        * edestruct (Hyp1 (k -1)) as [r2 [c2' [Hs2 [Hp2 Hv2]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          simpl in *; omega. simpl in *; omega.
          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, c2'. split; [| split ]. 

          admit. (* lemma *)
          admit. (* post *)
          simpl; eauto. 
    - inv Hin. simpl (_ |[ _ ]|). 
      intros r1 c2 Hleq Hs1. inv Hs1.
      + exists OOT, 0. split; [| split ]; eauto. constructor. eapply cost_gt_0.
        now eapply Hpost_zero; eauto. now simpl; eauto.
      + inv H0.

        * edestruct (Hyp1 (k -1)) as [r2 [c2' [Hs2 [Hp2 Hv2]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          simpl in *; omega. simpl in *; omega.
          destruct r2; [ simpl in Hv2; contradiction | ].
          eapply interpret_ctx_bstep_l in Hs2; [| eassumption ].
          destruct Hs2 as (rho2' & n1 & n2 & Hadd & Hctx & Heval); subst.
          inv Heval. inv H1. assert (Heq : n2 = 1) by (simpl in *; omega). subst. 
          edestruct (Hyp2 (k - 1 - cin1)) with (rho2 := rho2') as [r3 [c3 [Hs3 [Hp3 Hv3]]]];
            [ | | | now eapply H14 | ]; eauto.
          simpl in *; omega.
          admit. (* with peq *)
          simpl in *; omega.
          do 2 eexists. split. eapply interpret_ctx_bstep_r. eassumption. eassumption. 
          split. admit. (* post *)
          eapply preord_res_monotonic. eassumption. simpl in *; omega.

        * edestruct (Hyp1 (k -1)) as [r2 [c2' [Hs2 [Hp2 Hv2]]]]; [ | | | | | | now eapply H13 | ]; eauto.
          simpl in *; omega. simpl in *; omega.
          destruct r2; [ | simpl in Hv2; contradiction ].

          eexists OOT, (c2' - 1). split; [| split ]. 

          admit. (* lemma *)
          admit. (* post *)
          simpl; eauto. 

        
  (* Letapp inlining *)
  Lemma rw_fun_letapp_corr x f fds t xs fb vs c rho1 rho2 k z z' C' e1 :
    find_def f fds = Some (t, xs, fb) ->
    
    Disjoint _ (FromList xs :|: bound_var fb) (FromList vs) ->
    unique_functions fds ->
    Disjoint var (bound_stem_ctx c) (occurs_free_fundefs fds)  ->
    Disjoint var (bound_stem_ctx c) (name_in_fundefs fds)  ->

    inline_letapp
      (rename_all
         (set_list (combine xs vs) (M.empty var)) fb) x = Some (C', x') ->

    preord_env_P cenv PG (occurs_free (Efun fds (c |[ Eapp f t vs ]|))) k rho1 rho2 ->
    preord_exp cenv P1 PG k
               (Efun fds (c |[ Eletapp x f t vs e1 ]|), rho1)
               (Efun fds (c |[ C' |[ e1 ]| ]|), rho2).
  Proof.
    intros Hf1 Hd1 Hun1 Hd2 Hd3 Hnd Hpre.
    eapply preord_exp_fun_compat; eauto.
    assert (Hget1 : M.get f (def_funs fds fds rho1 rho1) = Some (Vfun rho1 fds f)). 
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }
    assert (Hget2 : M.get f (def_funs fds fds rho2 rho2) = Some (Vfun rho2 fds f)). 
    { rewrite def_funs_eq. reflexivity. eapply fun_in_fundefs_name_in_fundefs. eapply find_def_correct.
      eassumption. }

    eapply preord_exp_compat_vals_stem_set with (S1 := name_in_fundefs fds :|: occurs_free_fundefs fds) (S :=  name_in_fundefs fds :|: occurs_free_fundefs fds). 
    
    (* eapply preord_exp_compat_stem_vals_le with (xs := [f]) *)
    (*                                            (S1 := name_in_fundefs fds :|: occurs_free_fundefs fds); *)
    (*   [ | | simpl; rewrite Hget1; reflexivity | simpl; rewrite Hget2; reflexivity | ]. *)
    * intros k1 rho1' rho2' Hleq1 Hpre' Heq1 Heq2. 
      
      (*        Hgetl1 Hgetl2. *)
      (* simpl in Hgetl1, Hgetl2. *)
      (* destruct (M.get f rho1') eqn:Hgetx1; try congruence.  *)
      (* destruct (M.get f rho2') eqn:Hgetx2; try congruence.        *)
      (* inv Hgetl1; inv Hgetl2. *)

      assert (Hf1' := Hf1).
      eapply find_def_correct in Hf1; eapply fun_in_fundefs_name_in_fundefs in Hf1.      
      eapply preord_exp_app_l. intros rhoc rho' e1 vs1 f' xs1 B Hgetl Hget Hf Hset.
      rewrite def_funs_eq in Hget1, Hget2; eauto.
      inv Hget1; inv Hget2.
       
      
      (* eapply preord_env_eq_env.  *)
      (* eapply preord_exp_compat_vals_stem_set. in Hleq1.  *)
      (* repeat subst_exp. *)
      
      (* edestruct preord_env_P_get_list_l as [vs2 [Hget' Hvall]]; [ | | eassumption | ]. eapply Hpre'. *)
      (* normalize_occurs_free. now sets. *)
      (* do 2 subst_exp. *) 
      rewrite <- Heq1 in Hget. rewrite def_funs_eq in Hget; eauto. inv Hget. repeat subst_exp.
       
      eapply rename_all_correct.
      ++ eapply Disjoint_Included_l. eapply image'_get_set_list. 
         eapply Disjoint_sym. eapply Disjoint_Included_l; [| eassumption ].
         now sets.

      ++ edestruct preord_env_P_get_list_l as [vs2 [Hget' Hvall]]; [ | | eassumption | ]. eassumption.
         normalize_occurs_free. sets. 
         (* erewrite <- get_list_def_funs_Disjoint in Hget'.         *)
         eapply preord_env_P_inj_set_lists_l; [ | | | ]; eauto.
 
         eapply preord_env_eq_env.
         ** eapply preord_env_P_antimon. 
            eapply preord_env_P_def_funs_pre. eassumption.
            { intros. eapply preord_exp_refl; eauto. }
            eapply preord_env_P_monotonic; [| eassumption ]. omega.
            eapply Setminus_Included_Included_Union.
            eapply Included_trans. eapply occurs_free_in_fun. eapply find_def_correct; eauto.
            normalize_occurs_free. sets.
         ** eapply eq_env_P_refl.
         ** intros x Hin. eapply Heq2. inv Hin. eapply occurs_free_in_fun in H; [| eapply find_def_correct; eassumption ].
            inv H; eauto. contradiction. 
      ++ now left.
    * sets.
    * eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_pre with (e := c |[ Eapp f t vs ]|); eauto.
      { intros. eapply preord_exp_refl; eauto. }
      eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ]. omega. reflexivity.
      normalize_occurs_free. rewrite <- Union_assoc, <- Union_Setminus; tci. sets.
  Qed.

        
  (* can be restricted to bound_var on the path to hole in c *)
  Lemma occurs_free_app_bound_var x e:
    occurs_free e x ->
    ( forall c,
        ~ occurs_free (c |[e]|) x ->
        bound_var_ctx c x) /\
    ( forall fds,
        ~ occurs_free_fundefs (fds <[e]>) x ->
        bound_var_fundefs_ctx fds x).
  Proof.
    intro H.
    apply exp_fundefs_ctx_mutual_ind; intros.
    + exfalso. apply H0. apply H.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor 2. apply H0. intro. apply H1.
      apply occurs_free_Econstr.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eproj.
      right.
      split; auto.
    + simpl in H1.
      destruct (var_dec v x).
      subst. constructor.
      constructor. apply H0. intro. apply H1.
      apply occurs_free_Eprim.
      right.
      split; auto.
    + constructor. apply H0.
      intro.
      apply H1.
      simpl.
      eapply occurs_free_Ecase_Included.
      2: apply H2.
      apply in_app. right. constructor; auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs f4).
      destruct Hv. specialize (Dec x). destruct Dec.
      constructor.
      apply name_in_fundefs_bound_var_fundefs.
      auto.
      apply Bound_Fun12_c. apply H0. intro.
      apply H1.
      apply Free_Efun1; auto.
    + simpl in H1.
      constructor.
      apply H0. intro.
      apply H1.
      apply Free_Efun2.
      auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l (e0 |[ e ]|) f6)).
      destruct Hv. destruct (Dec x) as [Hin | Hnin].
      inv Hin. inv H2.
      constructor.
      constructor 4.
      apply name_in_fundefs_bound_var_fundefs. auto.
      assert (Hl := Decidable_FromList l).
      destruct Hl. destruct (Dec0 x) as [Hin | Hnin'].
      constructor 2; auto.
      constructor 3. apply H0. intro. apply H1. constructor; auto.
      intro. subst. apply Hnin. constructor. auto.
      intro. apply Hnin. constructor 2. auto.
    + simpl in H1.
      assert (Hv := Decidable_name_in_fundefs (Fcons v t l e0 (f7 <[ e ]>))).
      destruct Hv. destruct (Dec x) as [Hin | Hnin].
      inv Hin. now inv H2; eauto.
      apply Bound_Fcons24_c.
      eapply name_boundvar_ctx. eassumption.
      apply Bound_Fcons24_c.
      apply H0. intro. apply H1.
      constructor 2. apply H2.
      intro; apply Hnin. subst.
      constructor. auto.
  Qed.

  Lemma ub_find_def_nodup: forall t xs fb f fds,
      unique_bindings_fundefs fds ->
      find_def f fds = Some (t,xs,fb) ->
      NoDup xs.
  Proof.
    induction fds; intros.
    - simpl in H0.
      inv H.
      destruct (M.elt_eq f v).
      inv H0; auto.
      apply IHfds; auto.
    -           inv H0.
  Qed.

  Lemma Disjoint_bindings_fundefs: forall t f xs fb fds,
      unique_bindings_fundefs fds ->
      find_def f fds = Some (t, xs, fb) ->
      Disjoint _ (name_in_fundefs fds) (Union _ (FromList xs) (bound_var fb)).
  Proof.
    induction fds; intros.
    - simpl in H0.
      destruct (M.elt_eq f v).
      + subst.
        inv H0.
        simpl.
        inv H.
        split. intro. intro. inv H.
        inv H0.
        inv H.
        inv H1.
        apply H10; auto.
        apply H5; auto.
        inv H1.
        inv H8. specialize (H1 x). apply H1. split; auto.
        apply name_in_fundefs_bound_var_fundefs. auto.
        inv H9. specialize (H1 x). apply H1. split; auto.
        apply name_in_fundefs_bound_var_fundefs. auto.
      + inv H. simpl. specialize (IHfds H14 H0).
        apply Union_Disjoint_l; auto.
        split. intro. intro. destruct H. inv H.
        inv H1.
        apply H7.
        eapply name_boundvar_arg.
        apply H. apply H0.
        apply H7.
        eapply bv_in_find_def.
        apply H0. apply H.
    - inv H0.
  Qed.


  Lemma rw_correct e e' :
    gr_clos e e' ->
    forall rho rho' k,
      preord_env_P pr cenv (occurs_free e) k rho rho'->
      preord_exp pr cenv k (e, rho) (e', rho').
  Proof with now eauto.
    intros H.
    induction H; intros.
    - intros.
      inv H.
      inv H1.
      + apply preord_exp_compat; auto.
        intros.
        apply rm_constr; auto.
      + apply preord_exp_compat; auto.
        intros.
        apply rm_prim; auto.
      + apply preord_exp_compat; auto.
        intros.
        apply rm_proj; auto.
      + apply preord_exp_compat; auto.
        intros.
        apply rm_fundefs_of; auto.
      + eapply preord_exp_compat; auto.
        intros.
        eapply rm_any_fundefs; auto.
      + eapply preord_exp_compat; auto.
        intros.
        apply rw_case_equiv; auto.

      + eapply preord_exp_compat; auto.
        intros.
        apply rw_proj_equiv; auto.
      + eapply preord_exp_compat; auto.
        intros.

        apply rw_fun_corr; auto.
    - apply preord_exp_refl; auto.
    - eapply preord_exp_trans; eauto.
      intros.
      eapply IHclos_refl_trans2.
      apply preord_env_P_refl.
  Qed.

End Shrink_correct.





Lemma bound_var_rename_all:
  (forall e sigma,
      Same_set _ (bound_var e) (bound_var (rename_all sigma e))) /\
  (forall fds sigma,
      Same_set _ (bound_var_fundefs fds) (bound_var_fundefs (rename_all_fun sigma fds))).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - do 2 (rewrite bound_var_Econstr).
    rewrite H. reflexivity.
  - do 2 (rewrite bound_var_Ecase_nil). reflexivity.
  - do 2 (rewrite bound_var_Ecase_cons). rewrite <- H. simpl in H0. rewrite <- H0. reflexivity.
  - do 2 (rewrite bound_var_Eproj). rewrite <- H. reflexivity.
  - do 2 (rewrite bound_var_Efun). rewrite <- H. rewrite <- H0. reflexivity.
  - do 2 (rewrite bound_var_Eapp).
    reflexivity.
  - do 2 (rewrite bound_var_Eprim).
    rewrite <- H.
    reflexivity.
  - do 2 (rewrite bound_var_Ehalt).
    reflexivity.
  - do 2 (rewrite bound_var_fundefs_Fcons).
    rewrite <- H.
    rewrite <- H0.
    reflexivity.
  - rewrite bound_var_fundefs_Fnil.
    reflexivity.
Qed.

Lemma bound_var_rename_all_ns_mut:
  forall sigma,
    (forall (e : exp),
        bound_var e <--> bound_var (rename_all_ns sigma e)) /\
    (forall (fds : fundefs),
        bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  intro sig.
  apply exp_def_mutual_ind; intros; simpl; repeat (normalize_bound_var); split; try (rewrite H); try (rewrite H0); auto with Ensembles_DB.
Qed.

Lemma bound_var_rename_all_ns:
  (forall (e : exp) sigma,
      bound_var e <--> bound_var (rename_all_ns sigma e)).
Proof.
  intros. apply bound_var_rename_all_ns_mut.
Qed.

Lemma bound_var_rename_all_ns_fundefs:
  (forall (fds : fundefs) sigma,
      bound_var_fundefs fds <--> bound_var_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  intros. apply bound_var_rename_all_ns_mut.
Qed.


(* could prove <-> *)
Lemma unique_bindings_rename_all:
  (forall e sigma,
      unique_bindings e -> unique_bindings (rename_all sigma e)) /\
  (forall fds sigma,
      unique_bindings_fundefs fds -> unique_bindings_fundefs (rename_all_fun sigma fds)).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - inv H0. eapply H in H6.
    constructor; eauto.
    intro. apply H3.
    eapply (proj1 bound_var_rename_all).
    apply H0.
  - constructor.
  - inv H1.
    constructor.
    eapply H0 in H5.
    simpl in H5. apply H5.
    apply H. auto.
    rewrite <- (proj1 bound_var_rename_all).
    rewrite (proj1 bound_var_rename_all) with (e := (Ecase v l)) in H8.
    simpl in H8.
    apply H8.
  - inv H0.
    constructor; auto.
    intro; apply H3.
    eapply (proj1 bound_var_rename_all).
    eauto.
  - inv H1.
    constructor.
    apply H0. auto.
    apply H; auto.
    rewrite <- (proj1 bound_var_rename_all).
    rewrite <- (proj2 bound_var_rename_all).
    auto.
  - constructor.
  - inv H0; constructor.
    intro; apply H3.
    eapply (proj1 bound_var_rename_all).
    apply H0.
    apply H.
    auto.
  - constructor.
  - inv H1.
    constructor; auto.
    intro; apply H7.
    eapply (proj1 bound_var_rename_all).
    eauto.
    intro; apply H8.
    eapply (proj2 bound_var_rename_all).
    eauto.
    rewrite <- (proj1 bound_var_rename_all). auto.
    rewrite <- (proj2 bound_var_rename_all). auto.
    rewrite <- (proj1 bound_var_rename_all).
    rewrite <- (proj2 bound_var_rename_all).
    auto.
  - constructor.
Qed.

Lemma unique_bindings_rename_all_ns:
  (forall e sigma,
      unique_bindings e -> unique_bindings (rename_all_ns sigma e)) /\
  (forall fds sigma,
      unique_bindings_fundefs fds -> unique_bindings_fundefs (rename_all_fun_ns sigma fds)).
Proof.
  apply exp_def_mutual_ind; intros; simpl.
  - inv H0. eapply H in H6.
    constructor; eauto.
    intro. apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
  - constructor.
  - inv H1.
    constructor.
    eapply H0 in H5.
    simpl in H5. apply H5.
    apply H. auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite (bound_var_rename_all_ns) with (e := (Ecase v l)) in H8.
    simpl in H8.
    apply H8.
  - inv H0.
    constructor; auto.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    eauto.
  - inv H1.
    constructor.
    apply H0. auto.
    apply H; auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite <- (bound_var_rename_all_ns_fundefs).
    auto.
  - constructor.
  - inv H0; constructor.
    intro; apply H3.
    eapply (bound_var_rename_all_ns).
    apply H0.
    apply H.
    auto.
  - constructor.
  - inv H1.
    constructor; auto.
    intro; apply H7.
    eapply (bound_var_rename_all_ns).
    eauto.
    intro; apply H8.
    eapply (bound_var_rename_all_ns_fundefs).
    eauto.
    rewrite <- (bound_var_rename_all_ns). auto.
    rewrite <- (bound_var_rename_all_ns_fundefs). auto.
    rewrite <- (bound_var_rename_all_ns).
    rewrite <- (bound_var_rename_all_ns_fundefs).
    auto.
  - constructor.
Qed.

Lemma ub_fun_inlining: forall B1   xs fb B2 c f t vs c',
    unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)  ->
    unique_bindings (c' |[ Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) ]|) ]|).
Proof.
  intros.
  apply ub_app_ctx_f.
  apply ub_app_ctx_f in H.
  destructAll.
  split; auto.
  rewrite inv_app_Efun1 in H0. rewrite app_ctx_f_fuse in H0.
  apply ub_app_ctx_f in H0.
  destructAll.
  split.

  rewrite inv_app_Efun1. rewrite app_ctx_f_fuse.
  apply ub_app_ctx_f.
  split.

  {
    simpl.
    simpl in H0. inv H0.
    constructor; eauto.
    eapply fundefs_append_unique_bindings_l in H7.
    2: reflexivity.
    destructAll.
    eapply fundefs_append_unique_bindings_r; eauto. inv H4. auto.
    eapply Disjoint_Included_r. 2: apply H5.
    rewrite bound_var_fundefs_Fcons. right; right; right;  auto.
    eapply Disjoint_Included_r. 2: apply H8.
    rewrite fundefs_append_bound_vars.
    2: reflexivity.
    intro. intros.
    rewrite fundefs_append_bound_vars.  2: reflexivity.
    inv H0. left; auto.
    right.
    rewrite bound_var_fundefs_Fcons.
    right; right; right; auto.
  }
  split.

  apply unique_bindings_rename_all_ns.
  simpl in H0. inv H0.
  eapply fundefs_append_unique_bindings_l in H7. 2: reflexivity. destructAll.
  inv H4. auto.

  simpl. rewrite bound_var_Fun1_c.
  rewrite <- bound_var_rename_all_ns.
  simpl in H0. inv H0.
  apply Union_Disjoint_l.

  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  apply Union_Disjoint_l.

  eapply fundefs_append_unique_bindings_l in H7.
  2: apply reflexivity.
  destructAll.
  eapply Disjoint_Included_r. 2: apply H5. rewrite bound_var_fundefs_Fcons. right; right; left; auto.
  eapply fundefs_append_unique_bindings_l in H7.
  2: apply reflexivity.
  destructAll.
  inv H4. apply Disjoint_sym.
  auto.

  eapply Disjoint_Included_r.
  2: apply H8.
  rewrite fundefs_append_bound_vars.
  2: reflexivity.
  right. constructor 3. auto.

  eapply Disjoint_Included_r.
  2: apply H1.
  do 2 (rewrite bound_var_Efun).
  do 2 (rewrite bound_var_app_ctx).
  erewrite fundefs_append_bound_vars. 2: reflexivity.
  intro. intros.
  erewrite fundefs_append_bound_vars. 2: reflexivity.
  rewrite bound_var_fundefs_Fcons.
  inv H4. inv H5. eauto with Ensembles_DB.
  left; right; right; right; right. auto.
  inv H5.
  right. left; auto.
  left; right; right; right; left. rewrite <- bound_var_rename_all_ns in H4.  auto.
Qed.

Lemma ub_constr_dead: forall c x t ys e,
    unique_bindings (c |[ Econstr x t ys e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Econstr.
  left; auto.
Qed.

Lemma ub_prim_dead: forall c x t ys e,
    unique_bindings (c |[ Eprim x t ys e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Eprim.
  left; auto.
Qed.

Lemma ub_proj_dead: forall c x t n y e,
    unique_bindings (c |[ Eproj x t n y e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Eproj.
  left; auto.
Qed.

Lemma ub_fun_dead: forall c fds e,
    unique_bindings (c |[ Efun fds e]|)  ->
    unique_bindings (c |[e]|).
Proof.
  intros.
  apply ub_app_ctx_f in H.
  apply ub_app_ctx_f.
  destructAll.
  split; auto.
  inv H0.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H1.
  rewrite bound_var_Efun.
  right; auto.
Qed.

Lemma ub_case_inl: forall c x cl e,
    (exists co, findtag cl co = Some e) ->
    unique_bindings (c |[ Ecase x cl ]|) ->
    unique_bindings (c |[ e]|).
Proof.
  intros.
  apply ub_app_ctx_f.
  apply ub_app_ctx_f in H0.
  destructAll.
  apply findtag_In in H.
  apply in_split in H.
  destructAll.
  rewrite bound_var_Ecase_app in H2.
  rewrite bound_var_Ecase_cons in H2.
  apply unique_bindings_Ecase_l in H1.
  destructAll.
  split; auto.
  split; auto.
  eapply Disjoint_Included_r.
  2: apply H2.
  right; left; auto.
Qed.


Section occurs_free_rw.
  (* for each rw e e', OF e' \subset OF e *)

  (* restricted form of occurs_free_ctx_mut to inclusion *)
  Lemma occurs_free_ctx_mut_included:
    (forall c e e',
        Included _ (occurs_free e) (occurs_free e') ->
        Included _ (occurs_free (c|[ e]|)) (occurs_free (c|[ e']|))) /\
    (forall fds e e',
        Included _ (occurs_free e) (occurs_free e') ->
        Included _ (occurs_free_fundefs (fds <[ e]>)) (occurs_free_fundefs (fds<[ e']>))).
  Proof with eauto with Ensembles_DB.
    exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
      intros; repeat normalize_occurs_free;
        try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
          eauto with Ensembles_DB.
    rewrite name_in_fundefs_ctx...
    rewrite name_in_fundefs_ctx...
  Qed.

  Lemma occurs_free_exp_ctx_included:
    forall c e e',
      Included _ (occurs_free e) (occurs_free e') ->
      Included _ (occurs_free (c|[ e]|)) (occurs_free (c|[ e']|)).
  Proof.
    apply (proj1 occurs_free_ctx_mut_included).
  Qed.

  Lemma occurs_free_fundefs_ctx_included:
    forall fds e e',
      Included _ (occurs_free e) (occurs_free e') ->
      Included _ (occurs_free_fundefs (fds <[ e]>)) (occurs_free_fundefs (fds<[ e']>)).
  Proof.
    apply (proj2 occurs_free_ctx_mut_included).
  Qed.



  Lemma of_constr_dead: forall c x t ys e,
      num_occur e x 0 ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Econstr x t ys e ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Econstr.
    apply not_occurs_not_free in H.
    eauto with Ensembles_DB.
  Qed.

  Lemma of_prim_dead: forall c x t ys e,
      num_occur e x 0 ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Eprim x t ys e ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Eprim.
    apply not_occurs_not_free in H.
    eauto with Ensembles_DB.
  Qed.


  Lemma of_proj_dead: forall c x t n y e,
      num_occur e x 0 ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Eproj x t n y e ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Eproj.
    apply not_occurs_not_free in H.
    eauto with Ensembles_DB.
  Qed.

  Lemma of_fun_dead: forall c fds e,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      Included _ (occurs_free (c |[ e ]|)) (occurs_free (c |[ Efun fds e]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    rewrite occurs_free_Efun.
    apply disjoint_not_occurs_fun in H.
    eauto with Ensembles_DB.
  Qed.


  Lemma included_of_fundefs_append_r: forall B2 B2' B1,
      Included _ (occurs_free_fundefs B2) (occurs_free_fundefs B2') ->
      Included _ (name_in_fundefs B2') (name_in_fundefs B2) ->
      Included _ (occurs_free_fundefs (fundefs_append B1 B2)) (occurs_free_fundefs (fundefs_append B1 B2')).
  Proof.
    induction B1; intros.
    - simpl.
      repeat normalize_occurs_free.
      specialize (IHB1 H H0).
      apply Included_Union_compat.
      + apply Included_Setminus_compat.
        reflexivity.
        apply Included_Union_compat. reflexivity.
        apply Included_Union_compat. reflexivity.
        intro.
        intros.
        eapply fundefs_append_name_in_fundefs in H1.
        2: reflexivity.
        eapply fundefs_append_name_in_fundefs.
        reflexivity.
        inv H1. left; auto.
        right.
        apply H0. auto.
      + eauto with Ensembles_DB.
    - simpl. auto.
  Qed.


  (* local version *)
  Lemma of_fun_rm': forall f t xs fb B1 B2 e,
      unique_bindings_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      Included _ (occurs_free (Efun (fundefs_append B1 B2) e )) (occurs_free (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e)).
  Proof.
    intros.
    repeat normalize_occurs_free.
    rewrite fundefs_append_name_in_fundefs.
    2: reflexivity.
    rewrite fundefs_append_name_in_fundefs with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
    2: reflexivity.
    simpl.

    inv H0. apply plus_is_O in H3. destruct H3. subst.
    apply fundefs_append_num_occur' in H6.
    destructAll.
    apply plus_is_O in H2. destructAll.


    inv H1. apply plus_is_O in H10.
    destructAll.
    apply not_occurs_not_free in H5.
    apply not_occurs_not_free in H11.
    apply not_occurs_not_free in H9.

    apply Included_Union_compat.

    {
      clear H.
      induction B1.
      + inv H0; pi0.
        specialize (IHB1 H10).
        simpl.
        repeat normalize_occurs_free.
        apply Included_Union_compat.
        rewrite fundefs_append_name_in_fundefs.
        2: reflexivity.
        rewrite fundefs_append_name_in_fundefs with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
        2: reflexivity.
        simpl.
        apply not_occurs_not_free in H7.
        repeat (rewrite <- Setminus_Union).
        apply Included_Setminus_compat.
        apply Included_Setminus.
        apply Setminus_Disjoint_preserv_l.
        apply Setminus_Disjoint_preserv_l.
        apply Setminus_Disjoint_preserv_l.
        eauto with Ensembles_DB.
        reflexivity.
        reflexivity.
        eauto with Ensembles_DB.
      + simpl.
        normalize_occurs_free.
        eauto with Ensembles_DB.
    }

    apply not_occurs_not_free in H0.
    eauto 25 with Ensembles_DB.
  Qed.

  Lemma of_fun_rm:  forall c f t xs fb B1 B2 e,
      unique_bindings_fundefs (fundefs_append B1 (Fcons f t xs fb B2)) ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      Included _ (occurs_free (c |[ Efun (fundefs_append B1 B2) e  ]| )) (occurs_free (c |[ (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) ]|)).
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    apply of_fun_rm'; auto.
  Qed.

  Lemma of_case_fold': forall x cl co e,
      findtag cl co = Some e ->
      Included _ (occurs_free e) (occurs_free (Ecase x cl)).
  Proof.
    intros.
    eapply occurs_free_Ecase_Included.
    apply findtag_In_patterns.
    eauto.
  Qed.





  Lemma name_in_fundefs_rename_all_ns:
    forall sig f,
      name_in_fundefs f <--> name_in_fundefs (rename_all_fun_ns sig f).
  Proof.
    induction f; simpl; eauto with Ensembles_DB.
  Qed.

  Lemma not_Range_map_eq {A}:
    forall sig (x:A),
      ~ Range_map sig x ->
      ~ (exists z, M.get z sig = Some x).
  Proof.
    intros. intro. apply H. inv H0. exists x0; auto.
  Qed.

  Lemma not_Dom_map_eq {A}:
    forall (sig:M.t A) x,
      ~ Dom_map sig x ->
      M.get x sig = None.
  Proof.
    intro. intros.
    destruct (M.get x sig) eqn:gxs.
    exfalso; apply H. exists a; auto.
    auto.
  Qed.

  Hint Resolve not_Range_map_eq not_Dom_map_eq : core.

  Lemma one_rename_all_ns_mut: forall y x sig,
      ~ Range_map sig x  ->
      ~ Dom_map sig x ->
      ( forall e,
          rename_all_ns (M.set x y (M.empty var)) (rename_all_ns sig e) =  rename_all_ns (M.set x y sig) e  ) /\
      ( forall f,
          rename_all_fun_ns (M.set x y (M.empty var)) (rename_all_fun_ns sig f) =  rename_all_fun_ns (M.set x y sig) f).
  Proof.
    intros y x sig Hr Hd.
    eapply exp_def_mutual_ind; intros; simpl.
    - rewrite H.
      rewrite <- one_rename_all_list; auto.
    - rewrite <- one_rename_all_ar; auto.
    - simpl in H0. inv H0.
      rewrite H. auto.
    - rewrite <- one_rename_all_ar; auto.
      rewrite H. auto.
    - rewrite H. rewrite H0. reflexivity.
    - rewrite <- one_rename_all_ar; auto.
      rewrite <- one_rename_all_list; auto.
    - rewrite <- one_rename_all_list; auto.
      rewrite H. auto.
    - rewrite <- one_rename_all_ar; auto.
    - rewrite H; rewrite H0; auto.
    - auto.
  Qed.

  Lemma one_rename_all_ns:
    forall y x sig,
      ( forall e,
          ~ Range_map sig x  ->
          ~ Dom_map sig x ->
          rename_all_ns (M.set x y (M.empty var)) (rename_all_ns sig e) =  rename_all_ns (M.set x y sig) e  ).
  Proof.
    intros. apply one_rename_all_ns_mut; auto.
  Qed.

  Lemma one_rename_all_fun_ns: forall y x sig,
      ( forall f,
          ~ Range_map sig x  ->
          ~ Dom_map sig x ->
          rename_all_fun_ns (M.set x y (M.empty var)) (rename_all_fun_ns sig f) =  rename_all_fun_ns (M.set x y sig) f).
  Proof.
    intros. apply one_rename_all_ns_mut; auto.
  Qed.



  Lemma of_rename_all_ns_mut:
    (forall e sigma, (occurs_free (rename_all_ns sigma e)) \subset
                                                      Union _ (Setminus _ (occurs_free e) (Dom_map sigma)) (Range_map sigma))
    /\
    (forall fds sigma, (occurs_free_fundefs (rename_all_fun_ns sigma fds)) \subset
                                                                      Union _ (Setminus _ (occurs_free_fundefs fds) (Dom_map sigma)) (Range_map sigma)).
  Proof.
    apply exp_def_mutual_ind; intros.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        apply FromList_apply_r_list.
        eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans.
        apply H.
        intro.
        intros. inv H0.
        destruct (var_dec x v).
        * subst. right. constructor.
        * inv H1.
          left. left. split.
          right. split; auto.
          intro. apply n; inv H1.
          auto.
          auto.
        * auto.
    - simpl.
      repeat normalize_occurs_free.
      intro. intros.
      inv H.
      apply apply_r_sigma_in.
    - simpl.
      repeat normalize_occurs_free.
      specialize (H sigma).
      specialize (H0 sigma).
      repeat (apply Union_Included).
      + eapply Included_trans.
        intro; intro.
        inv H1.
        apply apply_r_sigma_in.
        eauto with Ensembles_DB.
      + eapply Included_trans.
        apply H.
        eauto with Ensembles_DB.
      + eapply Included_trans.
        apply H0.
        eauto with Ensembles_DB.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        intro. intro. inv H0.
        apply apply_r_sigma_in.
        eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans.
        apply H.
        intro.
        intros. inv H0.
        destruct (var_dec x v).
        * subst. right. constructor.
        * inv H1.
          left. left. split.
          right. split; auto.
          intro. apply n0; inv H1.
          auto.
          auto.
        * eauto.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      + eapply Included_trans.
        apply H.
        eauto with Ensembles_DB.
      + apply Setminus_Included_Included_Union.
        eapply Included_trans.
        apply H0.
        apply Union_Included.
        * intro. intro.
          inv H1.
          assert (Hh := Decidable_name_in_fundefs f2).
          inv Hh. specialize (Dec x).
          destruct Dec.
          right.
          apply name_in_fundefs_rename_all_ns. auto.
          left.  left. split. right. split; auto.
          intro; apply H3.
          auto.
        * left; right.
          auto.
    - simpl.
      repeat normalize_occurs_free.
      apply Union_Included.
      eapply Included_trans.
      apply FromList_apply_r_list.
      eauto with Ensembles_DB.
      eapply Included_trans.
      intro. intro. inv H.
      apply apply_r_sigma_in.
      eauto with Ensembles_DB.
    -  simpl.
       repeat normalize_occurs_free.
       apply Union_Included.
       + eapply Included_trans.
         apply FromList_apply_r_list.
         eauto with Ensembles_DB.
       + apply Setminus_Included_Included_Union.
         eapply Included_trans.
         apply H.
         intro.
         intros. inv H0.
         destruct (var_dec x v).
         * subst. right. constructor.
         * inv H1.
           left. left. split.
           right. split; auto.
           intro. apply n; inv H1.
           auto.
           intro.
           apply H2.
           auto.
         * eauto.
    - simpl.
      rewrite occurs_free_Ehalt.
      rewrite occurs_free_Ehalt.
      intro. intro. inv H. apply apply_r_sigma_in.
    - simpl.
      repeat normalize_occurs_free.

      apply Union_Included.
      + intro. intro. inv H1. apply H in H2.
        inv H2.
        left. inv H1.
        split.
        left. split; auto.
        intro.
        inv H1. apply H3; auto.
        rewrite <- name_in_fundefs_rename_all_ns in H3.
        apply H3; auto.
        auto.
        right.
        auto.
      + intro. intro. inv H1.
        apply H0 in H2.
        inv H2.
        inv H1. left.
        split; auto.
        right. split; auto.
        auto.
    - simpl.
      intro. intro. inv H.
  Qed.



  Lemma of_fun_inline':
    forall f fds t xs fb vs,
      find_def f fds = Some (t, xs, fb) ->
      List.length xs = List.length vs ->
      (Setminus var
                (occurs_free
                   (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
                (name_in_fundefs fds)) \subset
                                       Union var (occurs_free_fundefs fds)
                                       (Setminus var (occurs_free ( Eapp f t vs)) (name_in_fundefs fds)).
  Proof.
    intros.
    eapply Included_trans.
    eapply Included_Setminus_compat.
    apply of_rename_all_ns_mut.
    reflexivity.
    eapply Included_trans.
    apply Setminus_Union_distr.
    apply find_def_free_included in H.
    apply Union_Included.
    - eapply Included_trans.
      rewrite Dom_map_set_lists_ss; auto.
      apply H.
      left; auto.
    - apply Setminus_Included_Included_Union.
      eapply Included_trans.
      apply Range_map_set_list.
      rewrite occurs_free_Eapp.
      intro. intro.
      assert (Hh := Decidable_name_in_fundefs fds).
      destruct Hh.
      destruct (Dec x) as [Hin | Hnin].
      right; auto.
      left. right.
      split.
      left; auto.
      apply Hnin.
  Qed.


  Lemma of_fun_inline'':
    forall f fds t xs fb vs,
      find_def f fds = Some (t, xs, fb) ->
      List.length xs = List.length vs ->
      Union var
            (occurs_free
               (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb))
            (Union var
                   (name_in_fundefs fds)
                   (occurs_free_fundefs fds))
            \subset
            Union var (occurs_free ( Eapp f t vs))
            (Union var (name_in_fundefs fds)
                   (occurs_free_fundefs fds))
  .
  Proof.
    intros.
    assert (Hofi := of_fun_inline' f fds t xs fb vs H H0).
    rewrite Union_assoc.
    rewrite Union_assoc.
    apply Union_Included.
    - rewrite Union_Setminus.
      apply Union_Included.
      eapply Included_trans. apply Hofi.
      eauto with Ensembles_DB.
      eauto with Ensembles_DB.
      apply Decidable_name_in_fundefs.
    - right; auto.
  Qed.




  Lemma occurs_free_ctx_mut_included_u:
    forall S,
      Decidable S ->
      (forall c e e',
          Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
          Included _ (Union _ (occurs_free (c|[ e]|)) S)  (Union _ (occurs_free (c|[ e']|)) S)) /\
      (forall fds e e',
          Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
          Included _ (Union _ (occurs_free_fundefs (fds <[ e]>)) S)  (Union _ (occurs_free_fundefs (fds<[ e']>)) S)).
  Proof with eauto with Ensembles_DB.
    intros S Hds.
    exp_fundefs_ctx_induction IHc IHf; eauto; simpl;
      intros; repeat normalize_occurs_free;
        try (rewrite IHc; [| eassumption ]); try (rewrite IHB; [| eassumption ]);
          try (
              apply IHc in H;
              rewrite <- Union_assoc;
              rewrite <- Union_assoc;
              rewrite Union_Setminus_Setminus_Union; [|auto];
              rewrite Union_Setminus_Setminus_Union; [|auto];
              eauto with Ensembles_DB).
    {
      apply IHc in H.
      repeat (rewrite <- Union_assoc).
      apply Included_Union_compat; [reflexivity|].
      apply Included_Union_compat; [reflexivity|].
      intro. intro. inv H0.
      eapply Included_Union_l in H1. apply H in H1.
      inv H1. auto. auto.
      inv H1.
      auto.
      eapply Included_Union_r in H0. apply H in H0.
      inv H0; auto.
    }
    {
      apply IHf in H.
      rewrite name_in_fundefs_ctx with (e2 := e').
      do 2 (rewrite Union_commut with (s2 := S)).
      do 2 (rewrite  Union_assoc).
      do 2 (rewrite Union_commut with (s1 := S)).
      eauto with Ensembles_DB.
    }
    {
      apply IHc in H.
      do 2 (rewrite Union_commut with (s2 := S)).
      rewrite Union_assoc.
      rewrite Union_assoc with (s1 := S).

      rewrite Union_commut with (s1 := S).
      rewrite Union_commut with (s1 := S).
      rewrite Union_Setminus_Setminus_Union.
      rewrite Union_Setminus_Setminus_Union with (s3 := S).
      eauto with Ensembles_DB.
      auto.
      auto.
    }
    {
      apply IHf in H.
      rewrite name_in_fundefs_ctx with (e2 := e').


      do 2 (rewrite Union_commut with (s2 := S)).
      do 2 (rewrite Union_commut with (s1 := (Setminus var (occurs_free e)
                                                       (Union var [set v]
                                                              (Union var (FromList l) (name_in_fundefs (f7 <[ e' ]>))))))).
      rewrite Union_assoc.
      rewrite Union_assoc with (s1 := S).
      rewrite Union_commut with (s1 := S).
      rewrite Union_commut with (s1 := S).
      rewrite Union_Setminus_Setminus_Union.
      rewrite Union_Setminus_Setminus_Union with (s3 := S).
      eauto with Ensembles_DB.
      auto.
      auto.
    }
  Qed.

  (* todo: move *)
  Lemma nthN_FromList:
    forall {A} k ys n,
      nthN ys n = Some k ->
      @FromList A ys k.
  Proof.
    induction ys; intros.
    inv H.
    simpl in H.
    destruct n. inv H. constructor; auto.
    apply IHys in H.
    constructor 2. auto.
  Qed.

  Lemma occurs_free_exp_ctx_included_u:
    forall c e e' S,
      Decidable S ->
      Included _ (Union _ (occurs_free e) S) (Union _ (occurs_free e') S) ->
      Included _ (Union _ (occurs_free (c|[ e]|)) S) (Union _ (occurs_free (c|[ e']|)) S).
  Proof.
    intros.
    apply occurs_free_ctx_mut_included_u; auto.
  Qed.

  Lemma of_case_fold: forall c' c x cl  e ys co,
      findtag cl co = Some e ->
      Included _ (occurs_free (c' |[ Econstr x co ys (c |[ e ]|) ]|)) (occurs_free (c' |[Econstr x co ys (c |[Ecase x cl]|) ]|)) .
  Proof.
    intros.
    apply occurs_free_exp_ctx_included.
    do 2 (rewrite inv_app_Econstr).
    do 2 (rewrite app_ctx_f_fuse).
    apply occurs_free_exp_ctx_included.
    eapply occurs_free_Ecase_Included.
    apply findtag_In_patterns. apply H.
  Qed.






  Lemma of_fun_inline''':
    forall xs vs fb t c f fds,
      find_def f fds = Some (t, xs, fb) ->
      List.length xs = List.length vs ->
      Included _ (occurs_free (Efun fds (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|)))
               (occurs_free (Efun fds (c |[ Eapp f t vs ]|))).
  Proof.
    intros.
    repeat normalize_occurs_free.
    apply Union_Included.
    - left; auto.
    - assert (Hofi := of_fun_inline'' f fds t xs fb vs H H0).
      eapply occurs_free_exp_ctx_included_u with (c  := c) in Hofi.
      intro. intro.
      inv H1.
      assert (In var (Union var
                            (occurs_free
                               (c |[ rename_all_ns (set_list (combine xs vs) (M.empty var)) fb ]|))
                            (Union var (name_in_fundefs fds) (occurs_free_fundefs fds))) x).
      left. auto.
      apply Hofi in H1.
      inv H1. right. split; auto.
      inv H4.
      exfalso; auto.
      left; auto.
      apply Decidable_Union.
      apply Decidable_name_in_fundefs.
      apply occurs_free_dec_fundefs.
  Qed.



  Lemma of_constr_proj':
    forall x t ys c k v e n t',
      nthN ys n = Some k  ->
      Included _
               (occurs_free (Econstr x t ys (c |[rename_all_ns (M.set v k (M.empty var)) e]|)))
               (occurs_free (Econstr x t ys (c |[Eproj v t' n x e]|))).
  Proof.
    intros.
    repeat normalize_occurs_free.
    assert (Included _ (Union _ (occurs_free (c |[ rename_all_ns (M.set v k (M.empty var)) e ]|)) [set k])
                     (Union _ (occurs_free (c |[ Eproj v t' n x e ]|)) [set k])).
    eapply occurs_free_exp_ctx_included_u with (c  := c).
    split. intro. destruct (var_dec k x0); subst.
    left; constructor. right.
    intro; apply n0; auto. inv H0; auto.
    normalize_occurs_free.
    unfold rename.
    apply Union_Included.
    eapply Included_trans.

    apply of_rename_all_ns_mut.
    intro.
    intro. inv H0.
    inv H1.
    left.
    right.
    split.
    auto.
    intro.
    apply H2.
    inv H1.
    exists k.
    rewrite M.gss.
    auto.
    inv H1.
    destruct (var_dec x1 v).
    subst.
    rewrite M.gss in H0. inv H0.
    right. auto.
    rewrite M.gso in H0.
    rewrite M.gempty in H0.
    inv H0.
    auto.
    right; auto.
    intro.
    intro. inv H1.
    left; auto.
    destruct (var_dec x0 k).
    - subst. left. eapply nthN_FromList. eauto.
    - inv H2.
      right.
      split; auto.
      eapply Included_Union_l in H1.
      apply H0 in H1.
      inv H1. auto.
      exfalso.
      apply n0. inv H2. auto.
  Qed.



End occurs_free_rw.

Section Shrink_Rewrites.

  (* shrink rewrites  *)
  Inductive sr_rw: relation exp :=
  (* Rules about dead var elimination *)
  | Constr_dead_s: forall x t ys e,
      num_occur e x 0 ->
      sr_rw (Econstr x t ys e) e
  | Prim_dead_s: forall x p ys e,
      num_occur e x 0 ->
      sr_rw (Eprim x p ys e) e
  | Proj_dead_s: forall x t n y e,
      num_occur e x 0 ->
      sr_rw (Eproj x t n y e) e
  | Fun_dead_s: forall e fds,
      Forall (fun v => num_occur e v 0) (all_fun_name fds) ->
      sr_rw (Efun fds e) e
  | Fun_rem_s: forall f t xs fb B1 B2 e,
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) f 0 ->
      sr_rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) e) (Efun (fundefs_append B1 B2) e)
  (* Rules about inlining/constant-folding *)
  | Constr_case_s: forall x c cl co e ys,
      findtag cl co = Some e ->
      sr_rw (Econstr x co ys (c |[ Ecase x cl ]|)) (Econstr x co ys (c |[e]|))
  | Constr_proj_s: forall v  t t' n x e k ys c,
      nthN ys n = Some k ->
      sr_rw (Econstr x t ys (c |[Eproj v t' n x e]|)) (Econstr x t ys (c |[ rename_all_ns (M.set v k (M.empty var)) e]|))
  | Fun_inline_s: forall c  vs f  t xs fb  B1 B2,
      List.length xs = List.length vs ->
      num_occur (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|)) f 1 ->
      sr_rw (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|))
            (Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|)).


  Inductive gen_sr_rw : relation exp :=
  | Ctx_sr_rw : forall c e e',
      sr_rw e e' ->
      gen_sr_rw (c |[ e ]|) (c |[ e' ]|)
  .


  Definition gsr_clos := clos_refl_trans exp gen_sr_rw.


  Local Hint Constructors rw : core.

  Lemma Disjoint_dom_map :
    forall (sig:M.t M.elt) S,
      Disjoint _ (Dom_map sig) S ->
      forall (x:M.elt), In _ S x ->
                   M.get x sig  = None.
  Proof.
    intros. inv H. destruct (M.get x sig) eqn:gxs.
    exfalso. specialize (H1 x). apply H1. split; eauto.
    exists e. auto.
    auto.
  Qed.

  Notation "A =mg= B" := (map_get_r _ A B) (at level 81).

  Lemma Disjoint_dom_remove_all:
    forall l sig,
      Disjoint _ (Dom_map sig) (FromList l) ->
      remove_all sig l =mg= sig.
  Proof.
    induction l; simpl; intros.
    - apply smg_refl.
    - eapply smg_trans.
      apply IHl.
      split. intro. intro. inv H0. inv H1.
      destruct (var_dec x a). subst. rewrite M.grs in H0; inv H0.
      rewrite M.gro in H0 by auto.
      inv H. specialize (H1 x).
      apply H1. split; eauto.
      exists x0; auto. constructor 2; auto.
      apply remove_none.
      eapply Disjoint_dom_map; eauto with Ensembles_DB.
      constructor 1; auto.
  Qed.

  (** If the substitution is not shadowed in e, we can replace rename_all by
     rename_all_ns which does not consider variable captures *)
  Lemma Disjoint_dom_rename_all_eq:
    forall sig,
      (forall e,
          Disjoint _ (Dom_map sig) (bound_var e) ->
          rename_all sig e = rename_all_ns sig e) /\
      (forall fds,
          Disjoint _ (Dom_map sig) (bound_var_fundefs fds) ->
          rename_all_fun sig fds = rename_all_fun_ns sig fds).
  Proof with (eauto with Ensembles_DB).
    intro sig.
    apply exp_def_mutual_ind; intros; repeat normalize_bound_var_in_ctx; simpl.
    - rewrite <- H.
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map. apply H0. auto.
      eapply Disjoint_Included_r...
    - reflexivity.
    - rewrite H.
      assert ( Disjoint M.elt (Dom_map sig) (bound_var (Ecase v l)))...
      apply H0 in H2. simpl in H2.
      inv H2. reflexivity.
      eapply Disjoint_Included_r...
    - rewrite <- H.
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map...
      eapply Disjoint_Included_r...
    - rewrite <- H0...
      rewrite <- H...
      erewrite (proj1 prop_rename_all).
      erewrite (proj2 prop_rename_all).
      reflexivity.
      apply Disjoint_dom_remove_all. rewrite <- same_name_in_fun. eapply Disjoint_Included_r.
      apply name_in_fundefs_bound_var_fundefs. auto...
      apply Disjoint_dom_remove_all. rewrite <- same_name_in_fun. eapply Disjoint_Included_r.
      apply name_in_fundefs_bound_var_fundefs. auto...
    - reflexivity.
    - rewrite <- H...
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply remove_none.
      eapply Disjoint_dom_map...
    - reflexivity.
    - rewrite <- H...
      rewrite <- H0...
      erewrite (proj1 prop_rename_all).
      reflexivity.
      apply Disjoint_dom_remove_all...
    - reflexivity.
  Qed.


  Lemma occurs_free_ctx_not_bound:
    forall (x : var) (e : exp),
      occurs_free e x ->
      (forall c : exp_ctx, ~ bound_var_ctx c x ->  occurs_free (c |[ e ]|) x).
  Proof.
    intros.
    destruct (occurs_free_dec_exp (c |[ e ]|)).
    specialize (Dec x).
    inv Dec; auto.
    exfalso.
    apply H0.
    eapply occurs_free_app_bound_var; eauto.
  Qed.

  Lemma occurs_free_fundefs_ctx_not_bound:
    forall (x : var) (e : exp),
      occurs_free e x ->
      (forall fds : fundefs_ctx,
          ~ bound_var_fundefs_ctx fds x -> occurs_free_fundefs (fds <[ e ]>) x).
  Proof.
    intros.
    destruct (occurs_free_dec_fundefs (fds <[ e ]>)).
    specialize (Dec x).
    inv Dec; auto.
    exfalso.
    apply H0.
    eapply occurs_free_app_bound_var; eauto.
  Qed.

  Lemma Disjoint_bv_of_ctx:
    forall c e,
      unique_bindings (c |[ e]|) ->
      Disjoint _ (bound_var (c |[ e]|)) (occurs_free (c |[ e]|)) ->
      Disjoint _ (bound_var e) (occurs_free e).
  Proof.
    intros.
    split. intro. intro.
    destruct H1.
    destruct (bound_var_ctx_dec c).
    destruct (Dec x) as [Hin | Hnin].
    apply ub_app_ctx_f in H; destructAll.
    inv H4. specialize (H5 x). auto.
    inv H0. specialize (H3 x).
    apply H3.
    split. apply bound_var_app_ctx; auto.
    apply occurs_free_ctx_not_bound; auto.
  Qed.


  Lemma num_occur_list_not_dom: forall f sigma,
      ~ (Dom_map sigma f) ->
      forall l,
        num_occur_list l f <= num_occur_list (apply_r_list sigma l) f.
  Proof.
    induction l; auto.
    simpl.
    destruct (cps_util.var_dec f a).
    unfold apply_r.
    subst.
    destruct (M.get a sigma) eqn:gas.
    exfalso.
    apply H. exists e; auto.
    destruct (cps_util.var_dec a a). omega.
    exfalso; apply n. auto.
    destruct (cps_util.var_dec f (apply_r sigma a)); omega.
  Qed.

  Lemma num_occur_list_not_range: forall f sigma,
      ~ (Range_map sigma f) ->
      forall l,
        num_occur_list (apply_r_list sigma l) f  <= num_occur_list l f.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl.
      destruct (cps_util.var_dec f a).
      + subst.
        destruct (cps_util.var_dec a (apply_r sigma a)); omega.
      + destruct (cps_util.var_dec f (apply_r sigma a)).
        * exfalso. apply H.
          exists a.
          unfold apply_r in e.
          destruct  (Maps.PTree.get a sigma).
          subst; auto.
          exfalso; apply n; auto.
        * omega.
  Qed.

  Local Hint Constructors num_occur num_occur_fds num_occur_case num_occur_ec num_occur_fdc : core.

  (** If a variable is not in the range of a substitution, applying the
substitution to a term cannot increase the occurence count for that variable. *)
  Lemma num_occur_rename_all_not_range_mut:
    forall f,
      ( forall e m n sigma,
          num_occur e f m ->
          num_occur (rename_all sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m) /\
      ( forall fds m n sigma,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun sigma fds) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    intro f.
    apply exp_def_mutual_ind; intros.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _  H8 H9).
      apply plus_le_compat.
      apply H. intro. apply H2.
      apply Range_map_remove in H0. auto.
      apply num_occur_list_not_range. auto.
    - simpl in H0. inv H0.
      inv H6. inv H.
      inv H5.
      apply plus_le_compat.
      assert (Hll := num_occur_list_not_range _ _ H1 ([v])).
      simpl in Hll.    auto.
      auto.
    - simpl in H2. inv H1. inv H2. inv H8. inv H7.
      replace (num_occur_list [v] f + (n + m)) with
          (n + (num_occur_list [v] f + m)) by omega.
      unfold var.
      replace (num_occur_list [apply_r sigma v] f + (n0 + m0)) with
          (n0 + (num_occur_list [apply_r sigma v] f + m0)) by omega.
      apply plus_le_compat.
      eapply H; eauto.
      eapply H0; eauto.
      simpl. constructor.
      auto.

    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _ H9 H10).
      apply plus_le_compat.
      assert (Hll := num_occur_list_not_range _ _ H2 ([v0])).
      simpl in Hll.    auto.
      apply H. intro; apply H2.
      apply Range_map_remove in H0.
      auto.
    - inv H1.
      simpl in H2. inv H2.
      apply plus_le_compat.
      eapply H0; eauto.
      intro; apply H3.
      apply Range_map_remove_all in H1.
      auto.
      eapply H; eauto.
      intro.
      apply H3.
      apply Range_map_remove_all in H1.
      auto.
    - inv H. inv H0.
      assert (Hll := num_occur_list_not_range _ _ H1 (v::l)).
      auto.
    - inv H0; inv H1.
      apply plus_le_compat.
      eapply H; eauto.
      intro; apply H2.
      apply (@Range_map_remove var) in H0. auto.
      apply num_occur_list_not_range; auto.
    - inv H; inv H0.
      assert (Hll := num_occur_list_not_range _ _ H1 ([v])).
      auto.
    - inv H1; inv H2.
      apply plus_le_compat.
      eapply H; eauto.
      intro; apply H3.
      apply Range_map_remove_all in H1. auto.
      eapply H0; eauto.
    - inv H; inv H0. auto.
  Qed.

  Lemma num_occur_rename_all_not_range:
    forall f,
      ( forall e m n sigma,
          num_occur e f m ->
          num_occur (rename_all sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    apply num_occur_rename_all_not_range_mut.
  Qed.



  Lemma num_occur_rename_all_ns_not_range_mut:
    forall f sigma,
      ~ Range_map sigma f ->
      ( forall e m n,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          n <= m) /\
      ( forall fds m n,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
          n <= m).
  Proof.
    intros f sig Hs.
    apply exp_def_mutual_ind; simpl; intros.
    - inv H0; inv H1.
      specialize (H _ _ H8 H7).
      assert (Hnn := num_occur_list_not_range _ _ Hs l).
      omega.
    - inv H; inv H0.
      inv H5; inv H4.
      rewrite plus_0_r.
      rewrite plus_0_r.
      apply (num_occur_list_not_range _ _ Hs [v]).
    - inv H1. inv H2.
      inv H7. inv H6.
      specialize (H _ _ H8 H7).
      assert (  num_occur_list [apply_r sig v] f + m0 <=
                num_occur_list [v] f + m).
      eapply H0. constructor; auto. constructor; auto.
      simpl in *. omega.
    - inv H0; inv H1.
      specialize (H _ _ H9 H8).
      assert (Hnn := num_occur_list_not_range _ _ Hs [v0]).
      simpl in *. omega.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      omega.
    - inv H; inv H0.
      apply (num_occur_list_not_range _ _ Hs (v::l)).
    - inv H0; inv H1.
      specialize (H _ _ H8 H7).
      assert (Hnn := num_occur_list_not_range _ _ Hs l).
      omega.
    - inv H; inv H0.
      apply (num_occur_list_not_range _ _ Hs [v]).
    - inv H1; inv H2.
      specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      omega.
    - inv H; inv H0; auto.
  Qed.

  Lemma num_occur_rename_all_ns_not_range:
    forall f sigma,
      ( forall e m n,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          ~ Range_map sigma f ->
          n <= m).
  Proof.
    intros. eapply (proj1 (num_occur_rename_all_ns_not_range_mut _ _ H1)); eauto.
  Qed.

  Lemma num_occur_rename_all_fun_ns_not_range:
    forall f sigma fds m n,
      num_occur_fds fds f m ->
      num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
      ~ Range_map sigma f ->
      n <= m.
  Proof.
    intros. eapply (proj2 (num_occur_rename_all_ns_not_range_mut _ _ H1)); eauto.
  Qed.


  Lemma num_occur_rename_all_not_dom_mut:
    forall f,
      ( forall e m n sigma,
          num_occur e f m ->
          num_occur (rename_all_ns sigma e) f n  ->
          ~ Dom_map sigma f ->
          m <= n) /\
      ( forall fds m n sigma,
          num_occur_fds fds f m ->
          num_occur_fds (rename_all_fun_ns sigma fds) f n  ->
          ~ Dom_map sigma f ->
          m <= n).
  Proof.
    intro f.
    apply exp_def_mutual_ind; intros.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _  H8 H9).
      apply plus_le_compat.
      apply H. intro. apply H2.
      auto.
      apply num_occur_list_not_dom. auto.
    - simpl in H0. inv H0.
      inv H6. inv H.
      inv H5.
      apply plus_le_compat.
      apply (num_occur_list_not_dom _ _ H1 ([v])).
      auto.
    - simpl in H2. inv H1. inv H2. inv H8. inv H7.
      replace (num_occur_list [v] f + (n + m)) with
          (n + (num_occur_list [v] f + m)) by omega.
      unfold var.
      replace (num_occur_list [apply_r sigma v] f + (n0 + m0)) with
          (n0 + (num_occur_list [apply_r sigma v] f + m0)) by omega.
      apply plus_le_compat.
      eapply H; eauto.
      eapply H0; eauto.
      simpl. constructor.
      auto.
    - simpl in H1. inv H1.
      inv H0.
      specialize (H _ _ _ H9 H10).
      apply plus_le_compat.
      assert (Hll := num_occur_list_not_dom _ _ H2 ([v0])).
      simpl in Hll.    auto.
      apply H. intro; apply H2.
      auto.
    - inv H1.
      simpl in H2. inv H2.
      apply plus_le_compat.
      eapply H0; eauto.
      eapply H; eauto.
    - inv H. inv H0.
      assert (Hll := num_occur_list_not_dom _ _ H1 (v::l)).
      simpl in Hll.
      auto.
    - inv H0; inv H1.
      apply plus_le_compat.
      eapply H; eauto.
      apply num_occur_list_not_dom.
      auto.
    - inv H; inv H0.
      assert (Hll := num_occur_list_not_dom _ _ H1 ([v])).
      auto.
    - inv H1; inv H2.
      apply plus_le_compat.
      eapply H; eauto.

      eapply H0; eauto.
    - inv H; inv H0. auto.
  Qed.




  Lemma apply_r_set1:
    forall x y sig,
      apply_r (M.set x y sig) x = y.
  Proof.
    intros.
    unfold apply_r.
    rewrite M.gss. auto.
  Qed.

  Lemma num_occur_list_set:
    forall f y x sigma,
      f <> y ->
      forall l,
        num_occur_list (apply_r_list (M.set x y sigma) l) f  <=
        num_occur_list (apply_r_list sigma l) f.
  Proof.
    induction l; intros; simpl; auto.
    destruct (var_dec x a).
    - subst.
      rewrite apply_r_set1.
      destruct (cps_util.var_dec f y).
      exfalso; auto.
      destruct (cps_util.var_dec f (apply_r sigma a)); omega.
    - rewrite apply_r_set2  by auto.
      destruct (cps_util.var_dec f (apply_r sigma a)); omega.
  Qed.

  Lemma num_occur_rename_all_ns_set:
    forall f x y,
      f <> y ->
      ( forall e m n sigma,
          num_occur (rename_all_ns sigma e) f m ->
          num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
          n <= m) /\
      ( forall fds m n sigma,
          num_occur_fds (rename_all_fun_ns sigma fds) f m ->
          num_occur_fds (rename_all_fun_ns (M.set x y sigma) fds) f n  ->
          n <= m).
  Proof.
    intros f x y Hfy; apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - assert (Hl := num_occur_list_set _ _ x sigma Hfy l).
      specialize (H _ _ _ H8 H7).
      apply plus_le_compat; eauto.
    - inv H; inv H0.
      inv H5; inv H4.
      assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy [v]).
      simpl in Hl.
      simpl.
      do 2 (rewrite plus_0_r).
      auto.
    - inv H1; inv H2.
      inv H7; inv H6.
      rewrite OrdersEx.Nat_as_OT.add_shuffle3.
      rewrite  OrdersEx.Nat_as_OT.add_shuffle3 with (p := m).
      apply plus_le_compat; eauto.
    - assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy [v0]).
      specialize (H _ _ _ H9 H8).
      simpl; simpl in Hl.
      apply plus_le_compat; eauto.
    - inv H1; inv H2.
      apply plus_le_compat; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set).
      specialize (Hl _ _ x sigma Hfy (v::l)).
      auto.
    - assert (Hl := num_occur_list_set _ _ x sigma Hfy l).
      apply plus_le_compat; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set _ _ x sigma Hfy [v]).
      auto.
    - inv H1; inv H2.
      apply plus_le_compat; eauto.
    - inv H; inv H0; auto.
  Qed.



  Lemma num_occur_list_set_not_x:
    forall f y x sigma,
      ~ Dom_map sigma x ->
      f <> x ->
      forall l,
        num_occur_list (apply_r_list sigma l) f  <=
        num_occur_list (apply_r_list (M.set x y sigma) l) f.
  Proof.
    induction l; intros; simpl; auto.
    destruct (var_dec x a).
    - subst.
      rewrite apply_r_set1.
      destruct (cps_util.var_dec f y). subst.
      destruct (cps_util.var_dec y (apply_r sigma a)); omega.
      destruct (cps_util.var_dec f (apply_r sigma a)).
      exfalso. unfold apply_r  in e.
      destruct (Maps.PTree.get a sigma) eqn:gas.
      apply H. exists e0; auto.
      auto.
      auto.
    -     rewrite apply_r_set2; auto.
          destruct (cps_util.var_dec f (apply_r sigma a)); omega.
  Qed.



  Lemma num_occur_rename_all_ns_set_not_x:
    forall f x y sigma,
      ~ Dom_map sigma x ->
      f <> x ->
      ( forall e m n,
          num_occur (rename_all_ns sigma e) f m ->
          num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
          m <= n) /\
      ( forall fds m n,
          num_occur_fds (rename_all_fun_ns sigma fds) f m ->
          num_occur_fds (rename_all_fun_ns (M.set x y sigma) fds) f n  ->
          m <= n).
  Proof.
    intros f x y sigma Hdom Hfy; apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy l).
      specialize (H _ _ H8 H7).
      apply plus_le_compat; eauto.
    - inv H; inv H0.
      inv H5; inv H4.
      assert (Hl := num_occur_list_set_not_x).
      specialize (Hl f y x _ Hdom Hfy [v]).
      simpl in Hl.
      simpl.
      do 2 (rewrite plus_0_r).
      auto.
    - inv H1; inv H2.
      inv H7; inv H6.
      rewrite OrdersEx.Nat_as_OT.add_shuffle3.
      rewrite  OrdersEx.Nat_as_OT.add_shuffle3 with (p := m0).
      apply plus_le_compat; eauto.
    -     assert (Hl := num_occur_list_set_not_x).
          specialize (Hl f y x _ Hdom Hfy [v0]).
          specialize (H _ _ H9 H8).
          simpl; simpl in Hl.
          apply plus_le_compat; eauto.
    - inv H1; inv H2.
      apply plus_le_compat; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set_not_x).
      specialize (Hl f y x _ Hdom Hfy (v::l)).
      auto.
    -  assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy l).
       apply plus_le_compat; eauto.
    - inv H; inv H0.
      assert (Hl := num_occur_list_set_not_x f y x _ Hdom Hfy [v]).
      auto.
    - inv H1; inv H2.
      apply plus_le_compat; eauto.
    - inv H; inv H0; auto.
  Qed.

  Lemma num_occur_rename_all_ns_set_unchanged:
    forall f x y sigma e m n,
      ~ Dom_map sigma x ->
      f <> x ->
      f <> y ->
      num_occur (rename_all_ns sigma e) f m ->
      num_occur (rename_all_ns (M.set x y sigma) e) f n  ->
      m = n.
  Proof.
    intros.
    assert (n <= m). eapply (proj1 (num_occur_rename_all_ns_set _ _ _ H1)); eauto.
    assert (m <= n). eapply (proj1 (num_occur_rename_all_ns_set_not_x _ _ _ _ H H0)); eauto.
    omega.
  Qed.

  Lemma not_occur_rename_not_dom:
    forall sig v e,
      ~ Dom_map sig v ->
      num_occur (rename_all_ns sig e) v 0 ->
      num_occur e v 0.
  Proof.
    intros.
    assert (exists n, num_occur e v n) by apply e_num_occur.
    inv H1.
    assert (Hn0 := proj1 (num_occur_rename_all_not_dom_mut v) _ _ _ _ H2 H0 H).
    apply le_n_0_eq in Hn0. subst; auto.
  Qed.

  Definition rename_all_case sigma cl := (List.map (fun (p:var*exp) => let (k, e) := p in
                                                                    (k, rename_all_ns sigma e)) cl).


  Lemma num_occur_case_rename_all_ns_not_dom:
    forall f,
    forall cl sig n m,
      num_occur_case cl f n ->
      num_occur_case (rename_all_case sig cl) f m ->
      ~ Dom_map sig f ->
      n <= m.
  Proof.
    induction cl; intros.
    - inv H; inv H0; auto.
    - inv H; inv H0.
      apply plus_le_compat.
      eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
      eauto.
  Qed.



  Lemma num_occur_sig_unaffected:
    forall x sig n m e,
      ~ Dom_map sig x ->
      ~ Range_map sig x ->
      num_occur e x n ->
      num_occur (rename_all_ns sig e) x m ->
      n = m.
  Proof.
    intros.
    assert (n <= m).
    eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
    assert (m <= n).
    eapply (proj1 (num_occur_rename_all_ns_not_range_mut _ _ H0)); eauto.
    omega.
  Qed.

  Lemma num_occur_set_arl:
    forall x y,
      x <> y ->
      forall l,
        num_occur_list (apply_r_list (M.set x y (M.empty var)) l) y =
        num_occur_list l y + num_occur_list l x.
  Proof.
    intros x y Hxy. induction l.
    auto.
    simpl. destruct (cps_util.var_dec x a).
    - subst. rewrite apply_r_set1.
      destruct (cps_util.var_dec y a).
      exfalso; auto.
      destruct (cps_util.var_dec y y). 2: exfalso; auto.
      omega.
    - rewrite apply_r_set2 by auto.
      rewrite apply_r_empty.
      destruct (cps_util.var_dec y a); omega.
  Qed.

  Lemma num_occur_arl_kill:
    forall x sig,
      ~ Range_map sig x ->
      Dom_map sig x ->
      forall l,
        num_occur_list (apply_r_list sig l) x = 0.
  Proof.
    induction l.
    auto.
    simpl. destruct (cps_util.var_dec x (apply_r sig a)).
    - exfalso. unfold apply_r in e.
      destruct (Maps.PTree.get a sig) eqn:gas.
      subst.
      apply H. exists a; auto.
      subst.
      inv H0. rewrite H1 in gas. inv gas.
    - auto.
  Qed.

  Lemma num_occur_rename_all_ns_kill:
    forall x sig,
      ~ Range_map sig x ->
      Dom_map sig x ->
      (forall e,
          num_occur (rename_all_ns sig e) x 0 )/\
      (forall fds,
          num_occur_fds (rename_all_fun_ns sig fds) x 0).
  Proof.
    intros x sig Hrx Hdx.
    apply exp_def_mutual_ind; intros; simpl in *.
    - eapply num_occur_n. constructor. eauto.
      rewrite num_occur_arl_kill; auto.
    - eapply num_occur_n. constructor. constructor.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v]).
      simpl in Hn. simpl. omega.
    - eapply num_occur_n. constructor. constructor. eauto.
      inv H0; pi0; eauto. simpl.
      inv H0; pi0.  auto.
    - eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v0]).
      simpl in *; omega.
    - eapply num_occur_n. constructor; eauto.
      auto.
    - eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx (v::l)).
      simpl in *. omega.
    - eapply num_occur_n. constructor; eauto.
      rewrite num_occur_arl_kill; auto.
    - eapply num_occur_n. constructor; auto.
      assert (Hn := num_occur_arl_kill _ _ Hrx Hdx [v]).
      simpl in *; omega.
    - eapply num_occur_fds_n.  constructor; eauto.
      auto.
    - constructor.
  Qed.

  Lemma num_occur_rename_mut:
    forall x y,
      x <> y ->
      (forall e n m,
          num_occur e x n ->
          num_occur e y m ->
          num_occur (rename_all_ns (M.set x y (M.empty var)) e) x 0 /\
          num_occur (rename_all_ns (M.set x y (M.empty var)) e) y (n+m)) /\
      (forall fds n m,
          num_occur_fds fds x n ->
          num_occur_fds fds y m ->
          num_occur_fds (rename_all_fun_ns (M.set x y (M.empty var)) fds) x 0 /\
          num_occur_fds (rename_all_fun_ns (M.set x y (M.empty var)) fds) y (n+m)).
  Proof.
    intros x y Hxy.
    apply exp_def_mutual_ind; intros; simpl in *; try (inv H0; inv H1).
    - specialize (H _ _ H8 H7).
      destruct H. split.
      eapply num_occur_n.
      constructor. eauto.
      rewrite num_occur_arl; auto.
      eapply num_occur_n.
      constructor; eauto.
      rewrite num_occur_set_arl; auto. omega.
    - inv H; inv H0.
      inv H5; inv H4.
      split.
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl _ _ [v] Hxy).
      simpl in Hn. simpl.  rewrite plus_0_r. auto.
      eapply num_occur_n. constructor. auto.
      assert (Hnn := num_occur_set_arl _ _ Hxy [v]).
      simpl. simpl in Hnn. do 3 (rewrite plus_0_r). rewrite plus_comm. auto.
    - inv H1; inv H2. inv H7; inv H6.
      specialize (H _ _ H8 H7).
      assert (num_occur (Ecase v l) x ( num_occur_list [v] x + m)).
      constructor; auto.
      assert (num_occur (Ecase v l) y ( num_occur_list [v] y + m0)).
      constructor; auto.
      specialize (H0 _ _ H1 H2).
      destruct H. destruct H0.
      inv H0; inv H4.
      split.
      + eapply num_occur_n.
        constructor. constructor; eauto.
        simpl. auto.
      + eapply num_occur_n.
        constructor. constructor; eauto.
        simpl. omega.
    - specialize (H _ _ H9 H8).
      destruct H.
      split.
      eapply num_occur_n. constructor; eauto.
      assert (Hn := num_occur_arl _ _ [v0] Hxy).
      simpl in Hn. simpl. rewrite plus_0_r. auto.
      eapply num_occur_n. constructor; eauto.
      assert (Hnn := num_occur_set_arl _ _ Hxy [v0]).
      simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. rewrite Hnn. omega.
    - inv H1; inv H2.
      specialize (H _ _ H8 H9).
      specialize (H0 _ _ H5 H4).
      destructAll. split; eapply num_occur_n; eauto.
      omega.
    - inv H; inv H0. split; eapply num_occur_n; eauto.
      assert (Hn := num_occur_arl _ _ (v::l) Hxy).
      simpl in Hn. simpl.
      unfold var in *. unfold M.elt in *. omega.
      assert (Hnn := num_occur_set_arl _ _ Hxy (v::l)).
      simpl. simpl in Hnn. unfold var in *. unfold M.elt in *. omega.
    - specialize (H _ _ H8 H7).
      destruct H.
      split; eapply num_occur_n; eauto.
      rewrite num_occur_arl; auto.
      rewrite num_occur_set_arl; auto. omega.
    - inv H; inv H0.
      split; eapply num_occur_n; eauto.
      assert (Hn := num_occur_arl _ _ [v] Hxy).
      simpl in Hn. simpl. unfold var in *.
      unfold M.elt in *.
      omega.
      assert (Hnn := num_occur_set_arl _ _ Hxy [v]).
      simpl. simpl in Hnn. unfold var in *.  unfold M.elt in *. omega.
    - inv H1; inv H2. specialize (H _ _ H10 H9).
      specialize (H0 _ _ H11 H12).
      destruct H; destruct H0.
      split.
      eapply num_occur_fds_n. constructor; eauto.  auto.
      eapply num_occur_fds_n. constructor; eauto.  omega.
    - inv H; inv H0. split; auto.
  Qed.

  Lemma num_occur_rename_all_ctx_not_dom_mut:
    forall f,
      ( forall c m n sigma,
          num_occur_ec c f m ->
          num_occur_ec (rename_all_ctx_ns sigma c) f n  ->
          ~ Dom_map sigma f ->
          m <= n) /\
      ( forall fds m n sigma,
          num_occur_fdc fds f m ->
          num_occur_fdc (rename_all_fun_ctx_ns sigma fds) f n  ->
          ~ Dom_map sigma f ->
          m <= n).
  Proof.
    intro f.
    exp_fundefs_ctx_induction IHc IHfc; intros.
    - inv H0. inv H; auto.
    - simpl in H0. inv H0.
      inv H.
      specialize (IHc _ _ _  H7 H8).
      apply plus_le_compat.
      apply num_occur_list_not_dom. auto.
      apply IHc. auto.
    - simpl in H0. inv H0.
      inv H.
      apply plus_le_compat.
      apply (num_occur_list_not_dom _ _ H1 ([v0])).
      eauto.
    - simpl in H0. inv H0. inv H.
      apply plus_le_compat.
      apply num_occur_list_not_dom; auto.
      eauto.
    - simpl in H0. inv H0.
      inv H.
      repeat apply plus_le_compat.
      apply (num_occur_list_not_dom _ _ H1 ([v])).
      2: eauto.
      eapply num_occur_case_rename_all_ns_not_dom; eauto.
      eapply num_occur_case_rename_all_ns_not_dom; eauto.
    - inv H.
      simpl in H0. inv H0.
      apply plus_le_compat; eauto.
      eapply (proj2 (num_occur_rename_all_not_dom_mut _)); eauto.
    - inv H. inv H0.
      apply plus_le_compat; eauto.
      eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
    - inv H.
      simpl in H0. inv H0.
      apply plus_le_compat; eauto.
      eapply (proj2 (num_occur_rename_all_not_dom_mut _)); eauto.
    - inv H. inv H0.
      apply plus_le_compat; eauto.
      eapply (proj1 (num_occur_rename_all_not_dom_mut _)); eauto.
  Qed.

  (* move to cps_util *)
  Lemma e_num_occur_ec:
    forall c v, exists n, num_occur_ec c v n.
  Proof.
    intros.
    assert (exists n, num_occur (c |[ Ehalt v ]|) v n) by apply e_num_occur.
    destruct H.
    apply num_occur_app_ctx in H. destructAll.
    eauto.
  Qed.


  Lemma not_occur_rename_ctx_not_dom:
    forall sig v c,
      ~ Dom_map sig v ->
      num_occur_ec (rename_all_ctx_ns sig c) v 0 ->
      num_occur_ec c v 0.
  Proof.
    intros.
    assert (exists n, num_occur_ec c v n) by apply e_num_occur_ec.
    inv H1.
    assert (Hn0 := proj1 (num_occur_rename_all_ctx_not_dom_mut v) _ _ _ _ H2 H0 H).
    apply le_n_0_eq in Hn0. subst; auto.
  Qed.


  Lemma not_occur_list: forall v l,
      num_occur_list l v = 0 <->
      ~ FromList l v.
  Proof.
    induction l; split; intro.
    - intro.
      inv H0.
    - constructor.
    - intro.
      simpl in H.
      inv H0.
      destruct (cps_util.var_dec v v). inv H. apply n; auto.
      destruct (cps_util.var_dec v a). inv H. apply IHl in H.
      auto.
    - simpl.
      destruct (cps_util.var_dec v a).
      exfalso; apply H.
      constructor. auto.
      apply IHl.
      intro; apply H.
      constructor 2. auto.
  Qed.

  Lemma of_fun_inline:
    forall xs vs fb t c f B1 B2 c',
      unique_bindings (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|) ->
      num_occur
        (Efun (fundefs_append B1 (Fcons f t xs fb B2))
              (c |[ Eapp f t vs ]|)) f 1 ->
      List.length xs = List.length vs ->
      Included _ (occurs_free (c' |[Efun (fundefs_append B1 B2) (c |[ (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb)]|) ]|))
               (occurs_free (c' |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c |[ Eapp f t vs ]|) ]|)).
  Proof.
    intros xs vs fb t c f B1 B2 c' H Hnoc H0.
    eapply Included_trans.
    Focus 2.
    apply occurs_free_exp_ctx_included.
    apply of_fun_inline''' with (f := f) (fds := (fundefs_append B1 (Fcons f t xs fb B2))).
    2: apply H0.
    erewrite find_def_fundefs_append_r.
    simpl. destruct (M.elt_eq f f).
    reflexivity.
    exfalso. apply n. auto.
    simpl. destruct (M.elt_eq f f).
    reflexivity.
    exfalso. apply n. auto.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H1.
    apply name_not_in_fundefs_find_def_None.
    eapply fundefs_append_unique_bindings_l in H6.
    2: reflexivity.
    destructAll.
    rewrite bound_var_fundefs_Fcons in H4.
    intro.
    apply name_in_fundefs_bound_var_fundefs in H6.
    inv H4.
    specialize (H8 f).
    apply H8.
    split; eauto.
    apply of_fun_rm.
    apply ub_app_ctx_f in H.
    destructAll.
    inv H1. auto.
    {
      inv Hnoc.
      apply num_occur_app_ctx in H5.
      destructAll.
      inv H2. simpl in H3.
      destruct (cps_util.var_dec f f).
      2: (exfalso; apply n; auto).
      assert (x = 0 /\ num_occur_list vs f = 0 /\ m = 0).
      omega.
      clear H3.
      apply fundefs_append_num_occur' in H6.
      destructAll.
      pi0.
      inv H6; pi0.
      constructor.
      apply num_occur_app_ctx.
      exists 0, 0.
      split; auto.
      split; auto.
      assert (exists n, num_occur (rename_all_ns (set_list (combine xs vs) (M.empty var)) fb) f n) by apply e_num_occur.
      destruct H2.
      assert (x <= 0).
      eapply num_occur_rename_all_ns_not_range; eauto.
      intro.
      apply Range_map_set_list in H4.
      apply not_occur_list in H3. auto.
      apply le_n_0_eq in H4.
      subst. auto.
      rewrite <- plus_0_l.
      eapply fundefs_append_num_occur.
      reflexivity.
      auto.
      rewrite <- plus_0_l.
      constructor; auto.
    }
  Qed.


  Lemma sr_rw_in_rw: forall e e',
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      gen_sr_rw e e' ->
      gr_clos e e'.
  Proof.
    intros;
      inv H1;
      inv H2;
      try (solve [constructor; constructor; constructor; try (apply (not_occurs_not_free)); auto]).
    -  constructor. constructor.
       constructor.
       eapply Forall_impl. 2: apply H1.
       intros.
       apply not_occurs_not_free. auto.
    - do 2 (constructor).
      apply Fun_rem; auto.
      apply ub_app_ctx_f in H.
      destructAll.
      inv H2. apply unique_bind_has_unique_name.  auto.
    -  constructor.
       constructor.
       constructor; auto.
       apply ub_app_ctx_f in H.
       destructAll.
       inv H2.
       intro.
       apply H6.
       apply bound_var_app_ctx.
       left.
       apply bound_stem_var. auto.
    - constructor.
      constructor.
      assert (H' := H).
      apply ub_app_ctx_f in H. destructAll.
      inv H2.
      apply ub_app_ctx_f in H9. destructAll.
      rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).
      Focus 2. inv H4.  rewrite Dom_map_set. rewrite Dom_map_empty.
      eauto with Ensembles_DB.
      constructor; auto.
      + intro; apply H6.
        apply bound_var_app_ctx. left. apply bound_stem_var; auto.
      + intro.
        destruct (bound_var_ctx_dec c).
        specialize (Dec k). inv Dec.
        * inv H3. specialize (H9 k).
          apply H9.
          split; auto.
          rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
          left. left. apply bound_stem_var.
          auto.
        * inv H0. specialize (H9 k).
          apply H9.
          split.
          rewrite bound_var_app_ctx.
          rewrite bound_var_Econstr.
          rewrite bound_var_app_ctx. right. left. left.
          apply bound_stem_var. auto.
          apply occurs_free_ctx_not_bound; auto.
          apply nthN_FromList in H1. auto.
      + destruct (bound_var_ctx_dec c).
        specialize (Dec k). inv Dec.
        * intro.
          inv H3.
          specialize (H9 k).
          apply H9.
          split; auto.
          rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
          rewrite bound_var_Eproj. auto.
        * intro. inv H0.
          specialize (H9 k).
          apply H9. split.
          rewrite bound_var_app_ctx.
          rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
          rewrite bound_var_Eproj.  auto.
          apply occurs_free_ctx_not_bound; auto.
          apply nthN_FromList in H1. auto.
      + intro; subst.
        (* either k is in the bv of c and H2 is false,
            or k isn't and k is in of (since it appears in ys re:H1) *)
        destruct (bound_var_ctx_dec c).
        specialize (Dec k). inv Dec.
        * inv H3.
          specialize (H8 k).
          apply H8.
          split; auto.
        * inv H0.
          specialize (H8 k).
          apply H8. split; auto.
          rewrite bound_var_app_ctx.
          rewrite bound_var_Econstr. auto.
          apply occurs_free_ctx_not_bound; auto.
          apply nthN_FromList in H1. auto.
      + intro; subst.
        (* either k is in the bv of c and H2 is false,
            or k isn't and k is in of (since it appears in ys re:H1) *)
        destruct (bound_var_ctx_dec c).
        specialize (Dec k). inv Dec.
        * inv H3.
          specialize (H8 k).
          apply H8.
          split; auto.
          rewrite bound_var_Econstr. rewrite bound_var_app_ctx.
          auto.
        * inv H0.
          specialize (H8 k).
          apply H8. split; auto.
          rewrite bound_var_app_ctx.
          rewrite bound_var_Econstr.
          rewrite bound_var_app_ctx.
          auto.
          apply occurs_free_ctx_not_bound; auto.
          apply nthN_FromList in H1. auto.
    - (* fun inline *)
      eapply rt_trans.
      + constructor.
        constructor.
        apply Fun_inline.
        * erewrite find_def_fundefs_append_r. simpl.
          destruct (M.elt_eq f f). reflexivity. exfalso; auto.
          simpl.         destruct (M.elt_eq f f). reflexivity. exfalso; auto.
          apply name_not_in_fundefs_find_def_None.
          intro.
          apply ub_app_ctx_f in H. destructAll. inv H4.
          eapply fundefs_append_unique_bindings_l in H9.
          2: reflexivity.
          destructAll.
          inv H7.
          specialize (H9 f).
          apply H9. split.
          apply name_in_fundefs_bound_var_fundefs. auto.
          constructor. left. auto.
        * apply ub_app_ctx_f in H. destructAll.
          inv H2.
          split. intro. intro.
          inv H2.
          assert (Hof := Decidable_occurs_free (c0 |[ Eapp f t vs ]|)).
          inv Hof. specialize (Dec x).
          destruct Dec.
          {
            assert (Hnf:= Decidable_name_in_fundefs  (fundefs_append B1 (Fcons f t xs fb B2))).
            inv Hnf. destruct (Dec x) as [Hin | Hnin].
            eapply fundefs_append_unique_bindings_l in H8. 2: reflexivity.
            destructAll.
            eapply fundefs_append_name_in_fundefs in Hin. 2: reflexivity.
            inv Hin. inv H10. specialize (H12 x).
            apply H12. split.
            apply name_in_fundefs_bound_var_fundefs.
            auto.
            apply bound_var_fundefs_Fcons. now inv H5; auto.
            inv H10. inv H11.
            inv H10.
            inv H5; auto.
            inv H8; contradiction. inv H8; contradiction.
            apply name_in_fundefs_bound_var_fundefs in H10.
            inv H5; auto.
            inv H8. eapply H20. now constructor; eauto.
            inv H8. eapply H21. now constructor; eauto.
            (* now inv H20; contradiction. *)
            (* inv H8; contradiction. inv H21. specialize (H5 x). apply H5; auto. *)
            (* inv H22. specialize (H5 x). apply H5; auto. *)
            assert (occurs_free (Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|)) x).
            { apply Free_Efun1; auto. }
            assert (Hc := bound_var_ctx_dec c). inv Hc.
            destruct (Dec0 x) as [Hin' | Hnin'].
            inv H4. specialize (H10 x).
            apply H10. split. eassumption.
            constructor.
            eapply fundefs_append_bound_vars. reflexivity.
            right.
            apply bound_var_fundefs_Fcons.
            inv H5; auto.
            assert ((occurs_free (c |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|) ]|) x)).
            apply occurs_free_ctx_not_bound; auto.
            inv H0. specialize (H11 x).
            apply H11. split; auto.
            apply bound_var_app_ctx. right.
            rewrite bound_var_Efun.
            left.
            eapply fundefs_append_bound_vars. reflexivity.
            right. apply bound_var_fundefs_Fcons.
            inv H5; auto.
          }
          { assert (bound_var_ctx c0 x).
            eapply occurs_free_app_bound_var.
            2: apply n. constructor. auto.
            inv H9. specialize (H10 x).
            apply H10. split.
            rewrite bound_var_app_ctx. left; auto.
            eapply fundefs_append_bound_vars.
            reflexivity. right.
            rewrite bound_var_fundefs_Fcons.
            inv H5; eauto.
          }
        * apply unique_bind_has_unique_name.
          apply ub_app_ctx_f in H. destructAll.
          inv H2.
          auto.
        * split; intro. intro. inv H2.
          assert (Hc := bound_var_ctx_dec c).
          inv Hc. specialize (Dec x).
          apply ub_app_ctx_f in H. destructAll.
          inv Dec.
          inv H6. specialize (H8 x). apply H8. split; auto.
          apply bound_var_Efun.
          right. apply bound_var_app_ctx. left.
          apply bound_stem_var; auto.
          assert (occurs_free ( Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|)) x).
          apply Free_Efun2. auto.
          assert (occurs_free (c |[ Efun (fundefs_append B1 (Fcons f t xs fb B2)) (c0 |[ Eapp f t vs ]|) ]|) x).
          apply occurs_free_ctx_not_bound; auto.
          inv H0. specialize (H10 x). apply H10. split; auto.
          apply bound_var_app_ctx. right. apply bound_var_Efun.
          right. apply bound_var_app_ctx. left. apply bound_stem_var; auto.
        * apply ub_app_ctx_f in H. destructAll.
          inv H2.
          eapply Disjoint_Included_r.
          apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_l.
          2: apply H9.
          etransitivity.
          apply bound_stem_var.
          rewrite bound_var_app_ctx.
          apply Included_Union_l.
        * apply ub_app_ctx_f in H. destructAll.
          inv H2.
          eapply fundefs_append_unique_bindings_l in H8. 2: reflexivity.
          destructAll.
          inv H5; auto.
      + constructor.
        constructor.
        rewrite <- (proj1 (Disjoint_dom_rename_all_eq _)).
        Focus 2. rewrite Dom_map_set_list; auto. rewrite Dom_map_empty.
        apply ub_app_ctx_f in H. destructAll. inv H2.
        eapply fundefs_append_unique_bindings_l in H8. 2: reflexivity. destructAll. inv H5.
        rewrite Union_Empty_set_neut_r.
        split. intro. intro.  inv H5. inv H16. specialize (H5 x). apply H5; auto.
        apply Fun_rem.
        * apply ub_app_ctx_f in H. destructAll.
          inv H2.
          apply unique_bind_has_unique_name.
          auto.
        * inv H3.
          apply num_occur_app_ctx in H7. destructAll.
          inv H3.
          simpl in H5.
          destruct (cps_util.var_dec f f); [       | exfalso; apply n; auto].
          replace (x + S (num_occur_list vs f) + m)  with  (S (x + (num_occur_list vs f) + m)) in H5 by omega.
          inv H5.
          rewrite H4.
          pi0.
          assert (H8' := H8).
          apply fundefs_append_num_occur' in H8. destructAll.
          pi0.
          inv H5; pi0.
          constructor; auto.
          apply num_occur_app_ctx. exists 0; exists 0.
          split; auto.
          split; auto.
          assert (exists n, num_occur (rename_all (set_list (combine xs vs) (M.empty var)) fb) f n).
          apply e_num_occur.
          destruct H5.
          assert (x <= 0).
          eapply num_occur_rename_all_not_range; eauto.
          intro.
          apply Range_map_set_list in H6.
          revert H6.
          apply not_occur_list. auto.
          apply le_n_0_eq in H6; subst; auto.
  Qed.

  Lemma bound_var_rename_all_exp:
    forall e sigma,
      Same_set _ (bound_var e) (bound_var (rename_all sigma e)).
  Proof.
    intro. intro. split.
    intro. intro. apply bound_var_rename_all. auto.
    intro. intro. eapply bound_var_rename_all. eauto.
  Qed.

  Lemma rw_preserves: forall e e',
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      gsr_clos e e' ->
      unique_bindings e' /\
      Disjoint _ (bound_var e') (occurs_free e').
  Proof.
    intros e e' Hub Hdj H.
    induction H.
    - inv H. inv H0.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Econstr in H2.
        eauto with Ensembles_DB.
        rewrite bound_var_app_ctx in Hdj.
        rewrite bound_var_Econstr in Hdj.
        rewrite bound_var_app_ctx.
        eapply Disjoint_Included_r.
        apply of_constr_dead. apply H.
        eapply Disjoint_Included_l; eauto.
        auto with Ensembles_DB.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Eprim in H2.
        eauto with Ensembles_DB.
        rewrite bound_var_app_ctx in Hdj.
        rewrite bound_var_Eprim in Hdj.
        rewrite bound_var_app_ctx.
        eapply Disjoint_Included_r.
        apply of_prim_dead. apply H.
        eapply Disjoint_Included_l; eauto.
        auto with Ensembles_DB.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Eproj in H2.
        eauto with Ensembles_DB.
        rewrite bound_var_app_ctx in Hdj.
        rewrite bound_var_Eproj in Hdj.
        rewrite bound_var_app_ctx.
        eapply Disjoint_Included_r.
        apply of_proj_dead. apply H.
        eapply Disjoint_Included_l; eauto.
        auto with Ensembles_DB.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Efun in H2.
        eauto with Ensembles_DB.
        rewrite bound_var_app_ctx in Hdj.
        rewrite bound_var_Efun in Hdj.
        rewrite bound_var_app_ctx.
        eapply Disjoint_Included_r.
        apply of_fun_dead. apply H.
        eapply Disjoint_Included_l; eauto.
        auto with Ensembles_DB.
      + apply ub_app_ctx_f in Hub.
        destructAll.
        inv H1.
        rewrite bound_var_Efun in H2.
        rewrite fundefs_append_bound_vars in H2. 2: reflexivity.
        rewrite bound_var_fundefs_Fcons in H2.
        rewrite fundefs_append_bound_vars in H7. 2: reflexivity.
        rewrite bound_var_fundefs_Fcons in H7.
        split.
        apply ub_app_ctx_f.
        split; auto.
        split.
        constructor; auto.
        {
          eapply fundefs_append_unique_bindings_l in H6.
          2: reflexivity.
          destructAll.
          inv H3.
          eapply fundefs_append_unique_bindings_r; auto.
          rewrite bound_var_fundefs_Fcons in H4.
          eapply Disjoint_Included_r.
          2: apply H4.
          eauto with Ensembles_DB.
        }
        rewrite fundefs_append_bound_vars.
        2: reflexivity.
        eapply Disjoint_Included_r.
        2: apply H7.
        eauto with Ensembles_DB.
        rewrite bound_var_Efun.
        rewrite fundefs_append_bound_vars.
        2: reflexivity.
        eapply Disjoint_Included_r.
        2: apply H2.
        eauto with Ensembles_DB.

        eapply Disjoint_Included_r.
        eapply of_fun_rm.
        eauto.
        apply H.
        eapply Disjoint_Included_l.
        2: apply Hdj.
        do 2 (rewrite bound_var_app_ctx).
        do 2 (rewrite bound_var_Efun).
        rewrite fundefs_append_bound_vars.
        2: reflexivity.
        rewrite fundefs_append_bound_vars with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
        2: reflexivity.
        rewrite bound_var_fundefs_Fcons.
        eauto 25 with Ensembles_DB.
      + split.
        {
          rewrite inv_app_Econstr.
          rewrite app_ctx_f_fuse.
          rewrite app_ctx_f_fuse.
          rewrite inv_app_Econstr in Hub.
          rewrite app_ctx_f_fuse in Hub.
          rewrite app_ctx_f_fuse in Hub.
          eapply ub_case_inl.
          2: apply Hub.
          eexists; eauto.
        }
        eapply Disjoint_Included_r.
        eapply of_case_fold. apply H.
        eapply Disjoint_Included_l.
        2: apply Hdj.
        do 2 (rewrite bound_var_app_ctx).
        do 2 (rewrite bound_var_Econstr).
        do 2 (rewrite bound_var_app_ctx).
        apply Included_Union_compat.
        reflexivity.
        apply Included_Union_compat.
        apply Included_Union_compat.
        reflexivity.
        intro.
        intro.
        eapply Bound_Ecase. apply H0.
        apply findtag_In_patterns.
        eauto.
        reflexivity.
      + split.
        {
          rewrite inv_app_Econstr.
          rewrite app_ctx_f_fuse.
          rewrite app_ctx_f_fuse.
          rewrite inv_app_Econstr in Hub.
          rewrite app_ctx_f_fuse in Hub.
          rewrite app_ctx_f_fuse in Hub.
          eapply ub_proj_dead in Hub.
          apply ub_app_ctx_f in Hub.
          destructAll.
          rewrite bound_var_rename_all_ns in H2.
          eapply unique_bindings_rename_all_ns in H1.
          apply ub_app_ctx_f; eauto.
        }
        eapply Disjoint_Included_r.
        apply occurs_free_exp_ctx_included.
        apply of_constr_proj'.
        apply H.
        eapply Disjoint_Included_l.
        2: apply Hdj.
        do 2 (rewrite bound_var_app_ctx).
        repeat (normalize_bound_var).
        do 2 (rewrite bound_var_app_ctx).
        repeat normalize_bound_var.
        unfold rename.
        rewrite <- bound_var_rename_all_ns.
        eauto with Ensembles_DB.
      + split.

        eapply ub_fun_inlining; apply Hub.

        eapply Disjoint_Included_r.
        apply of_fun_inline; eauto.
        eapply Disjoint_Included_l.
        2: apply Hdj.
        do 2 (rewrite bound_var_app_ctx).
        repeat (normalize_bound_var).
        do 2 (rewrite bound_var_app_ctx).
        rewrite <- bound_var_rename_all_ns.
        rewrite fundefs_append_bound_vars.
        2: reflexivity.
        rewrite fundefs_append_bound_vars with (B3 := (fundefs_append B1 (Fcons f t xs fb B2))).
        2: reflexivity.
        repeat normalize_bound_var.
        eauto 25 with Ensembles_DB.
    - split; auto.
    - specialize (IHclos_refl_trans1 Hub Hdj).
      destructAll.
      apply IHclos_refl_trans2; auto.
  Qed.


  Definition closed e: Prop:=
    Same_set _ (Empty_set var) (occurs_free e).

  Lemma gsr_preserves_clos:
    forall e e',
      unique_bindings e ->
      closed e ->
      gsr_clos e e' ->
      unique_bindings e' /\
      closed e'.
  Proof.
    intros e e' Hub Hdj H.
    induction H.
    - inv H. inv H0.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Econstr in H2.
        eauto with Ensembles_DB.
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        apply of_constr_dead. apply H.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Eprim in H2.
        eauto with Ensembles_DB.
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        apply of_prim_dead. apply H.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Eproj in H2.
        eauto with Ensembles_DB.
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        apply of_proj_dead. apply H.
      + split.
        apply ub_app_ctx_f in Hub.
        apply ub_app_ctx_f. destructAll.
        inv H1.
        split; auto.
        split; auto.
        rewrite bound_var_Efun in H2.
        eauto with Ensembles_DB.
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        apply of_fun_dead. apply H.
      + apply ub_app_ctx_f in Hub.
        destructAll.
        inv H1.
        rewrite bound_var_Efun in H2.
        rewrite fundefs_append_bound_vars in H2. 2: reflexivity.
        rewrite bound_var_fundefs_Fcons in H2.
        rewrite fundefs_append_bound_vars in H7. 2: reflexivity.
        rewrite bound_var_fundefs_Fcons in H7.
        split.
        apply ub_app_ctx_f.
        split; auto.
        split.
        constructor; auto.
        {
          eapply fundefs_append_unique_bindings_l in H6.
          2: reflexivity.
          destructAll.
          inv H3.
          eapply fundefs_append_unique_bindings_r; auto.
          rewrite bound_var_fundefs_Fcons in H4.
          eapply Disjoint_Included_r.
          2: apply H4.
          eauto with Ensembles_DB.
        }
        rewrite fundefs_append_bound_vars.
        2: reflexivity.
        eapply Disjoint_Included_r.
        2: apply H7.
        eauto with Ensembles_DB.
        rewrite bound_var_Efun.
        rewrite fundefs_append_bound_vars.
        2: reflexivity.
        eapply Disjoint_Included_r.
        2: apply H2.
        eauto with Ensembles_DB.
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        eapply of_fun_rm.
        auto.
        auto.
      + split.
        {
          rewrite inv_app_Econstr.
          rewrite app_ctx_f_fuse.
          rewrite app_ctx_f_fuse.
          rewrite inv_app_Econstr in Hub.
          rewrite app_ctx_f_fuse in Hub.
          rewrite app_ctx_f_fuse in Hub.
          eapply ub_case_inl.
          2: apply Hub.
          eexists; eauto.
        }
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        eapply of_case_fold. auto.
      + split.
        {
          rewrite inv_app_Econstr.
          rewrite app_ctx_f_fuse.
          rewrite app_ctx_f_fuse.
          rewrite inv_app_Econstr in Hub.
          rewrite app_ctx_f_fuse in Hub.
          rewrite app_ctx_f_fuse in Hub.
          eapply ub_proj_dead in Hub.
          apply ub_app_ctx_f in Hub.
          destructAll.
          rewrite bound_var_rename_all_ns in H2.
          unfold rename.
          eapply unique_bindings_rename_all_ns in H1.
          apply ub_app_ctx_f; eauto.
        }
        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        apply occurs_free_exp_ctx_included.
        apply of_constr_proj'.
        auto.
      + split.

        eapply ub_fun_inlining; apply Hub.

        apply Included_Empty_set_l.
        eapply Proper_Included_r.
        auto.
        apply Hdj.
        apply of_fun_inline; eauto.
    - split; auto.
    - specialize (IHclos_refl_trans1 Hub Hdj).
      destructAll.
      apply IHclos_refl_trans2; auto.
  Qed.

  Lemma grs_in_gr: forall e e',
      unique_bindings e ->
      Disjoint _ (bound_var e) (occurs_free e) ->
      gsr_clos e e' ->
      gr_clos e e'.
  Proof.
    intros.
    induction H1.
    - apply sr_rw_in_rw; auto.
    - apply rt_refl.
    - eapply rt_trans; eauto.
      apply IHclos_refl_trans1; auto.
      apply rw_preserves in H1_ ; auto.
      destruct H1_.
      apply IHclos_refl_trans2; auto.
  Qed.

  Corollary sr_correct e e' :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    gsr_clos e e' ->
    forall pr cenv rho rho' k,
      preord_env_P pr cenv (occurs_free e) k rho rho'->
      preord_exp pr cenv k (e, rho) (e', rho').
  Proof.
    intros.
    apply rw_correct.
    apply grs_in_gr; auto.
    auto.
  Qed.

End Shrink_Rewrites.
