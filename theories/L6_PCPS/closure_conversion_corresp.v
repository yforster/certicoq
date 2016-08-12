Require Import cps cps_util set_util identifiers ctx hoare Ensembles_util
        List_util closure_conversion closure_conversion_correct functions.
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.


(** * Correspondance of the relational and the computational definitions of  closure conversion *)

Section CC_correct.

  Variable (clo_tag : cTag).

  Open Scope ctx_scope.


  (** All the variables greater or equal to x are in S (i.e. the "fresh" set) *)
  Definition fresh (S : Ensemble var) (x : var) :=
    forall y, (x <= y)%positive -> In _ S y.

  (** Free variable map invariant *)
  Definition FVmap_inv (FVmap : VarInfoMap) Scope Funs FVs : Prop :=
    Same_set _ Scope (fun x => M.get x FVmap = Some BoundVar) /\
    Same_set _ (Setminus _ Funs Scope)
             (fun x => exists x', M.get x FVmap = Some (MRFun x')) /\
    forall N x, (nthN FVs N = Some x /\ ~ In _ Scope x /\ ~ In _ Funs x) <->
           (M.get x FVmap = Some (FVar N)).

  (** Function names substitution *)
  Definition subst (FVmap : VarInfoMap) x : var :=
    match M.get x FVmap with
      | Some (MRFun x') => x'
      | _ => x
    end.

  (** A function that corresponds to an evaluation context *)
  Definition is_exp_ctx (f : exp -> exp) C : Prop := 
    forall e, f e = app_ctx_f C e. 

  (** Set of variables not in the map *)
  Definition binding_not_in_map {A} (S : Ensemble M.elt) (map : M.t A) := 
    forall x : M.elt, In M.elt S x -> M.get x map = None.

  (** Spec for [get_name] *)
  Lemma get_name_fresh S :
    {{ fun s => fresh S (next_var s) }}
      get_name
    {{ fun _ x s' => fresh S x /\ fresh (Setminus var S (Singleton var x)) (next_var s') }}.  
  Proof.   
    eapply pre_post_mp_l.
    eapply bind_triple. eapply get_triple.
    intros[x c i e] [x' c' i' e'].
    eapply pre_post_mp_l. eapply bind_triple.
    eapply put_triple. intros u [x'' c'' i'' e'']. eapply return_triple. 
    intros [x''' c''' i''' e'''] Heq1 [Heq2 Heq3] H; subst. inv Heq1. inv Heq2. inv Heq3. 
    split; eauto. intros y Hleq.
    constructor.
    - eapply H. simpl in *. zify. omega.
    - intros Hin. inv Hin. simpl in *. eapply Pos.le_nlt in Hleq.
      eapply Hleq. zify. omega.
  Qed.
  
  Lemma fresh_monotonic S S' x :
    Included _ S S' ->
    fresh S x ->
    fresh S' x.
  Proof.
    intros Hinc Hf x' Hleq. eapply Hinc. eapply Hf. eassumption.
  Qed.  
  
  Lemma FVmap_inv_set_bound FVmap Scope Funs FVs x :
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (M.set x BoundVar FVmap) (Union _ (Singleton _ x) Scope) Funs FVs.
  Proof. 
    intros [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + unfold In. now rewrite M.gss.
      + inv Hin. inv H; congruence.
        eapply H1 in H. edestruct H as [t' Heq].
        unfold In. rewrite M.gso; now eauto.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + eauto.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        right. eapply H1. eauto.
    - intros y Hin. inv Hin. destruct (Coqlib.peq y x); subst.
      + exfalso. eauto.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x' Heq].
        * constructor; eauto.
        * eexists. rewrite M.gso; eauto.
    - eapply H2. destruct H as [x' Heq].
      destruct (Coqlib.peq x x0); subst.
      + rewrite M.gss in Heq. congruence.
      + repeat eexists. rewrite M.gso in Heq; eauto.
    - intros Hc. destruct H as [x' Heq].
      destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in Heq. congruence.
      + inv Hc. inv H; congruence.
        eapply H2; eauto. repeat eexists.
        rewrite M.gso in Heq; eauto.
    - intros [Hnth [Hnin Hnin']].
      destruct (Coqlib.peq x0 x); subst.
      + exfalso. eauto. 
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto.
        rewrite M.gso in H; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. inv Hc. inv H0; congruence.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [Hc _]]].
        eapply H3 in H0; eauto. contradiction.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc.
        rewrite M.gso in H; eauto.
        edestruct H3 as [_ [_ [_ Hc']]].
        eapply H3 in Hc; eauto. contradiction.
  Qed.

  Lemma FVmap_inv_set_funs FVmap Scope Funs FVs x x' :
    ~ In _ Scope x ->
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (M.set x (MRFun x') FVmap) Scope (Union _ (Singleton _ x) Funs) FVs.
  Proof. 
    intros Hnin [H1 [H2 H3]]. repeat split.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + contradiction.
      + eapply H1 in Hin. edestruct Hin as [t'' Heq].
        unfold In. rewrite M.gso; eauto.
    - intros y Hin. destruct (Coqlib.peq y x); subst.
      + unfold In in Hin. rewrite M.gss in Hin; congruence.
      + unfold In in Hin. rewrite M.gso in Hin; [| now eauto ].
        now eapply H1.
    - intros y Hin. inv Hin. destruct (Coqlib.peq y x); subst.
      + repeat eexists. rewrite M.gss. reflexivity.
      + edestruct H2 as [H2' _].
        edestruct H2' as [x'' Heq].
        inv H. inv H4; congruence. constructor; eassumption.
        repeat eexists. rewrite M.gso; eassumption.
    - destruct (Coqlib.peq x0 x); subst; eauto. right.
      eapply H2. edestruct H as [x'' Hget].
      rewrite M.gso in Hget; [| now eauto ].
      repeat eexists; eauto. 
    - destruct H as [x'' Hget].
      destruct (Coqlib.peq x0 x); subst; eauto.
      rewrite M.gso in Hget; [| now eauto ].
      intros Hc. apply H1 in Hc. congruence.
    - intros [Hnth [Hnin1 Hnin2]].
      destruct (Coqlib.peq x0 x); subst.
      + exfalso. eauto.
      + edestruct H3 as [Heq _].
        rewrite M.gso; eauto. eapply Heq; repeat split; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + eapply H3; eauto. rewrite M.gso in H; eauto.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. rewrite M.gso in H; eauto.
        eapply H1 in Hc. congruence.
    - destruct (Coqlib.peq x0 x); subst.
      + rewrite M.gss in H. congruence.
      + intros Hc. rewrite M.gso in H; eauto.
        inv Hc. inv H0; congruence.
        edestruct H2 as [H2' _].  edestruct (H2' x0) as [y Hge'].
        constructor. eauto. intros Hc. eapply H1 in Hc. 
        congruence. congruence.
  Qed.

  (** Spec for [get_var] *)
  Lemma get_var_project_var_sound Scope Funs c Γ FVs FVmap S x :
    binding_in_map (Singleton _ x) FVmap ->
    (* binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap -> *)
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (next_var s') /\
           let '(x', f) := t in
           project_var clo_tag Scope Funs (subst FVmap) c Γ FVs S x x' C S' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hin Minv. destruct Minv as [Minv1 [Minv2 Minv3]]. 
    unfold get_var. edestruct (Hin x) as [inf Hget]; eauto. 
    destruct inf; rewrite Hget. 
    - eapply bind_triple.
      + eapply get_name_fresh.     
      + intros x' s. eapply return_triple. intros s' [Hf Hf'].
        eexists (Eproj_c x' _ n Γ Hole_c). repeat eexists. 
        * eassumption.
        * edestruct Minv3 as [H1 [H2 [H3 H4]]]. now repeat eexists; eauto.
          econstructor 3; eauto.
          eapply Hf. zify; omega.
    - eapply bind_triple.
      + eapply get_name_fresh.  
      + intros x' s. eapply return_triple. intros s' [Hf Hf'].
        edestruct Minv2 as [H1 H2]; eauto. 
        exists (Econstr_c x' clo_tag [v; Γ] Hole_c). repeat eexists.
        * eassumption.
        * replace v with ((subst FVmap) x)
            by (unfold subst; rewrite Hget; reflexivity). 
          econstructor; eauto.
          intros Hc. eapply Minv1 in Hc. congruence.
          eapply H2. repeat eexists; eauto.
          eapply Hf. zify; omega.    
    - eapply return_triple. intros [s d] Hin'.      
      exists Hole_c. repeat eexists. 
      + eassumption. 
      + constructor. eapply Minv1. eauto.
  Qed.
  
  (** Spec for [get_vars] *)
  Lemma get_vars_project_vars_sound Scope Funs c Γ FVs FVmap S xs :
    binding_in_map (FromList xs) FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ
    {{ fun _ t s' =>
         exists C S', 
           fresh S' (next_var s') /\
           let '(xs', f) := t in
           project_vars clo_tag Scope Funs (subst FVmap) c Γ FVs S xs xs' C S' /\
           is_exp_ctx f C }}.
  Proof.
    intros Hb Hfv.
    revert S Hb Hfv. induction xs; intros S Hb Hfv. 
    - eapply return_triple. intros s Hf.
      eexists Hole_c. repeat eexists; eauto.
      constructor.
    - eapply bind_triple.
      + eapply get_var_project_var_sound; eauto.
        intros x Hin. eapply Hb. 
        inv Hin. constructor. eauto.
      + intros [x f] [x1 c1 f1 e1].
        eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_r. intros [Hproj Hctx].
        eapply bind_triple.
        eapply (IHxs S'); eauto.
        intros y Hin. eapply Hb. constructor 2. eassumption.
        intros [xs' f'] [x4 c4 f4 e4]. eapply return_triple.  
        intros s [C' [S'' [Hf' [Hproj' Hctx']]]].
        exists (comp_ctx_f C C'), S''.
        split; [ eassumption |].
        split. now econstructor; eauto.
        intros e. rewrite <- app_ctx_f_fuse. congruence.
  Qed.
  
  Lemma subst_BoundVar_f_eq_subdomain FVmap x S :
    f_eq_subdomain S ((subst FVmap) {x ~> x}) (subst (M.set x BoundVar FVmap)).
  Proof.  
    intros x'. unfold subst, extend. rewrite M.gsspec.
    destruct (Coqlib.peq x' x). now eauto. reflexivity. 
  Qed.

  Lemma subst_BoundVar_f_eq FVmap x :
    f_eq ((subst FVmap) {x ~> x}) (subst (M.set x BoundVar FVmap)).
  Proof.  
    intros x'. unfold subst, extend. rewrite M.gsspec.
    destruct (Coqlib.peq x' x). now eauto. reflexivity. 
  Qed.

  Lemma Disjoint_free_set FVmap Scope Funs FVs S :
    binding_not_in_map S FVmap ->
    FVmap_inv FVmap Scope Funs FVs ->
    Disjoint _ S (Union var Scope
                        (Union var Funs (FromList FVs))).
  Proof.             
    intros Hb [Hinv1 [Hinv2 Hinv3]].
    constructor. intros x Hc. inv Hc. 
    assert (Hdec1 : Decidable Scope).
    { eapply Decidable_Same_set. apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros; congruence. 
      - right. intros; congruence. }
    assert (Hdec2 : Decidable (Setminus _ Funs Scope)).
    { eapply Decidable_Same_set. apply Same_set_sym. eassumption.
      constructor. intros x'. destruct (M.get x' FVmap).
      - destruct v; eauto;
        right; intros [y Hc]; congruence. 
      - right. intros [y Hc]; congruence. }
    destruct Hdec1, Hdec2. destruct (Dec x). 
    - eapply Hinv1 in H1.
      unfold In in H1. rewrite Hb in H1; eauto. congruence.
    - destruct (Dec0 x).
      + eapply Hinv2 in H2. destruct H2 as [y Heq].
        rewrite Hb in Heq; eauto. congruence.
      + inv H0; try contradiction.
        inv H3. eapply H2; constructor; eauto.
        unfold In, FromList in H0.        
        edestruct In_nthN as [N Hnth]; [ eassumption |].
        edestruct Hinv3 as [H' _].
        assert (H3 : ~ Funs x) by (intros Hc; eapply H2; constructor; eauto).
        specialize (H' (conj Hnth (conj H1 H3))). rewrite Hb in H'; congruence.
  Qed.
  
  Lemma binding_not_in_map_antimon (A : Type) (S S' : Ensemble M.elt) (rho : M.t A):
    Included M.elt S' S -> binding_not_in_map S rho -> binding_not_in_map S' rho.
  Proof. 
    intros Hin Hb x Hin'. eauto.
  Qed.

  Lemma binding_not_in_map_set_not_In_S {A} S map x (v : A) :
    binding_not_in_map S map ->
    ~ In _ S x ->
    binding_not_in_map S (M.set x v map). 
  Proof. 
    intros HB Hnin x' Hin.
    rewrite M.gsspec. destruct (Coqlib.peq x' x); subst; try contradiction. 
    eauto. 
  Qed.

  Import MonadNotation.

  Transparent bind ret.

  (** This identity is very useful to make the computation of the IH to appear
      as a subcomputation in the goal *)
  Lemma st_eq_Ecase {S} m1 (m2 : state S (var * (exp -> exp))) y :
    st_eq
      (ys <- m1 ;; 
       ys' <- ret (y :: ys) ;;
       t1 <- m2 ;;
       let '(x, f) := t1 in
       ret (Ecase x ys', f))
      (fe <- (ys <- m1 ;;
             t1 <- m2 ;;
             let '(x, f1) := t1 in    
             ret (Ecase x ys, f1)) ;;
       match fe with
         | (Ecase x ys, f) =>
           ret (Ecase x (y :: ys), f)
         | _ => ret fe
       end).
  Proof.
    unfold pbind, ret.
    intros s. simpl. destruct (runState m1 s).
    destruct (runState m2 s0). destruct p as [x f].
    reflexivity.
  Qed.

  Global Opaque bind ret.

  Global Instance FVmap_inv_Scope_Proper :
    Proper (Logic.eq ==> Same_set var ==> Logic.eq ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq2; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite Heq2.
      intros H. rewrite <- Heq2. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq2; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq2.
      intros H. rewrite Heq2. eapply H3. eassumption. 
  Qed.

  Global Instance FVmap_inv_Funs_Proper :
    Proper (Logic.eq ==> Logic.eq ==> Same_set var ==> Logic.eq ==> iff) FVmap_inv.
  Proof. 
    intros M1 M2 Heq1 S1 S2 Heq2 S3 S4 Heq3 l1 l2 Heq4; subst; split; intros [H1 [H2 H3]].
    - (split; [| split ]); try rewrite <- Heq3; eauto.
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite Heq3.
      intros H. rewrite <- Heq3. eapply H3. eassumption. 
    - (split; [| split ]); try rewrite Heq3; eauto. 
      split. intros [Hnth [Hnin1 Hnin2]]. eapply H3. repeat split; eauto.
      now rewrite <- Heq3.
      intros H. rewrite Heq3. eapply H3. eassumption. 
  Qed.

  Lemma FVmapInv_add_params FVmap xs Scope Funs FVs :
    FVmap_inv FVmap Scope Funs FVs ->
    FVmap_inv (add_params xs FVmap) (Union _ Scope (FromList xs)) Funs FVs. 
  Proof. 
    revert FVmap Scope. induction xs; intros FVmap Scope Hinv.
    - rewrite FromList_nil, Union_Empty_set_neut_r. eauto.
    - rewrite FromList_cons.
      rewrite Union_assoc, Union_commut with (s2 := Singleton M.elt a), <- Union_assoc. 
      eapply FVmap_inv_set_bound; eauto.
  Qed.

  Lemma binding_in_map_add_params S FVmap xs :
    binding_in_map S FVmap ->
    binding_in_map (Union _ S  (FromList xs)) (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb.
    - intros x. rewrite FromList_nil, Union_Empty_set_neut_r. eauto.
    - intros x. rewrite FromList_cons.
      rewrite Union_commut with (s2 := FromList xs), Union_assoc.
      simpl. eapply binding_in_map_set; eauto. 
  Qed.

  Lemma binding_not_in_map_add_params S FVmap xs :
    binding_not_in_map S FVmap ->
    Disjoint _ S (FromList xs) ->
    binding_not_in_map S (add_params xs FVmap).
  Proof.
    revert S FVmap. induction xs; intros S FVmap Hb Hd.
    - eauto.
    - rewrite FromList_cons in Hd.
      eapply binding_not_in_map_set_not_In_S; eauto.
      + eapply IHxs. eassumption.
        constructor. intros x Hc. inv Hc. eapply Hd. now constructor; eauto.
      + intros Hc. eapply Hd. eauto.
  Qed.
  
  Lemma FVmap_inv_empty :
    FVmap_inv (Maps.PTree.empty VarInfo) (Empty_set M.elt) (Empty_set M.elt) [].
  Proof.
    repeat split; (try now intros Hc; inv Hc); (try now intros x Hc; inv Hc). 
    intros x Hx. unfold In in Hx. rewrite M.gempty in Hx. now inv Hx.
    destruct H as [x' Hget]. rewrite M.gempty in Hget. now inv Hget.
    rewrite M.gempty in H. now inv H.
  Qed.
    
  Lemma FVmap_inv_set_free_var FVmap Scope Funs FVs x n:
    FVmap_inv FVmap Scope Funs FVs ->
    N.of_nat (length FVs) = n ->
    ~ In _ Scope x -> ~ In  _ Funs x -> ~ List.In x FVs ->
    FVmap_inv (Maps.PTree.set x (FVar n) FVmap) Scope Funs (FVs ++ [x]). 
  Proof.  
    intros [H1 [H2 H3]] Hlen Hnin1 Hnin2.
    split; [| split ]. 
    - split.
      + intros x' Hin. assert (Hin' := Hin). eapply H1 in Hin.
        destruct (Coqlib.peq x' x).
        subst; contradiction.
        unfold In. now rewrite M.gso; eauto.
      + intros x' Hget. eapply H1. 
        unfold In in Hget. rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        subst; congruence. now eauto.
    - split.
      + intros x' Hin. assert (Hin' := Hin). inv Hin'. 
        eapply H2 in Hin. edestruct Hin as [y Heq].
        destruct (Coqlib.peq x' x).
        subst; contradiction.
        eexists. rewrite M.gso; eauto.
      + intros x' [y Hget]. eapply H2. 
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        subst; congruence.
        now eauto.
    - intros N x'. split.
      + intros [Hnth [Hnin1' Hnin2']].
        destruct (nthN_app FVs [x] N) as [Hn | [Hn Hlen']].
        * destruct (Coqlib.peq x' x); subst.
          exfalso. eapply H. eapply nthN_In. rewrite <- Hnth. now eauto.
          edestruct H3 as [Hget _].
          rewrite M.gso; eauto. eapply Hget. repeat split; eauto.
          rewrite <- Hnth. now eauto.
        * subst. rewrite Hnth in Hn. eapply nthN_is_Some_length in Hnth.
          rewrite app_length in Hnth. simpl length in *.
          destruct (N - N.of_nat (length FVs))%N eqn:Heq; simpl in Hn; try congruence.
          inv Hn. rewrite M.gss; eauto.
          repeat f_equal. zify. omega. 
      + subst. intros Hget.
        rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x).
        * subst. inv Hget. repeat split; eauto.
          rewrite nthN_app_geq. rewrite N.sub_diag. reflexivity. 
          zify; omega. 
        * edestruct H3 as [_ [H1' [H2' H3']]].
          eassumption.
          repeat split; eauto. apply nthN_is_Some_app. eassumption.
  Qed.

  Lemma make_record_cTag_preserves_prop n P :
    {{ fun s => P (next_var s) }} make_record_cTag n {{ fun _ _ s => P (next_var s) }}.
  Proof.
    eapply pre_post_mp_l. eapply bind_triple. eapply get_triple.
    intros [x1 c1 f1 e1] [x2 c2 f2 e2].
    apply pre_post_mp_l. eapply bind_triple. now apply put_triple.
    intros x s. eapply return_triple. intros s' [[H1 H3] H2]; subst. inv H1.
    eassumption.
  Qed.
  
  Lemma make_env_spec fv FVmap_o c Γ_n Γ_o Scope Funs FVs S :
    binding_in_map (FromList (PS.elements fv)) FVmap_o ->
    binding_not_in_map (Union M.elt S (Singleton M.elt Γ_o)) FVmap_o ->
    FVmap_inv FVmap_o Scope Funs FVs ->
    {{ fun s => fresh S (next_var s) }}
      make_env clo_tag fv (Maps.PTree.empty VarInfo) FVmap_o c Γ_n Γ_o 
    {{ fun s t  s' =>
         let '(c', FVmap_n, f) := t in
         exists C S' FVs',
           fresh S' (next_var s') /\
           project_vars clo_tag Scope Funs (subst FVmap_o) c Γ_o FVs S (PS.elements fv) FVs' C S' /\
           is_exp_ctx f (comp_ctx_f C (Econstr_c Γ_n c' FVs' Hole_c)) /\
           binding_in_map (FromList (PS.elements fv)) FVmap_n /\
           binding_not_in_map (Complement _ (FromList (PS.elements fv))) FVmap_n /\
           FVmap_inv FVmap_n (Empty_set _) (Empty_set _) (PS.elements fv)
     }}.
  Proof.
    intros Hb1 Hb2 Minv. unfold make_env.
    destruct ((fix
                 add_fvs (l : list Maps.PTree.elt) (n : N) (map : Maps.PTree.t VarInfo)
                 {struct l} : Maps.PTree.t VarInfo * N :=
                 match l with
                   | [] => (map, n)
                   | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                 end)
                (PS.elements fv) 0%N (Maps.PTree.empty VarInfo)) as [map_new n] eqn:Heq.
    eapply bind_triple.
    - eapply get_vars_project_vars_sound; eauto.
    - intros [xs f] s1.
      eapply pre_existential. intros C1. eapply pre_existential. intros S'.
      eapply pre_curry_r. intros [Hvars Hctx].
      eapply bind_triple. now eapply make_record_cTag_preserves_prop.
      intros tau s2. eapply return_triple.
      intros s3 Hf. do 3 eexists. 
      repeat (split; [ eassumption |]). split.
      + intros e. rewrite Hctx. rewrite <- app_ctx_f_fuse. now f_equal.
      + replace map_new with
        (fst ((fix
                add_fvs (l : list Maps.PTree.elt) (n : N)
                (map : Maps.PTree.t VarInfo) {struct l} :
                Maps.PTree.t VarInfo * N :=
                match l with
                  | [] => (map, n)
                  | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
                end) (PS.elements fv) 0%N (Maps.PTree.empty VarInfo)))
          by (rewrite Heq; eauto).
        clear.
        assert (He : FVmap_inv (Maps.PTree.empty VarInfo)
                               (Empty_set M.elt) (Empty_set M.elt) (@nil PS.elt))
          by apply FVmap_inv_empty.
        assert (Hb : binding_in_map (FromList (@nil PS.elt)) (Maps.PTree.empty VarInfo))
          by (intros x H; inv H).
        assert (Hb' : binding_not_in_map (Complement _ (FromList ((@nil PS.elt))))
                                         (Maps.PTree.empty VarInfo))
          by (intros x H; rewrite Maps.PTree.gempty; reflexivity).
        assert (Hlen : N.of_nat (@length PS.elt []) = 0%N) by eauto.
        assert (Hnin : forall x, List.In x (PS.elements fv) -> ~ List.In x (@nil PS.elt))
          by (intros x H1 H2; inv H2).
        assert (Hdup :  NoDupA eq (PS.elements fv)) by apply PS.elements_spec2w.
        replace (PS.elements fv) with ([] ++ PS.elements fv) at 1 3 6 by reflexivity.
        revert Hlen He Hb Hb' Hnin Hdup. generalize (Maps.PTree.empty VarInfo) as FVmap_i.
        generalize (@nil PS.elt). generalize 0%N. 
        induction (PS.elements fv); intros n vars FVmap_i Hlen Hinv Hb Hb' Hnin Hdup.
        * simpl. rewrite app_nil_r. simpl. eauto.
        * simpl. replace (vars ++ a :: l) with ((vars ++ [a]) ++ l). simpl.
          eapply IHl. rewrite app_length. simpl. zify. omega.
          eapply FVmap_inv_set_free_var. now eauto. eassumption. 
          now intros Hc; inv Hc. now intros Hc; inv Hc. 
          eapply Hnin. constructor. reflexivity.
          intros x H. eapply binding_in_map_set. eassumption.
          rewrite FromList_app, FromList_cons, FromList_nil, Union_Empty_set_neut_r in H.
          eassumption.
          eapply binding_not_in_map_set_not_In_S.
          eapply binding_not_in_map_antimon; [| eassumption ].  
          eapply Complement_antimon. rewrite FromList_app. now apply Included_Union_l.
          intros Hc. eapply Hc.
          rewrite FromList_app, FromList_cons, FromList_nil. now eauto.
          intros x Hin Hc. eapply Hnin.
          now constructor 2; eauto. inv Hdup.
          apply Coqlib.in_app in Hc. inv Hc; eauto. inv H. 
          exfalso. eapply H1. eapply In_InA. eauto. now eapply Pos.eq_equiv. 
          eassumption. now inv H0. now inv Hdup.
          rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma subst_MRFun_f_eq (FVmap : VarInfoMap) (x x' : var) :
    f_eq ((subst FVmap) {x ~> x'}) (subst (M.set x (MRFun x') FVmap)).
  Proof.
    unfold subst. intros y. unfold extend.
    rewrite M.gsspec. destruct (Coqlib.peq y x); eauto.
  Qed.


  Lemma make_full_closure_spec B FVmap_n FVmap_o Γ Scope Funs FVs FVs' S S1 S2 S1' S2' :
    binding_in_map S1 FVmap_o -> 
    binding_in_map S2 FVmap_n ->
    binding_not_in_map S1' FVmap_o -> 
    binding_not_in_map S2' FVmap_n ->
    FVmap_inv FVmap_o Scope Funs FVs ->
    FVmap_inv FVmap_n (Empty_set _) (Empty_set _) FVs' ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B FVmap_n FVmap_o Γ
    {{ fun s t s' =>
         let '(FVmap_n', FVmap_o', f) := t in
         exists C S',
           fresh S' (next_var s') /\
           make_closures clo_tag B S Γ C (subst FVmap_n') S' /\
           is_exp_ctx f C /\
           f_eq_subdomain (Setminus _ Funs (Union _ Scope (name_in_fundefs B)))
                          (subst FVmap_o) (subst FVmap_o') /\
           binding_in_map (Union _ S1 (name_in_fundefs B)) FVmap_o' /\
           binding_in_map (Union _ S2 (name_in_fundefs B)) FVmap_n' /\
           binding_not_in_map (Setminus _ S1' (name_in_fundefs B)) FVmap_o' /\
           binding_not_in_map (Setminus _ S2' (name_in_fundefs B)) FVmap_n' /\
           FVmap_inv FVmap_o' (Union _ (name_in_fundefs B) Scope) Funs FVs /\
           FVmap_inv FVmap_n' (Empty_set _) (name_in_fundefs B) FVs'
     }}.
  Proof with now eauto with Ensembles_DB.
    revert FVmap_n FVmap_o Γ Scope Funs FVs FVs' S S1 S2 S1' S2'.
    induction B;
      intros FVmap_n FVmap_o Γ Scope Funs FVs FVs' S
             S1 S2 S1' S2' Hb1 Hb2 Hb1' Hb2'  Minv_o Minv_n. 
    - eapply bind_triple; [ now apply get_name_fresh |].
      intros x s1. eapply pre_curry_l. intros Hx.
      eapply bind_triple; [ eapply IHB; eassumption |].
      intros [[FVmap_n' FVmap_o'] f'] _.
      eapply pre_existential. intros C. eapply pre_existential. intros S'.
      eapply pre_curry_r.
      intros [Hclo [Hctx [Hfeq [Hbn [Hbo [Hbn' [Hbo' [Minv_o' Minv_n']]]]]]]].
      apply return_triple. 
      intros s3 Hf. do 2 eexists. split. eassumption. 
      split. econstructor. eassumption. eapply Hx. zify; omega.
      rewrite <- subst_MRFun_f_eq. reflexivity.
      split. intros e'. simpl. rewrite Hctx. reflexivity.
      split. rewrite <- subst_BoundVar_f_eq.
      apply f_eq_subdomain_extend_not_In_S_r.
      intros Hc. inv Hc. eapply H0. right. left. now eauto.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
      split.
      eapply binding_in_map_antimon;[| eapply binding_in_map_set; eassumption ]...
      split. simpl.
      eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ]...
      split. eapply binding_not_in_map_set_not_In_S.
      eapply binding_not_in_map_antimon; [| eassumption ]...
      intros Hc. inv Hc. eapply H0. left. now eauto.
      split. eapply binding_not_in_map_set_not_In_S.
      eapply binding_not_in_map_antimon; [| eassumption ]...
      intros Hc. inv Hc. eapply H0. left. now eauto.
      split. simpl. rewrite <- Union_assoc. eapply FVmap_inv_set_bound.
      eassumption.
      simpl. apply FVmap_inv_set_funs. now apply not_In_Empty_set.
      eassumption. 
    - eapply return_triple. intros s Hs. do 2 eexists.
      split. eassumption. split. now constructor.
      split. intros e. reflexivity.
      split. intros x H. reflexivity.
      split. intros x H. eapply Hb1. now rewrite Union_Empty_set_neut_r in H.
      split. intros x H. eapply Hb2. now rewrite Union_Empty_set_neut_r in H.
      split. eapply binding_not_in_map_antimon; [| eassumption ]...
      split. eapply binding_not_in_map_antimon; [| eassumption ]...
      split. rewrite Union_Empty_set_neut_l. eassumption.
      eassumption. 
  Qed.

  (* Rewrite does not exactly works for these two, but they are still useful as lemmas *)
  Global Instance project_var_Proper Scope Funs :
    Proper
      (f_eq_subdomain (Setminus _ Funs Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_var clo_tag Scope Funs).
  Proof. 
    constructor; subst; intros Hproj; inv Hproj; try (now constructor; eauto).
    - rewrite H; now econstructor; eauto.
    - rewrite <- H; now econstructor; eauto.
  Qed.
  
  Global Instance project_vars_Proper Scope Funs :
    Proper
      (f_eq_subdomain (Setminus _ Funs Scope) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
      (project_vars clo_tag Scope Funs).
  Proof. 
      constructor; subst; intros Hproj; induction Hproj; try (now constructor; eauto).
      - econstructor. eapply project_var_Proper; eauto.
        now symmetry. now eauto.
      - econstructor. now eapply project_var_Proper; eauto. now eauto.
  Qed.

  Lemma Closure_conversion_f_eq_subdomain_mut :
    (forall e Scope Funs σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
       Closure_conversion clo_tag Scope Funs σ' c Γ FVs e e' C) /\
    (forall B Funs σ σ' c FVs B'
       (Hinc : Included _ (name_in_fundefs B) Funs)
       (Hcc : Closure_conversion_fundefs clo_tag Funs σ c FVs B B')
       (Hfeq : f_eq_subdomain Funs σ σ'),
       Closure_conversion_fundefs clo_tag Funs σ' c FVs B B').
  Proof with now eauto with Ensembles_DB. 
    eapply exp_def_mutual_ind; intros; inv Hcc.
    - econstructor; try reflexivity.
      rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      inv H11. constructor.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      inv H13. inv H4. simpl in H1; subst. destruct H2 as [C' [e' [Heq Hcc]]].
      constructor. now split; eauto.
      assert (Hcc' : Closure_conversion clo_tag Scope Funs σ' c0 Γ FVs
                                        (Ecase v l)  (Ecase x' l') C).
      { eapply H0. econstructor; eauto. eassumption. }
      now inv Hcc'.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_var_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity. eassumption.
      rewrite <- image_f_eq_subdomain;  eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption. rewrite <- image_f_eq_subdomain; eassumption.
      eassumption. rewrite <- image_f_eq_subdomain; eassumption.
      eassumption. eapply H.
      now apply Included_refl. eassumption. reflexivity.
      eapply H0. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - econstructor; try reflexivity; try eassumption.
      rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
    - econstructor; try reflexivity. rewrite <- image_f_eq_subdomain; eassumption.
      eapply project_vars_Proper; [ symmetry; eassumption | | | | | | | | | ];
      try reflexivity. eassumption.
      eapply H. eassumption. eapply f_eq_subdomain_antimon; [| eassumption ]...
    - rewrite Hfeq. econstructor; try eassumption.
      rewrite <- image_f_eq_subdomain; [| eassumption ]. eassumption.
      eapply H0; [| now eauto | now eauto ].
      eapply Included_trans; [| eassumption ]...
      eapply H. eassumption.
      eapply f_eq_subdomain_antimon; [| eassumption ]...
      eapply Hinc. left. eauto.
    - constructor. 
  Qed.

  Corollary Closure_conversion_f_eq_subdomain :
    forall e Scope Funs σ σ' c FVs Γ e' C
       (Hcc : Closure_conversion clo_tag Scope Funs σ c Γ FVs e e' C)
       (Hfeq : f_eq_subdomain (Setminus _ Funs Scope) σ σ'),
      Closure_conversion clo_tag Scope Funs σ' c Γ FVs e e' C.
  Proof.
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.

  Corollary Closure_conversion_fundefs_f_eq_subdomain :
  (forall B Funs σ σ' c FVs B'
       (Hinc : Included _ (name_in_fundefs B) Funs)
       (Hcc : Closure_conversion_fundefs clo_tag Funs σ c FVs B B')
       (Hfeq : f_eq_subdomain Funs σ σ'),
       Closure_conversion_fundefs clo_tag Funs σ' c FVs B B').
  Proof. 
    now apply Closure_conversion_f_eq_subdomain_mut.
  Qed.
  

  Lemma subst_add_params_f_eq_subdomain S l FVmap :
    Disjoint _ (FromList l) S ->
    f_eq_subdomain S
     (subst (add_params l FVmap)) (subst FVmap).
  Proof.
    intros Hd. induction l.
    - simpl. reflexivity.
    - simpl. rewrite <- subst_BoundVar_f_eq_subdomain.
      eapply f_eq_subdomain_extend_not_In_S_l.
      intros H. eapply Hd. constructor. rewrite FromList_cons.
      now left. eassumption.
      eapply IHl. eapply Disjoint_Included_l; [| eassumption ].
      rewrite FromList_cons. now apply Included_Union_r.
  Qed.

  Global Instance fresh_Proper : Proper (Same_set _ ==> eq ==> iff) fresh.
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; split; intros x H.
    now rewrite <- Hseq; eauto.
    now rewrite Hseq; eauto.
  Qed.
  
  Lemma image_extend_In_S f x x' S :
    In _ S x ->
    Same_set _ (image (f {x ~> x'}) S)
             (Union _ (image f (Setminus _ S (Singleton _ x)))
                    (Singleton _ x')).
  Proof.
    intros HinS. split. 
    - intros y [y' [Hin Heq]]; subst. 
      destruct (Coqlib.peq x y').
      + subst. rewrite extend_gss. eauto.
      + rewrite extend_gso; eauto. left.
        eexists; split; eauto. constructor; eauto.
        intros Hc; inv Hc; congruence.
    - intros y Hin.
      destruct (Coqlib.peq x' y); subst.
      + eexists; split; eauto. rewrite extend_gss; eauto.
      + inv Hin. 
        * destruct H as [y' [Hin Heq]]; subst. inv Hin.
          eexists; split. now eauto. rewrite extend_gso; eauto.
          intros Heq; subst. eauto.
        * inv H. congruence. 
  Qed.

  Lemma bound_var_occurs_free_Fcons_Included v t l e B :
    Included var (Union var (bound_var e) (occurs_free e))
             (Union var (bound_var_fundefs (Fcons v t l e B))
                    (occurs_free_fundefs (Fcons v t l e B))).
  Proof.
    rewrite bound_var_fundefs_Fcons.
    rewrite !Union_assoc,
    Union_commut with (s2 := FromList l), Union_commut with (s2 := bound_var e), <- !Union_assoc.
    apply Included_Union_compat. now apply Included_refl.
    eapply Included_trans. eapply occurs_free_in_fun with (B := Fcons v t l e B).
    econstructor. now eauto. apply Included_Union_compat. now apply Included_refl. 
    simpl. rewrite <- Union_assoc. apply Included_Union_compat. now apply Included_refl. 
    apply Included_Union_compat; [| now apply Included_refl ].
    now eapply name_in_fundefs_bound_var_fundefs.
  Qed.

  Lemma bound_var_occurs_free_fundefs_Fcons_Included v t l e B :
    Included var (Union var (bound_var_fundefs B) (occurs_free_fundefs B))
     (Union var (bound_var_fundefs (Fcons v t l e B))
            (occurs_free_fundefs (Fcons v t l e B))).
  Proof.
    normalize_bound_var. normalize_occurs_free.
    rewrite !Union_assoc, Union_commut with (s2 := bound_var_fundefs B), <- !Union_assoc. 
    apply Included_Union_compat. now apply Included_refl.
    rewrite Union_commut with (s1 := Singleton _ _) , <- !Union_assoc.
    rewrite <- Union_Setminus; eauto with Ensembles_DB typeclass_instances.
  Qed.    



  Lemma bound_var_ctx_app_Ecase_cons_mut :
    (forall C x c e P,
      Same_set _ (bound_var (C |[ Ecase x ((c, e) :: P) ]|))
               (Union _ (bound_var e) (bound_var (C |[ Ecase x P ]|)))) /\
    (forall Cf x c e P,
       Same_set _ (bound_var_fundefs (Cf <[ Ecase x ((c, e) :: P) ]>))
               (Union _ (bound_var e) (bound_var_fundefs (Cf <[ Ecase x P ]>)))).
  Proof. 
    exp_fundefs_ctx_induction IHe IHB; intros;
    simpl; repeat normalize_bound_var;
    try now (try rewrite IHe; try rewrite IHB; eauto 6 with Ensembles_DB).
  Qed.

  Corollary bound_var_ctx_app_Ecase_cons C x c e P :
    Same_set _ (bound_var (C |[ Ecase x ((c, e) :: P) ]|))
             (Union _ (bound_var e) (bound_var (C |[ Ecase x P ]|))).
  Proof.     
    now apply bound_var_ctx_app_Ecase_cons_mut.
  Qed.

  Corollary bound_var_fundefs_ctx_app_Ecase_cons Cf x c e P :
    Same_set _ (bound_var_fundefs (Cf <[ Ecase x ((c, e) :: P) ]>))
             (Union _ (bound_var e) (bound_var_fundefs (Cf <[ Ecase x P ]>))).
  Proof.     
    now apply bound_var_ctx_app_Ecase_cons_mut.
  Qed.

  
  Hint Resolve image_Setminus_extend : functions_BD.

  Lemma exp_closure_conv_Closure_conv_sound :
    (forall e Scope Funs c Γ FVs FVmap S
       (* The invariant the relates [FVmap] and [Scope], [Funs], [FV] *)
       (Minv : FVmap_inv FVmap Scope Funs FVs)
       (* [FVmap] contains all the free variables *)
       (Hbin1 : binding_in_map (occurs_free e) FVmap)
       (* [FVmap] does not contain the variables in [S] or [Γ] *)
       (Hbin2 : binding_not_in_map (Union _ S (Singleton _ Γ)) FVmap)
       (* [S] is disjoint with the free and bound variables of [e] and [Γ] *)
       (HD1 : Disjoint _ S (Union _ (image (subst FVmap) (Setminus _ Funs Scope))
                                  (Union _ (bound_var e)
                                         (Union _ (occurs_free e) (Singleton _ Γ)))))
       (* The current environment argument is fresh *)
       (HD2 : ~ In _ (Union _ (bound_var e) (occurs_free e)) Γ),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            exists C, is_exp_ctx (snd ef) C /\
                 Closure_conversion clo_tag Scope Funs (subst FVmap) c Γ FVs e (fst ef) C /\
                 fresh S (next_var s')
       }}) /\
    (forall B FVmap Funs FVs S c
       (Minv : FVmap_inv FVmap (Empty_set _) Funs FVs)
       (Hbin1 : binding_in_map (Union _ (occurs_free_fundefs B) (name_in_fundefs B)) FVmap)
       (Hbin2 : binding_not_in_map S FVmap)
       (HD1 : Disjoint _ S (Union _ (image (subst FVmap) Funs)
                                  (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))))
       (Hinc : Included _ (name_in_fundefs B) Funs),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>     
            Closure_conversion_fundefs clo_tag Funs (subst FVmap) c FVs B B' /\
            fresh S (next_var s')
       }}).
  Proof with now eauto with Ensembles_DB functions_BD.
    eapply exp_def_mutual_ind; intros; simpl. Opaque exp_closure_conv.
    - eapply bind_triple.
      + eapply get_vars_project_vars_sound; [ | eassumption ].
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_r. intros [Hproj Hctx].
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Econstr_Included.
        * eapply binding_not_in_map_antimon. 
          apply Included_Union_compat.
          eapply project_vars_free_set_Included; now eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * eapply Disjoint_Included_l.
          eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite <- subst_BoundVar_f_eq, (Union_commut (Singleton _ _)), <- Setminus_Union.
          apply Included_Union_compat. now eapply image_Setminus_extend.
          rewrite !Union_assoc. apply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Econstr_Included.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Econstr, occurs_free_Econstr. 
          destruct (Coqlib.peq Γ v); subst. now eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * intros e' s'.
          eapply return_triple. intros s'' [C' [Hctx' [Hcc Hf'']]]; eauto.
          eexists. split. now eapply Hctx. split.
          simpl. rewrite Hctx'. econstructor; [| eassumption |].
          eapply Disjoint_free_set  with (S := S) in  Minv.
          apply Disjoint_sym in Minv. (* hackish way to make hint externs search work *)
          now eauto 15 with Ensembles_DB. 
          eapply binding_not_in_map_antimon; [| eassumption ].
          now apply Included_Union_l.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- subst_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. inv Hc. now eauto. reflexivity.
          eapply fresh_monotonic. now eapply project_vars_free_set_Included; eauto.
          eassumption.
    - eapply bind_triple with (post' := fun _ l i => l = [] /\ fresh S (next_var i)).
      + eapply return_triple; eauto. 
      + intros pats' s2.
        eapply bind_triple.
        * eapply frame_rule. eapply get_var_project_var_sound; eauto.
          intros x Hx. eapply Hbin1. rewrite occurs_free_Ecase_nil. eassumption.
        * intros [x f] s. eapply return_triple.
          intros s' [Heq [C [S' [Hf [Hproj Hctx]]]]]. rewrite Heq.
          eexists. split; eauto. split. econstructor; [| eassumption |].
          eapply Disjoint_free_set in Minv. apply Disjoint_sym in Minv.
          now eauto 15 with Ensembles_DB. 
          eapply binding_not_in_map_antimon; [| eassumption ].
          now apply Included_Union_l.
          now constructor. eapply fresh_monotonic.
          now eapply project_var_free_set_Included; eauto.
          eassumption.
    - setoid_rewrite assoc. eapply bind_triple.
      + eapply H; [ eassumption | | eassumption | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          eapply occurs_free_Ecase_Included. now constructor.
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          rewrite !Union_assoc. apply Included_Union_compat; [| now apply Included_refl ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor. 
        * intros Hc. apply HD2.
          rewrite bound_var_Ecase_cons, occurs_free_Ecase_cons.
          inv Hc; eauto.
      + intros [e' f'] s'. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase.
        eapply pre_existential. intros C. apply pre_curry_l; intros Hctx.
        apply pre_curry_l; intros Hcc. eapply bind_triple.
        eapply H0 with (FVmap := FVmap) (Γ := Γ) (c := c0);
          [ eassumption | | eassumption | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Ecase_cons...
        * eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now apply Included_refl.
          rewrite !Union_assoc. apply Included_Union_compat; [| now apply Included_refl ].
          eapply bound_var_occurs_free_Ecase_cons_Included.
        * intros Hc. apply HD2.
          rewrite bound_var_Ecase_cons, occurs_free_Ecase_cons.
          inv Hc; eauto.
        * intros [e'' f s''].   
          edestruct e''; eapply return_triple; intros s''' [C2 [Hctx2 [Hcc2'  Hf2]]];
          inv Hcc2'. 
          eexists. repeat split. eassumption.
          econstructor ; [ eassumption | eassumption | now constructor; eauto ].
          eassumption.
    - eapply bind_triple.
      + eapply get_var_project_var_sound; [ | eassumption ].
        intros x Hx. inv Hx. eapply Hbin1. eauto.
      + intros [x f] s. eapply pre_existential. intros C.
        eapply pre_existential. intros S'.
        eapply pre_curry_r. intros [Hproj Hctx].
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eproj_Included.
        * eapply binding_not_in_map_antimon.
          apply Included_Union_compat. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc. now eapply HD1; eauto. inv H0; eapply HD2; eauto.
        * eapply Disjoint_Included_l. eapply project_var_free_set_Included; now eauto.
          rewrite <- subst_BoundVar_f_eq, (Union_commut (Singleton _ _)), <- Setminus_Union.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat. now eapply image_Setminus_extend.
          rewrite !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Eproj_Included.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Eproj, occurs_free_Eproj. 
          destruct (Coqlib.peq Γ v); subst. now eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * intros e' s'. eapply return_triple. intros s'' [C' [Hctx' [Hcc Hf'']]].
          eexists. split. now eapply Hctx. split.
          simpl. rewrite Hctx'. econstructor; [| eassumption |].
          eapply Disjoint_free_set in Minv. apply Disjoint_sym in Minv.
          now eauto 15 with Ensembles_DB.
          eapply binding_not_in_map_antimon; [| eassumption ].
          now apply Included_Union_l.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- subst_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. inv Hc. now eauto. reflexivity.
          eapply fresh_monotonic.
          now eapply project_var_free_set_Included; eauto.
          eassumption.
    - eapply bind_triple; [ now eapply get_name_fresh |].
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      eapply bind_triple.
      + eapply make_env_spec. eapply binding_in_map_antimon; [| eassumption ].
        * intros x Hfv. eapply occurs_free_Efun. left.
          eapply fundefs_fv_correct. eassumption. 
        * eapply binding_not_in_map_antimon; [| eassumption ]...
        * eassumption.
      + intros [[c' FVmap'] f] _. eapply pre_existential; intros C1.
        eapply pre_existential; intros S2. eapply pre_existential; intros FVs'.
        eapply pre_curry_r. intros [Hproj [Hctx1 [Hb1 [Hb1' Minv1]]]].
        eapply bind_triple; [ eapply make_full_closure_spec; eassumption |].
        intros [[FVmap_n FVmap_o] f'] s2. eapply pre_existential; intros C2.
        eapply pre_existential; intros S3. eapply pre_curry_r.
        intros [Hmc [Hctx2 [Hfeq [Hb2 [Hb2' [Hb3 [Hb3' [Minv_n Minv_o]]]]]]]].
        eapply bind_triple.
        * eapply H0 with (S := S3) ; [ eassumption | | | | ].
          eapply binding_in_map_antimon; [| eassumption ].
          now apply occurs_free_Efun_Included.
          eapply binding_not_in_map_antimon; [| eassumption ].
          rewrite <- Included_Setminus_Disjoint. 
          eapply Included_Union_compat; [| now apply Included_refl ]. 
          eapply Included_trans. eapply Included_trans.
          now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto.
          now eauto with Ensembles_DB.
          repeat normalize_bound_var_in_ctx. eapply Union_Disjoint_l.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_preserv_r. do 2 apply Included_Union_preserv_l.
          now apply name_in_fundefs_bound_var_fundefs.
          apply Disjoint_sym. eapply Disjoint_Singleton_r. intros Hc. eapply HD2.
          left. left. now apply name_in_fundefs_bound_var_fundefs.
          eapply Disjoint_Included_r; [| eapply Disjoint_Included_l; [| eassumption ] ].
          eapply Included_Union_compat. rewrite Union_commut, <- image_f_eq_subdomain. 
          apply image_monotonic... eassumption.
          rewrite !Union_assoc. eapply Included_Union_compat.
          now apply bound_var_occurs_free_Efun_Included.
          now apply Included_refl.
          eapply Included_trans. eapply Included_trans.
          now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto.
          now apply Setminus_Included.
          intros H'. eapply HD2. now eapply bound_var_occurs_free_Efun_Included.
        * intros [e' f''] s3.
          eapply pre_existential. intros C. eapply pre_curry_l. intros Hctx.
          eapply pre_curry_l. intros Hcc.
          eapply bind_triple.
          eapply H. eassumption.
          eapply binding_in_map_antimon; [| eassumption ].
          rewrite fundefs_fv_correct. now apply Included_refl.
          eapply binding_not_in_map_antimon with (S' := S3); [| eassumption ].
          eapply Included_trans. eapply Included_trans. eapply Included_trans.
          now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto.          
          now apply Setminus_Included.
          intros x H'. constructor. intros Hc.
          eapply HD1. constructor.
          now eauto. do 2 right. left. rewrite occurs_free_Efun.
          left. eapply fundefs_fv_correct. eassumption.
          intros Hc. eapply HD1. constructor. now eauto.
          right. left. rewrite bound_var_Efun. left.
          now apply name_in_fundefs_bound_var_fundefs.
          eapply Union_Disjoint_r.
          apply Disjoint_sym. eapply make_closures_image_Disjoint. eassumption.  
          eapply Disjoint_Included_l_sym.
          now eapply make_closures_free_set_Included; eauto.
          eapply Disjoint_Included_r.
          now eapply project_vars_free_set_Included; eauto.
          eapply Disjoint_Included_r. now eapply Setminus_Included.
          eapply Disjoint_Included_l_sym; [| eassumption ].
          apply Included_Union_preserv_r. rewrite Union_assoc.
          apply Included_Union_preserv_l.
          now apply bound_var_occurs_free_fundefs_Efun_Included.
          now apply Included_refl.
          intros B s4. apply return_triple. intros s5 [Hcc'' Hf'']; eauto.
          eexists.  split. eassumption. 
          split. simpl. rewrite Hctx, Hctx2.
          assert (HD3 :
                    Disjoint M.elt S
                             (Union var (bound_var_fundefs f2)
                                    (Union var Scope
                                           (Union var (image (subst FVmap) (Setminus var Funs Scope))
                                                  (Union var (FromList FVs) (Singleton var Γ)))))).
          { eapply Disjoint_free_set in Minv. eapply Disjoint_sym in Minv.
            repeat normalize_bound_var_in_ctx. now eauto 15 with Ensembles_DB.
            eapply binding_not_in_map_antimon; [| eassumption ]. now apply Included_Union_l. }
          econstructor; [ |  | eassumption | | |  | eassumption | eassumption | ]. 
          now eapply fundefs_fv_correct. now eauto with Ensembles_DB.
          eapply Disjoint_Included_r; [| eassumption ]. 
          eapply Included_Union_compat. now apply name_in_fundefs_bound_var_fundefs.
          now apply Included_refl.
          eapply Hf1. zify; omega.
          eapply Disjoint_Included_l.
          eapply project_vars_free_set_Included; eassumption.
          now eauto 15 with Ensembles_DB. 
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite Union_commut. symmetry. eassumption.
          eapply fresh_monotonic; [ | eassumption ].
          eapply Included_trans. eapply Included_trans.
          now eapply make_closures_free_set_Included; eauto.
          now eapply project_vars_free_set_Included; eauto.
          now apply Setminus_Included.
    - eapply bind_triple.
      + eapply get_var_project_var_sound; [  | eassumption ].
        eapply binding_in_map_antimon; [| eassumption ].
        rewrite occurs_free_Eapp...
      + intros [x f] s1. eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_curry_r. intros [Hvar Hctx1].
        eapply bind_triple.
        * eapply get_vars_project_vars_sound; [ | eassumption ].
          eapply binding_in_map_antimon; [| eassumption ].
          rewrite occurs_free_Eapp...
        * intros [xs f'] s2. eapply pre_existential. intros C2.
          eapply pre_existential. intros S''.
          eapply pre_curry_r. intros [Hvars  Hctx2]. eapply bind_triple.
          eapply get_name_fresh.
          intros x' i. eapply pre_curry_l. intros Hf1.
          eapply bind_triple.
          now eapply get_name_fresh. 
          intros x'' s3. eapply pre_curry_l. intros Hf2. 
          eapply return_triple.
          intros s5 Hf5. simpl. exists (comp_ctx_f C1 C2).
          split. intros e. rewrite <- app_ctx_f_fuse. congruence.
          split; eauto.
          econstructor;
            [ | econstructor; eassumption | eapply Hf1; now apply Pos.le_refl
              | eapply Hf2; now apply Pos.le_refl
              | intros Hc; subst x';  eapply Hf2;
                [ now apply Pos.le_refl | now eauto ]].
          eapply Disjoint_free_set in Minv. apply Disjoint_sym in Minv.
          now eauto 15 with Ensembles_DB.
          eapply binding_not_in_map_antimon; [| eassumption ]...
          eapply fresh_monotonic; [| eassumption ].
          do 2 (eapply Included_trans; [ now apply Setminus_Included |]).
          eapply Included_trans. now eapply project_vars_free_set_Included; eauto.
          eapply Included_trans. now eapply project_var_free_set_Included; eauto.
          now apply Included_refl.
    - eapply bind_triple.
      + eapply get_vars_project_vars_sound; [ | eassumption ].
        intros x Hx. eapply Hbin1. eauto.
      + intros [xs f] s. eapply pre_existential. intros C1.
        eapply pre_existential. intros S'.
        eapply pre_curry_r. intros [Hproj Hctx].
        eapply bind_triple.
        eapply H with (Scope := Union var (Singleton var v) Scope)
                      (S := S')
                      (FVmap := Maps.PTree.set v BoundVar FVmap).
        * eapply FVmap_inv_set_bound. eassumption. 
        * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
          now eapply occurs_free_Eprim_Included.
        * eapply binding_not_in_map_antimon. 
          apply Included_Union_compat.
          eapply project_vars_free_set_Included; now eauto.
          now apply Included_refl.
          eapply binding_not_in_map_set_not_In_S. eassumption.
          intros Hc; inv Hc. now eapply HD1; eauto.
          inv H0; eapply HD2; eauto.
        * eapply Disjoint_Included_l. eapply project_vars_free_set_Included; now eauto.
          eapply Disjoint_Included_r; [| eassumption ].
          apply Included_Union_compat.
          rewrite <- subst_BoundVar_f_eq, Union_commut, <- Setminus_Union.
          now eapply image_Setminus_extend.
          rewrite !Union_assoc.
          apply Included_Union_compat; [| now apply Included_refl ].
          now apply bound_var_occurs_free_Eprim_Included.
        * intros Hc. inv Hc; eapply HD2; eauto.
          rewrite bound_var_Eprim, occurs_free_Eprim. 
          destruct (Coqlib.peq Γ v); subst. now eauto.
          right. right. constructor; eauto. intros Hc; inv Hc. congruence.
        * intros e' s'. eapply return_triple.
          intros s'' [C' [Hctx' [Hcc Hf'']]]; eauto.
          eexists. split. now eapply Hctx. split.
          simpl. rewrite Hctx'. econstructor; [| eassumption |].
          eapply Disjoint_free_set in Minv.
          apply Disjoint_sym in Minv. now eauto 15 with Ensembles_DB.
          eapply binding_not_in_map_antimon; [| eassumption ].
          now apply Included_Union_l.
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          rewrite <- subst_BoundVar_f_eq. apply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. inv Hc. now eauto. reflexivity.
          eapply fresh_monotonic. now eapply project_vars_free_set_Included; eauto.
          eassumption.
    - eapply bind_triple. now apply get_name_fresh.
      intros x s2. apply pre_curry_l. intros Hf1. 
      eapply bind_triple.
      eapply H with (Scope := FromList l) (Funs := Funs) (FVs := FVs)
                                          (S := Setminus _ S (Singleton _ x)).
      + rewrite <- Union_Empty_set_neut_l with (s := FromList l).
        eapply FVmapInv_add_params. eassumption.
      + eapply binding_in_map_antimon; [| eapply binding_in_map_add_params; eassumption ].
        rewrite Union_commut. rewrite Union_commut with (s1 := occurs_free_fundefs _).
        eapply occurs_free_in_fun. constructor. eauto.
      + intros x'. rewrite <- (@Union_Setminus _ _ _ _), Union_commut, Union_Same_set. 
        eapply binding_not_in_map_add_params. eassumption.
        repeat normalize_bound_var_in_ctx...
        apply Singleton_Included. eapply Hf1. zify; omega.
      + rewrite !Union_assoc. apply Disjoint_sym. apply Union_Disjoint_l.
        eapply Disjoint_Included_r_sym. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ]. rewrite <- !Union_assoc.
        apply Included_Union_compat. rewrite image_f_eq_subdomain.
        apply image_monotonic. now apply Setminus_Included. 
        apply subst_add_params_f_eq_subdomain. now eauto with Ensembles_DB.
        now apply bound_var_occurs_free_Fcons_Included.
        now eauto with Ensembles_DB.
      + intros Hc. eapply HD1. inv Hc.
        constructor; [ | now eauto ]; eapply Hf1; zify; omega.
        constructor. eapply Hf1; zify; omega. right.
        eapply occurs_free_in_fun with (B := Fcons v t l e f5) in H1; [| econstructor; now eauto ].
        inv H1; eauto. inv H2; eauto. left.
        now eapply name_in_fundefs_bound_var_fundefs.
      + intros [e' f] s3. apply pre_existential. intros C1.
        eapply pre_curry_l. intros Hctx. eapply pre_curry_l. intros Hcc.
        eapply bind_triple.
        eapply H0 with (S := Setminus _ S (Singleton _ x)); [ eassumption | | | | ].
        * eapply binding_in_map_antimon; [| eassumption ].
          simpl. rewrite Union_assoc. apply Included_Union_compat.
          now apply occurs_free_fundefs_Fcons_Included. now apply Included_refl.
        * eapply binding_not_in_map_antimon. now apply Setminus_Included.
          eassumption.
        * eapply Disjoint_Included_r.
          do 2 (apply Included_Union_compat; [ now apply Included_refl |]).
          now apply (occurs_free_fundefs_Fcons_Included  v t l e f5).
          repeat normalize_bound_var_in_ctx. eauto 15 with Ensembles_DB.           
        * eapply Included_trans; [| eassumption ]. now apply Included_Union_r.
        * intros B' s5.
          assert (Ha: exists v', Maps.PTree.get v FVmap = Some (MRFun v')).
          { destruct Minv as [_ [HM _]]. eapply HM. rewrite Setminus_Empty_set_neut_r.
            eapply Hinc. left; eauto. }
          destruct Ha as [v' Ha']. rewrite Ha'.
          eapply return_triple. intros s6 [Hcc2 Hf]. 
          split; [| eapply fresh_monotonic; [ now apply Setminus_Included | eassumption ]].
          simpl. rewrite Hctx.
          replace v' with ((subst FVmap) v) by (unfold subst; rewrite Ha'; reflexivity).
          econstructor; [| eassumption | eassumption |].
          eapply (Disjoint_Included_l _ _ S).
          intros x' Hx'. eapply Hx'. zify; omega.
          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
          eapply Closure_conversion_f_eq_subdomain. eassumption.
          eapply subst_add_params_f_eq_subdomain...
    - eapply return_triple. intros s Hf.
      split; [| eassumption ]. constructor.
  Qed.

  Transparent exp_closure_conv.

  Lemma get_var_is_exp_ctx  x FVmap c Γ :
    {{ fun s => True }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (exists C, is_exp_ctx f C) 
     }}.
  Proof with now eauto with Ensembles_DB.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply post_trivial.
        intros x' i. apply return_triple.
        intros _ _.
        eexists (Eproj_c x' c n Γ Hole_c).
        intros e. reflexivity.
      + eapply bind_triple. apply post_trivial.
        intros x' i. apply return_triple.
        intros _ _.
        eexists (Econstr_c x' clo_tag [v; Γ] Hole_c).
        intros e'. reflexivity.
      + apply return_triple.
        intros _ _. exists Hole_c. intros ?; reflexivity.
    - apply return_triple.
      intros _ _. exists Hole_c. intros ?; reflexivity.
  Qed.

  Lemma get_vars_is_exp_ctx  xs FVmap c Γ :
    {{ fun s => True }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (exists C, is_exp_ctx f C) 
     }}.
  Proof with now eauto with Ensembles_DB.
    induction xs.
    - apply return_triple. intros _ _.
      exists Hole_c; intros ?; reflexivity. 
    - eapply bind_triple.
      + apply get_var_is_exp_ctx.
      + intros [x f] i. apply pre_post_mp_l.
        eapply bind_triple.
        * apply IHxs.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [C2 Hctx] [C1 Hctx'].
          exists (comp_ctx_f C1 C2). intros e.
          rewrite <- app_ctx_f_fuse. congruence.
  Qed.

  Lemma make_env_is_exp_ctx FVset FVmap FVmap' c Γ Γ' :
    {{ fun s => True }}
      make_env clo_tag FVset FVmap FVmap' c Γ Γ'
    {{ fun s t s' =>
         let '(_, _, f) := t in
         (exists C, is_exp_ctx f C) 
     }}.
  Proof with now eauto with Ensembles_DB.
    unfold make_env.
    destruct
      ((fix add_fvs (l : list Maps.PTree.elt)
            (n : N)
            (map : Maps.PTree.t VarInfo)
            {struct l} :
          Maps.PTree.t VarInfo * N :=
          match l with
            | [] => (map, n)
            | x :: xs =>
              add_fvs xs 
                      (n + 1)%N
                      (Maps.PTree.set x 
                                      (FVar n) map)
          end) (PS.elements FVset) 0%N
               (Maps.PTree.empty VarInfo)).
    eapply bind_triple.
    + apply get_vars_is_exp_ctx.
    + intros [xs f] i. apply pre_post_mp_l.
      eapply bind_triple. apply post_trivial.
      intros. eapply return_triple. intros _ _ [C Hctx]. 
      eexists (comp_ctx_f C (Econstr_c Γ x xs Hole_c)).
      intros e. rewrite <- app_ctx_f_fuse, Hctx.
      reflexivity.
  Qed.

  Lemma pre_post_trivial {A S} (Pre : S -> Prop) (Post : S -> A -> S -> Prop) e :
    (forall i x i', Pre i -> Post i x i') ->
    {{ Pre }} e {{ Post }}.
  Proof.
    unfold triple.
    intros. destruct runState. eauto.
  Qed.


  Lemma exp_closure_conv_is_exp_ctx e c Γ FVmap :
    {{ fun s => True }}
      exp_closure_conv clo_tag e FVmap c Γ
    {{ fun s ef s' =>
         exists C, is_exp_ctx (snd ef) C
     }}.
  Proof.
    destruct e. 
    - eapply bind_triple.
      now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros.
      now eapply return_triple.
    - unfold exp_closure_conv.
      eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.            
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple. now apply make_env_is_exp_ctx.
      intros [[? ?] ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      destruct x0 as [[? ?] ?]. 
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
    - eapply bind_triple. now apply get_var_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple. now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply bind_triple; [ now apply post_trivial | intros].
      eapply return_triple. intros _ _ [C1 H1] [C2 H2]. 
      simpl. eexists (comp_ctx_f C2 C1). intros e'.
      rewrite <- app_ctx_f_fuse. congruence. 
    - eapply bind_triple.
      now apply get_vars_is_exp_ctx.
      intros [? ?]; intros. eapply pre_post_mp_l.
      eapply bind_triple; [ now apply post_trivial | intros].
      now eapply return_triple.
  Qed.

  Lemma get_var_bound_var_Included  x FVmap c Γ S S':
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            (Included _ (bound_var e) (Union _ S' ((Setminus _ S (Singleton _ x')))) ->
             Included _ (bound_var (f e)) (Union _ S' S))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin. rewrite bound_var_Eproj.
        apply Union_Included. eapply Included_trans; [ eassumption |]...
        apply Singleton_Included. right. eapply Hf. zify; omega.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin'. rewrite bound_var_Econstr.
        apply Union_Included. eapply Included_trans; [ eassumption |]...
        apply Singleton_Included. right. eapply Hf. zify; omega.
      + apply return_triple.
        intros i' Hf. split.
        * intros e Hin'. eapply Included_trans; [ eassumption |]...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e Hin'. eapply Included_trans; [ eassumption |]...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_bound_var_Included xs FVmap c Γ S S':
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (FromList xs'))) ->
            Included _ (bound_var (f e)) (Union _ S' S)) /\
           fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof.
    revert S S'; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split;
        intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_bound_var_Included.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * apply IHxs. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs Hf']. split.
          intros e Hin'. eapply Hx. eapply Hxs.
          rewrite FromList_cons in Hin'. rewrite Setminus_Union. eassumption.
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.

  Lemma make_full_closure_bound_var_Included B m1 m2 Γ S :
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Same_set _ (bound_var (f e)) (Union _ (bound_var  e) (name_in_fundefs B))) /\
         Included _ (image (subst m1') (name_in_fundefs B)) S /\
         fresh S (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S. 
    - eapply bind_triple. now apply get_name_fresh.
      intros x s1. apply pre_curry_l. intros Hf1.
      eapply bind_triple. now eapply IHB.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [Hinc [Him Hf]]. split; [| split ].
      + intros e'. rewrite bound_var_Econstr; simpl.
        rewrite Hinc...
      + rewrite <- subst_MRFun_f_eq. rewrite image_extend_In_S.
        simpl. apply Union_Included.
        eapply Included_trans.
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set,
        Union_Empty_set_neut_l.
        apply image_monotonic. now apply Setminus_Included.
        eapply Included_trans. eassumption. now apply Setminus_Included.
        apply Singleton_Included. eapply Hf1. zify; omega.
        now left; eauto.
      + eapply fresh_monotonic; [| eassumption ].
        now apply Setminus_Included.
    - apply return_triple. intros s Hf.
      simpl. split; [ |  split; [| now eauto] ].
      intros e. now rewrite Union_Empty_set_neut_r.
      rewrite image_Empty_set. now apply Included_Empty_set.
  Qed.

  Lemma exp_closure_conv_bound_var_Included_mut :
    (forall e c Γ FVmap S
       (HD: Disjoint _ S (Union _ (bound_var e) (occurs_free e))),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
         {{ fun s ef s' =>
              Included _ (bound_var ((snd ef) (fst ef)))
                       (Union _ (bound_var e) S) /\
              fresh S (next_var s')
          }}) /\
    (forall B FVmap S c
       (HD : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B))),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
         {{ fun s B' s' =>
              Included _ (bound_var_fundefs B')
                       (Union _ (bound_var_fundefs B)
                              (Union _ S (image (subst FVmap) (name_in_fundefs B)))) /\
              fresh S (next_var s')
          }}).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros.
    - eapply bind_triple.
      + eapply get_vars_bound_var_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Econstr...
      + intros [xs f] i. apply pre_curry_l; intros Hf.
        eapply bind_triple. eapply IHe. 
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Econstr_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split.
        simpl in *. eapply Hf. rewrite !bound_var_Econstr.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc. 
        apply Included_Union_compat; [ eassumption | now apply Included_refl].
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple. apply get_var_bound_var_Included.
      intros Hc. eapply HD. now constructor; eauto.
      intros [x f] _. apply return_triple. intros i'.
      intros [He Hf]. split. simpl.
      eapply He. rewrite !bound_var_Ecase_nil.
      now apply Included_Empty_set.
      eapply fresh_monotonic; [| eassumption ]...
    - unfold exp_closure_conv. setoid_rewrite assoc.
      eapply bind_triple.
      + eapply IHe. eapply Disjoint_Included_r; [| eassumption ].
        eapply bound_var_occurs_free_Ecase_Included. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase. eapply pre_curry_l; intros He'.
        eapply bind_triple.
        { eapply post_conj.
          - eapply IHl with (FVmap := FVmap) (Γ := Γ) (c := c0).
            eapply Disjoint_Included_r; [| eassumption ].
            now eapply bound_var_occurs_free_Ecase_cons_Included.
          - eapply pre_strenghtening;
            [ | now eapply exp_closure_conv_is_exp_ctx
                with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap)].
            intros. simpl; eauto. }
        intros [e'' f''] s''.
        destruct e''; apply return_triple;
        try (intros s''' [[Hin Hf] _]; split; eauto;
             eapply Included_trans; [ eassumption |]; normalize_bound_var;
             now eauto with Ensembles_DB).
        intros s''' [[Hin Hf] [C Hctx]]; split; eauto. simpl in *.
        rewrite Hctx. rewrite bound_var_ctx_app_Ecase_cons, bound_var_Ecase_cons.
        apply Union_Included.
        * eapply Included_trans. eassumption. eauto with Ensembles_DB.
        * rewrite <- Hctx. eapply Included_trans. eassumption.
          eauto with Ensembles_DB.
    - eapply bind_triple.
      + eapply get_var_bound_var_Included. intros Hc. eapply HD; eauto.
      + intros [xs f] i. apply pre_curry_l. intros Hf.
        eapply bind_triple.
        apply IHe. 
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eproj_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split. 
        simpl in *. eapply Hf. rewrite !bound_var_Eproj.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc... 
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple. now apply get_name_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      eapply bind_triple with
      (post' :=
         fun _ t s' =>
           let '(_, f) := t in
           (forall e0 : exp,
              Included var (bound_var e0)
                       (Union var (bound_var (Efun f2 e)) S) ->
              Included var (bound_var (f e0))
                       (Union var (bound_var (Efun f2 e)) S)) /\
           fresh (Setminus var S (Singleton var Γ')) (next_var s')).
      + unfold make_env.
        destruct
          ((fix
              add_fvs (l : list Maps.PTree.elt) (n : N) (map : Maps.PTree.t VarInfo)
              {struct l} : Maps.PTree.t VarInfo * N :=
              match l with
                | [] => (map, n)
                | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
              end) _ _ _ ) as [m1' n].
        eapply bind_triple.
        apply get_vars_bound_var_Included with (S' := Union _ (bound_var (Efun f2 e)) S).
        rewrite <- fundefs_fv_correct.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        apply Included_Union_preserv_r. normalize_occurs_free...
        intros [xs f] s2. apply pre_curry_l. intros He. 
        eapply bind_triple. apply make_record_cTag_preserves_prop.
        intros c' s3. apply return_triple. intros s4 Hf. split.
        intros e' He'.
        rewrite <- Union_Same_set with (s6 := S),
                Union_commut with (s6 := S), Union_assoc.
        eapply He. rewrite bound_var_Econstr. 
        apply Union_Included.
        eapply Included_trans; [ eassumption |]...
        apply Included_Union_preserv_l. apply Included_Union_preserv_r.
        apply Singleton_Included. apply Hf1. zify; omega.
        now apply Setminus_Included.
        eapply fresh_monotonic; [| eassumption ]...
      + intros [[c' map'] f] _. apply pre_curry_l.
        intros He. eapply bind_triple.
        now apply make_full_closure_bound_var_Included.
        intros [[map_n map_o] f'] _. apply pre_curry_l.
        intros He'. eapply pre_curry_l. intros Him.
        eapply bind_triple. eapply IHe.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Efun_Included.
        intros [e' f''] s. apply pre_curry_l. intros He''.
        eapply bind_triple. apply IHB.
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_fundefs_Efun_Included.
        intros B' s2. apply return_triple. intros s3 [HB Hf].
        simpl in *. split. 
        eapply He. rewrite !bound_var_Efun.
        apply Union_Included.
        eapply Included_trans. eassumption.
        apply Union_Included. eauto with Ensembles_DB.
        apply Union_Included. eauto with Ensembles_DB.
        eapply Included_trans. eassumption. eauto with Ensembles_DB.
        rewrite <- Union_Same_set with (s5 := (Union _ (Union _ _ _) _)),
                                      Union_commut.
        rewrite He'. apply Union_Included.
        eapply Included_trans. eassumption. apply Union_Included.
        now eauto with Ensembles_DB. now eauto with Ensembles_DB.
        do 3 apply Included_Union_preserv_l.
        now apply name_in_fundefs_bound_var_fundefs.
        eauto with Ensembles_DB.
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      eapply get_var_bound_var_Included.
      intros Hc. now eapply HD; eauto.
      intros [g f] s1. apply pre_curry_l. intros He.
      eapply bind_triple.
      eapply get_vars_bound_var_Included.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      rewrite occurs_free_Eapp...
      intros [xs f'] s2. apply pre_curry_l. intros He'.
      eapply bind_triple. now apply get_name_fresh.
      intros ptr s3. apply pre_curry_l. intros Hf.
      eapply bind_triple. now apply get_name_fresh.
      intros env s4. apply pre_curry_l. intros Hf'.
      apply return_triple. intros s5. intros Hf''.
      simpl in *. split.
      eapply He. eapply He'.
      rewrite !bound_var_Eproj, !bound_var_Eapp, !Union_Empty_set_neut_l.
      apply Union_Included. eapply Singleton_Included.
      eapply Hf'. zify; omega.
      eapply Singleton_Included. eapply Hf. zify; omega.
      eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      + eapply get_vars_bound_var_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite occurs_free_Eprim...
      + intros [xs f] i.
        apply pre_curry_l. intros Hf.
        eapply bind_triple.
        apply IHe. 
        eapply Disjoint_Included_l. now apply Setminus_Included.
        eapply Disjoint_Included_r; [| eassumption ].
        now apply bound_var_occurs_free_Eprim_Included.
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [He' Hf'']. split. 
        simpl in *. eapply Hf. rewrite !bound_var_Eprim.
        rewrite <- Union_assoc, Union_commut with (s2 := Setminus _ _ _), Union_assoc... 
        eapply fresh_monotonic; [| eassumption ]...
    - eapply bind_triple.
      now apply get_name_fresh.
      intros env s1. apply pre_curry_l; intros Hf.
      eapply bind_triple. eapply IHe.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply bound_var_occurs_free_Fcons_Included.
      intros [e' f] s2. apply pre_curry_l. intros He.
      eapply bind_triple. eapply IHB.
      eapply Disjoint_Included_l. now apply Setminus_Included.
      eapply Disjoint_Included_r; [| eassumption ].
      now apply bound_var_occurs_free_fundefs_Fcons_Included.
      intros B s3. eapply return_triple.
      intros s4 [Hin Hf']. split. simpl.
      rewrite !bound_var_fundefs_Fcons.
      apply Union_Included.
      destruct (Maps.PTree.get v FVmap) as [v' | ] eqn:Heq;
        try destruct v'; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r.
      rewrite image_Union, image_Singleton. apply Included_Union_preserv_l.
      unfold subst. rewrite Heq. now eauto.
      apply Union_Included. rewrite FromList_cons.
      apply Union_Included. apply Included_Union_preserv_r.
      apply Included_Union_preserv_l. apply Singleton_Included.
      eapply Hf. zify; omega. now eauto with Ensembles_DB.
      apply Union_Included. eapply Included_trans; [ eassumption |]...
      eauto with Ensembles_DB.
      eapply Included_trans; [ eassumption |].
      apply Union_Included. now eauto with Ensembles_DB.
      apply Union_Included. now eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r. 
      apply image_monotonic. now apply Included_Union_r.
      eapply fresh_monotonic; [|  eassumption ]...
    - apply return_triple. intros. split; eauto.
      now apply Included_Union_l.
  Qed.

  Lemma get_var_bound_var_Included' x FVmap c Γ S :
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (bound_var (f e)) (Union _ (bound_var e) (Singleton _ x'))) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin.
    unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. rewrite bound_var_Eproj...
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e. rewrite bound_var_Econstr...
      + apply return_triple.
        intros i' Hf. split.
        * intros e...
        * intros x' Hleq. constructor. now eauto.
          intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      + intros e...
      + intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_bound_var_Included' xs FVmap c Γ S:
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var (f e)) (Union _ (bound_var e) (FromList xs'))) /\
           fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction xs; intros S Hd.
    - apply return_triple. intros i Hf.
      split.
      intros ?; rewrite !FromList_nil...
      intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_bound_var_Included'.
        intros Hin'. eapply Hd. constructor; eauto.
        rewrite FromList_cons. left; eauto.
      + intros [x f] i. apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * apply IHxs. eapply Disjoint_Included_l.
          now apply Setminus_Included.
          eapply Disjoint_Included_r; [| eassumption ].
          rewrite FromList_cons. now apply Included_Union_r.
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [Hxs Hf']. split.
          intros e. eapply Included_trans. eapply Hx.
          eapply Included_trans. eapply Included_Union_compat. eapply Hxs.
          now apply Included_refl. rewrite FromList_cons...
          rewrite FromList_cons, <- Setminus_Union. eassumption.
  Qed.
  
  Lemma get_var_unique_bindings x FVmap c Γ S S' :
    ~ In _ S x ->
    {{ fun s => fresh S (next_var s) }}
      get_var clo_tag x FVmap c Γ 
    {{ fun s t s' =>
         let (x', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (Singleton _ x'))) ->
            Disjoint _ S' S  ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (Singleton _ x')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    intros Hnin. unfold get_var. destruct (Maps.PTree.get x FVmap) eqn:Heq.
    - destruct v.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin Hd Hun. constructor; [| eassumption ].
        intros Hc. eapply Hd.
        eapply Hin in Hc. inv Hc. constructor. eauto. 
        eapply Hf. zify; omega. inv H. exfalso; eauto.
      + eapply bind_triple. apply get_name_fresh.
        intros x' i. apply return_triple.
        intros i' [Hf Hf']. split; [| eassumption].
        intros e Hin Hd Hun. constructor; [| eassumption ].
        intros Hc. eapply Hd.
        eapply Hin in Hc. inv Hc. constructor. eauto. 
        eapply Hf. zify; omega. inv H. exfalso; eauto.
      + apply return_triple.
        intros i' Hf. split.
        intros e Hin Hd Hun. eassumption. 
        intros x' Hleq. constructor. now eauto.
        intros Hc; inv Hc. now eauto.
    - apply return_triple; simpl. intros i Hf. split.
      intros e Hin Hd Hun. eassumption.
      intros x' Hleq. constructor. now eauto.
      intros Hc; inv Hc. now eauto.
  Qed.

  Lemma get_vars_unique_bindings xs FVmap c Γ S S' :
    Disjoint _ S (FromList xs) ->
    {{ fun s => fresh S (next_var s) }}
      get_vars clo_tag xs FVmap c Γ 
    {{ fun s t s' =>
         let (xs', f) := t in
         (forall e,
            Included _ (bound_var e) (Union _ S' (Setminus _ S (FromList xs'))) ->
            Disjoint _ S' S  ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (FromList xs')) (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S S'; induction xs; intros S S' Hd.
    - apply return_triple. intros i Hf.
      split;
        intros ?; rewrite !FromList_nil, !Setminus_Empty_set_neut_r in *; eauto.
    - eapply bind_triple.
      + apply get_var_unique_bindings;
        intros Hin'; eapply Hd; constructor; eauto;
        rewrite FromList_cons; left; eauto.
      + intros [x f] i.
        apply pre_curry_l. intros Hx.
        eapply bind_triple.
        * rewrite FromList_cons in Hd.
          eapply post_conj;
          [apply get_vars_bound_var_Included | apply IHxs ]...
        * intros [xs' f'] i'. apply return_triple.
          intros i'' [[Hxs1 _] [Hxs2 Hf']]. split.
          intros e Hin' Hd' Hun. eapply Hx.
          eapply Hxs1. eapply Included_trans. eassumption.
          rewrite FromList_cons. apply Included_Union_compat. now apply Included_refl.
          eauto with Ensembles_DB.
          eassumption.
          eapply Hxs2. eapply Included_trans. eassumption.
          apply Included_Union_compat. now apply Included_refl.
          rewrite FromList_cons... eauto with Ensembles_DB.
          eassumption. rewrite FromList_cons, <- Setminus_Union...
  Qed.
  
  Lemma make_full_closure_unique_bindings B m1 m2 Γ S :
    unique_functions B ->
    {{ fun s => fresh S (next_var s) }}
      make_full_closure clo_tag B m1 m2 Γ
    {{ fun s t s' =>
         let '(m1', _, f) := t in
         (forall e,
            Disjoint _ (bound_var e) (bound_var_fundefs B) ->
            unique_bindings e ->
            unique_bindings (f e)) /\
         fresh (Setminus _ S (image (subst m1') (name_in_fundefs B)))
               (next_var s')
     }}.
  Proof with now eauto with Ensembles_DB.
    revert S; induction B; intros S Hun. 
    - eapply bind_triple. now apply get_name_fresh.
      intros x s1. apply pre_curry_l. intros Hf1. inv Hun.
      eapply bind_triple. eapply post_conj. now eapply IHB.
      now apply make_full_closure_bound_var_Included.
      intros [[m1' m2'] f1] _. apply return_triple.
      intros s2 [[Hun Hf] [Heq [Hinc _]]]. split.
      + intros e' Hun1 Hin1. constructor.
        intros Hb. eapply Hun1.
        constructor. apply Heq in Hb. inv Hb; eauto.
        exfalso. now eauto. rewrite bound_var_fundefs_Fcons...
        eapply Hun; eauto.
        rewrite bound_var_fundefs_Fcons in Hun1. 
        eauto with Ensembles_DB.
      + eapply fresh_monotonic; [| eassumption ].
        rewrite <- subst_MRFun_f_eq. simpl.
        rewrite image_extend_In_S.  rewrite Setminus_Union.
        apply Included_Setminus_compat. reflexivity.
        rewrite Union_commut. eapply Included_Union_compat.
        reflexivity. apply image_monotonic...
        now eauto.
    - apply return_triple. intros s Hf.
      simpl. split. now eauto.
      rewrite image_Empty_set, Setminus_Empty_set_neut_r. eassumption.
  Qed.

  Lemma unique_bindings_ctx_app_Ecase_cons_mut :
    (forall C x c e P
       (Hun1 : unique_bindings e)
       (Hun2 : unique_bindings (C |[ Ecase x P ]|))
       (Hd : Disjoint _ (bound_var e) (bound_var (C |[ Ecase x P ]|))),
       unique_bindings (C |[ Ecase x ((c, e) :: P) ]|)) /\
    (forall Cf x c e P
       (Hun1 : unique_bindings e)
       (Hun2 : unique_bindings_fundefs (Cf <[ Ecase x P ]>))
       (Hd : Disjoint _ (bound_var e) (bound_var_fundefs (Cf <[ Ecase x P ]>))),
       unique_bindings_fundefs (Cf <[ Ecase x ((c, e) :: P) ]>)).
  Proof with now eauto with Ensembles_DB. 
    exp_fundefs_ctx_induction IHe IHB; intros; simpl in *;
    try now (inv Hun2; repeat normalize_bound_var_in_ctx;
             constructor; [| now eauto with Ensembles_DB ];
             intros Hc; eapply bound_var_ctx_app_Ecase_cons in Hc;
             (inv Hc; [ | now  eauto ]); eapply Hd; eauto).
    - constructor; eassumption.
    - eapply unique_bindings_Ecase_l in Hun2.
      repeat normalize_bound_var_in_ctx.      
      destruct Hun2 as [Hun1' [Hun2' [Hun3' [Hd1 [Hd2 Hd3]]]]].
      eapply unique_bindings_Ecase_r; try eassumption.
      eapply IHe; eauto with Ensembles_DB.
      rewrite bound_var_ctx_app_Ecase_cons...
      rewrite bound_var_ctx_app_Ecase_cons...
    - inv Hun2; repeat normalize_bound_var_in_ctx.
      constructor. now eauto with Ensembles_DB.
      eassumption. rewrite bound_var_ctx_app_Ecase_cons...
    - inv Hun2; repeat normalize_bound_var_in_ctx.
      constructor. eassumption.
      now eauto with Ensembles_DB.
      rewrite bound_var_fundefs_ctx_app_Ecase_cons...
    - inv Hun2; repeat normalize_bound_var_in_ctx.
      constructor;
        try rewrite bound_var_ctx_app_Ecase_cons; try now eauto with Ensembles_DB.
      intros Hc. eapply bound_var_ctx_app_Ecase_cons in Hc.
      inv Hc; [ | now  eauto ]; eapply Hd; eauto.
    - inv Hun2; repeat normalize_bound_var_in_ctx.
      constructor;
        try rewrite bound_var_fundefs_ctx_app_Ecase_cons; try now eauto with Ensembles_DB.
      intros Hc. eapply bound_var_fundefs_ctx_app_Ecase_cons in Hc.
      inv Hc; [ | now  eauto ]; eapply Hd; eauto.
  Qed.


  Lemma unique_bindings_ctx_app_Ecase_cons :
    (forall C x c e P
       (Hun1 : unique_bindings e)
       (Hun2 : unique_bindings (C |[ Ecase x P ]|))
       (Hd : Disjoint _ (bound_var e) (bound_var (C |[ Ecase x P ]|))),
       unique_bindings (C |[ Ecase x ((c, e) :: P) ]|)).
  Proof.
    now apply unique_bindings_ctx_app_Ecase_cons_mut.
  Qed.


  Lemma fresh_Instersection S1 S2 x :
    fresh S1 x ->
    fresh S2 x ->
    fresh (Intersection _ S1 S2) x.
  Proof.
    intros Hf1 Hf2 x' Hleq. eauto.
  Qed.

  Lemma fresh_Setminus S1 S2 S3 x :
    fresh (Setminus _ S1 S2) x ->
    fresh (Setminus _ S1 S3) x ->
    fresh (Setminus _ S1 (Union _ S2 S3)) x.
  Proof.
    intros Hf1 Hf2 x' Hleq. constructor.
    now eapply Hf1. intros Hc. inv Hc. eapply Hf1 in H; eauto.
    eapply Hf2 in H; eauto.
  Qed.

  Lemma fundefs_closure_conv_in_image_subst_map B map c :
    {{ fun _ => True }}
      fundefs_closure_conv clo_tag B map c
    {{ fun _ B' _ =>
         Same_set _ (name_in_fundefs B') (image (subst map) (name_in_fundefs B)) }}.
  Proof with now eauto with Ensembles_DB.
    induction B.
    - eapply bind_triple. now apply post_trivial.
      intros x s1. eapply bind_triple. now apply post_trivial.
      intros e' s2. eapply bind_triple. now apply IHB.
      intros B' s3. apply return_triple. intros _ Hseq.
      simpl. rewrite image_Union, image_Singleton...
    - apply return_triple. simpl. intros. 
      rewrite image_Empty_set...
  Qed.

  Lemma exp_closure_conv_unique_bindings_mut :
    (forall e c Γ FVmap S
       (HD: Disjoint _ S (Union _ (bound_var e) (occurs_free e)))
       (Hun : unique_bindings e),
       {{ fun s => fresh S (next_var s) }}
         exp_closure_conv clo_tag e FVmap c Γ
       {{ fun s ef s' =>
            unique_bindings ((snd ef) (fst ef)) /\
            fresh (Setminus _ S (bound_var ((snd ef) (fst ef)))) (next_var s')
        }}) /\
    (forall B FVmap S c
       (HD : Disjoint _ S (Union _ (bound_var_fundefs B) (occurs_free_fundefs B)))
       (Hun : unique_bindings_fundefs B),
       {{ fun s => fresh S (next_var s) }}
         fundefs_closure_conv clo_tag B FVmap c
       {{ fun s B' s' =>
          unique_bindings_fundefs B' /\
          fresh (Setminus _ S (bound_var_fundefs B')) (next_var s')
        }}).
  Proof with now eauto with Ensembles_DB.
    exp_defs_induction IHe IHl IHB; intros.
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite occurs_free_Econstr...
      + intros [xs f] i.
        eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]]. 
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin'].
        eapply bind_triple. inv Hun.
        eapply post_conj;
          [ eapply IHe; eauto | eapply exp_closure_conv_bound_var_Included_mut ];
        (eapply Disjoint_Included_l;
         [ now apply Setminus_Included |
           eapply Disjoint_Included_r;
             [ now apply bound_var_occurs_free_Econstr_Included | eassumption ]]).
        intros [e' f'] i'. apply return_triple.
        intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
        simpl in *. inv Hun. eapply Hun'. rewrite bound_var_Econstr.
        apply Union_Included;
          [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx. now eauto with Ensembles_DB.
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Econstr...
        eapply Setminus_Disjoint_preserv... 
    - eapply bind_triple with (post' := fun _ P i =>  P = [] /\  fresh S (next_var i)) .
      now apply return_triple.
      intros P' i. apply pre_curry_l. intros Heq; subst.
      eapply bind_triple.
       eapply post_conj;
        [ eapply get_var_unique_bindings | eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; now constructor; eauto.
       intros [x f] _. apply return_triple. intros i' [[He _] [Hin Hf]].
       split; eauto. simpl. eapply He; try now constructor.
       rewrite bound_var_Ecase_nil... eauto with Ensembles_DB.
       eapply fresh_monotonic; [| eassumption ]. simpl.
       eapply Included_Setminus_compat. reflexivity.
       eapply Included_trans. eapply Hin. rewrite bound_var_Ecase_nil...
    - unfold exp_closure_conv. setoid_rewrite assoc.
      inv Hun. eapply bind_triple.
      + eapply post_conj.
        * eapply IHe. eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor.
          eassumption.
        * eapply exp_closure_conv_bound_var_Included_mut.
          eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_Included. now constructor.
      + intros [e' f'] s'. simpl. setoid_rewrite assoc. simpl.
        setoid_rewrite st_eq_Ecase.
        eapply pre_strenghtening. intros i [[Hun' Hf] [Hin _]]. 
        exact (conj (conj Hun' Hin) Hf).
        eapply pre_curry_l; intros [He' Hin]. 
        eapply bind_triple.
        { eapply post_conj.
          - eapply IHl with (FVmap := FVmap) (Γ := Γ) (c := c0).
            eapply Disjoint_Included_l. now apply Setminus_Included.
            eapply Disjoint_Included_r; [| eassumption ].
            now eapply bound_var_occurs_free_Ecase_cons_Included. 
            eassumption.
          - eapply post_conj.
            + eapply pre_strenghtening;
              [ | now eapply exp_closure_conv_is_exp_ctx
                  with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap)].
              intros. simpl; eauto.
            + eapply exp_closure_conv_bound_var_Included_mut
              with (e := (Ecase v l)) (c := c0) (Γ := Γ) (FVmap := FVmap).
              eapply Disjoint_Included_l. now apply Setminus_Included.
              eapply Disjoint_Included_r; [| eassumption ].
              now eapply bound_var_occurs_free_Ecase_cons_Included. }
        intros [e'' f''] s''. 
        destruct e''; apply return_triple;
        try now (intros ? [[? Hf] [? [? ?]]]; split;
                 [ now eauto | eapply fresh_monotonic; [| now apply Hf ];
                               eauto with Ensembles_DB ]).
        intros s''' [[Hin' Hf'] [[C Hctx] [Hin'' Hf'']]]; split; eauto. simpl in *.
        rewrite Hctx. apply unique_bindings_ctx_app_Ecase_cons.
        eassumption. now rewrite <- Hctx.
        rewrite <- Hctx. eapply Disjoint_Included_r. eassumption.
        eapply Union_Disjoint_r. eapply Disjoint_Included_l. eassumption.
        repeat normalize_bound_var_in_ctx...
        now eauto with Ensembles_DB. 
        simpl in *. rewrite Hctx in *. rewrite bound_var_ctx_app_Ecase_cons.
        rewrite <- Setminus_Union. eassumption.
    - eapply bind_triple.
      + eapply post_conj;
        [ eapply get_var_unique_bindings | eapply get_var_bound_var_Included' ];
        intros Hc; eapply HD; eauto.
      + intros [xs f] i. eapply pre_strenghtening. intros ? [[Hun' _] [Hin Hf]].
        exact (conj (conj Hun' Hin) Hf).
        apply pre_curry_l; intros [Hun' Hin']. inv Hun.
        eapply bind_triple.
        * eapply post_conj.
          eapply IHe. eapply Setminus_Disjoint_preserv.
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_Eproj_Included.
          eassumption.
          eapply exp_closure_conv_bound_var_Included_mut.
          eapply Setminus_Disjoint_preserv.
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_Eproj_Included.
        * intros [e' f'] s'. simpl. apply return_triple.
          intros i''. intros [[Hun'' Hf''] [Hinc _]]. split.
          simpl in *. eapply Hun'. rewrite bound_var_Eproj.
          apply Union_Included;
            [ | apply Included_Union_preserv_l; now apply Included_Union_l ].
        rewrite <- Union_assoc...
        repeat normalize_bound_var_in_ctx...
        constructor; [| eassumption ]. intros Hc. eapply Hinc in Hc.
        inv Hc. now eauto. inv H. eapply HD. constructor. now eauto. now left; eauto.
        eapply fresh_monotonic; [| eassumption ]. simpl in *.
        rewrite Setminus_Union.
        rewrite <- (Setminus_Disjoint (Setminus _ _ _) (Singleton _ v)), Setminus_Union.
        apply Included_Setminus_compat. now eauto with Ensembles_DB.
        eapply Included_trans. eapply Hin'. rewrite bound_var_Eproj...
        eapply Setminus_Disjoint_preserv... 
    - eapply bind_triple. now apply get_name_fresh.
      intros Γ' s1. eapply pre_curry_l. intros Hf1.
      unfold make_env.
      destruct
        ((fix
            add_fvs (l : list Maps.PTree.elt) (n : N) (map : Maps.PTree.t VarInfo)
            {struct l} : Maps.PTree.t VarInfo * N :=
            match l with
              | [] => (map, n)
              | x :: xs => add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
            end) _ _ _ ) as [m1' n].
      setoid_rewrite assoc.
      eapply bind_triple.
      eapply post_conj;
        [ eapply get_vars_unique_bindings | eapply get_vars_bound_var_Included' ];
        eapply Setminus_Disjoint_preserv;
        (eapply Disjoint_Included_r; [| eassumption ]);
        rewrite <- fundefs_fv_correct; rewrite occurs_free_Efun...
      intros [xs f1] s2. eapply pre_strenghtening. intros ? [[Hun1 _] [Hin Hf]].
      exact (conj (conj Hun1 Hin) Hf).
      apply pre_curry_l; intros [Hun1 Hin1]. inv Hun.
      setoid_rewrite assoc.
      eapply bind_triple. now apply make_record_cTag_preserves_prop.
      intros c1 s3.  eapply bind_triple.
      now eapply return_triple with
      (Post := fun s r s' =>
                 fresh (Setminus var (Setminus var S (Singleton var Γ')) (FromList xs))
                       (next_var s') /\
                 r = (c1, m1', fun e0 : exp => f1 (Econstr Γ' c1 xs e0))).
      intros [[c' m] f] s4. eapply pre_curry_r; intros Heq; inv Heq.
      eapply bind_triple.
      eapply post_conj;
        [ eapply make_full_closure_unique_bindings |
          eapply make_full_closure_bound_var_Included ]. admit.
      intros [[m m'] f'] s5. eapply pre_strenghtening.
      intros ? [[Hun2 Hf] [Hseq [Hin2 _]]]. exact (conj (conj Hun2 (conj Hin2 Hseq)) Hf).
      apply pre_curry_l; intros [Hun2 [Hin2 Hseq]].
      eapply bind_triple.
      + eapply post_conj.
         eapply IHe. rewrite Setminus_Union.
         rewrite Setminus_Union.
         eapply Disjoint_Included_l; [ now apply Setminus_Included | ].         
         eapply Disjoint_Included_r; [| eassumption ].
         now eapply bound_var_occurs_free_Efun_Included. eassumption. 
         eapply exp_closure_conv_bound_var_Included_mut. rewrite Setminus_Union.
         rewrite Setminus_Union.
         eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
         eapply Disjoint_Included_r; [| eassumption ].
         now eapply bound_var_occurs_free_Efun_Included.
      + intros [e' f''] s6. eapply pre_strenghtening. intros ? [[Hun3 _] [Hin3 Hf]]. 
        exact (conj (conj Hun3 Hin3) Hf). eapply pre_curry_l. intros [Hun3 Hin3].
        eapply bind_triple.
        * eapply post_conj.
          eapply IHB. rewrite Setminus_Union.
          rewrite Setminus_Union.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_fundefs_Efun_Included. eassumption.
          eapply post_conj.
          eapply exp_closure_conv_bound_var_Included_mut. rewrite Setminus_Union.
          rewrite Setminus_Union.
          eapply Disjoint_Included_l; [ now apply Setminus_Included | ].
          eapply Disjoint_Included_r; [| eassumption ].
          now eapply bound_var_occurs_free_fundefs_Efun_Included.
          eapply pre_strenghtening; [| eapply fundefs_closure_conv_in_image_subst_map ].
          now intros; simpl; eauto. 
        * intros B' s7. apply return_triple.
          intros s8 [[Hun4 Hf'] [[Hinc4 Hf] Hin5]]. simpl in *.
          split. eapply Hun1. repeat normalize_bound_var.
          rewrite Hseq. repeat apply Union_Included.
          eapply Included_trans. eassumption.
          repeat apply Union_Included. eapply Included_Union_preserv_l.
          now eapply (Included_Union_l _ (Union _ (bound_var e) (Singleton _ Γ'))).
          eapply Included_Union_preserv_r... rewrite <- Hin5.
          eapply Included_trans. now eapply name_in_fundefs_bound_var_fundefs.
          eapply Included_trans. eassumption.
          now eauto with Ensembles_DB.
          eapply Included_trans. eassumption.
          now eauto with Ensembles_DB.
          do 2 eapply Included_Union_preserv_l.
          now apply name_in_fundefs_bound_var_fundefs.
          now eauto with Ensembles_DB.
          rewrite Union_assoc. eapply Union_Disjoint_l.
          repeat normalize_bound_var_in_ctx.
          eapply Disjoint_Included_r. now apply Setminus_Included.
          eapply Disjoint_Included_l_sym; [| eassumption ]...
          eapply Disjoint_Setminus_r...
          constructor. intros Hc. eapply bound_var_Efun in Hc. 
          inv Hc. eapply Hinc4 in H. inv H.
          eapply HD with (x := Γ'). constructor. eapply Hf1. zify; omega.
          now repeat normalize_bound_var; eauto. inv H0.
          inv H. inv H0. inv H. now eauto.
          eapply Hin2 in H. inv H. inv H0. now eauto.
          rewrite Hseq in H. inv H. eapply Hin3 in H0.
          inv H0. eapply HD with (x := Γ'). constructor. eapply Hf1. zify; omega.
          now repeat normalize_bound_var; eauto. inv H.
          inv H0. inv H. now eauto.
          eapply HD with (x := Γ'). constructor. eapply Hf1. zify; omega.
          left. rewrite bound_var_Efun. left. now eapply name_in_fundefs_bound_var_fundefs.
          constructor. eapply Hun2. eapply Disjoint_Included_l. eassumption.
          eapply Union_Disjoint_l. eassumption.
          eapply (Disjoint_Included_l _ _ S). now eauto with Ensembles_DB.
          repeat normalize_bound_var_in_ctx...
          eassumption. eassumption.
          rewrite Hseq.
          eapply Disjoint_Included_r.
  Abort.

End CC_correct.