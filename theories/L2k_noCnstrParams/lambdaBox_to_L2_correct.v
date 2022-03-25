From CertiCoq Require Import L3_to_L4_correct.
From CertiCoq.L2k Require Import compile wcbvEval.
From MetaCoq.Erasure Require Import EWcbvEval EAst ESpineView ERemoveParams EEtaExpanded EAstUtils EGlobalEnv.
From MetaCoq.Template Require Import MCList utils.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Global Instance erasable_term : switchterm :=
{|
has_tBox := true
; has_tRel := true
; has_tVar := false
; has_tEvar := false
; has_tLambda := true
; has_tLetIn := true
; has_tApp := true
; has_tConst := true
; has_tConstruct := true
; has_tCase := true
; has_tProj := true
; has_tFix := true
; has_tCoFix := false
|}.

Notation "Σ ⊢ s ▹ t" := (EWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Definition notwrong t := match t with TWrong _ => False | _ => True end.

Local Existing Instance EWcbvEval.target_wcbv_flags.


Lemma instantiate_csubst Σ b0' b1 :
       (term.instantiate (compile Σ b0') 0 (compile Σ b1)) = (compile Σ (ECSubst.csubst b0' 0 b1)).
Proof.
Admitted.
 
Import TermSpineView.

Ltac simp_compile := simp compile; try rewrite <- !compile_equation_1.
Tactic Notation "simp_compile" "in" hyp(H) :=
   simp compile in H; try rewrite <- !compile_equation_1 in H.

Lemma compile_mkApps_nonnil Σ f v :
  ~~ isApp f -> v <> [] ->
  compile Σ (mkApps f v) = match construct_viewc f with 
    | view_construct kn c => 
      let cargs := map (fun x => compile Σ x) v in
      let n := MCOption.option_default (fun '(p, args) => p + args) (EGlobalEnv.lookup_constructor_pars_args Σ kn c) 0 in
      TmkApps (TConstruct kn c (list_terms (firstn n cargs))) (list_terms (skipn n cargs))
    | view_other fn nconstr =>  TmkApps (compile Σ fn) (list_terms (map (fun x => compile Σ x) v))
end.
Proof.
  rewrite compile_equation_1.
  intros napp hv.
  destruct (TermSpineView.view_mkApps (TermSpineView.view (mkApps f v)) napp hv) as [hna [hv' ->]].
  cbn. destruct (construct_viewc f); cbn; simp compile => //; now rewrite map_InP_spec.
Qed.

Lemma compile_mkApps Σ fn args : ~~ isApp fn ->
  compile Σ (mkApps fn args) = match construct_viewc fn with 
  | view_construct kn c =>
    let cargs := map (fun x => compile Σ x) args in
    let n := MCOption.option_default (fun '(p, args) => p + args) (EGlobalEnv.lookup_constructor_pars_args Σ kn c) 0 in
    TmkApps (TConstruct kn c (list_terms (firstn n cargs))) (list_terms (skipn n cargs))
    | view_other fn nconstr =>  TmkApps (compile Σ fn) (list_terms (map (fun x => compile Σ x) args))
  end.
Proof.
  intros napp.
  destruct args using rev_case; simp_eta.
  - destruct construct_viewc. cbn [mkApps map app firstn skipn].
    rewrite firstn_nil skipn_nil. now simp compile. reflexivity.
  - rewrite compile_mkApps_nonnil; eauto. destruct args; cbn; congruence.
Qed.  

Opaque compile.

Lemma lookup_env_LookupDfn_const Σ kn g body :
  lookup_env Σ kn = Some (ConstantDecl g) ->
  g.(cst_body) = Some body ->
  LookupDfn kn (compile_ctx Σ) (compile Σ body).
Proof.
  intros H Hg.
Admitted.

Theorem compile_yields_correct Σ n t :
  program.crctEnv (compile_ctx Σ) ->
  isEtaExp Σ t ->
  wellformed Σ n t ->
  L2k.program.crctTerm (compile_ctx Σ) n (compile Σ t).
Proof.
  funelim (isEtaExp Σ t); simp_eta; simp_compile; cbn [wellformed]; intros Henv Hexp Hwf; rtoProp; try now (econstructor; eauto).
  - eapply Nat.ltb_lt in H0. econstructor; eauto.
  - cbn in Hwf. easy.
  - cbn in H0. easy.
  - destruct lookup_env eqn:E; invs H0.
    destruct g; invs H2. destruct c.
    destruct cst_body eqn:E2. 2: admit.
    econstructor; eauto.
    eapply lookup_env_LookupDfn_const; cbn; eauto. reflexivity.
  - destruct lookup_env eqn:E1; invs H0.
    destruct g eqn:E2; invs H2.
    destruct nth_error eqn:E3; invs H1.
    destruct (nth_error (ind_ctors o) i) eqn:E4; invs H2.
    econstructor; eauto.
    econstructor. econstructor. all: admit.
  - cbn. econstructor. admit. eauto. admit.
  - simp compile. admit.
  - admit.
  - cbn in H0. easy.
  - rewrite compile_mkApps => //. cbn [construct_viewc]. admit.
  - rewrite compile_mkApps => //. rewrite Heq. admit.
Admitted.

Lemma decompose_app_tApp_split :
forall (f a : Extract.E.term) (hd : term) (args : list term),
decompose_app (Extract.E.tApp f a) = (hd, args) ->
f = Extract.E.mkApps hd (remove_last args) /\ a = last args a /\ args <> nil /\ ~~ isApp hd.
Proof.
  intros. split. now eapply EEtaExpanded.decompose_app_tApp_split.
  split. now eapply EEtaExpanded.decompose_app_tApp_split.
  revert H. cbn. assert ([a] <> nil) by congruence. revert H. generalize [a].
  intros. split. induction f in l, H, H0 |- *; invs H0; try congruence.
  eapply IHf1 in H2; eauto. congruence.
  now eapply EAstUtils.decompose_app_rec_notApp in H0.
Qed.

Lemma TmkApps_app t l1 l2 :
  TmkApps t (list_terms (l1 ++ l2)) = TmkApps (TmkApps t (list_terms l1)) (list_terms l2).
Proof.
  induction l1 in t, l2 |- *; cbn; try congruence.
Qed.

Lemma tappend_list_terms l1 l2 :
  list_terms (l1 ++ l2) = tappend (list_terms l1) (list_terms l2).
Proof.
  induction l1; cbn; try congruence.
Qed.

Lemma tappend_WcbvEvals p l1 l2 l1' l2' :
  WcbvEvals p l1 l1'-> WcbvEvals p l2 l2' ->
  WcbvEvals p (tappend l1 l2) (tappend l1' l2').
Proof.
  intros H1 H2. induction H1; cbn; eauto.
Qed.

Theorem compile_correct Σ t v :
  program.crctEnv (compile_ctx Σ) ->
  L2k.program.crctTerm (compile_ctx Σ) 0 (compile Σ t) ->
  Σ ⊢ t ▹ v ->
  WcbvEval (compile_ctx Σ) (compile Σ t) (compile Σ v).
Proof.
  intros Henv Hwrong Heval.
  induction Heval; revert Hwrong; simp compile; (try rewrite <- !compile.compile_equation_1); intros Hwrong; cbn.
  - destruct (EAstUtils.decompose_app (EAst.tApp a t0)) as [hd args] eqn:da.
    rewrite  (EAstUtils.decompose_app_inv da).
    rewrite compile_mkApps => //. eapply (EAstUtils.decompose_app_notApp); eauto.
    admit.
  - revert Hwrong. simp compile. destruct (EAstUtils.decompose_app (EAst.tApp f a)) as [hd args] eqn:da.
    rewrite  (EAstUtils.decompose_app_inv da). simp_compile.
    rewrite compile_mkApps => //. eapply (EAstUtils.decompose_app_notApp); eauto.
    eapply decompose_app_tApp_split in da as (-> & heq & hnil & hnapp).
    destruct (construct_viewc hd) eqn:E.
    + eapply eval_construct in Heval1 as (? & ? & ?).
      solve_discr.
    + rewrite (remove_last_last _ a hnil) -heq map_app.
      rewrite TmkApps_app. cbn. intros Hwrong. invs Hwrong.
      forward IHHeval1. rewrite compile_mkApps => //. rewrite E. eassumption.
      forward IHHeval2. eassumption.
      econstructor.
      * rewrite compile_mkApps in IHHeval1 => //. rewrite E in IHHeval1.
        simp_compile in IHHeval1. eapply IHHeval1.
      * eapply IHHeval2. 
      * unfold term.whBetaStep. rewrite instantiate_csubst. eapply IHHeval3.
        rewrite <- instantiate_csubst. eapply instantiate_preserves_crctTerm. lia.
        eapply WcbvEval_preserves_crctTerm; eauto.
        eapply WcbvEval_preserves_crctTerm in IHHeval1.
        simp_compile in IHHeval1. invs IHHeval1. eassumption.
        eauto. rewrite compile_mkApps => //. now rewrite E.
  - invs Hwrong. econstructor; eauto.
    rewrite instantiate_csubst. eapply IHHeval2. 
    rewrite <- instantiate_csubst.
    eapply instantiate_preserves_crctTerm; eauto.
    eapply WcbvEval_preserves_crctTerm; eauto.
  - invs Hwrong.
    forward IHHeval1. eassumption. econstructor.
    + rewrite compile_mkApps in IHHeval1 => //. cbn [construct_viewc] in IHHeval1.
      eapply IHHeval1; eauto.
    + unfold term.whCaseStep. admit.
    + eapply IHHeval2. unfold ETyping.iota_red. admit.
  - cbn in i. discriminate.
  - admit.
  - admit.
  - admit.
  - exfalso. invs Hwrong. eapply WcbvEval_preserves_crctTerm in H5; eauto.
    rewrite compile_mkApps in H5 => //. cbn [construct_viewc] in H5.
    revert H5. simp_compile. clear. intros H.
    enough (program.crctTerm (compile_ctx Σ) 0 (TWrong "TCofix")) as Hinv by invs Hinv.
    revert H.
    generalize (list_terms (map (fun x : term => compile Σ x) args)), (TWrong "TCofix"). induction t0; cbn; eauto.
    intros. eapply IHt0 in H. now invs H.
  - destruct p as [[]]. simp_compile. unfold compile_unfold_clause_1_clause_10. admit.    
  - econstructor.
    + admit.
    + eapply IHHeval. admit.
  - unfold compile_unfold_clause_1_clause_10. admit.
  - unfold compile_unfold_clause_1_clause_10. admit.
  - revert Hwrong. simp compile. 
    destruct (EAstUtils.decompose_app (EAst.tApp f a)) as [hd args] eqn:da.
    rewrite  (EAstUtils.decompose_app_inv da). simp_compile.
    rewrite compile_mkApps => //. eapply (EAstUtils.decompose_app_notApp); eauto.
    eapply decompose_app_tApp_split in da as (-> & heq & hnil & hnapp).
    
    destruct (construct_viewc hd) eqn:E.
    + eapply eval_construct in Heval1 as (? & ? & ?).
      subst. intros Hwrong. invs Hwrong.
      pose proof (mkApps_app (EAst.tConstruct ind n) x [a']).
      cbn in H. rewrite <- H. clear H.
      rewrite compile_mkApps => //. cbn [construct_viewc].
      rewrite (remove_last_last args a); eauto.
      rewrite !map_app. cbn [map]. econstructor.
      rewrite !tappend_list_terms.
      eapply tappend_WcbvEvals.
      forward IHHeval1. admit.
      rewrite !compile_mkApps in IHHeval1 => //.
      cbn [construct_viewc] in *.
      invs IHHeval1. eapply H0.
      econstructor. rewrite <- heq. eapply IHHeval2.
      rewrite (remove_last_last args a) in H5; eauto.
      rewrite map_app tappend_list_terms in H5.
      admit.
      econstructor.
    + destruct (EAstUtils.decompose_app (EAst.tApp f' a')) as [hd' args'] eqn:da'.
      rewrite  (EAstUtils.decompose_app_inv da'). simp_compile.
      rewrite compile_mkApps => //. eapply (EAstUtils.decompose_app_notApp); eauto.
      eapply decompose_app_tApp_split in da' as (-> & heq' & hnil' & hnapp').

      destruct (construct_viewc hd') eqn:E'.
      * rewrite (remove_last_last _ a hnil) -heq map_app.
        rewrite TmkApps_app. cbn. intros Hwrong. invs Hwrong.
        forward IHHeval1. rewrite compile_mkApps => //. rewrite E. eassumption.
        forward IHHeval2. eassumption.
        rewrite compile_mkApps in IHHeval1 => //. rewrite E in IHHeval1.

        todo "contradictory".
      * rewrite (remove_last_last _ a hnil) -heq map_app.
        rewrite TmkApps_app. cbn. intros Hwrong. invs Hwrong.
        forward IHHeval1. rewrite compile_mkApps => //. rewrite E. eassumption.
        forward IHHeval2. eassumption.
        rewrite (remove_last_last _ a' hnil') -heq' map_app.
        rewrite TmkApps_app. cbn. eapply wAppCong.
        -- rewrite !compile_mkApps in IHHeval1 IHHeval2 => //.
           rewrite E E' in IHHeval1 IHHeval2. eapply IHHeval1.
        -- admit.           
        -- eapply IHHeval2.
  - destruct t0; invs i; simp_compile; try now econstructor.
    revert Hwrong. simp_compile. cbn. easy.
Admitted.