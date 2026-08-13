Require Import ExactBacktranslation.RoundTrip.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.IndexedContexts.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import CompilerIE.Compiler.
Require Import ExactBacktranslation.GlobalEvaluation.
Require Import ExactBacktranslation.NativeBundleInvariant.
Require Import LogRelIE.LemmasIntro.
Require Import StlcIso.TypeSafety.
Require Import StlcIso.CanForm.
Require Import StlcIso.SpecTyping.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.LemmasEvaluation.
Require Import Db.WellScoping.
From Coq Require Import Lia.

(** The exact semantic target for a generated forward cast. Both directions
    are needed so the common Iso term can mediate contextual equivalence
    between its ordinary erasure and the Equi identity. *)
Definition GeneratedCastLR : Prop :=
  forall A B (d : ClosedCastEq A B),
    ValidTy A -> ValidTy B ->
    forall dir n,
      ⟪ pempty ⊩ compile_global_up d ⟦dir,n⟧ equi_identity A
        : embed (tarr A B) ⟫.

Lemma generated_cast_lr_zero {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir,
    ⟪ pempty ⊩ compile_global_up d ⟦dir,0⟧ equi_identity A
      : embed (tarr A B) ⟫.
Proof.
  intros VA VB dir. repeat split.
  - cbn. rewrite !repEmul_embed_leftinv. now apply compile_global_up_typing.
  - cbn. rewrite !isToEq_embed_leftinv.
    now apply equi_identity_heterogeneous_typing.
  - intros w Hw γi γe Henv.
    unfold lev in Hw. assert (w = 0) by lia. subst w. apply termrel_zero.
Qed.

Lemma iso_typing_well_scoped {Γ t T} :
  ⟪ Γ i⊢ t : T ⟫ -> StlcIso.SpecSyntax.wsTm (dom Γ) t.
Proof.
  induction 1; cbn;
    eauto using StlcIso.SpecSyntax.wsTm,
      StlcIso.LemmasTyping.getEvar_wsIx.
Qed.

Lemma equi_typing_well_scoped {Γ t T} :
  ⟪ Γ e⊢ t : T ⟫ -> StlcEqui.SpecSyntax.wsTm (dom Γ) t.
Proof.
  induction 1; cbn;
    eauto using StlcEqui.SpecSyntax.wsTm,
      StlcEqui.LemmasTyping.getEvar_wsIx.
Qed.

Lemma generated_cast_lr_one {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir,
    ⟪ pempty ⊩ compile_global_up d ⟦dir,1⟧ equi_identity A
      : embed (tarr A B) ⟫.
Proof.
  intros VA VB dir. repeat split.
  - cbn. rewrite !repEmul_embed_leftinv. now apply compile_global_up_typing.
  - cbn. rewrite !isToEq_embed_leftinv.
    now apply equi_identity_heterogeneous_typing.
  - intros w Hw γi γe Henv.
    destruct w as [|w]; [apply termrel_zero|].
    unfold lev in Hw. assert (w = 0) by lia. subst w.
    assert (Hti : StlcIso.SpecSyntax.wsTm 0 (compile_global_up d)).
    { exact (iso_typing_well_scoped
        (@compile_global_up_typing empty A B d VA VB)). }
    assert (Hte : StlcEqui.SpecSyntax.wsTm 0 (equi_identity A)).
    { exact (equi_typing_well_scoped
        (@equi_identity_heterogeneous_typing A B d VA VB)). }
    rewrite (wsClosed_invariant Hti γi),
            (wsClosed_invariant Hte γe).
    destruct (compile_global_up_terminates d VA VB)
      as (vf & Hvf & Hef).
    pose proof (StlcIso.TypeSafety.preservation_star Hef ValidEnv_nil
      (@compile_global_up_typing empty A B d VA VB)) as Htvf.
    destruct (StlcIso.CanForm.can_form_tarr Hvf Htvf)
      as (body & -> & Hbody).
    eapply termrel_antired_star_left.
    + exact Hef.
    + apply valrel_in_termrel.
      change (valrel dir 1 (ptarr (embed A) (embed B))
        (StlcIso.SpecSyntax.abs A body)
        (StlcEqui.SpecSyntax.abs A (StlcEqui.SpecSyntax.var 0))).
      replace (StlcIso.SpecSyntax.abs A body) with
        (StlcIso.SpecSyntax.abs (repEmul (embed A)) body)
        by now rewrite repEmul_embed_leftinv.
      replace (StlcEqui.SpecSyntax.abs A (StlcEqui.SpecSyntax.var 0)) with
        (StlcEqui.SpecSyntax.abs (isToEq (embed A))
          (StlcEqui.SpecSyntax.var 0))
        by now rewrite isToEq_embed_leftinv.
      eapply valrel_lambda.
      * now apply ValidTy_implies_ValidPTy_embed.
      * now apply ValidTy_implies_ValidPTy_embed.
      * now rewrite isToEq_embed_leftinv.
      * unfold OfType, OfTypeStlcIso, OfTypeStlcEqui.
        cbn. rewrite !repEmul_embed_leftinv, !isToEq_embed_leftinv.
        repeat split; try exact I.
        -- exact Htvf.
        -- now apply equi_identity_heterogeneous_typing.
      * rewrite isToEq_embed_leftinv. now apply tyeq_refl.
      * intros w' vs vu Hw' Hsize Hvr.
        assert (w' = 0) by lia. subst w'. apply termrel_zero.
Qed.

Theorem generated_cast_lr_all_worlds {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir n,
    ⟪ pempty ⊩ compile_global_up d ⟦dir,n⟧ equi_identity A
      : embed (tarr A B) ⟫.
Proof.
  intros VA VB dir n. repeat split.
  - cbn. rewrite !repEmul_embed_leftinv.
    now apply compile_global_up_typing.
  - cbn. rewrite !isToEq_embed_leftinv.
    now apply equi_identity_heterogeneous_typing.
  - intros w Hw gamma_i gamma_e Henv.
    assert (Hti : StlcIso.SpecSyntax.wsTm 0 (compile_global_up d)).
    { exact (iso_typing_well_scoped
        (@compile_global_up_typing empty A B d VA VB)). }
    assert (Hte : StlcEqui.SpecSyntax.wsTm 0 (equi_identity A)).
    { exact (equi_typing_well_scoped
        (@equi_identity_heterogeneous_typing A B d VA VB)). }
    rewrite (wsClosed_invariant Hti gamma_i),
            (wsClosed_invariant Hte gamma_e).
    destruct (compile_global_up_function_shape d VA VB)
      as (body & Hshape).
    assert (Habsty : StlcIso.SpecTyping.Typing empty
      (StlcIso.SpecSyntax.abs A body) (tarr A B)).
    { eapply StlcIso.TypeSafety.preservation_star; eauto using ValidEnv_nil.
      now apply compile_global_up_typing. }
    assert (Hof : OfType (ptarr (embed A) (embed B))
      (I.abs (repEmul (embed A)) body)
      (E.abs A (E.var 0))).
    { rewrite repEmul_embed_leftinv. unfold OfType.
      split.
      - split; [exact I|].
        cbn. rewrite !repEmul_embed_leftinv. exact Habsty.
      - split; [exact I|].
        cbn. rewrite !isToEq_embed_leftinv.
        now apply equi_identity_heterogeneous_typing. }
    assert (Hlambda : valrel dir w (ptarr (embed A) (embed B))
      (I.abs (repEmul (embed A)) body)
      (E.abs A (E.var 0))).
    { eapply native_valrel_lambda_from_oftype; [exact Hof|].
      intros w' vi ve Hw' Hsize Harg.
      destruct (compile_global_pair_native_action d VA VB
        dir w' vi ve Harg) as (vo & Hvo & Happ & Hout).
      assert (Hprefix : StlcIso.SpecEvaluation.evalStar
        (I.app (compile_global_up d) vi)
        (I.app (I.abs A body) vi)).
      { exact (StlcIso.LemmasEvaluation.evalstar_ctx
          (I.papp₁ I.phole vi) I Hshape). }
      assert (Happabs : StlcIso.SpecEvaluation.evalStar
        (I.app (I.abs A body) vi) vo).
      { eapply StlcIso.LemmasEvaluation.determinacyStar;
          eauto using StlcIso.LemmasEvaluation.values_are_normal. }
      assert (Hbeta : StlcIso.SpecEvaluation.eval
        (I.app (I.abs A body) vi) (body[beta1 vi])).
      { apply StlcIso.SpecEvaluation.eval_eval₀.
        apply StlcIso.SpecEvaluation.eval_beta.
        exact (proj1 (valrel_implies_Value Harg)). }
      assert (Hbody : StlcIso.SpecEvaluation.evalStar
        (body[beta1 vi]) vo).
      { eapply StlcIso.LemmasEvaluation.determinacyStar1;
          eauto using StlcIso.LemmasEvaluation.values_are_normal. }
      cbn. eapply termrel_antired_star_left; [exact Hbody|].
      now apply valrel_in_termrel. }
    rewrite repEmul_embed_leftinv in Hlambda.
    eapply termrel_antired_star_left; [exact Hshape|].
    now apply valrel_in_termrel.
Qed.

Theorem generated_cast_lr : GeneratedCastLR.
Proof.
  intros A B d VA VB dir n.
  now apply generated_cast_lr_all_worlds.
Qed.

Theorem generated_down_cast_lr_all_worlds {A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir n,
    ⟪ pempty ⊩ compile_global_down d ⟦dir,n⟧ equi_identity B
      : embed (tarr B A) ⟫.
Proof.
  intros VA VB dir n. repeat split.
  - cbn. rewrite !repEmul_embed_leftinv.
    now apply compile_global_down_typing.
  - cbn. rewrite !isToEq_embed_leftinv.
    now apply equi_identity_reverse_heterogeneous_typing.
  - intros w Hw gamma_i gamma_e Henv.
    assert (Hti : StlcIso.SpecSyntax.wsTm 0 (compile_global_down d)).
    { exact (iso_typing_well_scoped
        (@compile_global_down_typing empty A B d VA VB)). }
    assert (Hte : StlcEqui.SpecSyntax.wsTm 0 (equi_identity B)).
    { exact (equi_typing_well_scoped
        (@equi_identity_reverse_heterogeneous_typing A B d VA VB)). }
    rewrite (wsClosed_invariant Hti gamma_i),
            (wsClosed_invariant Hte gamma_e).
    destruct (compile_global_down_function_shape d VA VB)
      as (body & Hshape).
    assert (Habsty : StlcIso.SpecTyping.Typing empty
      (StlcIso.SpecSyntax.abs B body) (tarr B A)).
    { eapply StlcIso.TypeSafety.preservation_star; eauto using ValidEnv_nil.
      now apply compile_global_down_typing. }
    assert (Hof : OfType (ptarr (embed B) (embed A))
      (I.abs (repEmul (embed B)) body)
      (E.abs B (E.var 0))).
    { rewrite repEmul_embed_leftinv. unfold OfType.
      split.
      - split; [exact I|].
        cbn. rewrite !repEmul_embed_leftinv. exact Habsty.
      - split; [exact I|].
        cbn. rewrite !isToEq_embed_leftinv.
        now apply equi_identity_reverse_heterogeneous_typing. }
    assert (Hlambda : valrel dir w (ptarr (embed B) (embed A))
      (I.abs (repEmul (embed B)) body)
      (E.abs B (E.var 0))).
    { eapply native_valrel_lambda_from_oftype; [exact Hof|].
      intros w' vi ve Hw' Hsize Harg.
      destruct (compile_global_pair_native_reverse_action d VA VB
        dir w' vi ve Harg) as (vo & Hvo & Happ & Hout).
      assert (Hprefix : StlcIso.SpecEvaluation.evalStar
        (I.app (compile_global_down d) vi)
        (I.app (I.abs B body) vi)).
      { exact (StlcIso.LemmasEvaluation.evalstar_ctx
          (I.papp₁ I.phole vi) I Hshape). }
      assert (Happabs : StlcIso.SpecEvaluation.evalStar
        (I.app (I.abs B body) vi) vo).
      { eapply StlcIso.LemmasEvaluation.determinacyStar;
          eauto using StlcIso.LemmasEvaluation.values_are_normal. }
      assert (Hbeta : StlcIso.SpecEvaluation.eval
        (I.app (I.abs B body) vi) (body[beta1 vi])).
      { apply StlcIso.SpecEvaluation.eval_eval₀.
        apply StlcIso.SpecEvaluation.eval_beta.
        exact (proj1 (valrel_implies_Value Harg)). }
      assert (Hbody : StlcIso.SpecEvaluation.evalStar
        (body[beta1 vi]) vo).
      { eapply StlcIso.LemmasEvaluation.determinacyStar1;
          eauto using StlcIso.LemmasEvaluation.values_are_normal. }
      cbn. eapply termrel_antired_star_left; [exact Hbody|].
      now apply valrel_in_termrel. }
    rewrite repEmul_embed_leftinv in Hlambda.
    eapply termrel_antired_star_left; [exact Hshape|].
    now apply valrel_in_termrel.
Qed.

Lemma closed_openlrn_weaken {Gamma ts tu T dir n} :
  StlcIso.SpecSyntax.wsTm 0 ts ->
  StlcEqui.SpecSyntax.wsTm 0 tu ->
  ⟪pempty ⊩ ts ⟦dir,n⟧ tu : T⟫ ->
  ⟪Gamma ⊩ ts ⟦dir,n⟧ tu : T⟫.
Proof.
  intros Hsi Hse (Hti & Hte & Hrel). repeat split.
  - rewrite <- (ap_id I.Tm I.Tm ts).
    eapply StlcIso.LemmasTyping.typing_sub; eauto using
      StlcIso.LemmasTyping.wtSub_closed.
  - rewrite <- (ap_id E.Tm E.Tm tu).
    eapply StlcEqui.LemmasTyping.typing_sub; eauto using
      StlcEqui.LemmasTyping.wtSub_closed.
  - intros w Hw gamma_i gamma_e Henv.
    rewrite (wsClosed_invariant Hsi gamma_i),
            (wsClosed_invariant Hse gamma_e).
    specialize (Hrel w Hw (idm I.Tm) (idm E.Tm) envrel_triv).
    now rewrite !ap_id in Hrel.
Qed.

Lemma generated_cast_lr_in_context {Gamma A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B -> forall dir n,
    ⟪Gamma ⊩ compile_global_up d ⟦dir,n⟧ equi_identity A
      : embed (tarr A B)⟫.
Proof.
  intros VA VB dir n.
  eapply closed_openlrn_weaken.
  - exact (iso_typing_well_scoped
      (@compile_global_up_typing empty A B d VA VB)).
  - exact (equi_typing_well_scoped
      (@equi_identity_heterogeneous_typing A B d VA VB)).
  - now apply generated_cast_lr_all_worlds.
Qed.

Lemma indexed_typing_valid {Gamma t A} :
  ValidEnv Gamma -> ⟪Gamma ic⊢ t : A⟫ -> ValidTy A.
Proof.
  intros VG Ht.
  eapply StlcIso.LemmasTyping.typed_terms_are_valid;
    eauto using compile_indexed_typing.
Qed.

(** Fundamental theorem for the exact compiler.  At a conversion, the
    term-level bundle theorem consumes the induction hypothesis directly;
    hence the generated application has precisely the source computation's
    CBV behavior, including divergence. *)
Theorem compile_indexed_correct {Gamma t A} :
  ValidEnv Gamma -> ⟪Gamma ic⊢ t : A⟫ ->
  forall dir n,
    ⟪embedCtx Gamma ⊩ compile_indexed t ⟦dir,n⟧
      erase_indexed_raw t : embed A⟫.
Proof.
  intros VG Ht. induction Ht; intros dir n; cbn [erase_indexed_raw].
  - eapply compat_var. now apply embedCtx_works.
  - eapply compat_lambda_embed'.
    + now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
    + exact H.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      match goal with
      | Hbody : ICTyping _ _ _ |- _ =>
          exact (indexed_typing_valid
            (RecTypes.ValidTy.ValidEnv_cons VG H) Hbody)
      end.
    + apply IHHt. now apply RecTypes.ValidTy.ValidEnv_cons.
  - eapply (compat_app (τ₁ := embed A) (τ₂ := embed B)).
    + now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      exact (indexed_typing_valid VG Ht2).
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      exact (indexed_typing_valid VG (@IC_WtApp Γ A B f x Ht1 Ht2)).
    + now apply IHHt1.
    + now apply IHHt2.
  - apply compat_unit.
  - apply compat_true.
  - apply compat_false.
  - eapply compat_ite.
    + now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
    + now apply IHHt1.
    + now apply IHHt2.
    + now apply IHHt3.
  - eapply compat_pair.
    + now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      eapply indexed_typing_valid; eauto.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      eapply indexed_typing_valid; eauto.
    + now apply IHHt1.
    + now apply IHHt2.
  - pose proof (indexed_typing_valid VG Ht) as VP.
    apply ValidTy_invert_prod in VP as [VA VB].
    eapply (compat_proj₁ (τ₁ := embed A) (τ₂ := embed B)).
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      exact VA.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      exact VB.
    + now apply IHHt.
  - pose proof (indexed_typing_valid VG Ht) as VP.
    apply ValidTy_invert_prod in VP as [VA VB].
    eapply (compat_proj₂ (τ₁ := embed A) (τ₂ := embed B)).
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      exact VA.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      exact VB.
    + now apply IHHt.
  - eapply compat_inl.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      eapply indexed_typing_valid; eauto.
    + now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
    + now apply IHHt.
  - eapply compat_inr.
    + now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      eapply indexed_typing_valid; eauto.
    + now apply IHHt.
  - eapply (compat_caseof
      (τ₁ := embed A) (τ₂ := embed B) (τ := embed C)).
    + now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
    + now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
    + now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
    + now apply IHHt1.
    + apply IHHt2. now apply RecTypes.ValidTy.ValidEnv_cons.
    + apply IHHt3. now apply RecTypes.ValidTy.ValidEnv_cons.
  - eapply compat_seq.
    + now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
    + apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      eapply indexed_typing_valid; eauto.
    + now apply IHHt1.
    + now apply IHHt2.
  - repeat split.
    + rewrite repEmulCtx_embedCtx_leftinv, repEmul_embed_leftinv.
      exact (compile_indexed_typing
        (@IC_WtCoerce Γ A B d x H H0 Ht)).
    + rewrite isToEqCtx_embedCtx_leftinv, isToEq_embed_leftinv.
      exact (erase_indexed_raw_typing
        (@IC_WtCoerce Γ A B d x H H0 Ht)).
    + intros w Hw gamma_i gamma_e Henv.
      cbn.
      replace (StlcIso.SpecSyntax.apTm gamma_i (compile_global_pair d))
        with (compile_global_pair d).
      2:{ symmetry. exact (wsClosed_invariant
            (iso_typing_well_scoped
              (@compile_global_pair_typing empty A B d H H0)) gamma_i). }
      eapply compile_global_up_native_termrel; [exact H|exact H0|].
      exact (proj2 (proj2 (IHHt VG dir n)) w Hw gamma_i gamma_e Henv).
Qed.

Lemma erased_cast_lr {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir n,
    ⟪ pempty ⊩ compile_global_up d ⟦dir,n⟧
        CompilerIE.Compiler.compie (compile_global_up d)
      : embed (tarr A B) ⟫.
Proof.
  intros VA VB dir n.
  change (OpenLRN dir n (embedCtx empty) (compile_global_up d)
    (CompilerIE.Compiler.compie (compile_global_up d))
    (embed (tarr A B))).
  apply CompilerIE.Compiler.compie_correct.
  - eauto with tyvalid.
  - now apply ValidTy_arr.
  - now apply compile_global_up_typing.
Qed.

Lemma erased_down_cast_lr {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir n,
    ⟪ pempty ⊩ compile_global_down d ⟦dir,n⟧
        CompilerIE.Compiler.compie (compile_global_down d)
      : embed (tarr B A) ⟫.
Proof.
  intros VA VB dir n.
  change (OpenLRN dir n (embedCtx empty) (compile_global_down d)
    (CompilerIE.Compiler.compie (compile_global_down d))
    (embed (tarr B A))).
  apply CompilerIE.Compiler.compie_correct.
  - exact ValidEnv_nil.
  - now apply ValidTy_arr.
  - now apply compile_global_down_typing.
Qed.

(** At world zero, the erased cast and identity share the same typed Iso
    mediator without inspecting values.  [generated_cast_lr_all_worlds]
    supplies the corresponding property at every successor world. *)
Corollary erased_cast_and_identity_share_zero_mediator {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B -> forall dir,
    ⟪ pempty ⊩ compile_global_up d ⟦dir,0⟧
        CompilerIE.Compiler.compie (compile_global_up d)
      : embed (tarr A B) ⟫ /\
    ⟪ pempty ⊩ compile_global_up d ⟦dir,0⟧ equi_identity A
      : embed (tarr A B) ⟫.
Proof.
  intros VA VB dir. split.
  - now apply erased_cast_lr.
  - now apply generated_cast_lr_zero.
Qed.
