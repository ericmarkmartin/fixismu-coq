Require Import ExactBacktranslation.SemanticBridge.
Require Import ExactBacktranslation.EquiContextFrontend.
Require Import ExactBacktranslation.IndexedContexts.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import LogRelIE.LemmasPseudoType.
Require Import RecTypes.ValidTy.
Require Import CompilerIE.Compiler.
Require Import ExactBacktranslation.NativeBundleInvariant.
Require Import Db.WellScoping.
From Coq Require Import Lia.

Local Ltac crush :=
  cbn in * |- ;
  repeat
    (cbn;
     repeat crushLRMatch2;
     try assumption;
     crushOfType;
     CompilerIE.Compiler.I.crushTyping;
     CompilerIE.Compiler.E.crushTyping;
     repeat crushValidPTyMatch;
     repeat crushValidTyMatch2;
     repeat crushRepEmulEmbed;
     repeat CompilerIE.Compiler.I.crushStlcSyntaxMatchH;
     repeat CompilerIE.Compiler.E.crushStlcSyntaxMatchH;
     subst); try lia; auto.

Lemma indexed_context_result_valid {Gamma0 A0 Gamma C A} :
  ValidEnv Gamma0 -> ValidTy A0 -> ValidEnv Gamma ->
  ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ -> ValidTy A.
Proof.
  intros VG0 VA0 VG HC. induction HC;
    eauto using indexed_typing_valid, ValidTy_arr, ValidTy_prod, ValidTy_sum,
      RecTypes.ValidTy.ValidEnv_cons.
  all: crushValidTy.
Qed.

Lemma compile_indexed_correct' {Gamma t A P dir n} :
  ValidEnv Gamma -> IndexedCompiler.ICTyping Gamma t A -> P = embed A ->
  ⟪embedCtx Gamma ⊩ IndexedCompiler.compile_indexed t ⟦dir,n⟧
      RoundTrip.erase_indexed_raw t : P⟫.
Proof. intros VG Ht ->. now apply compile_indexed_correct. Qed.

(** The exact structural context compiler satisfies the same logical relation
    as the term compiler.  Its syntax contains no observation index: its only
    additional terms are the ordinary generated Iso coercions at source
    conversion nodes. *)
Theorem compile_indexed_context_correct {Gamma0 A0 Gamma C A} :
  ValidEnv Gamma0 -> ValidEnv Gamma ->
  ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
  forall dir n,
  ⟪ ⊩ compile_indexed_context C ⟦dir,n⟧ erase_indexed_context_raw C
      : embedCtx Gamma0, embed A0 → embedCtx Gamma, embed A⟫.
Proof.
  intros VG0 VG HC dir n. unfold OpenLRCtxN. split; [|split].
  - cbn. rewrite !repEmulCtx_embedCtx_leftinv, !repEmul_embed_leftinv.
    now apply compile_indexed_context_typing.
  - cbn. rewrite !isToEqCtx_embedCtx_leftinv, !isToEq_embed_leftinv.
    unfold erase_indexed_context_raw.
    now apply StlcEqui.SpecAnnot.eraseAnnot_pctxT,
      erase_indexed_context_typing.
  - intros hole_i hole_e Hrel.
    assert (VA0 : ValidTy A0).
    { eapply StlcIso.LemmasTyping.typed_terms_are_valid; [exact VG0|].
      pose proof (proj1 Hrel) as Htyped.
      rewrite repEmulCtx_embedCtx_leftinv,
        repEmul_embed_leftinv in Htyped.
      exact Htyped. }
    induction HC; cbn.
    + exact Hrel.
    + eapply compat_lambda_embed'.
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * exact H.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        eapply indexed_context_result_valid.
        -- exact VG0.
        -- exact VA0.
        -- exact (RecTypes.ValidTy.ValidEnv_cons VG H).
        -- exact HC.
      * apply IHHC. exact (RecTypes.ValidTy.ValidEnv_cons VG H).
    + eapply (compat_app (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        eapply indexed_typing_valid; eauto.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply IHHC.
      * exact (compile_indexed_correct VG H0 dir n).
    + eapply (compat_app (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * exact (compile_indexed_correct VG H1 dir n).
      * now apply IHHC.
    + eapply compat_ite; crush;
        eapply compile_indexed_correct'; crush.
    + eapply compat_ite; crush;
        eapply compile_indexed_correct'; crush.
    + eapply compat_ite; crush;
        eapply compile_indexed_correct'; crush.
    + eapply (compat_pair (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        exact (indexed_context_result_valid VG0 VA0 VG HC).
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        eapply indexed_typing_valid; eauto.
      * now apply IHHC.
      * exact (compile_indexed_correct VG H dir n).
    + eapply (compat_pair (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        eapply indexed_typing_valid; eauto.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        exact (indexed_context_result_valid VG0 VA0 VG HC).
      * exact (compile_indexed_correct VG H dir n).
      * now apply IHHC.
    + destruct (ValidTy_invert_prod H) as [VA VB].
      eapply (compat_proj₁ (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply IHHC.
    + destruct (ValidTy_invert_prod H) as [VA VB].
      eapply (compat_proj₂ (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply IHHC.
    + eapply (compat_inl (τ₁ := embed A) (τ₂ := embed B)).
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        exact (indexed_context_result_valid VG0 VA0 VG HC).
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply IHHC.
    + eapply (compat_inr (τ₁ := embed A) (τ₂ := embed B)).
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        exact (indexed_context_result_valid VG0 VA0 VG HC).
      * now apply IHHC.
    + eapply (compat_caseof
        (τ₁ := embed A) (τ₂ := embed B) (τ := embed R)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply IHHC.
      * exact (compile_indexed_correct
          (RecTypes.ValidTy.ValidEnv_cons VG H1) H dir n).
      * exact (compile_indexed_correct
          (RecTypes.ValidTy.ValidEnv_cons VG H2) H0 dir n).
    + eapply (compat_caseof
        (τ₁ := embed A) (τ₂ := embed B) (τ := embed R)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * exact (compile_indexed_correct VG H dir n).
      * apply IHHC. exact (RecTypes.ValidTy.ValidEnv_cons VG H1).
      * exact (compile_indexed_correct
          (RecTypes.ValidTy.ValidEnv_cons VG H2) H0 dir n).
    + eapply (compat_caseof
        (τ₁ := embed A) (τ₂ := embed B) (τ := embed R)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * now apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
      * exact (compile_indexed_correct VG H dir n).
      * exact (compile_indexed_correct
          (RecTypes.ValidTy.ValidEnv_cons VG H1) H0 dir n).
      * apply IHHC. exact (RecTypes.ValidTy.ValidEnv_cons VG H2).
    + eapply (compat_seq (τ₂ := embed A)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        eapply indexed_typing_valid; eauto.
      * now apply IHHC.
      * exact (compile_indexed_correct VG H dir n).
    + eapply (compat_seq (τ₂ := embed A)).
      * now apply LogRelIE.LemmasPseudoType.ValidEnv_implies_ValidPEnv_embedCtx.
      * apply LogRelIE.LemmasPseudoType.ValidTy_implies_ValidPTy_embed.
        exact (indexed_context_result_valid VG0 VA0 VG HC).
      * exact (compile_indexed_correct VG H dir n).
      * now apply IHHC.
    + pose proof (IHHC VG) as Hinner.
      repeat split.
      * rewrite repEmulCtx_embedCtx_leftinv, repEmul_embed_leftinv.
        eapply (@StlcIso.SpecTyping.WtApp Gamma
          (GlobalCoercions.compile_global_up d)
          (StlcIso.SpecSyntax.pctx_app hole_i (compile_indexed_context C))
          A B).
        -- now apply GlobalCoercions.compile_global_up_typing.
        -- pose proof (proj1 Hinner) as Htyped.
           rewrite repEmulCtx_embedCtx_leftinv,
             repEmul_embed_leftinv in Htyped.
           exact Htyped.
      * rewrite isToEqCtx_embedCtx_leftinv, isToEq_embed_leftinv.
        pose proof (proj1 (proj2 Hinner)) as Htyped.
        rewrite isToEqCtx_embedCtx_leftinv,
          isToEq_embed_leftinv in Htyped.
        eapply StlcEqui.SpecTyping.WtEq.
        -- exact (CertificateIndexed.casteq_sound d).
        -- exact H.
        -- exact H0.
        -- exact Htyped.
      * intros w Hw gamma_i gamma_e Henv. cbn.
        replace (StlcIso.SpecSyntax.apTm gamma_i
          (GlobalCoercions.compile_global_pair d))
          with (GlobalCoercions.compile_global_pair d).
        -- eapply NativeBundleInvariant.compile_global_up_native_termrel;
             [exact H|exact H0|].
           exact (proj2 (proj2 Hinner) w Hw gamma_i gamma_e Henv).
        -- symmetry.
           exact (@wsClosed_invariant
             StlcIso.SpecSyntax.Tm StlcIso.SpecSyntax.WsTm
             StlcIso.SpecSyntax.Tm StlcIso.Inst.vrTm
             StlcIso.Inst.TmKit.inst_ap StlcIso.SpecSyntax.WsTm
             (@StlcIso.Inst.wsApTm StlcIso.SpecSyntax.Tm
               StlcIso.Inst.vrTm _ _ StlcIso.SpecSyntax.WsTm
               StlcIso.Inst.wsVrTm StlcIso.Inst.wsWkTm
               (@wsLiftXX StlcIso.SpecSyntax.Tm
                 StlcIso.Inst.vrTm StlcIso.SpecSyntax.WsTm))
             (GlobalCoercions.compile_global_pair d)
             (iso_typing_well_scoped
               (@GlobalCoercions.compile_global_pair_typing
                 empty A B d H H0)) gamma_i).
Qed.
