Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcIso.SpecEquivalent.
Require Import StlcIso.LemmasEvaluation.

Require Import CompilerFI.CompilerFI.

Require Import UValFI.UVal.

Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LRFI.
Require Import LogRelFI.LemmasLR.

Require Import BacktransFI.Emulate.
Require Import BacktransFI.InjectExtract.
Require Import BacktransFI.UpgradeDowngrade.

Lemma equivalencePreservation {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫.
Proof.
  (* sufficient to prove one direction of equi-termination *)
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂ τ τ'},
            ⟪ F.empty ⊢ t₁ : τ ⟫ →
            ⟪ F.empty ⊢ t₂ : τ ⟫ →
            ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
            ∀ {C}, ⟪ ia⊢ C : I.empty , compfi_ty τ → I.empty , τ' ⟫ →
                 I.Terminating (I.pctx_app (compfi t₁) (eraseAnnot_pctx C)) → I.Terminating (I.pctx_app (compfi t₂) (eraseAnnot_pctx C))) as Hltor
      by (intros t₁ t₂ τ ty1 ty2 ceq;
          assert (⟪ F.empty ⊢ t₂ ≃ t₁ : τ ⟫)
            by (apply F.pctx_equiv_symm; assumption);
          split;
          refine (Hltor _ _ _ _ _ _ _ _ _); eassumption).

  intros t₁ t₂ τ τ' ty₁ ty₂ ceq Cu tCu term.
  destruct (I.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_gt , S n ⟧ compfi t₁ : embed τ ⟫) as lre₁
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply compfi_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ F.app (inject (S (S n)) τ) t₁ ⟦ dir_gt , S n ⟧ compfi t₁ : pEmulDV (S (S n)) precise (compfi_ty τ) ⟫) as lrpe₁
      by (eapply inject_works_open;
          eauto using dwp_precise with arith).

  assert (⟪ ⊩ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) ⟦ dir_gt , S n ⟧ (eraseAnnot_pctx Cu) :
              pempty , pEmulDV (S (S n)) precise (compfi_ty τ) → pempty , pEmulDV (S (S n)) precise τ' ⟫) as lrem₁ by
      (change pempty with (toEmulDV (S (S n)) precise I.empty);
       eapply emulate_pctx_works; eauto using dwp_precise with arith).

  pose proof (proj2 (proj2 lrem₁) _ _ lrpe₁) as lrfull₁.

  assert (F.Terminating (F.pctx_app (F.app (inject (S (S n)) τ) t₁)
                                    (F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu)))) as termF
    by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  change (F.app (inject (S (S n)) τ) t₁) with (F.pctx_app t₁ (F.eraseAnnot_pctx (F.a_papp₂ τ (UValFI (S (S n)) (compfi_ty τ)) (injectA (S (S n)) τ) F.a_phole))) in termF.
  rewrite <- F.pctx_cat_app in termF.
  rewrite <- F.eraseAnnot_pctx_cat in termF.

  assert (⟪ ⊢ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) : F.empty, UValFI (S (S n)) (compfi_ty τ) → F.empty, UValFI (S (S n)) τ' ⟫)
    by (change F.empty with (toUVals (S (S n)) I.empty);
        eapply F.eraseAnnot_pctxT, emulate_pctx_T; assumption).

  pose proof (tEmCu := emulate_pctx_T (n := S (S n)) tCu).
  assert (F.Terminating (F.pctx_app t₂ (F.eraseAnnot_pctx (F.pctxA_cat
                 (F.a_papp₂ τ (UValFI (S (S n)) (compfi_ty τ)) (injectA (S (S n)) τ) F.a_phole)
                 (emulate_pctx (S (S n)) Cu))))) as termS'
      by (eapply ceq;
          eauto using F.pctxtyping_cat_annot, injectAT, emulate_pctx_T, F.PCtxTypingAnnot).

  destruct (F.Terminating_TermHor termS') as [m termSm']; clear termS'.

  assert (⟪ pempty ⊩ t₂ ⟦ dir_lt , S m ⟧ compfi t₂ : embed τ ⟫) as lre₂
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply compfi_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ F.app (inject (S (S n)) τ) t₂ ⟦ dir_lt , S m ⟧ compfi t₂ : pEmulDV (S (S n)) imprecise (compfi_ty τ) ⟫) as lrpe₂
      by (eapply inject_works_open;
          eauto using dwp_imprecise).

  assert (⟪ ⊩ F.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) ⟦ dir_lt , S m ⟧ (eraseAnnot_pctx Cu) : 
              pempty , pEmulDV (S (S n)) imprecise (compfi_ty τ) → pempty , pEmulDV (S (S n)) imprecise τ' ⟫) as lrem₂
      by (change pempty with (toEmulDV (S (S n)) imprecise I.empty);
          eapply emulate_pctx_works; eauto using dwp_imprecise).

  pose proof (proj2 (proj2 lrem₂) _ _ lrpe₂) as lrfull₂.
  rewrite F.eraseAnnot_pctx_cat, F.pctx_cat_app in termSm'.

  eapply (adequacy_lt lrfull₂ termSm'); eauto with arith.
Qed.

Lemma fullAbstraction {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫ ↔
  ⟪ I.empty i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫.
Proof.
  intros.
  split;
  eauto using equivalenceReflection, equivalencePreservation.
Qed.

(* Print Assumptions fullAbstraction. *)
