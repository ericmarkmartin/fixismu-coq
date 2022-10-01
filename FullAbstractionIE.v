Require Import StlcIsoValid.SpecTyping.
Require Import StlcIsoValid.SpecEquivalent.
Require Import StlcIsoValid.LemmasEvaluation.
Require Import StlcIsoValid.LemmasTyping.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.LemmasEvaluation.

Require Import CompilerIE.CompilerIE.

Require Import UValIE.UVal.

Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.

Require Import BacktransIE.Emulate.
Require Import BacktransIE.InjectExtract.
Require Import BacktransIE.UpgradeDowngrade.

Lemma equivalencePreservation {t₁ t₂ τ} :
  ValidTy τ ->
  ⟪ I.empty i⊢ t₁ : τ ⟫ →
  ⟪ I.empty i⊢ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫ →
  ⟪ E.empty e⊢ compie t₁ ≃ compie t₂ : τ ⟫.
Proof.
  (* sufficient to prove one direction of equi-termination *)
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂ τ τ'},
             ValidTy τ ->
             ValidTy τ' ->
            ⟪ I.empty i⊢ t₁ : τ ⟫ →
            ⟪ I.empty i⊢ t₂ : τ ⟫ →
            ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫ →
            ∀ {C}, ⟪ ea⊢ C : E.empty , τ → E.empty , τ' ⟫ →
                 E.Terminating (E.pctx_app (compie t₁) (eraseAnnot_pctx C)) → E.Terminating (E.pctx_app (compie t₂) (eraseAnnot_pctx C))) as Hltor.
  { intros t₁ t₂ τ vτ ty1 ty2 ceq.
    assert (⟪ I.empty i⊢ t₂ ≃ t₁ : τ ⟫) as ceq'
            by (apply I.pctx_equiv_symm; assumption).
    split;
      refine (Hltor _ _ _ _ _ _ _ _ _ _ H0); crushValidTy.
  }

  intros t₁ t₂ τ τ' vτ vτ' ty₁ ty₂ ceq Cu tCu term.
  destruct (E.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_gt , S n ⟧ compie t₁ : embed τ ⟫) as lre₁.
  { change pempty with (embedCtx (repEmulCtx pempty)).
      eapply compie_correct; crushValidTy_with_UVal.
      cbn; eauto using ValidEnv_nil. }
  assert (⟪ pempty ⊩ I.app (inject (S (S n)) τ) t₁ ⟦ dir_gt , S n ⟧ compie t₁ : pEmulDV (S (S n)) precise τ ⟫) as lrpe₁
      by (eapply inject_works_open;
          eauto using dwp_precise with arith).

  assert (⟪ ⊩ I.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) ⟦ dir_gt , S n ⟧ (eraseAnnot_pctx Cu) :
              pempty , pEmulDV (S (S n)) precise τ → pempty , pEmulDV (S (S n)) precise τ' ⟫) as lrem₁ by
      (change pempty with (toEmulDV (S (S n)) precise E.empty);
       eapply emulate_pctx_works; eauto using dwp_precise with arith tyvalid).

  pose proof (proj2 (proj2 lrem₁) _ _ lrpe₁) as lrfull₁.

  assert (I.Terminating (I.pctx_app (I.app (inject (S (S n)) τ) t₁)
                                    (I.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu)))) as termI
    by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  change (I.app (inject (S (S n)) τ) t₁) with (I.pctx_app t₁ (I.eraseAnnot_pctx (I.ia_papp₂ τ (UValIE (S (S n)) τ) (injectA (S (S n)) τ) I.ia_phole))) in termI.
  rewrite <- I.pctx_cat_app in termI.
  rewrite <- I.eraseAnnot_pctx_cat in termI.

  assert (⟪ i⊢ I.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) : I.empty, UValIE (S (S n)) τ → I.empty, UValIE (S (S n)) τ' ⟫) by
    (change I.empty with (toUVals (S (S n)) E.empty);
        eapply I.eraseAnnot_pctxT, emulate_pctx_T; eauto with tyvalid).

  assert (vε : ValidEnv E.empty) by eauto with tyvalid.
  pose proof (tEmCu := emulate_pctx_T (n := S (S n)) vε vτ' tCu).
  assert (I.Terminating (I.pctx_app t₂ (I.eraseAnnot_pctx (I.pctxA_cat
                 (I.ia_papp₂ τ (UValIE (S (S n)) τ) (injectA (S (S n)) τ) I.ia_phole)
                 (emulate_pctx (S (S n)) Cu))))) as termS'.
  { eapply ceq.
    repeat (I.crushTypingMatchIAH + I.crushTypingMatchIAH2);
    crushValidTy_with_UVal; eauto using injectAT, emulate_pctx_T, I.PCtxTypingAnnot.
    assumption.
  }

  destruct (I.Terminating_TermHor termS') as [m termSm']; clear termS'.

  assert (⟪ pempty ⊩ t₂ ⟦ dir_lt , S m ⟧ compie t₂ : embed τ ⟫) as lre₂
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply compie_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ I.app (inject (S (S n)) τ) t₂ ⟦ dir_lt , S m ⟧ compie t₂ : pEmulDV (S (S n)) imprecise τ ⟫) as lrpe₂
      by (eapply inject_works_open;
          eauto using dwp_imprecise).

  assert (⟪ ⊩ I.eraseAnnot_pctx (emulate_pctx (S (S n)) Cu) ⟦ dir_lt , S m ⟧ (eraseAnnot_pctx Cu) : 
              pempty , pEmulDV (S (S n)) imprecise τ → pempty , pEmulDV (S (S n)) imprecise τ' ⟫) as lrem₂
      by (change pempty with (toEmulDV (S (S n)) imprecise E.empty);
          eapply emulate_pctx_works; eauto using dwp_imprecise).

  pose proof (proj2 (proj2 lrem₂) _ _ lrpe₂) as lrfull₂.
  rewrite I.eraseAnnot_pctx_cat, I.pctx_cat_app in termSm'.

  eapply (adequacy_lt lrfull₂ termSm'); eauto with arith.
Qed.

Lemma fullAbstraction {t₁ t₂ τ} :
  ValidTy τ ->
  ⟪ I.empty i⊢ t₁ : τ ⟫ →
  ⟪ I.empty i⊢ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫ ↔
  ⟪ E.empty e⊢ compie t₁ ≃ compie t₂ : τ ⟫.
Proof.
  intros.
  split;
  eauto using equivalenceReflectionEmpty, equivalencePreservation.
Qed.

Print Assumptions fullAbstraction.
