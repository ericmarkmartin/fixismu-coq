Require Export StlcFix.SpecTyping.
Require Export StlcFix.SpecAnnot.
Require Export StlcFix.SpecEvaluation.

Definition PCtxEquivalent (Γ: Env) (t₁ t₂: Tm) (τ: Ty) : Prop :=
  ∀ C τ',
    ⟪ a⊢ C : Γ , τ → empty, τ' ⟫ →
    (pctx_app t₁ (eraseAnnot_pctx C))⇓ ↔ (pctx_app t₂ (eraseAnnot_pctx C))⇓.
Notation "⟪  Γ ⊢ t₁ ≃ t₂ : τ  ⟫" :=
  (PCtxEquivalent Γ t₁ t₂ τ)
  (at level 0, Γ at level 98, t₁ at level 98, t₂ at level 98, τ at level 98).

Lemma pctx_equiv_symm {Γ t₁ t₂ τ} :
  ⟪ Γ ⊢ t₁ ≃ t₂ : τ ⟫ → ⟪ Γ ⊢ t₂ ≃ t₁ : τ ⟫.
Proof.
  unfold PCtxEquivalent.
  intros equiv C τ' ty; split;  
  apply (equiv C τ' ty).
Qed.
