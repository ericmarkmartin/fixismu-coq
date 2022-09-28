Require Export StlcEqui.SpecTyping.
Require Export StlcEqui.SpecEvaluation.
Require Export StlcEqui.SpecAnnot.

(* Note that this definition quantifies over an explicitly annotated StlcIso context.
 * This allows our back-translation to make use of information from the typing judgement.
 * In the paper, this is formalized by defining the back-translation by induction on the typing judgement, but we cannot do that here, because the typing judgement is in Prop and Prop is computationally irrelevant.
 *)
Definition PCtxEquivalent (Γ: Env) (t₁ t₂: Tm) (τ: Ty) : Prop :=
  ∀ C τ',
    ValidTy τ' ->
    ⟪ ea⊢ C : Γ , τ → empty, τ' ⟫ →
    (pctx_app t₁ (eraseAnnot_pctx C))⇓ ↔ (pctx_app t₂ (eraseAnnot_pctx C))⇓.
Notation "⟪  Γ e⊢ t₁ ≃ t₂ : τ  ⟫" :=
  (PCtxEquivalent Γ t₁ t₂ τ)
  (at level 0, Γ at level 98, t₁ at level 98, t₂ at level 98, τ at level 98).

Lemma pctx_equiv_symm {Γ t₁ t₂ τ} :
  ⟪ Γ e⊢ t₁ ≃ t₂ : τ ⟫ → ⟪ Γ e⊢ t₂ ≃ t₁ : τ ⟫.
Proof.
  unfold PCtxEquivalent.
  intros equiv C τ' vτ' ty; split;
  apply (equiv C τ' vτ' ty).
Qed.
