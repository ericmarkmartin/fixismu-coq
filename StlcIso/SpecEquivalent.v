Require Export StlcIso.SpecTyping.
Require Export StlcIso.SpecEvaluation.
Require Export StlcIso.SpecAnnot.

(* Note that this definition quantifies over an explicitly annotated StlcIso context.
 * This allows our back-translation to make use of information from the typing judgement.
 * In the paper, this is formalized by defining the back-translation by induction on the typing judgement, but we cannot do that here, because the typing judgement is in Prop and Prop is computationally irrelevant.
 *)
Definition PCtxEquivalent (Γ: Env) (t₁ t₂: Tm) (τ: Ty) : Prop :=
  ∀ C τ',
    ⟪ ia⊢ C : Γ , τ → empty, τ' ⟫ →
    (pctx_app t₁ (eraseAnnot_pctx C))⇓ ↔ (pctx_app t₂ (eraseAnnot_pctx C))⇓.
Notation "⟪  Γ i⊢ t₁ ≃ t₂ : τ  ⟫" :=
  (PCtxEquivalent Γ t₁ t₂ τ)
  (at level 0, Γ at level 98, t₁ at level 98, t₂ at level 98, τ at level 98).

Lemma pctx_equiv_symm {Γ t₁ t₂ τ} :
  ⟪ Γ i⊢ t₁ ≃ t₂ : τ ⟫ → ⟪ Γ i⊢ t₂ ≃ t₁ : τ ⟫.
Proof.
  unfold PCtxEquivalent.
  intros equiv C τ' ty; split;
  apply (equiv C τ' ty).
Qed.
