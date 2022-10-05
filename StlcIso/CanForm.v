Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecTyping.

Lemma can_form_tarr {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ i⊢ t : tarr τ₁ τ₂ ⟫) :
  ∃ t₂,
    t = abs τ₁ t₂ ∧
    ⟪ Γ r▻ τ₁ i⊢ t₂ : τ₂ ⟫.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tunit {Γ t}
  (v: Value t) (wt: ⟪ Γ i⊢ t : tunit ⟫) :
    t = unit.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tbool {Γ t}
  (v: Value t) (wt: ⟪ Γ i⊢ t : tbool ⟫) :
    t = true ∨ t = false.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tprod {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ i⊢ t : tprod τ₁ τ₂ ⟫) :
  ∃ t₁ t₂,
    t = pair t₁ t₂ ∧
    ⟪ Γ i⊢ t₁ : τ₁ ⟫ ∧
    ⟪ Γ i⊢ t₂ : τ₂ ⟫.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tsum {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ i⊢ t : tsum τ₁ τ₂ ⟫) :
    (∃ t₁, t = inl t₁ ∧ ⟪  Γ i⊢ t₁ : τ₁ ⟫) ∨
    (∃ t₂, t = inr t₂ ∧ ⟪  Γ i⊢ t₂ : τ₂ ⟫).
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_trec {Γ t τ}
   (v: Value t) (wt: ⟪ Γ i⊢ t : trec τ ⟫) :
     exists t', t = fold_ t' ∧ ⟪ Γ i⊢ t' : τ[beta1 (trec τ)] ⟫.
Proof. depind wt; try contradiction; eauto. Qed.

Ltac stlcCanForm1 :=
  match goal with
    | [ wt: ⟪ _ i⊢ ?t : tarr _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tarr vt wt); subst; clear wt
    | [ wt: ⟪ _ i⊢ ?t : tunit ⟫, vt: Value ?t |- _ ] =>
      pose proof (can_form_tunit vt wt); subst; clear wt
    | [ wt: ⟪ _ i⊢ ?t : tbool ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tbool vt wt); subst; clear wt
    | [ wt: ⟪ _ i⊢ ?t : tprod _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tprod vt wt) as (? & ? & ? & ? & ?); subst; clear wt
    | [ wt: ⟪ _ i⊢ ?t : tsum _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tsum vt wt) as [[? [? ?]]|[? [? ?]]]; subst; clear wt; simpl in vt
    | [ wt: ⟪ _ i⊢ ?t : trec _ ⟫, vt: Value ?t |- _ ] =>
      pose proof (can_form_trec vt wt); subst; clear wt
  end.

Ltac stlcCanForm :=
  repeat stlcCanForm1.
