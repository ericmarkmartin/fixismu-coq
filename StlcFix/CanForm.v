Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecTyping.

Lemma can_form_tarr {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tarr τ₁ τ₂ ⟫) :
  ∃ t₂,
    t = abs τ₁ t₂ ∧
    ⟪ Γ ▻ τ₁ ⊢ t₂ : τ₂ ⟫.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tunit {Γ t}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tunit ⟫) :
    t = unit.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tbool {Γ t}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tbool ⟫) :
    t = true ∨ t = false.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tprod {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tprod τ₁ τ₂ ⟫) :
  ∃ t₁ t₂,
    t = pair t₁ t₂ ∧
    ⟪ Γ ⊢ t₁ : τ₁ ⟫ ∧
    ⟪ Γ ⊢ t₂ : τ₂ ⟫.
Proof. depind wt; try contradiction; eauto. Qed.

Lemma can_form_tsum {Γ t τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ ⊢ t : tsum τ₁ τ₂ ⟫) :
    (∃ t₁, t = inl t₁ ∧ ⟪  Γ ⊢ t₁ : τ₁ ⟫) ∨
    (∃ t₂, t = inr t₂ ∧ ⟪  Γ ⊢ t₂ : τ₂ ⟫).
Proof. depind wt; try contradiction; eauto. Qed.

Ltac stlcCanForm1 :=
  match goal with
    | [ wt: ⟪ _ ⊢ ?t : tarr _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tarr vt wt); subst; clear wt
    | [ wt: ⟪ _ ⊢ ?t : tunit ⟫, vt: Value ?t |- _ ] =>
      pose proof (can_form_tunit vt wt); subst; clear wt
    | [ wt: ⟪ _ ⊢ ?t : tbool ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tbool vt wt); subst; clear wt
    | [ wt: ⟪ _ ⊢ ?t : tprod _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tprod vt wt) as (? & ? & ? & ? & ?); subst; clear wt
    | [ wt: ⟪ _ ⊢ ?t : tsum _ _ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tsum vt wt) as [[? [? ?]]|[? [? ?]]]; subst; clear wt; simpl in vt
  end.

Ltac stlcCanForm :=
  repeat stlcCanForm1.
