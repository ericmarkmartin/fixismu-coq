Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.LemmasTyping.

(* Lemma can_form_tarr {Γ t τ₁ τ₂} *)
(*   (v: Value t) (wt: ⟪ Γ e⊢ t : τ₁ e⇒ τ₂ ⟫)  : *)
(*   ∃ σ₁ t₂, *)
(*     ⟪ τ₁ ≗ σ₁ ⟫ → *)
(*     t = abs σ₁ t₂ ∧ *)
(*     ⟪ Γ e▻ τ₁ e⊢ t₂ : τ₂ ⟫. *)
(* Proof. depind wt; try contradiction; eauto. *)
(*        depind T; try inversion H; eauto. *)
(*        - (* tarr *) *)
(*          subst. *)
(*          apply (IHwt _ _ v). *)

(*        - (* trec *) idtac. *)
(* Qed. *)

Lemma trec_tunit_eq_tunit : ⟪ tunit ≗ trec tunit ⟫.
Proof.
  constructor;
  eauto with contr.
  cbn.
  apply tyeq_refl.
Qed.

Lemma can_form_tarr {Γ t τ τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ e⊢ t : τ ⟫) (tyeq: ⟪ τ ≗ τ₁ r⇒ τ₂ ⟫) :
  ValidEnv Γ ->
  ValidTy τ ->
  ValidTy τ₁ →
  ValidTy τ₂ →
  ∃ t₂ τ₁',
    ⟪ τ₁' ≗ τ₁ ⟫ ∧
      ValidTy τ₁' /\
    t = abs τ₁' t₂ ∧
    ⟪ Γ r▻ τ₁ e⊢ t₂ : τ₂ ⟫.
Proof.
  depind wt; try inversion tyeq; try contradiction; eauto;
  subst; intros.
  - exists t, τ₁0.
    destruct (ValidTy_invert_arr H1) as [τ1_v τ2_v].
    repeat (split; eauto).
    apply (WtEq _ H5); eauto.
    eapply (eqctx_implies_eqty (Γ r▻ τ₁0));
    eauto using enveq_refl with tyvalid tyeq.
  - apply IHwt; eauto.
    unshelve eapply (eq_trans_contr _ H tyeq); eauto with simple_contr_rec tyvalid.
  - apply IHwt; eauto.
    unshelve eapply (eq_trans_contr _ H tyeq); eauto with simple_contr_rec tyvalid.
Qed.

Lemma can_form_tunit {Γ t τ}
  (v: Value t) (wt: ⟪ Γ e⊢ t : τ ⟫) (tyeq: ⟪ τ ≗ tunit ⟫) :
    t = unit.
Proof.
  depind wt; try inversion tyeq; try contradiction; eauto.
  subst.
  apply (IHwt v H).
  apply (IHwt v).
  subst.
  unshelve eapply (eq_trans_contr _ H tyeq);
    eauto with simple_contr_rec.
Qed.

Lemma can_form_tunit' {Γ t}
  (v: Value t) (wt: ⟪ Γ e⊢ t : tunit ⟫) :
    t = unit.
Proof.
  apply (can_form_tunit v wt).
  eapply tyeq_refl.
Qed.

Lemma can_form_tbool {Γ t τ}
  (v: Value t) (wt: ⟪ Γ e⊢ t : τ ⟫) (tyeq: ⟪ τ ≗ tbool ⟫):
    t = true ∨ t = false.
Proof.
  depind wt; try inversion tyeq; try contradiction; eauto;
  subst;
  apply (IHwt v).
  assumption.
  unshelve eapply (eq_trans_contr _ H tyeq);
    eauto with simple_contr_rec.
Qed.

Lemma can_form_tbool' {Γ t}
  (v: Value t) (wt: ⟪ Γ e⊢ t : tbool ⟫) :
    t = true ∨ t = false.
Proof. apply (can_form_tbool v wt); apply tyeq_refl. Qed.

Lemma can_form_tprod {Γ t τ τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ e⊢ t : τ ⟫) (tyeq: ⟪ τ ≗ τ₁ r× τ₂ ⟫) :
  ValidEnv Γ →
  ValidTy τ₁ ->
  ValidTy τ₂ ->
  ∃ t₁ t₂, t = pair t₁ t₂ ∧
  ⟪ Γ e⊢ t₁ : τ₁ ⟫ ∧
  ⟪ Γ e⊢ t₂ : τ₂ ⟫.
Proof.
  depind wt; try inversion tyeq; try contradiction;
  subst; intros.
  - exists t₁, t₂. repeat split; eapply WtEq; eauto using typed_terms_are_valid with tyvalid.
  - apply IHwt; eauto.
    refine (eq_trans_contr _ H _);
    eauto with simple_contr_rec.
  - apply IHwt; eauto.
    (refine (eq_trans_contr _ H _); eauto with simple_contr_rec).
Qed.

Lemma can_form_tsum {Γ t τ τ₁ τ₂}
  (v: Value t) (wt: ⟪ Γ e⊢ t : τ ⟫) (tyeq: ⟪ τ ≗ τ₁ r⊎ τ₂ ⟫) :
  ValidEnv Γ ->
  ValidTy τ₁ →
  ValidTy τ₂ →
    (∃ t₁, t = inl t₁ ∧ ⟪  Γ e⊢ t₁ : τ₁ ⟫) ∨
    (∃ t₂, t = inr t₂ ∧ ⟪  Γ e⊢ t₂ : τ₂ ⟫).
Proof.
  depind wt; try inversion tyeq; try contradiction; subst.
  - left;
    exists t; repeat split; eapply WtEq; eauto using typed_terms_are_valid.
  - right;
    exists t; repeat split; eapply WtEq; eauto using typed_terms_are_valid .
  - intros.
    apply IHwt; eauto.
    refine (eq_trans_contr _ H _); eauto with simple_contr_rec tyvalid.
  - intros.
    apply IHwt; eauto.
    refine (eq_trans_contr _ H _); eauto with simple_contr_rec tyvalid.
Qed.

Ltac stlcCanForm1 :=
  match goal with
    | [ wt: ⟪ _ e⊢ ?t : tarr ?τ₁ ?τ₂ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tarr (τ₁ := τ₁) (τ₂ := τ₂) vt wt); subst; clear wt
    | [ wt: ⟪ _ e⊢ ?t : tunit ⟫, vt: Value ?t |- _ ] =>
      pose proof (can_form_tunit vt wt); subst; clear wt
    | [ wt: ⟪ _ e⊢ ?t : tbool ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tbool vt wt); subst; clear wt
    | [ wt: ⟪ _ e⊢ ?t : tprod ?τ₁ ?τ₂ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tprod (τ₁ := τ₁) (τ₂ := τ₂) vt wt) as (? & ? & ? & ? & ?);
      eauto with tyeq tyvalid;
      subst; clear wt
    | [ wt: ⟪ _ e⊢ ?t : tsum ?τ₁ ?τ₂ ⟫, vt: Value ?t |- _ ] =>
      destruct (can_form_tsum (τ₁ := τ₁) (τ₂ := τ₂) vt wt) as [[? [? ?]]|[? [? ?]]];
      eauto with tyeq tyvalid;
      subst; clear wt; simpl in vt
  end.

Ltac stlcCanForm :=
  repeat stlcCanForm1.
