Require Import StlcEqui.CanForm.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.LemmasTyping.
Require Import StlcEqui.LemmasProgramContext.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     subst*);
  try discriminate;
  eauto with eval.

Ltac progressH :=
  match goal with
    | [ H: ⟪ _ : _ r∈ empty ⟫ |- _         ] => inversion H
    | [ H: _ ∨ _             |- _         ] => destruct H
    | [ H: True              |- _         ] => clear H
    | [ H: False             |- _         ] => inversion H
    | [                      |- False ∨ _ ] => right
    | [                      |- True ∨ _  ] => left; auto
  end;
  stlcCanForm.

Hint Constructors eval : pctx.
Hint Constructors eval₀ : pctx.
Hint Extern 20 (Value _) => cbn : pctx.
Hint Extern 20 (ECtx _) => cbn : pctx.

(* Lemma local_progress {t U} (wt: ⟪ empty ⊢ t : U ⟫) : *)
(*   Value t ∨ *)
(*   ∃ C t₀ t₀', *)
(*     t = pctx_app t₀ C ∧ *)
(*     t₀ -->₀ t₀' ∧ *)
(*     ECtx C. *)
(* Proof. *)
(*   depind wt; *)
(*   repeat *)
(*     (try progressH; cbn in *; destruct_conjs; subst); *)
(*     eauto 20 with pctx; *)
(*     try (exists phole; cbn; eauto 20 with pctx; fail). *)
(* Qed. *)

(* Lemma progress {t U} (wt: ⟪ empty ⊢ t : U ⟫) : *)
(*   Value t ∨ *)
(*   ∃ t', t --> t'. *)
(* Proof. *)
(*   destruct (local_progress wt); destruct_conjs; *)
(*     subst; eauto using eval. *)
(* Qed. *)

Lemma context_replacement {Γ C t t' T}
  (hyp: ∀ Γ' T', ValidEnv Γ' -> ⟪ Γ' e⊢ t : T' ⟫ → ⟪ Γ' e⊢ t' : T' ⟫) :
  ValidEnv Γ ->
    ⟪ Γ e⊢ pctx_app t C : T ⟫ →
    ⟪ Γ e⊢ pctx_app t' C : T ⟫.
Proof.
  intros vΓ wt; depind wt; crushTyping;
    induction C; crush; eauto with typing.
Qed.

Lemma preservation₀ {t t'} (r : t -->₀ t') :
  ∀ {Γ τ}, ValidEnv Γ -> ⟪ Γ e⊢ t : τ ⟫ → ⟪ Γ e⊢ t' : τ ⟫.
Proof.
  induction r;
    eauto using context_replacement;
    crushTyping.
  - refine (typed_terms_are_valid _ _ _ H6).
    eauto with tyvalid.
  - now eapply ValidTy_invert_arr in H4.
  - crushTyping.
    eapply (WtEq _ (tyeq_symm H2)); try assumption.
    now eapply ValidTy_invert_arr in H4.
  - now refine (typed_terms_are_valid _ _ _ H4).
  - now eapply ValidTy_invert_prod in H2.
  - now refine (typed_terms_are_valid _ _ _ H3).
  - now eapply ValidTy_invert_prod in H2.
  - crushTyping.
    now refine (typed_terms_are_valid _ _ _ H6).
    now eapply ValidTy_invert_sum in H1.
  - crushTyping.
    now refine (typed_terms_are_valid _ _ _ H6).
    now eapply ValidTy_invert_sum in H1.
Qed.

Lemma preservation {t t'} (r: t --> t') :
  ∀ {Γ τ}, ValidEnv Γ -> ⟪ Γ e⊢ t : τ ⟫ → ⟪ Γ e⊢ t' : τ ⟫.
Proof.
  induction r.
  eauto using context_replacement, preservation₀.
Qed.

Lemma preservation_star {t t'} (r: t -->* t') :
  ∀ {Γ τ}, ValidEnv Γ -> ⟪ Γ e⊢ t : τ ⟫ → ⟪ Γ e⊢ t' : τ ⟫.
Proof.
  induction r;
  eauto using preservation.
Qed.

Lemma termination_value {t τ} (wt: ⟪ empty e⊢ t : τ ⟫) :
  t⇓ → ∃ t', t -->* t' ∧ Value t'.
Proof.
  destruct 1; crush.
Qed.
