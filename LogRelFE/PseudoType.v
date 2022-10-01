Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.SpecSyntax.
Require Import UValFE.UVal.

Module F.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.LemmasTyping.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecEquivalent.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
  Include StlcFix.SpecAnnot.
End F.

Module E.
  Include RecTypes.SpecTypes.
  Include RecTypes.InstTy.
  Include RecTypes.Contraction.
  Include RecTypes.ValidTy.
  Include RecTypes.LemmasTypes.
  Include StlcEqui.LemmasEvaluation.
  Include StlcEqui.LemmasTyping.
  Include StlcEqui.SpecEvaluation.
  Include StlcEqui.SpecEquivalent.
  Include StlcEqui.SpecAnnot.
  Include StlcEqui.SpecTyping.
  Include StlcEqui.SpecSyntax.
End E.

Inductive Prec : Set :=
| precise
| imprecise.

Inductive PTy : Set :=
| ptarr (τ₁ τ₂ : PTy)
| ptunit
| ptbool
| ptprod (τ₁ τ₂ : PTy)
| ptsum (τ₁ τ₂ : PTy)
| pEmulDV (n : nat) (p : Prec) (τ : E.Ty).

Fixpoint repEmul (τ : PTy) : F.Ty :=
  match τ with
    | ptarr τ₁ τ₂ => F.tarr (repEmul τ₁) (repEmul τ₂)
    | ptunit => F.tunit
    | ptbool => F.tbool
    | ptprod τ₁ τ₂ => F.tprod (repEmul τ₁) (repEmul τ₂)
    | ptsum τ₁ τ₂ => F.tsum (repEmul τ₁) (repEmul τ₂)
    | pEmulDV n p T => UValFE n T
  end.

Fixpoint fxToIs (τ : PTy) : E.Ty :=
  match τ with
    | ptunit => E.tunit
    | ptbool => E.tbool
    | ptprod τ₁ τ₂ => E.tprod (fxToIs τ₁) (fxToIs τ₂)
    | ptarr τ₁ τ₂ => E.tarr (fxToIs τ₁) (fxToIs τ₂)
    | ptsum τ₁ τ₂ => E.tsum (fxToIs τ₁) (fxToIs τ₂)
    | pEmulDV n p T => T
  end.

Definition OfTypeStlcFix (τ : PTy) (t : F.Tm) : Prop :=
  F.Value t ∧ (F.Typing F.empty t (repEmul τ) ).

(* Fixpoint OfTypeStlcEqui' (τ : PTy) (t : U.UTm) : Prop := *)
(*   match τ with *)
(*     | ptarr τ₁ τ₂ => *)
(*       match t with *)
(*         | U.abs _ => True *)
(*         | _       => False *)
(*       end *)
(*     | ptunit => t = U.unit *)
(*     (* | ptbool => t = U.true ∨ t = U.false *) *)
(*     (* | ptprod τ₁ τ₂ => *) *)
(*     (*   match t with *) *)
(*     (*     | U.pair t₁ t₂ => OfTypeStlcEqui' τ₁ t₁ ∧ OfTypeStlcEqui' τ₂ t₂ *) *)
(*     (*     | _            => False *) *)
(*     (*   end *) *)
(*     | ptsum τ₁ τ₂ => *)
(*       match t with *)
(*         | U.inl t₁ => OfTypeStlcEqui' τ₁ t₁ *)
(*         | U.inr t₂ => OfTypeStlcEqui' τ₂ t₂ *)
(*         | _        => False *)
(*       end *)
(*     | pEmulDV n p => U.Value t *)
(*   end. *)
(* Arguments OfTypeStlcEqui' !τ !t /. *)

Definition OfTypeStlcEqui (τ : PTy) (t : E.Tm) : Prop :=
  E.Value t ∧ E.Typing (E.empty) t (fxToIs τ).

Arguments OfTypeStlcEqui !τ !t /.

Definition OfType (τ : PTy) (t₁ : F.Tm) (t₂ : E.Tm) : Prop :=
  OfTypeStlcFix τ t₁ ∧ OfTypeStlcEqui τ t₂.

Inductive PEnv : Set :=
| pempty
| pevar (Γ : PEnv) (τ : PTy).

Notation "Γ p▻ T" := (pevar Γ T) (at level 55, left associativity).

Fixpoint pdom (Γ : PEnv) : Dom :=
  match Γ with
    | pempty => 0
    | pevar Γ _ => S (pdom Γ)
  end.

Reserved Notation "⟪  i : T p∈ Γ  ⟫"
  (at level 0, i at level 98, Γ at level 98).
Inductive GetEvarP : PEnv → Ix → PTy → Prop :=
  | GetEvarHere {Γ T} :
      ⟪   O : T p∈ Γ p▻ T  ⟫
  | GetEvarThere {Γ T T' i} :
      ⟪   i : T p∈ Γ      ⟫ →
      ⟪ S i : T p∈ Γ p▻ T' ⟫
where "⟪  i : T p∈ Γ  ⟫" := (GetEvarP Γ i T).

Lemma pdom_works {i T Γ} :
  ⟪ i : T p∈ Γ ⟫ → pdom Γ ∋ i.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma pdom_works_inv {i Γ} :
  pdom Γ ∋ i → ∃ τ, ⟪ i : τ p∈ Γ ⟫.
Proof.
  revert i. induction Γ; intros i.
  - inversion 1.
  - inversion 1.
    + subst. exists τ. constructor.
    + subst. destruct (IHΓ i0 H1) as (τ0 & iinΓ).
      exists τ0. constructor. assumption.
Qed.

Fixpoint repEmulCtx (Γ : PEnv) : F.Env :=
  match Γ with
    | pempty => F.empty
    | pevar Γ τ => F.evar (repEmulCtx Γ) (repEmul τ)
  end.

Lemma repEmulCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  F.GetEvar (repEmulCtx Γ) i (repEmul τ).
Proof.
  induction 1; eauto using F.GetEvar.
Qed.

Fixpoint fxToIsCtx (Γ : PEnv) : E.Env :=
  match Γ with
  | pempty => E.empty
  | pevar Γ τ => E.evar (fxToIsCtx Γ) (fxToIs τ)
  end.

Lemma fxToIsCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  E.GetEvar (fxToIsCtx Γ) i (fxToIs τ).
Proof.
  induction 1; eauto using E.GetEvar.
Qed.

Fixpoint embed (τ : F.Ty) : PTy :=
  match τ with
    | F.tunit => ptunit
    | F.tarr τ₁ τ₂ => ptarr (embed τ₁) (embed τ₂)
    | F.tbool => ptbool
    | F.tprod τ₁ τ₂ => ptprod (embed τ₁) (embed τ₂)
    | F.tsum τ₁ τ₂ => ptsum (embed τ₁) (embed τ₂)
  end.

Fixpoint embedCtx (Γ : F.Env) : PEnv :=
  match Γ with
    | F.empty => pempty
    | F.evar Γ τ => pevar (embedCtx Γ) (embed τ)
  end.

Lemma embedCtx_works {Γ i τ} :
  F.GetEvar Γ i τ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP.
Qed.

Lemma embedCtx_works_inv {Γ i τ} :
  ⟪ i : τ p∈ embedCtx Γ ⟫ →
  exists τ', τ = embed τ' ∧ (F.GetEvar Γ i τ').
Proof.
  revert i τ. induction Γ; intros i τ' iτ; simpl in *; inversion iτ; subst.
  - exists τ; intuition.
  - destruct (IHΓ _ _ H3) as [τ'' [eq ty]].
    exists τ''; intuition; eauto using GetEvarP.
Qed.

Lemma OfTypeStlcEqui_fxToIs {vu τ τ'}:
  fxToIs τ = fxToIs τ' ->
  OfTypeStlcEqui τ vu ->
  OfTypeStlcEqui τ' vu.
Proof.
  intros eq [vvu tyu].
  split; [assumption|].
  now rewrite <-eq.
Qed.

