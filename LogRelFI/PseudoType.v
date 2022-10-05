Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcIsoValid.LemmasEvaluation.
(* Require Import StlcIso.LemmasScoping. *)
Require Import StlcIsoValid.SpecEvaluation.
Require Import StlcIsoValid.SpecEquivalent.
(* Require Import StlcIso.SpecScoping. *)
Require Import StlcIsoValid.SpecSyntax.
Require Import UValFI.UVal.

Module F.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.LemmasTyping.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecEquivalent.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
  Include StlcFix.SpecAnnot.
End F.

Module I.
  Include StlcIsoValid.LemmasEvaluation.
  Include StlcIsoValid.LemmasTyping.
  Include StlcIsoValid.SpecEvaluation.
  Include StlcIsoValid.SpecEquivalent.
  Include StlcIsoValid.SpecAnnot.
  Include StlcIsoValid.SpecTyping.
  Include StlcIsoValid.SpecSyntax.
End I.

Inductive Prec : Set :=
| precise
| imprecise.

Inductive PTy : Set :=
| ptarr (τ₁ τ₂ : PTy)
| ptunit
| ptbool
| ptprod (τ₁ τ₂ : PTy)
| ptsum (τ₁ τ₂ : PTy)
| pEmulDV (n : nat) (p : Prec) (τ : I.Ty).

Notation "A p⊎ B" := (ptsum A B) (at level 85, right associativity).
Notation "A p× B" := (ptprod A B) (at level 85, right associativity).
Notation "A p⇒ B" := (ptarr A B) (at level 85, right associativity).

Fixpoint repEmul (τ : PTy) : F.Ty :=
  match τ with
    | ptarr τ₁ τ₂ => F.tarr (repEmul τ₁) (repEmul τ₂)
    | ptunit => F.tunit
    | ptbool => F.tbool
    | ptprod τ₁ τ₂ => F.tprod (repEmul τ₁) (repEmul τ₂)
    | ptsum τ₁ τ₂ => F.tsum (repEmul τ₁) (repEmul τ₂)
    | pEmulDV n p T => UValFI n T
  end.

Fixpoint fxToIs (τ : PTy) : I.Ty :=
  match τ with
    | ptunit => I.tunit
    | ptbool => I.tbool
    | ptprod τ₁ τ₂ => I.tprod (fxToIs τ₁) (fxToIs τ₂)
    | ptarr τ₁ τ₂ => I.tarr (fxToIs τ₁) (fxToIs τ₂)
    | ptsum τ₁ τ₂ => I.tsum (fxToIs τ₁) (fxToIs τ₂)
    | pEmulDV n p T => T
  end.

Definition OfTypeStlcFix (τ : PTy) (t : F.Tm) : Prop :=
  F.Value t ∧ (F.Typing F.empty t (repEmul τ) ).

(* Fixpoint OfTypeStlcIso' (τ : PTy) (t : U.UTm) : Prop := *)
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
(*     (*     | U.pair t₁ t₂ => OfTypeStlcIso' τ₁ t₁ ∧ OfTypeStlcIso' τ₂ t₂ *) *)
(*     (*     | _            => False *) *)
(*     (*   end *) *)
(*     | ptsum τ₁ τ₂ => *)
(*       match t with *)
(*         | U.inl t₁ => OfTypeStlcIso' τ₁ t₁ *)
(*         | U.inr t₂ => OfTypeStlcIso' τ₂ t₂ *)
(*         | _        => False *)
(*       end *)
(*     | pEmulDV n p => U.Value t *)
(*   end. *)
(* Arguments OfTypeStlcIso' !τ !t /. *)

Definition OfTypeStlcIso (τ : PTy) (t : I.Tm) : Prop :=
  I.Value t ∧ I.Typing (I.empty) t (fxToIs τ).

Arguments OfTypeStlcIso !τ !t /.

Definition OfType (τ : PTy) (t₁ : F.Tm) (t₂ : I.Tm) : Prop :=
  OfTypeStlcFix τ t₁ ∧ OfTypeStlcIso τ t₂.

Inductive PEnv : Set :=
| pempty
| pevar (Γ : PEnv) (τ : PTy).

Notation "Γ p▻ T" := (pevar Γ T) (at level 55, left associativity).

Fixpoint pdom (Γ : PEnv) : Dom :=
  match Γ with
    | pempty => 0
    | pevar Γ _ => S (pdom Γ)
  end.

Inductive wsPTy (γ : Dom) : PTy → Prop :=
| WsPTUnit : wsPTy γ ptunit
| WsPBool : wsPTy γ ptbool
| WsPFn {τ τ'} : wsPTy γ τ → wsPTy γ τ' → wsPTy γ (τ p⇒ τ')
| WsPSum {τ τ'} : wsPTy γ τ → wsPTy γ τ' → wsPTy γ (τ p⊎ τ')
| WsPProd {τ τ'} : wsPTy γ τ → wsPTy γ τ' → wsPTy γ (τ p× τ')
| WsPEmulDv {n p τ} : wsTy 0 τ → wsPTy γ (pEmulDV n p τ).

Section WellScoping.

  Inductive innerPClosed : PTy → Prop :=
    | innerPUnitClosed : innerPClosed ptunit
    | innerPBoolClosed : innerPClosed ptbool
    | innerPFnClosed {τ τ'} : innerPClosed τ → innerPClosed τ' → innerPClosed (τ p⇒ τ)
    | innerPSumClosed {τ τ'} : innerPClosed τ → innerPClosed τ' → innerPClosed (τ p⊎ τ)
    | innerPProdClosed {τ τ'} : innerPClosed τ → innerPClosed τ' → innerPClosed (τ p× τ)
    | innerPEmulDvClosed {n p τ} : ⟨ 0 ⊢ τ ⟩ → innerPClosed (pEmulDV n p τ).

  Lemma WsPTy_mono {n m : nat} {τ} : n <= m → wsPTy n τ → wsPTy m τ.
  Proof.
    intros ineq cτn.
    revert m ineq.
    induction cτn; constructor; eauto.
  Qed.

End WellScoping.

Instance WsPTy : Ws PTy := wsPTy.

Section Application.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {wkY: Wk Y}.

  Context {vrPTy: Vr PTy}.
  Context {liftYPTy: Lift Y PTy}.

  Fixpoint apPTy (ζ: Sub Y) (τ: PTy) {struct τ} : PTy :=
    match τ with
      | ptarr τ₁ τ₂ => ptarr (apPTy ζ τ₁) (apPTy ζ τ₂)
      | ptunit => ptunit
      | ptbool => ptbool
      | ptprod τ₁ τ₂ => ptprod (apPTy ζ τ₁) (apPTy ζ τ₂)
      | ptsum τ₁ τ₂ => ptsum (apPTy ζ τ₁) (apPTy ζ τ₂)
      | pEmulDV n p τ => pEmulDV n p τ
    end.

  Global Arguments apPTy ζ !τ.
End Application.

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

Fixpoint fxToIsCtx (Γ : PEnv) : I.Env :=
  match Γ with
  | pempty => I.empty
  | pevar Γ τ => I.evar (fxToIsCtx Γ) (fxToIs τ)
  end.

Lemma fxToIsCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  I.GetEvar (fxToIsCtx Γ) i (fxToIs τ).
Proof.
  induction 1; eauto using I.GetEvar.
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

Lemma OfTypeStlcIso_fxToIs {vu τ τ'}:
  fxToIs τ = fxToIs τ' ->
  OfTypeStlcIso τ vu ->
  OfTypeStlcIso τ' vu.
Proof.
  intros eq [vvu tyu].
  split; [assumption|].
  now rewrite <-eq.
Qed.
