Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Export StlcEqui.SpecSyntax.
Require Export StlcEqui.Inst.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Max.
Require Import Coq.micromega.Lia.

(** * Typing *)

Reserved Notation "⟪  Γ e⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98 ).
Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | WtVar {i T} :
      ⟪ i : T r∈ Γ ⟫ →
      ⟪ Γ e⊢ var i : T ⟫
  | WtAbs {t τ₁ τ₂} :
      ⟪ Γ r▻ τ₁ e⊢ t : τ₂ ⟫ →
      ValidTy τ₁ ->
      ⟪ Γ e⊢ abs τ₁ t : tarr τ₁ τ₂ ⟫
  | WtApp {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ e⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ Γ e⊢ t₂ : τ₁ ⟫ →
      ⟪ Γ e⊢ app t₁ t₂ : τ₂ ⟫
  | WtUnit :
      ⟪ Γ e⊢ unit : tunit ⟫
  | WtTrue :
      ⟪ Γ e⊢ true : tbool ⟫
  | WtFalse :
      ⟪ Γ e⊢ false : tbool ⟫
  | WtIte {t₁ t₂ t₃ T} :
      ⟪ Γ e⊢ t₁ : tbool ⟫ →
      ⟪ Γ e⊢ t₂ : T ⟫ →
      ⟪ Γ e⊢ t₃ : T ⟫ →
      ⟪ Γ e⊢ ite t₁ t₂ t₃ : T ⟫
  | WtPair {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ e⊢ t₁ : τ₁ ⟫ →
      ⟪ Γ e⊢ t₂ : τ₂ ⟫ →
      ⟪ Γ e⊢ pair t₁ t₂ : tprod τ₁ τ₂ ⟫
  | WtProj1 {t τ₁ τ₂} :
      ⟪ Γ e⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ e⊢ proj₁ t : τ₁ ⟫
  | WtProj2 {t τ₁ τ₂} :
      ⟪ Γ e⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ e⊢ proj₂ t : τ₂ ⟫
  | WtInl {t τ₁ τ₂} :
      ⟪ Γ e⊢ t : τ₁ ⟫ →
      ValidTy τ₂ ->
      ⟪ Γ e⊢ inl t : tsum τ₁ τ₂ ⟫
  | WtInr {t τ₁ τ₂} :
      ⟪ Γ e⊢ t : τ₂ ⟫ →
      ValidTy τ₁ ->
      ⟪ Γ e⊢ inr t : tsum τ₁ τ₂ ⟫
  | WtCaseof {t₁ t₂ t₃ τ₁ τ₂ T} :
      ⟪ Γ e⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ e⊢ t₂ : T ⟫ →
      ⟪ Γ r▻ τ₂ e⊢ t₃ : T ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ Γ e⊢ caseof t₁ t₂ t₃ : T ⟫
  | WtSeq {t₁ t₂ T} :
      ⟪ Γ e⊢ t₁ : tunit ⟫ →
      ⟪ Γ e⊢ t₂ : T ⟫ →
      ⟪ Γ e⊢ seq t₁ t₂ : T ⟫
  | WtEq {t T U} :
      ⟪ T ≗ U ⟫ →
      ValidTy T ->
      ValidTy U ->
      ⟪ Γ e⊢ t : T ⟫ →
      ⟪ Γ e⊢ t : U ⟫
where "⟪  Γ e⊢ t : T  ⟫" := (Typing Γ t T).
Hint Constructors Typing : wt.

Lemma quuux (Γ Γ' : Env) (i : Ix) {τ τ'} :
  ⟪ Γ ≗≗ Γ' ⟫ →
  ⟪ i : τ r∈ Γ ⟫ →
  ⟪ i : τ' r∈ Γ' ⟫ →
  ⟪ τ ≗ τ' ⟫.
Proof.
  revert Γ Γ'.
  induction i.
  - (* i = 0 *)
    intros.
    destruct Γ, Γ';
    inversion H0;
    inversion H1;
    inversion H;
    subst;
    assumption.
  - (* i = S i *)
    intros.
    destruct Γ, Γ';
    inversion H0;
    inversion H1;
    inversion H;
    subst.
    eapply IHi; eauto.
Qed.


Lemma quuuuuux (Γ Γ' : Env) : ⟪ Γ ≗≗ Γ' ⟫ → dom Γ = dom Γ'.
Proof.
  induction 1; eauto.
  cbn.
  f_equal.
  assumption.
Qed.


Lemma ty_in_env_implies_contr_ty {i τ Γ} : ContrEnv Γ → ⟪ i : τ r∈ Γ ⟫ → SimpleContr τ.
Proof.
  revert i.
  depind Γ;
  intros.
  inversion H0.
  destruct i.
  inversion H; subst.
  inversion H0; subst.
  assumption.
  inversion H0; subst.
  inversion H; subst.
  apply (IHΓ i H3 H5).
Qed.

Hint Resolve ty_in_env_implies_contr_ty : wt.

Lemma ClosedEnv_implies_Closed_varty {Γ i T} :
  ClosedEnv Γ -> ⟪ i : T r∈ Γ ⟫ -> ⟨ 0 ⊢ T ⟩.
Proof.
  intros cenv wtv.
  induction wtv; inversion cenv; eauto.
Qed.

Hint Resolve ClosedEnv_implies_Closed_varty : wt.

Lemma ty_in_valid_env_valid {i τ Γ} : ValidEnv Γ → ⟪ i : τ r∈ Γ ⟫ → ValidTy τ.
Proof.
  intros [env_cl env_contr] wti.
  split;
  eauto with wt.
Qed.
Hint Resolve ty_in_valid_env_valid : wt.

Lemma quux (Γ Γ' : Env) (i : Ix) {τ : Ty} :
  ⟪ Γ ≗≗ Γ' ⟫ →
  ⟪ i : τ r∈ Γ ⟫ →
  exists τ', ⟪ τ ≗ τ' ⟫ ∧ ⟪ i : τ' r∈ Γ' ⟫.
Proof.
  intro enveq.
  revert i.
  revert τ.
  induction enveq.
  - inversion 1.
  - destruct i.
    + intros.
      inversion H0; subst.
      exists τ'. repeat split.
      assumption. constructor.
    + intros.
      inversion H0; subst.
      destruct (IHenveq τ0 i H5) as (? & ? & ?).
      exists x; split. assumption.
      constructor.
      assumption.
Qed.

(* Lemma barbaz {Γ t τ} : ContrEnv Γ → ⟪ Γ e⊢ t : τ ⟫ → SimpleContr τ. *)
(* Proof. *)
(*   intros contr_env ty. *)
(*   revert ty contr_env. *)
(*   induction 0. *)
(*   - intros. *)
(*     dependent destruction ty; try contradiction. *)
(*     + exact (ty_in_env_implies_contr_ty contr_env H). *)
(*     +  *)


(* Contr Vs Rec *)
Lemma eqctx_implies_eqty (Γ Γ' : Env) (τ : Ty) (t : Tm) :
  ⟪ Γ ≗≗ Γ' ⟫ →
  ValidEnv Γ ->
  ValidEnv Γ' ->
  ⟪ Γ e⊢ t : τ ⟫ →
  ⟪ Γ' e⊢ t : τ ⟫.
Proof.
  intros env_eq Γ_valid Γ'_valid ty.
  revert Γ' Γ_valid Γ'_valid env_eq.
  induction ty; try (constructor; fail); intros; eauto with wt.
  - destruct (quux _ _ _ env_eq H) as (T' & tyeq & ?).
    apply tyeq_symm in tyeq.
    apply (WtEq _ tyeq); eauto with wt.
  - constructor; try assumption.
    apply IHty; eauto with wt tyeq tyvalid.
  - econstructor; eauto with wt tyeq tyvalid.
Qed.

Reserved Notation "⟪ e⊢ C : Γ₀ , τ₀ → Γ , τ ⟫"
  (at level 0, C at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  e⊢  C  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
Inductive PCtxTyping (Γ₀: Env) (τ₀: Ty) : Env → PCtx → Ty → Prop :=
  | WtPHole :
      ⟪ e⊢ phole : Γ₀, τ₀ → Γ₀, τ₀ ⟫
  | WtPAbs {Γ C τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, τ₂ ⟫ →
      ValidTy τ₁ ->
      ⟪ e⊢ pabs τ₁ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
  | WtPAppl {Γ C t₂ τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ →
      ⟪ Γ e⊢ t₂ : τ₁ ⟫ →
      ⟪ e⊢ papp₁ C t₂ : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPAppr {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ e⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ e⊢ papp₂ t₁ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPIteI {Γ C t₂ t₃ T} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ , tbool ⟫ →
      ⟪ Γ e⊢ t₂ : T ⟫ →
      ⟪ Γ e⊢ t₃ : T ⟫ →
      ⟪ e⊢ pite₁ C t₂ t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | WtPIteT {Γ t₁ C t₃ T} :
      ⟪ Γ e⊢ t₁ : tbool ⟫ →
      ⟪ e⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ Γ e⊢ t₃ : T ⟫ →
      ⟪ e⊢ pite₂ t₁ C t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | WtPIteE {Γ t₁ t₂ C T} :
      ⟪ Γ e⊢ t₁ : tbool ⟫ →
      ⟪ Γ e⊢ t₂ : T ⟫ →
      ⟪ e⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ e⊢ pite₃ t₁ t₂ C : Γ₀ , τ₀ → Γ , T ⟫
  | WtPPair₁ {Γ C t₂ τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ Γ e⊢ t₂ : τ₂ ⟫ →
      ⟪ e⊢ ppair₁ C t₂ : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | WtPPair₂ {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ e⊢ t₁ : τ₁ ⟫ →
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ e⊢ ppair₂ t₁ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | WtPProj₁ {Γ C τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ e⊢ pproj₁ C : Γ₀, τ₀ → Γ, τ₁ ⟫
  | WtPProj₂ {Γ C τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ e⊢ pproj₂ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPInl {Γ C τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ValidTy τ₂ ->
      ⟪ e⊢ pinl C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | WtPInr {Γ C τ₁ τ₂} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ValidTy τ₁ ->
      ⟪ e⊢ pinr C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | WtPCaseof₁ {Γ C t₂ t₃ τ₁ τ₂ T} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ e⊢ t₂ : T ⟫ →
      ⟪ Γ r▻ τ₂ e⊢ t₃ : T ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ e⊢ pcaseof₁ C t₂ t₃ : Γ₀, τ₀ → Γ, T ⟫
  | WtPCaseof₂ {Γ t₁ C t₃ τ₁ τ₂ T} :
      ⟪ Γ e⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ e⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, T ⟫ →
      ⟪ Γ r▻ τ₂ e⊢ t₃ : T ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ e⊢ pcaseof₂ t₁ C t₃ : Γ₀, τ₀ → Γ, T ⟫
  | WtPCaseof₃ {Γ t₁ t₂ C τ₁ τ₂ T} :
      ⟪ Γ e⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ e⊢ t₂ : T ⟫ →
      ⟪ e⊢ C : Γ₀, τ₀ → Γ r▻ τ₂, T ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ e⊢ pcaseof₃ t₁ t₂ C : Γ₀, τ₀ → Γ, T ⟫
  | WtPSeq₁ {Γ C t₂ T} :
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, tunit ⟫ →
      ⟪ Γ e⊢ t₂ : T ⟫ →
      ⟪ e⊢ pseq₁ C t₂ : Γ₀, τ₀ → Γ, T ⟫
  | WtPSeq₂ {Γ C t₁ T} :
      ⟪ Γ e⊢ t₁ : tunit ⟫ →
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ⟪ e⊢ pseq₂ t₁ C : Γ₀, τ₀ → Γ, T ⟫
  | WtPEq {Γ C T U} :
      ⟪ T ≗ U ⟫ →
      ValidTy T ->
      ValidTy U ->
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ⟪ e⊢ C : Γ₀, τ₀ → Γ, U ⟫
where "⟪ e⊢ C : Γ₀ , τ₀ → Γ , τ ⟫" := (PCtxTyping Γ₀ τ₀ Γ C τ).

Lemma pctxtyping_app {Γ₀ t₀ τ₀ Γ C τ} :
  ⟪ Γ₀ e⊢ t₀ : τ₀ ⟫ → ⟪ e⊢ C : Γ₀, τ₀ → Γ , τ ⟫ → ⟪ Γ e⊢ pctx_app t₀ C : τ ⟫.
Proof.
  intros wt₀ wC;
  induction wC; cbn; subst; eauto using Typing.
Qed.

Lemma pctxtyping_cat {Γ₀ τ₀ C₁ Γ₁ τ₁ C₂ Γ₂ τ₂} :
  ⟪ e⊢ C₁ : Γ₀, τ₀ → Γ₁ , τ₁ ⟫ →
  ⟪ e⊢ C₂ : Γ₁, τ₁ → Γ₂ , τ₂ ⟫ →
  ⟪ e⊢ pctx_cat C₁ C₂ : Γ₀, τ₀ → Γ₂ , τ₂ ⟫.
Proof.
  intros wC₁ wC₂.
  induction wC₂; cbn; eauto using PCtxTyping.
Qed.

Definition WtSub (Γ₁ Γ₂: Env) (ζ: Sub Tm) : Prop :=
  ∀ i T, ⟪ i : T r∈ Γ₁ ⟫ → ⟪ Γ₂ e⊢ (ζ i) : T ⟫.
