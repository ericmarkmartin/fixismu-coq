Require Export LogRelIE.PseudoType.
Require Export LogRelIE.InstPTy.
Require Export RecTypes.Contraction.
Require Export LogRelIE.Contraction.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Max.
Require Import Coq.micromega.Lia.

Fixpoint pNumbFree (τ : PTy) : nat :=
  match τ with
  | ptunit => 0
  | ptbool => 0
  | ptprod τ1 τ2 => max (pNumbFree τ1) (pNumbFree τ2)
  | ptsum τ1 τ2 => max (pNumbFree τ1) (pNumbFree τ2)
  | ptarr τ1 τ2 => max (pNumbFree τ1) (pNumbFree τ2)
  | ptrec τ => pred (pNumbFree τ)
  | ptvar i => S i
  | pEmulDV n p τ => 0
  end.
Arguments pNumbFree !τ.

Lemma pNumbFree_sound τ : innerPClosed τ → ws (pNumbFree τ) τ.
Proof.
  induction τ; cbn; try constructor; dependent destruction H.
  - refine (WsPTy_mono _ (IHτ1 H)); lia.
  - refine (WsPTy_mono _ (IHτ2 H)); lia.
  - refine (WsPTy_mono _ (IHτ1 H)); lia.
  - refine (WsPTy_mono _ (IHτ2 H)); lia.
  - refine (WsPTy_mono _ (IHτ1 H)); lia.
  - refine (WsPTy_mono _ (IHτ2 H)); lia.
  - refine (WsPTy_mono _ (IHτ H)); lia.
  - induction i; constructor; assumption.
  - assumption.
Qed.

Definition pDecideClosed τ := match pNumbFree τ with
                             | 0 => B.true
                             | _ => B.false
                             end.

Arguments pDecideClosed /.
Lemma decidePClosed_sound {τ} : innerPClosed τ → Is_true (pDecideClosed τ) -> ⟨ 0 ⊢ τ ⟩.
Proof.
  unfold pDecideClosed, WsTy.
  remember (pNumbFree τ).
  destruct n; intuition.
  rewrite Heqn.
  now eapply pNumbFree_sound.
Qed.

Lemma pNumbFree_complete {τ n} : ⟨ n ⊢ τ ⟩ -> pNumbFree τ <= n.
Proof.
  induction 1; cbn; try lia.
  induction H; lia.
Qed.

Lemma pNumbFree_complete' {τ} : ⟨ 0 ⊢ τ ⟩ -> pNumbFree τ = 0.
Proof.
  intros cl.
  cut (pNumbFree τ <= 0).
  - lia.
  - now eapply pNumbFree_complete.
Qed.

Lemma pDecideClosed_complete {τ} : ⟨ 0 ⊢ τ ⟩ -> Is_true (pDecideClosed τ).
Proof.
  intros cτ.
  assert (nc := pNumbFree_complete cτ).
  assert (eq : pNumbFree τ = 0) by lia.
  unfold pDecideClosed.
  now rewrite eq.
Qed.

Inductive ClosedPEnv : PEnv → Prop :=
  | PEmptyClosed : ClosedPEnv pempty
  | VarPClosed {Γ τ} :
      ⟨ 0 ⊢ τ ⟩ →
      ClosedPEnv Γ →
      ClosedPEnv (Γ p▻ τ).

#[export]
Hint Constructors wsPTy : cty.
#[export]
Hint Constructors ClosedPEnv : cenv.

Definition ValidPTy : PTy -> Prop := fun τ => ⟨ 0 ⊢ τ ⟩ /\ SimplePContr τ.
Definition ValidPEnv : PEnv -> Prop := fun Γ => ClosedPEnv Γ /\ ContrPEnv Γ.

Lemma ValidPTy_SimplePContr {τ} : ValidPTy τ -> SimplePContr τ.
Proof.
  now destruct 1.
Qed.
#[export]
Hint Resolve ValidPTy_SimplePContr : simple_p_contr_rec.

Lemma ValidPEnv_nil : ValidPEnv pempty.
Proof.
  split; constructor; eauto.
Qed.
#[export]
Hint Resolve ValidPEnv_nil : ptyvalid.

Lemma ValidPEnv_cons {Γ τ} : ValidPEnv Γ -> ValidPTy τ -> ValidPEnv (Γ p▻ τ).
Proof.
  intros [env_cl env_contr] [ty_cl ty_contr].
  split; constructor; eauto.
Qed.
#[export]
Hint Resolve ValidPEnv_cons : ptyvalid.

Lemma ValidPEnv_invert_cons {Γ τ} : ValidPEnv (Γ p▻ τ) → ValidPEnv Γ ∧ ValidPTy τ.
Proof.
  intro vΓ.
  destruct vΓ as (closedΓ & contrΓ).
  inversion closedΓ; inversion contrΓ; subst.
  split; split; assumption.
Qed.

Lemma ValidPEnv_getevar {Γ i τ} : ValidPEnv Γ → ⟪ i : τ p∈ Γ ⟫ → ValidPTy τ.
Proof.
  revert Γ.
  induction i; intros Γ vΓ ev.
  - inversion ev; subst.
    destruct (ValidPEnv_invert_cons vΓ) as (_ & vτ).
    assumption.
  - inversion ev; subst.
    destruct (ValidPEnv_invert_cons vΓ) as (vΓ0 & _).
    apply (IHi Γ0 vΓ0 H1).
Qed.

Lemma ValidPTy_unfold_trec {τ} : ValidPTy (ptrec τ) -> ValidPTy (τ[beta1 (ptrec τ)]).
Proof.
  intros (clτ & crτ).
  inversion clτ; subst.
  split.
  - now eauto using (wsAp (X := PTy)), (wsSub_sub_beta1 (X := PTy)).
  - now eapply (SimplePContr_pUnfoldOnce (ptrec τ)).
Qed.
