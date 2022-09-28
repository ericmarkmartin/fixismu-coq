Require Import LogRelIE.InstPTy.
Require Import LogRelIE.PseudoTypeIE.

Require Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Module B := Coq.Init.Datatypes.

Require Import RecTypes.Contraction.

Require Import InstPTy.

Require Import Coq.micromega.Lia.

Inductive SimplePContr : PTy → Prop :=
  | SimpContrPUnit : SimplePContr ptunit
  | SimpContrPBool : SimplePContr ptbool
  | SimpContrPArrow {τ τ'} : SimplePRec τ → SimplePRec τ' → SimplePContr (ptarr τ τ')
  | SimpContrPSum {τ τ'} : SimplePRec τ → SimplePRec τ' → SimplePContr (ptsum τ τ')
  | SimpContrPProd {τ τ'} : SimplePRec τ → SimplePRec τ' → SimplePContr (ptprod τ τ')
  | SimpContrPRec {τ} : SimplePContr τ → SimplePContr (ptrec τ)
  | SimpContrPEmulDV {n p τ} : SimpleContr τ → SimplePContr (pEmulDV n p τ)
  with SimplePRec : PTy → Prop :=
  | SimplePAlpha {i} : SimplePRec (ptvar i)
  | SimplePRecContr {τ} : SimplePContr τ → SimplePRec τ.

Scheme simp_p_contr_mut_ind := Induction for SimplePContr Sort Prop
  with simp_p_rec_mut_ind := Induction for SimplePRec Sort Prop.

Combined Scheme simp_p_contr_comb_ind from simp_p_contr_mut_ind, simp_p_rec_mut_ind.

Hint Constructors SimplePContr : simple_p_contr_rec.
Hint Constructors SimplePRec : simple_p_contr_rec.

Definition pUnfoldOnce (τ : PTy) : PTy :=
  match τ with
    | ptrec τ => τ [(beta1 (ptrec τ))]
    | _ => τ
  end.

Fixpoint pUnfoldn (n : nat) (τ : PTy) :=
  match n with
    | 0 => τ
    | S n => pUnfoldn n (pUnfoldOnce τ)
  end.

Inductive ContrPEnv : PEnv → Prop :=
| ContrPEnvEmpty : ContrPEnv pempty
| ContrPEnvEvar {Γ τ} :
  ContrPEnv Γ →
  SimplePContr τ →
  ContrPEnv (Γ p▻ τ).

Definition SimplePContrSub ( ξ : Sub PTy) : Prop := forall i : Ix, SimplePContr (ξ i).
Definition SimplePRecSub ( ξ : Sub PTy) : Prop := forall i : Ix, SimplePRec (ξ i).

Lemma SimplePContrRec_ren :
  (forall τ (sτ : SimplePContr τ) (ξ : Sub Ix), SimplePContr τ[ξ]) /\
  (forall τ (sτ : SimplePRec τ) (ξ : Sub Ix), SimplePRec τ[ξ]).
Proof.
  apply simp_p_contr_comb_ind; cbn; intros;
    repeat change (apPTy ?ξ ?τ) with τ[ξ];
    constructor; auto.
Qed.

Corollary SimplePRec_wk {τ} : SimplePRec τ → SimplePRec τ[wk].
Proof. intros s. now apply SimplePContrRec_ren. Qed.

Lemma SimplePContrSub_implies_SimplePRecSub {ξ} : SimplePContrSub ξ → SimplePRecSub ξ.
Proof.
  unfold SimplePContrSub, SimplePRecSub.
  intros.
  specialize (H i).
  exact (SimplePRecContr H).
Qed.

Lemma SimplePRecSub_implies_SimplePRecSubUp {ξ} : SimplePRecSub ξ → SimplePRecSub (up ξ).
Proof.
  unfold SimplePRecSub.
  intros.

  destruct i; cbn.
  constructor.

  apply SimplePRec_wk.
  exact (H i).
Qed.

Lemma SimplePRecSub_implies_SimplePRec {τ ξ} : SimplePRec τ → SimplePRecSub ξ → SimplePRec τ[ξ].
Proof.
  intro H.
  Hint Constructors SimplePContr : contr.
  Hint Constructors SimplePRec : contr.
  apply (simp_p_rec_mut_ind
           (fun {τ} (_ : SimplePContr τ) => (forall ξ : Sub PTy, SimplePRecSub ξ → SimplePContr τ[ξ]))
           (fun {τ} (_ : SimplePRec τ) => (forall ξ : Sub PTy, SimplePRecSub ξ → SimplePRec τ[ξ]))); cbn; eauto with contr.

  intros.
  constructor.
  eauto using H0, SimplePRecSub_implies_SimplePRecSubUp.
Qed.

Lemma SimplePContrSub_implies_SimplePContr {τ ξ} : SimplePContr τ → SimplePRecSub ξ → SimplePContr τ[ξ].
  intro H.
  apply (simp_p_contr_mut_ind
           (fun {τ} (_ : SimplePContr τ) => (forall ξ : Sub PTy, SimplePRecSub ξ → SimplePContr τ[ξ]))
           (fun {τ} (_ : SimplePRec τ) => (forall ξ : Sub PTy, SimplePRecSub ξ → SimplePRec τ[ξ]))).
  cbn.
  constructor.

  intros.
  cbn.
  constructor.

  intros.
  cbn.
  constructor.
  apply H0.
  assumption.
  apply H1.
  assumption.

  intros.
  cbn.
  constructor.
  apply H0.
  assumption.
  apply H1.
  assumption.

  intros.
  cbn.
  constructor.
  apply H0.
  assumption.
  apply (H1 ξ0 H2).

  intros.
  cbn.
  constructor.
  apply (H0 ξ0↑).
  apply SimplePRecSub_implies_SimplePRecSubUp.
  assumption.

  intros.
  cbn.
  constructor.
  assumption.

  intros.
  cbn.
  exact (H0 i).

  intros.
  specialize (H0 ξ0).
  apply SimplePRecSub_implies_SimplePRec.
  apply SimplePRecContr.
  assumption.
  assumption.
  assumption.
Qed.

Lemma SimplePRecSub_beta {τ} : SimplePContr τ -> SimplePRecSub (beta1 τ).
Proof.
  intros srec i; cbn.
  destruct i; cbn; constructor; auto.
Qed.

Lemma punfold_preserves_contr {τ} : SimplePContr τ -> SimplePContr (τ [beta1 (ptrec τ)]).
Proof.
  eauto using SimplePContrSub_implies_SimplePContr, SimplePRecSub_beta, SimpContrPRec.
Qed.

Lemma SimplePContr_pUnfoldOnce (τ : PTy) : SimplePContr τ -> SimplePContr (pUnfoldOnce τ).
Proof.
  destruct τ; cbn; eauto with simple_p_contr_rec.
  intros contr.
  dependent destruction contr.
  eauto using punfold_preserves_contr.
Qed.

Hint Resolve SimplePContr_pUnfoldOnce : simple_p_contr_rec.

Lemma SimplePRec_pUnfoldOnce (τ : PTy) : SimplePRec τ -> SimplePRec (pUnfoldOnce τ).
Proof.
  destruct 1;
  eauto using SimplePRec, SimplePContr_pUnfoldOnce.
Qed.

Hint Resolve SimplePRec_pUnfoldOnce : simple_contr_rec.

Lemma SimplePRec_invert_arrow {τ σ} :
  SimplePRec (τ p⇒ σ) → SimplePRec τ ∧ SimplePRec σ.
Proof.
  intros carr.
  remember (τ p⇒ σ) as τ'.
  destruct carr; [inversion Heqτ'|].
  destruct H; inversion Heqτ'.
  now subst.
Qed.

Hint Resolve SimplePRec_invert_arrow : simple_contr_p_rec.

Lemma SimplePRec_invert_arrow_argty {τ σ} :
  SimplePRec (τ p⇒ σ) → SimplePRec τ.
Proof.
  eapply SimplePRec_invert_arrow.
Qed.

Hint Resolve SimplePRec_invert_arrow_argty : simple_contr_p_rec.

Lemma SimplePRec_invert_arrow_retty {τ σ} :
  SimplePRec (τ p⇒ σ) → SimplePRec σ.
Proof.
  eapply SimplePRec_invert_arrow.
Qed.

Hint Resolve SimplePRec_invert_arrow_retty : simple_contr_p_rec.

Fixpoint LMC_pty (τ : PTy) {struct τ} : nat :=
  match τ with
  | ptrec τ => S (LMC_pty τ)
  | _ => 0
  end.

Lemma LMC_ind_pty : forall (P : PTy -> Type),
    (forall τ, SimplePContr τ -> LMC_pty τ = 0 -> P τ) ->
    (forall n, (forall τ, SimplePContr τ -> LMC_pty τ = n -> P τ) -> (forall τ, SimplePContr τ -> LMC_pty τ = S n -> P τ)) ->
    forall τ, SimplePContr τ -> P τ.
Proof.
  intros P P0 Ps τ.
  remember (LMC_pty τ) as n.
  revert τ Heqn.
  induction n; eauto.
Qed.

Lemma decide_pmu (τ : PTy) : (exists τ', τ = ptrec τ') \/ LMC_pty τ = 0.
Proof.
  destruct τ; cbn; eauto.
Qed.

Lemma LMC_SimplePContr (τ : PTy) : SimplePContr τ → forall ξ, LMC_pty τ[ξ] = LMC_pty τ.
Proof.
  induction τ; cbn; try lia.
  intros.
  f_equal.
  eapply IHτ.
  intros.
  inversion H.
  assumption.
  intros.
  exfalso.
  inversion H.
Qed.

Lemma LMC_pUnfoldOnce (τ : PTy) : SimplePContr τ → LMC_pty τ > 0 → LMC_pty (pUnfoldOnce τ) = pred (LMC_pty τ).
Proof.
  intros.
  destruct (decide_pmu τ) as [(τ' & ?) | ?]; [| lia].
  subst. cbn. pose proof (LMC_SimplePContr τ').
  assert (SimplePContr τ') by (inversion H; assumption).
  specialize (H1 H2 (beta1 (ptrec τ'))).
  rewrite H1.
  lia.
Qed.

Lemma pUnfoldn_dec_lmc (τ : PTy) (n : nat) : SimplePContr τ → LMC_pty τ >= n → LMC_pty (pUnfoldn n τ) = LMC_pty τ - n.
Proof.
  revert τ; induction n; intros.
  - cbn; lia.
  - cbn.
    replace (LMC_pty τ - S n) with (LMC_pty (pUnfoldOnce τ) - n).
    eapply IHn.
    + eauto with simple_p_contr_rec.
    + rewrite LMC_pUnfoldOnce; try lia.
      assumption.
    + rewrite LMC_pUnfoldOnce; try lia.
      assumption.
Qed.

Lemma pUnfoldn_LMC {τ} : SimplePContr τ -> LMC_pty (pUnfoldn (LMC_pty τ) τ) = 0.
Proof.
  intros contrτ.
  replace 0 with (LMC_pty τ - LMC_pty τ) by lia.
  eapply pUnfoldn_dec_lmc.
  - assumption.
  - lia.
Qed.

Lemma pUnfoldn_LMC_rec {τ} : SimplePRec τ -> LMC_pty (pUnfoldn (LMC_pty τ) τ) = 0.
Proof.
  destruct 1.
  - now cbn.
  - now eapply pUnfoldn_LMC.
Qed.
