Require Export RecTypes.InstTy.
Require Export RecTypes.SpecTypes.

Require Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Module B := Coq.Init.Datatypes.

Require Import Lia.

Fixpoint LMC (τ : Ty) {struct τ} : nat :=
  match τ with
  | trec τ => S (LMC τ)
  | _ => 0
  end.

Inductive SimpleContr : Ty → Prop :=
| SimpContrUnit : SimpleContr tunit
| SimpContrBool : SimpleContr tbool
| SimpContrArrow {τ τ'} : SimpleRec τ → SimpleRec τ' → SimpleContr (τ r⇒ τ')
| SimpContrSum {τ τ'} : SimpleRec τ → SimpleRec τ' → SimpleContr (τ r⊎ τ')
| SimpContrProd {τ τ'} : SimpleRec τ → SimpleRec τ' → SimpleContr (τ r× τ')
| SimpContrRec {τ} : SimpleContr τ → SimpleContr (trec τ)
with SimpleRec : Ty → Prop :=
| SimpleAlpha {i} : SimpleRec (tvar i)
| SimpleRecContr {τ} : SimpleContr τ → SimpleRec τ.

Scheme simp_contr_mut_ind := Induction for SimpleContr Sort Prop
  with simp_rec_mut_ind := Induction for SimpleRec Sort Prop.

Combined Scheme simp_contr_comb_ind from simp_contr_mut_ind, simp_rec_mut_ind.



Hint Constructors SimpleContr : simple_contr_rec.
Hint Constructors SimpleRec : simple_contr_rec.

Definition unfoldOnce (τ : Ty) : Ty :=
  match τ with
    | trec τ => τ [ (beta1 (trec τ))]
    | _ => τ
  end.
Fixpoint unfoldn (n : nat) (τ : Ty) : Ty :=
  match n with
    | 0 => τ
    | S n => unfoldn n (unfoldOnce τ)
  end.

Lemma LMC_ind : forall (P : Ty -> Prop),
    (forall τ, SimpleContr τ -> LMC τ = 0 -> P τ) ->
    (forall n, (forall τ, SimpleContr τ -> LMC τ = n -> P τ) -> (forall τ, SimpleContr τ -> LMC τ = S n -> P τ)) ->
    forall τ, SimpleContr τ -> P τ.
Proof.
  intros P P0 Ps τ.
  remember (LMC τ) as n.
  revert τ Heqn.
  induction n; eauto.
Qed.

Lemma LMC_ind' : forall (Pc : forall {τ : Ty}, SimpleContr τ -> Prop) (Pr : forall {τ : Ty}, SimpleRec τ -> Prop),
    (forall {τ} (sc : SimpleContr τ), LMC τ = 0 -> Pc sc) ->
    (forall {τ} (sr : SimpleRec τ), LMC τ = 0 -> Pr sr) ->
    (forall n, (forall {τ} (sc : SimpleContr τ), LMC τ = n -> Pc sc) -> (forall {τ} (sc : SimpleContr τ), LMC τ = S n -> Pc sc)) ->
    (forall n, (forall {τ} (sr : SimpleRec τ), LMC τ = n -> Pr sr) -> (forall {τ} (sr : SimpleRec τ), LMC τ = S n -> Pr sr)) ->
    forall {τ}, (forall (sc : SimpleContr τ), Pc sc) /\ (forall (sr : SimpleRec τ), Pr sr).
Proof.
  intros Pc Pr Pc0 Pr0 Pcs Prs τ.
  remember (LMC τ) as n.
  revert τ Heqn.
  induction n.
  - intros τ eq0.
    split; eauto using Pc0, Pr0.
  - intros τ eqsn.
    split.
    + intros contr.
      eapply (Pcs n); eauto.
      intros τ0 contr0 eqn.
      refine (proj1 (IHn τ0 _) contr0); auto.
    + intros rec.
      eapply (Prs n); eauto.
      intros τ0 contr0 eqn.
      refine (proj2 (IHn τ0 _) contr0); auto.
Qed.

Lemma LMC_ind'' : forall (Pc : forall {τ : Ty}, SimpleContr τ -> Prop) (Pr : forall {τ : Ty}, SimpleRec τ -> Prop),
    (forall n, (forall {τ} (sc : SimpleContr τ), LMC τ < n -> Pc sc) -> (forall {τ} (sc : SimpleContr τ), LMC τ = n -> Pc sc)) ->
    (forall n, (forall {τ} (sr : SimpleRec τ), LMC τ < n -> Pr sr) -> (forall {τ} (sr : SimpleRec τ), LMC τ = n -> Pr sr)) ->
    forall {τ}, (forall (sc : SimpleContr τ), Pc sc) /\ (forall (sr : SimpleRec τ), Pr sr).
Proof.
  intros Pc Pr Hc Hr.
  cut (forall {n} {τ}, LMC τ <= n -> (forall (sc : SimpleContr τ), Pc _ sc) /\ (forall (sr : SimpleRec τ), Pr _ sr)).
  - intros H τ.
    eapply (H (LMC τ)); lia.
  - intros n.
    induction n.
    + intros τ eq.
      split.
      * intros sc.
        eapply (Hc 0); lia.
      * intros sr.
        eapply (Hr 0); lia.
    + intros τ eq.
      destruct (PeanoNat.Nat.eq_dec (LMC τ) (S n)) as [eqLt|eqLt].
      * split.
        intros sc.
        eapply (Hc (S n)); try lia.
        intros τ' sc' ineq.
        eapply IHn; lia.
        intros sr.
        eapply (Hr (S n)); try lia.
        intros τ' sc' ineq.
        eapply IHn; lia.
      * eapply IHn; lia.
Qed.

Definition SimpleContrSub (ξ : Sub Ty) : Prop := forall i : Ix, SimpleContr (ξ i).
Definition SimpleRecSub (ξ : Sub Ty) : Prop := forall i : Ix, SimpleRec (ξ i).

Lemma SimpleContrRec_ren :
  (forall τ (sτ : SimpleContr τ) (ξ : Sub Ix), SimpleContr τ[ξ]) /\
  (forall τ (sτ : SimpleRec τ) (ξ : Sub Ix), SimpleRec τ[ξ]).
Proof.
  apply simp_contr_comb_ind; cbn; intros;
    repeat change (apTy ?ξ ?τ) with τ[ξ];
    constructor; auto.
Qed.

Corollary SimpleRec_wk {τ} : SimpleRec τ → SimpleRec τ[wk].
Proof. intros s. now apply SimpleContrRec_ren. Qed.

Corollary SimpleContr_wk {τ} : SimpleContr τ → SimpleContr τ[wk].
Proof. intros s. now apply SimpleContrRec_ren. Qed.

Lemma SimpleContrSub_implies_SimpleRecSub {ξ} : SimpleContrSub ξ → SimpleRecSub ξ.
Proof.
  unfold SimpleContrSub, SimpleRecSub.
  intros.
  specialize (H i).
  exact (SimpleRecContr H).
Qed.

Lemma SimpleRecSub_implies_SimpleRecSubUp {ξ} : SimpleRecSub ξ → SimpleRecSub (up ξ).
Proof.
  unfold SimpleRecSub.
  intros.

  destruct i; cbn.
  constructor.

  apply SimpleRec_wk.
  exact (H i).
Qed.

Lemma SimpleRecSub_implies_SimpleRec {τ ξ} : SimpleRec τ → SimpleRecSub ξ → SimpleRec τ[ξ].
Proof.
  intro H.
  Hint Constructors SimpleContr : contr.
  Hint Constructors SimpleRec : contr.
  apply (simp_rec_mut_ind
           (fun {τ} (_ : SimpleContr τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleContr τ[ξ]))
           (fun {τ} (_ : SimpleRec τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleRec τ[ξ]))); cbn; eauto with contr.

  intros.
  constructor.
  eauto using H0, SimpleRecSub_implies_SimpleRecSubUp.
Qed.

Lemma SimpleContrSub_implies_SimpleContr {τ ξ} : SimpleContr τ → SimpleRecSub ξ → SimpleContr τ[ξ].
  intro H.
  apply (simp_contr_mut_ind
           (fun {τ} (_ : SimpleContr τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleContr τ[ξ]))
           (fun {τ} (_ : SimpleRec τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleRec τ[ξ]))).
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
  apply SimpleRecSub_implies_SimpleRecSubUp.
  assumption.

  intros.
  cbn.
  exact (H0 i).

  intros.
  specialize (H0 ξ0).
  apply SimpleRecSub_implies_SimpleRec.
  apply SimpleRecContr.
  assumption.
  assumption.
  assumption.
Qed.

Lemma SimpleRecSub_beta {τ} : SimpleContr τ -> SimpleRecSub (beta1 τ).
Proof.
  intros srec i; cbn.
  destruct i; cbn; constructor; auto.
Qed.

Lemma unfold_preserves_contr {τ} : SimpleContr τ -> SimpleContr (τ [beta1 (trec τ)]).
Proof.
  eauto using SimpleContrSub_implies_SimpleContr, SimpleRecSub_beta, SimpContrRec.
Qed.

Lemma SimpleContr_unfoldOnce (τ : Ty) : SimpleContr τ -> SimpleContr (unfoldOnce τ).
Proof.
  destruct τ; cbn; eauto with simple_contr_rec.
  intros contr.
  dependent destruction contr.
  eauto using unfold_preserves_contr.
Qed.

Hint Resolve SimpleContr_unfoldOnce : simple_contr_rec.

(* Lemma unfold_preserves_contr_conv {τ} : SimpleContr (τ [beta1 (trec τ)]) → SimpleContr τ. *)
(* Proof. *)
(*   revert τ. *)
(*   induction 1 using LMC_ind. *)
(*   induction τ; cbn; eauto with simple_contr_rec. *)
(*   intros contr. *)
(*   eauto using SimpleContrSub_implies_SimpleContr, SimpleRecSub_beta, SimpContrRec. *)
(* Qed. *)

(* Lemma SimpleContr_invert_unfoldOnce (τ : Ty) : SimpleContr (unfoldOnce τ) → SimpleContr τ. *)
(* Proof. *)
(*   induction τ; cbn; eauto with simple_contr_rec. *)
(*   intros contr. *)
(*   constructor. *)
(*   apply SimpleContrSub_implies_SimpleContr. *)
(*   cbn in contr. *)
(*   dependent induction τ; cbn in contr; change (apTy ?ξ ?τ) with τ[ξ] in *. *)
(*   - inversion contr; subst. intuition. *)
(*     repeat constructor. *)
(*   -  *)
(*   cbn in contr. *)

Lemma SimpleRec_unfoldOnce (τ : Ty) : SimpleRec τ -> SimpleRec (unfoldOnce τ).
Proof.
  destruct 1;
  eauto using SimpleRec, SimpleContr_unfoldOnce.
Qed.

Hint Resolve SimpleRec_unfoldOnce : simple_contr_rec.

Lemma SimpleContr_unfoldn (τ : Ty) (n : nat) : SimpleContr τ -> SimpleContr (unfoldn n τ).
Proof.
  revert τ; induction n; cbn; eauto with simple_contr_rec.
Qed.

Lemma unfoldn_tunit {n} : unfoldn n tunit = tunit.
Proof.
  induction n.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma unfoldn_tbool {n} : unfoldn n tbool = tbool.
Proof.
  induction n.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma unfoldn_tarr {n τ σ} : unfoldn n (tarr σ τ)
 = tarr σ τ.
Proof.
  induction n.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma unfoldn_tprod {n τ σ} : unfoldn n (tprod σ τ) = tprod σ τ.
Proof.
  induction n.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma unfoldn_tsum {n τ σ} : unfoldn n (tsum σ τ) = tsum σ τ.
Proof.
  induction n.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma unfoldn_tvar {n i} : unfoldn n (tvar i) = tvar i.
Proof.
  induction n.
  - now cbn.
  - cbn. now rewrite IHn.
Qed.

Lemma SimpleRec_unfoldn (τ : Ty) (n : nat) : SimpleRec τ -> SimpleRec (unfoldn n τ).
Proof.
  destruct 1.
  - rewrite unfoldn_tvar.
    eauto with simple_contr_rec.
  - constructor.
    now eapply SimpleContr_unfoldn.
Qed.

Hint Resolve SimpleRec_unfoldn : simple_contr_rec.

Lemma SimpleRec_invert_arrow {τ σ} :
  SimpleRec (tarr τ σ) -> SimpleRec τ * SimpleRec σ.
Proof.
  intros carr.
  remember (tarr τ σ) as τ'.
  destruct carr; [inversion Heqτ'|].
  destruct H; inversion Heqτ'.
  now subst.
Qed.

Lemma SimpleRec_invert_arrow_1 {τ σ} :
  SimpleRec (tarr τ σ) -> SimpleRec τ.
Proof.
  eapply SimpleRec_invert_arrow.
Qed.

Hint Resolve SimpleRec_invert_arrow_1 : simple_contr_rec.

Lemma SimpleRec_invert_arrow_2 {τ σ} :
  SimpleRec (tarr τ σ) -> SimpleRec σ.
Proof.
  eapply SimpleRec_invert_arrow.
Qed.

Hint Resolve SimpleRec_invert_arrow_2 : simple_contr_rec.

Lemma SimpleRec_invert_prod {τ σ} :
  SimpleRec (tprod τ σ) -> SimpleRec τ * SimpleRec σ.
Proof.
  intros carr.
  remember (tprod τ σ) as τ'.
  destruct carr; [inversion Heqτ'|].
  destruct H; inversion Heqτ'.
  now subst.
Qed.

Lemma SimpleRec_invert_prod_1 {τ σ} :
  SimpleRec (tprod τ σ) -> SimpleRec τ.
Proof.
  eapply SimpleRec_invert_prod.
Qed.

Hint Resolve SimpleRec_invert_prod_1 : simple_contr_rec.

Lemma SimpleRec_invert_prod_2 {τ σ} :
  SimpleRec (tprod τ σ) -> SimpleRec σ.
Proof.
  eapply SimpleRec_invert_prod.
Qed.

Hint Resolve SimpleRec_invert_prod_2 : simple_contr_rec.

Lemma SimpleRec_invert_sum {τ σ} :
  SimpleRec (tsum τ σ) -> SimpleRec τ * SimpleRec σ.
Proof.
  intros carr.
  remember (tsum τ σ) as τ'.
  destruct carr; [inversion Heqτ'|].
  destruct H; inversion Heqτ'.
  now subst.
Qed.

Lemma SimpleRec_invert_sum_1 {τ σ} :
  SimpleRec (tsum τ σ) -> SimpleRec τ.
Proof.
  eapply SimpleRec_invert_sum.
Qed.

Hint Resolve SimpleRec_invert_sum_1 : simple_contr_rec.

Lemma SimpleRec_invert_sum_2 {τ σ} :
  SimpleRec (tsum τ σ) -> SimpleRec σ.
Proof.
  eapply SimpleRec_invert_sum.
Qed.

Hint Resolve SimpleRec_invert_sum_2 : simple_contr_rec.

Lemma SimpleRec_invert_trec {τ} :
  SimpleRec (trec τ) -> SimpleRec (τ [beta1 (trec τ)]).
Proof.
  eapply SimpleRec_unfoldOnce.
Qed.

Hint Resolve SimpleRec_invert_trec : simple_contr_rec.


Reserved Notation "⟪ τ ≗ τ' ⟫"
  (at level 0, τ at level 98, τ' at level 98).
CoInductive Tyeq : Ty → Ty → Prop :=
| EqPrim : ⟪ tunit ≗ tunit ⟫
| EqBool : ⟪ tbool ≗ tbool ⟫
| EqArr {τ τ' σ σ'} :
    ⟪ τ ≗ σ ⟫ →
    ⟪ τ' ≗ σ' ⟫ →
    ⟪ tarr τ τ' ≗ tarr σ σ' ⟫
| EqSum {τ τ' σ σ'} :
    ⟪ τ ≗ σ ⟫ →
    ⟪ τ' ≗ σ' ⟫ →
    ⟪ τ r⊎ τ' ≗ σ r⊎ σ' ⟫
| EqProd {τ τ' σ σ'} :
    ⟪ τ ≗ σ ⟫ →
    ⟪ τ' ≗ σ' ⟫ →
    ⟪ τ r× τ' ≗ σ r× σ' ⟫
| EqVar {i} :
    ⟪ tvar i ≗ tvar i ⟫
| EqMuL {τ σ} :
    (* ⟪ fu' τ ≗ σ ⟫ → *)
    ⟪ τ[beta1 (trec τ)] ≗ σ ⟫ →
    (* SimpleContr τ → *)
    ⟪ trec τ ≗ σ ⟫
| EqMuR {τ σ} :
    (* LMC τ = 0 → *)
    (* SimpleContr σ → *)
    ⟪ τ ≗ σ[beta1 (trec σ)] ⟫ →
    ⟪ τ ≗ trec σ ⟫
where "⟪ τ ≗ τ' ⟫" := (Tyeq τ τ').

Hint Constructors Tyeq : tyeq.


Inductive ContrEnv : Env → Prop :=
| ContrEnvEmpty : ContrEnv empty
| ContrEnvEvar {Γ τ} :
  ContrEnv Γ →
  SimpleContr τ →
  ContrEnv (Γ r▻ τ).

Reserved Notation "⟪ Γ ≗≗ Γ' ⟫"
  (at level 0, Γ at level 98, Γ' at level 98).
Inductive TyeqEnv : Env → Env → Prop :=
| TyeqEnvEmpty : ⟪ empty ≗≗ empty ⟫
| TyeqEnvEvar {Γ Γ' τ τ'} :
  ⟪ τ ≗ τ' ⟫ →
  ⟪ Γ ≗≗ Γ' ⟫ →
  ⟪ Γ r▻ τ ≗≗ Γ' r▻ τ' ⟫
where "⟪ Γ ≗≗ Γ' ⟫" := (TyeqEnv Γ Γ').

Hint Constructors TyeqEnv : tyeq.


Lemma decide_mu (τ : Ty) : (exists τ', τ = trec τ') \/ LMC τ = 0.
Proof.
  destruct τ; cbn; eauto.
Qed.

(* CoFixpoint EqMuR' {τ σ} : *)
(*   SimpleContr σ → ⟪ τ ≗ σ[beta1 (trec σ)] ⟫ → ⟪ τ ≗ trec σ ⟫. *)
(* Proof. *)
(*   intros cσ eq. *)
(*   destruct (decide_mu τ) as [[τ' ->]|eq']. *)
(*   - dependent destruction eq. *)
(*   eapply EqMuL; try assumption. *)
(*   eapply EqMuR'; try assumption. *)

Lemma LMC_SimpleContr (τ : Ty) : SimpleContr τ → forall ξ, LMC τ[ξ] = LMC τ.
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

Lemma LMC_unfoldOnce (τ : Ty) : SimpleContr τ → LMC τ > 0 → LMC (unfoldOnce τ) = pred (LMC τ).
Proof.
  intros.
  destruct (decide_mu τ) as [(τ' & ?) | ?]; [| lia].
  subst. cbn. pose proof (LMC_SimpleContr τ').
  assert (SimpleContr τ') by (inversion H; assumption).
  specialize (H1 H2 (beta1 (trec τ'))).
  rewrite H1.
  lia.
Qed.


Lemma foo (τ : Ty) (n : nat) : SimpleContr τ → LMC τ >= n → LMC (unfoldn n τ) = LMC τ - n.
Proof.
  revert τ; induction n; intros.
  - cbn; lia.
  - cbn.
    replace (LMC τ - S n) with (LMC (unfoldOnce τ) - n).
    eapply IHn.
    + eauto with simple_contr_rec.
    + rewrite LMC_unfoldOnce; try lia.
      assumption.
    + rewrite LMC_unfoldOnce; try lia.
      assumption.
Qed.
(*     specialize (IHn (unfoldOnce τ)). *)
(*     pose proof (LMC_unfoldOnce (unfoldn n τ) (SimpleContr_unfoldn τ n H)). *)
(*     assert (LMC τ >= n) by lia. *)
(*     specialize (IHn H H2). *)
(*     rewrite IHn in H1. *)
(*     assert (LMC τ - n > 0) by lia. *)
(*     specialize (H1 H3). *)
(*     lia. *)
(* Qed. *)

Lemma unfoldn_LMC {τ} : SimpleContr τ -> LMC (unfoldn (LMC τ) τ) = 0.
Proof.
  intros contrτ.
  replace 0 with (LMC τ - LMC τ) by lia.
  eapply foo.
  - assumption.
  - lia.
Qed.

Lemma unfoldn_LMC_rec {τ} : SimpleRec τ -> LMC (unfoldn (LMC τ) τ) = 0.
Proof.
  destruct 1.
  - now cbn.
  - now eapply unfoldn_LMC.
Qed.


Lemma unfolding_ind : forall (P : Ty -> Prop),
    (forall τ, SimpleContr τ -> LMC τ = 0 -> P τ) ->
    (forall τ, SimpleContr τ -> P (τ [beta1 (trec τ)]) -> P (trec τ)) ->
    forall τ, SimpleContr τ -> P τ.
Proof.
  intros P P0 Ps τ contr.
  induction contr using LMC_ind.
  - eauto.
  - destruct contr; try inversion H0.
    eapply (Ps _ contr).
    eapply H.
    + eapply SimpleContrSub_implies_SimpleContr; try assumption.
      eapply SimpleRecSub_beta.
      constructor; assumption.
    + erewrite LMC_SimpleContr; auto.
Qed.



CoFixpoint tyeq_refl {τ} : ⟪ τ ≗ τ ⟫.
Proof.
  destruct τ; repeat constructor; eapply tyeq_refl.
Qed.
Hint Resolve tyeq_refl : tyeq.

(* Lemma eq_refl_itleft' {τ} (n : nat) : *)
(*        (forall n', n' < n -> exists τ', unfoldn n' τ = trec τ') -> *)
(*        0 < n -> *)
(*        SimpleContr τ -> *)
(*        SimpleContr (unfoldn n τ) -> ⟪ unfoldn n τ ≗ τ ⟫ *)
(* with eq_refl_itright' {τ} (n n' : nat) : *)
(*        SimpleContr τ -> SimpleContr (unfoldn n' τ) -> LMC (unfoldn n τ) = 0 -> *)
(*        (forall n', n' < n -> exists τ', unfoldn n' τ = trec τ') -> *)
(*        n' < n -> *)
(*        ⟪ unfoldn n τ ≗ unfoldn n' τ ⟫. *)
(* Proof. *)
(* Admitted. *)

Lemma bar'' (τ : Ty) : LMC τ = 0 → unfoldOnce τ = τ.
Proof.
  intros.
  destruct τ; cbn; trivial.
  cbn in H; lia.
Qed.

CoFixpoint bar' (τ σ : Ty) : SimpleContr τ → ⟪ τ ≗ σ ⟫ → ⟪ unfoldOnce τ ≗ σ ⟫.
Proof.
  intros.
  destruct (decide_mu τ) as [(τ' & ?) | ?].
  - subst; cbn.
    inversion H0.
    + assumption.
    + eapply EqMuR.
      now apply (bar' (trec τ')).
  - now rewrite (bar'' τ H1).
Qed.

Lemma ty_eq_unf_ty (τ σ : Ty) (n : nat) : SimpleContr τ → ⟪ τ ≗ σ ⟫ -> ⟪ unfoldn n τ ≗ σ ⟫.
Proof.
  (* induction n. *)
  revert τ.
  induction n; first [trivial].
  eauto using bar', eq_refl with simple_contr_rec.
Qed.

Lemma ty_eq_unfoldn (τ : Ty) (n : nat) : SimpleContr τ → ⟪ unfoldn n τ ≗ τ ⟫.
Proof.
  eauto using tyeq_refl, ty_eq_unf_ty.
Qed.

Lemma ty_eq_unfoldonce (τ : Ty) : SimpleContr τ → ⟪ unfoldOnce τ ≗ τ ⟫.
Proof.
  exact (ty_eq_unfoldn τ 1).
Qed.

Lemma ty_eq_unfoldrec (τ : Ty) : SimpleContr τ → ⟪ τ[beta1 (trec τ)] ≗ (trec τ) ⟫.
Proof.
  intros contr.
  apply (ty_eq_unfoldonce (trec τ)).
  constructor.
  exact contr.
Qed.

Lemma ty_eq_peel_recs (σ τ : Ty) (n : nat) : SimpleContr τ → ⟪ σ ≗ τ ⟫ -> ⟪ σ ≗ unfoldn n τ ⟫.
Proof.
  revert σ τ.
  induction n; first [trivial].
  cofix ty_eq_peel_recs.
  intros σ τ contrτ eq.
  destruct eq;
  rewrite ?unfoldn_tunit, ?unfoldn_tbool, ?unfoldn_tarr, ?unfoldn_tsum, ?unfoldn_tprod, ?unfoldn_tvar;
  try constructor; try assumption.
  - now eapply ty_eq_peel_recs.
  - eapply IHn;
    eauto with simple_contr_rec.
Qed.

Lemma ty_eq_peel_recs' (σ τ : Ty) (n : nat) : SimpleRec τ → ⟪ σ ≗ τ ⟫ -> ⟪ σ ≗ unfoldn n τ ⟫.
Proof.
  destruct 1.
  - now rewrite unfoldn_tvar.
  - now eapply ty_eq_peel_recs.
Qed.

Lemma ty_eq_peel_recs_left (σ τ : Ty) (n : nat) : SimpleContr σ → ⟪ σ ≗ τ ⟫ -> ⟪ unfoldn n σ ≗ τ ⟫.
Proof.
  revert σ τ.
  induction n; first [trivial].
  cofix ty_eq_peel_recs_left.
  intros σ τ contrτ eq.
  destruct eq;
  rewrite ?unfoldn_tunit, ?unfoldn_tbool, ?unfoldn_tarr, ?unfoldn_tsum, ?unfoldn_tprod, ?unfoldn_tvar;
  try constructor; try assumption.
  - eapply IHn;
   eauto with simple_contr_rec.
  - now eapply ty_eq_peel_recs_left.
Qed.

Lemma ty_eq_peel_recs_left' (σ τ : Ty) (n : nat) : SimpleRec σ → ⟪ σ ≗ τ ⟫ -> ⟪ unfoldn n σ ≗ τ ⟫.
Proof.
  destruct 1.
  - now rewrite unfoldn_tvar.
  - now eapply ty_eq_peel_recs_left.
Qed.

CoFixpoint tyeq_symm {τ σ} : ⟪ τ ≗ σ ⟫ → ⟪ σ ≗ τ ⟫.
Proof.
  intros eq.
  destruct eq;
    constructor;
    eauto using Tyeq.
Qed.

Local Ltac invert_impossible_eqs :=
  match goal with
  | H: tunit = tvar _ |- _ => inversion H
  | H: tunit = tarr _ _ |- _ => inversion H
  | H: tunit = tprod _ _ |- _ => inversion H
  | H: tunit = tsum _ _ |- _ => inversion H
  | H: tunit = trec _ |- _ => inversion H
  | H: tbool = tvar _ |- _ => inversion H
  | H: tbool = tarr _ _ |- _ => inversion H
  | H: tbool = tprod _ _ |- _ => inversion H
  | H: tbool = tsum _ _ |- _ => inversion H
  | H: tbool = trec _ |- _ => inversion H
  | H: tarr _ _ = tunit |- _ => inversion H
  | H: tarr _ _ = tbool |- _ => inversion H
  | H: tarr _ _ = tvar _ |- _ => inversion H
  | H: tarr _ _ = tprod _ _ |- _ => inversion H
  | H: tarr _ _ = tsum _ _ |- _ => inversion H
  | H: tarr _ _ = trec _ |- _ => inversion H
  | H: tprod _ _ = tunit |- _ => inversion H
  | H: tprod _ _ = tbool |- _ => inversion H
  | H: tprod _ _ = tvar _ |- _ => inversion H
  | H: tprod _ _ = tarr _ _ |- _ => inversion H
  | H: tprod _ _ = tsum _ _ |- _ => inversion H
  | H: tprod _ _ = trec _ |- _ => inversion H
  | H: tsum _ _ = tunit |- _ => inversion H
  | H: tsum _ _ = tbool |- _ => inversion H
  | H: tsum _ _ = tvar _ |- _ => inversion H
  | H: tsum _ _ = tarr _ _ |- _ => inversion H
  | H: tsum _ _ = tprod _ _ |- _ => inversion H
  | H: tsum _ _ = trec _ |- _ => inversion H
  | H: trec _ = tunit |- _ => inversion H
  | H: trec _ = tbool |- _ => inversion H
  | H: trec _ = tvar _ |- _ => inversion H
  | H: trec _ = tarr _ _ |- _ => inversion H
  | H: trec _ = tprod _ _ |- _ => inversion H
  | H: trec _ = tsum _ _ |- _ => inversion H
  | H: tvar _ = tunit |- _ => inversion H
  | H: tvar _ = tbool |- _ => inversion H
  | H: tvar _ = tarr _ _ |- _ => inversion H
  | H: tvar _ = tprod _ _ |- _ => inversion H
  | H: tvar _ = tsum _ _ |- _ => inversion H
  | H: tvar _ = trec _ |- _ => inversion H
  | _ => idtac
  end.

CoFixpoint eq_trans_contr_0 {τ ρ} {σ1 σ2 : Ty} :
  SimpleRec σ1 ->
  LMC σ1 = 0 ->
  σ1 = σ2 -> ⟪ τ ≗ σ1 ⟫ → ⟪ σ2 ≗ ρ ⟫ → ⟪ τ ≗ ρ ⟫.
Proof.
  intros recσ eqLMC eqσ eq1 eq2.
  destruct eq1; destruct eq2; invert_impossible_eqs;
  match goal with
  | |- ⟪ trec _ ≗ _ ⟫ => eapply EqMuL
  | |- ⟪ _ ≗ trec _ ⟫ => eapply EqMuR
  | H: LMC (trec _) = 0 |- _ => inversion H
  | |- _ => try constructor
  end; try (inversion eqσ; subst; try assumption; constructor); try assumption.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (ty_eq_peel_recs' _ _ (LMC σ) _ eq1_1) _).
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eapply ty_eq_peel_recs_left'.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    now inversion eqσ; subst.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (ty_eq_peel_recs' _ _ (LMC σ') _ eq1_2) _).
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eapply ty_eq_peel_recs_left'.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    now inversion eqσ; subst.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (EqArr eq1_1 eq1_2) _); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (ty_eq_peel_recs' _ _ (LMC σ) _ eq1_1) _).
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eapply ty_eq_peel_recs_left'.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    now inversion eqσ; subst.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (ty_eq_peel_recs' _ _ (LMC σ') _ eq1_2) _).
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eapply ty_eq_peel_recs_left'.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    now inversion eqσ; subst.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (EqSum eq1_1 eq1_2) _); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (ty_eq_peel_recs' _ _ (LMC σ) _ eq1_1) _).
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eapply ty_eq_peel_recs_left'.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    now inversion eqσ; subst.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (ty_eq_peel_recs' _ _ (LMC σ') _ eq1_2) _).
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    eapply ty_eq_peel_recs_left'.
    eauto using unfoldn_LMC_rec with simple_contr_rec.
    now inversion eqσ; subst.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl (EqProd eq1_1 eq1_2) _); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl _ (EqArr eq2_1 eq2_2)); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl _ (EqSum eq2_1 eq2_2)); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl _ (EqProd eq2_1 eq2_2)); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl _ (EqMuL eq2)); subst; eauto with simple_contr_rec.
  - refine (eq_trans_contr_0 _ _ _ _ _ _ eq_refl eq1 eq2); subst; eauto with simple_contr_rec.
  - inversion eqLMC.
Qed.

Lemma eq_trans_rec_helper {τ ρ} {σ1 σ2 : Ty} :
  SimpleRec σ1 ->
  σ1 = σ2 -> ⟪ τ ≗ σ1 ⟫ → ⟪ σ2 ≗ ρ ⟫ → ⟪ τ ≗ ρ ⟫.
Proof.
  intros recσ1 eq eq1 eq2.
  refine (eq_trans_contr_0 _ _ _ (ty_eq_peel_recs' _ _ (LMC σ1) _ eq1) (ty_eq_peel_recs_left' _ _ (LMC σ2) _ eq2));
    subst;
  eauto using unfoldn_LMC_rec with simple_contr_rec.
Qed.

Lemma eq_trans_rec {τ σ ρ} :
  SimpleRec σ →
  ⟪ τ ≗ σ ⟫ → ⟪ σ ≗ ρ ⟫ → ⟪ τ ≗ ρ ⟫.
Proof.
  eauto using eq_trans_rec_helper with simple_contr_rec.
Qed.

Lemma eq_trans_contr {τ σ ρ} :
  SimpleContr σ →
  ⟪ τ ≗ σ ⟫ → ⟪ σ ≗ ρ ⟫ → ⟪ τ ≗ ρ ⟫.
Proof.
  eauto using eq_trans_rec with simple_contr_rec.
Qed.
(* Lemma eq_pres_contr_l' {τ σ} : ⟪ τ ≗ σ ⟫ → SimpleContr τ → SimpleContr σ *)
(* with eq_pres_rec_l' {τ σ} : ⟪ τ ≗ σ ⟫ → SimpleRec τ → SimpleRec σ. *)
(* Proof. *)
(*   - intros. *)
(*     dependent destruction H; try (constructor; fail). *)
(*     + inversion H1; subst; constructor. *)
(*       apply (eq_pres_rec_l' _ _ H H4). *)
(*       apply (eq_pres_rec_l' _ _ H0 H5). *)
(*     + inversion H1; subst; constructor. *)
(*       apply (eq_pres_rec_l' _ _ H H4). *)
(*       apply (eq_pres_rec_l' _ _ H0 H5). *)
(*     + inversion H1; subst; constructor. *)
(*       apply (eq_pres_rec_l' _ _ H H4). *)
(*       apply (eq_pres_rec_l' _ _ H0 H5). *)
(*     + inversion H0. *)
(*     + admit. *)
(*     + admit. *)
(*   - intros. *)
(*     dependent destruction H; try (constructor; constructor; fail). *)
(*     + inversion H1; inversion H2; subst; constructor; constructor. *)
(*       apply (eq_pres_rec_l' _ _ H H6). *)
(*       apply (eq_pres_rec_l' _ _ H0 H7). *)
(*     + inversion H1; inversion H2; subst; constructor; constructor. *)
(*       apply (eq_pres_rec_l' _ _ H H6). *)
(*       apply (eq_pres_rec_l' _ _ H0 H7). *)
(*     + inversion H1; inversion H2; subst; constructor; constructor. *)
(*       apply (eq_pres_rec_l' _ _ H H6). *)
(*       apply (eq_pres_rec_l' _ _ H0 H7). *)
(*     + admit. *)
(*     + admit. *)
(* Admitted. *)

(* (*   induction H. *) *)
(* (*   try assumption. *) *)
(* (* Admitted. *) *)


(* Lemma eq_pres_contr_l {τ σ} : ⟪ τ ≗ σ ⟫ → SimpleContr σ → SimpleContr τ. *)
(* Proof. *)
(* Admitted. *)

(* Lemma eq_pres_contr_r {τ σ} : ⟪ τ ≗ σ ⟫ → SimpleContr σ → SimpleContr τ. *)
(* Proof. *)
(* Admitted. *)

(* Lemma eq_trans_contr {τ ρ} {σ1 σ2 : Ty} : *)
(*   SimpleRec σ1 -> *)
(*   σ1 = σ2 -> ⟪ τ ≗ σ1 ⟫ → ⟪ σ2 ≗ ρ ⟫ → ⟪ τ ≗ ρ ⟫. *)
(* Proof. *)
(*   remember (LMC σ1) as n. *)
(*   revert Heqn. *)
(*   eapply (lt_wf_ind n (fun n => forall τ ρ σ1 σ2, n = LMC σ1  → SimpleRec σ1 -> σ1 = σ2 → ⟪ τ ≗ σ1 ⟫ → ⟪ σ2 ≗ ρ ⟫ → ⟪ τ ≗ ρ ⟫)). *)
(*   clear n τ ρ σ1 σ2. *)
(*   cofix eq_trans_contr. *)
(*   intros n IHn τ ρ σ1 σ2. *)
(*   intros eqn recσ eqσ eq1 eq2. *)
(*   destruct eq1; destruct eq2; invert_impossible_eqs; *)
(*   match goal with *)
(*   | |- ⟪ trec _ ≗ _ ⟫ => eapply EqMuL *)
(*   | |- ⟪ _ ≗ trec _ ⟫ => eapply EqMuR *)
(*   | |- _ => try constructor *)
(*   end; try (inversion eqσ; subst; try assumption; constructor); try assumption. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq_refl _ _ eq1_1 _); inversion eqσ; subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1_2 _); inversion eqσ; subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ (EqArr eq1_1 eq1_2) _); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1_1 _); inversion eqσ; subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1_2 _); inversion eqσ; subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ (EqSum eq1_1 eq1_2) _); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1_1 _); inversion eqσ; subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1_2 _); inversion eqσ; subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ (EqProd eq1_1 eq1_2) _); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1 (EqArr eq2_1 eq2_2)); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1 (EqSum eq2_1 eq2_2)); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1 (EqProd eq2_1 eq2_2)); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1 (EqMuL eq2 H0)); subst; eauto with simple_contr_rec. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ eq1 eq2); subst; eauto with simple_contr_rec. *)
(*   - cbn in eqn. *)
(*     destruct n; inversion eqn as [eqn']. *)
(*     refine (IHn n _ _ _ _ _ _ _ _ eq1 eq2). *)
(*     + now lia. *)
(*     + transitivity (LMC σ); [assumption|symmetry]. *)
(*       transitivity (LMC (trec σ) - 1); [|cbn;lia]. *)
(*       eapply (LMC_unfoldOnce (trec σ)). *)
(*       eauto with simple_contr_rec. *)
(*       cbn; lia. *)
(*     + now eapply SimpleRec_invert_trec. *)
(*     + inversion eqσ; now subst. *)
(*   - refine (eq_trans_contr _ _ _ _ _ _ (EqMuR H eq1) eq2); eauto. *)
(* Qed. *)

(* Lemma eq_trans {τ τ' τ''} : ⟪ τ ≗ τ' ⟫ → ⟪ τ' ≗ τ'' ⟫ → ⟪ τ ≗ τ'' ⟫. Proof. Admitted. *)

(* CoFixpoint eq_refl_contr {τ} : SimpleContr τ → ⟪ τ ≗ τ ⟫ *)
(* with eq_refl_itleft' {τ} (n : nat) : *)
(*        (forall n', n' < n -> exists τ', unfoldn n' τ = trec τ') -> *)
(*        0 < n -> *)
(*        SimpleContr τ -> *)
(*        SimpleContr (unfoldn n τ) -> ⟪ unfoldn n τ ≗ τ ⟫ *)
(* with eq_refl_itright' {τ} (n n' : nat) : *)
(*        SimpleContr τ -> SimpleContr (unfoldn n' τ) -> LMC (unfoldn n τ) = 0 -> *)
(*        (forall n', n' < n -> exists τ', unfoldn n' τ = trec τ') -> *)
(*        n' < n -> *)
(*        ⟪ unfoldn n τ ≗ unfoldn n' τ ⟫. *)
(* Proof. *)
(*   - destruct 1; repeat (match goal with H : SimpleRec ?t |- _ => destruct H end); *)
(*       eauto with tyeq. *)
(*     eapply EqMuL; eauto. *)
(*     change (τ[beta1 (trec τ)]) with (unfoldn 1 (trec τ)). *)
(*     eapply eq_refl_itleft'; eauto with simple_contr_rec. *)
(*     intros n' ineq; assert (n' = 0) by lia; cbn; subst. *)
(*     exists τ; auto. *)
(*   - intros recs nn0 contr contr'. *)
(*     destruct (decide_mu (unfoldn n τ)) as [[τ2 eq2]|lmceq]. *)
(*     + rewrite eq2 in *. *)
(*       remember (trec τ2) in contr'. *)
(*       destruct contr'; inversion Heqt; subst. *)
(*       eapply EqMuL; eauto with simple_contr_rec. *)
(*       change (τ2[beta1 (trec τ2)]) with (unfoldOnce (trec τ2)). *)
(*       rewrite <- eq2. *)
(*       change (unfoldOnce (unfoldn (S n) τ)) with (unfoldn (S (S n)) τ). *)
(*       eapply (eq_refl_itleft' _ (S n)); eauto with simple_contr_rec. *)
(*       intros n' ineq. *)
(*       destruct (dec_lt n' n) as [ineq'|nineq']. *)
(*       * exact (recs n' ineq'). *)
(*       * assert (n' = n) by lia; subst. *)
(*         exists τ2; auto. *)
(*     + destruct (recs 0 nn0) as [τ' eq]; cbn in eq; subst τ. *)
(*       dependent destruction contr. *)
(*       eapply EqMuR; subst; eauto with simple_contr_rec. *)
(*       change (τ'[beta1 (trec τ')]) with (unfoldOnce (trec τ')). *)
(*       change (unfoldOnce (trec τ')) with (unfoldn 1 (trec τ')). *)
(*       destruct (dec_lt 1 n). *)
(*       eapply (eq_refl_itright' _ n 1); eauto with simple_contr_rec. *)
(*       assert (eqn' : 1 = n) by lia; rewrite eqn'. *)
(*       eapply eq_refl_contr; eauto with simple_contr_rec. *)
(*       (* eapply (eq_refl_itright' _ n 0); eauto. *) *)
(*   - intros contr contr' lmc0 recs ineq. *)
(*     destruct (recs n' ineq) as [τ' eq]. *)
(*     rewrite eq. *)
(*     eapply EqMuR; eauto with simple_contr_rec. *)
(*     + rewrite eq in contr'. *)
(*       dependent destruction contr'. *)
(*       eauto. *)
(*     + change (τ'[beta1 (trec τ')]) with (unfoldOnce (trec τ')). *)
(*       rewrite <- eq. *)
(*       change (unfoldOnce (unfoldn n' τ)) with (unfoldn (S n') τ). *)
(*       destruct (dec_lt (S n') n). *)
(*       * eapply (eq_refl_itright' _ n (S n')); eauto with simple_contr_rec. *)
(*       * assert (eqn' : S n' = n) by lia; rewrite eqn'. *)
(*         eapply eq_refl_contr; eauto with simple_contr_rec. *)
(* Qed. *)

Lemma enveq_refl {Γ} : ⟪ Γ ≗≗ Γ ⟫.
Proof.
  induction Γ;
  constructor;
  [ exact tyeq_refl | exact IHΓ ].
Qed.

(* Lemma contr_env_pres_r {Γ Γ'} : *)
(*   ⟪ Γ ≗≗ Γ' ⟫ → *)
(*   ContrEnv Γ → *)
(*   ContrEnv Γ'. *)
(* Proof. *)
(*   revert Γ. *)
(*   induction Γ'; intros; constructor. *)
(*   destruct Γ; *)
(*   inversion H; subst. *)
(*   inversion H0; subst. *)
(*   exact (IHΓ' Γ H6 H3). *)
(*   inversion H; *)
(*   inversion H0; subst. *)
(*   inversion H6. *)
(*   inversion H8; subst. *)
(*   exact (tyeq_pres_contr_l H4 H7). *)
(* Qed. *)

(* Lemma contr_env_pres_l {Γ Γ'} : *)
(*   ⟪ Γ ≗≗ Γ' ⟫ → *)
(*   ContrEnv Γ' → *)
(*   ContrEnv Γ. *)
(* Proof. *)
(*   revert Γ'. *)
(*   induction Γ; intros; constructor. *)
(*   dependent destruction Γ'; *)
(*   inversion H; *)
(*   inversion H0; subst. *)
(*   exact (IHΓ Γ' H6 H9). *)
(*   inversion H; *)
(*   inversion H0; subst. *)
(*   inversion H6. *)
(*   inversion H8; subst. *)
(*   exact (eq_pres_contr_r H3 H7). *)
(* Qed. *)

Lemma tyeq_invert_tarr {τ₁ τ₂ τ₃ τ₄} :
  ⟪ τ₁ r⇒ τ₂ ≗ τ₃ r⇒ τ₄ ⟫ ->
  ⟪ τ₁ ≗ τ₃ ⟫ /\ ⟪ τ₂ ≗ τ₄ ⟫.
Proof.
  remember (τ₁ r⇒ τ₂) as τ₅.
  remember (τ₃ r⇒ τ₄) as τ₆.
  destruct 1; invert_impossible_eqs.
  inversion Heqτ₅.
  inversion Heqτ₆.
  now subst.
Qed.

Lemma tyeq_invert_tprod {τ₁ τ₂ τ₃ τ₄} :
  ⟪ τ₁ r× τ₂ ≗ τ₃ r× τ₄ ⟫ ->
  ⟪ τ₁ ≗ τ₃ ⟫ /\ ⟪ τ₂ ≗ τ₄ ⟫.
Proof.
  remember (τ₁ r× τ₂) as τ₅.
  remember (τ₃ r× τ₄) as τ₆.
  destruct 1; invert_impossible_eqs.
  inversion Heqτ₅.
  inversion Heqτ₆.
  now subst.
Qed.

Lemma tyeq_invert_tsum {τ₁ τ₂ τ₃ τ₄} :
  ⟪ τ₁ r⊎ τ₂ ≗ τ₃ r⊎ τ₄ ⟫ ->
  ⟪ τ₁ ≗ τ₃ ⟫ /\ ⟪ τ₂ ≗ τ₄ ⟫.
Proof.
  remember (τ₁ r⊎ τ₂) as τ₅.
  remember (τ₃ r⊎ τ₄) as τ₆.
  destruct 1; invert_impossible_eqs.
  inversion Heqτ₅.
  inversion Heqτ₆.
  now subst.
Qed.


Ltac crushTypeEqualitiesMatchH :=
  match goal with
  | [ H : ⟪ _ r⇒ _ ≗ _ r⇒ _ ⟫ |- _ ] => destruct (tyeq_invert_tarr H); clear H
  | [ H : ⟪ _ r× _ ≗ _ r× _ ⟫ |- _ ] => destruct (tyeq_invert_tprod H); clear H
  | [ H : ⟪ _ r⊎ _ ≗ _ r⊎ _ ⟫ |- _ ] => destruct (tyeq_invert_tsum H); clear H
  end.


Fixpoint checkContractive (τ : Ty) : bool :=
  match τ with
  | tunit => B.true
  | tbool => B.true
  | τ1 r⇒ τ2 => checkNonExpansive τ1 && checkNonExpansive τ2
  | τ1 r⊎ τ2 => checkNonExpansive τ1 && checkNonExpansive τ2
  | τ1 r× τ2 => checkNonExpansive τ1 && checkNonExpansive τ2
  | trec τ => checkContractive τ
  | tvar i => B.false
  end
with checkNonExpansive (τ : Ty) : bool :=
       match τ with
       | tvar i => B.true
       | tunit => B.true
       | tbool => B.true
       | τ1 r⇒ τ2 => checkNonExpansive τ1 && checkNonExpansive τ2
       | τ1 r⊎ τ2 => checkNonExpansive τ1 && checkNonExpansive τ2
       | τ1 r× τ2 => checkNonExpansive τ1 && checkNonExpansive τ2
       | trec τ => checkContractive τ
       end.

Arguments checkContractive !τ.
Arguments checkNonExpansive !τ.

Lemma checkContractive_sound {τ} : Is_true (checkContractive τ) -> SimpleContr τ
with checkNonExpansive_sound {τ} : Is_true (checkNonExpansive τ) -> SimpleRec τ.
Proof.
  induction τ; cbn; intros check_res;
    try apply andb_prop_elim in check_res;
    try destruct check_res;
    try constructor; eauto with simple_contr_rec.
  induction τ; cbn; intros check_res;
    try apply andb_prop_elim in check_res;
    try destruct check_res;
    try constructor; try constructor;
    eauto with simple_contr_rec.
Qed.

Lemma checkContractive_checkNonExpansive {τ} : Is_true (checkContractive τ) -> Is_true (checkNonExpansive τ).
Proof.
  induction τ; cbn; eauto.
Qed.

Lemma checkContractive_complete {τ} : SimpleContr τ -> Is_true (checkContractive τ)
with checkNonExpansive_complete {τ} : SimpleRec τ -> Is_true (checkNonExpansive τ).
Proof.
  destruct 1; cbn; eauto using andb_prop_intro.
  destruct 1; cbn; eauto using andb_prop_intro.
  eapply checkContractive_checkNonExpansive.
  eauto.
Qed.
