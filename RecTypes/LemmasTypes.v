Require Export Db.Spec.
Require Export Db.Lemmas.

Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.


Lemma closed_implies_not_var {i} :
  ⟨ 0 ⊢ (tvar i) ⟩ → False.
Proof.
  intros.
  inversion H.
  inversion H1.
Qed.
#[export]
Hint Resolve closed_implies_not_var : cty.

Lemma closed_implies_not_var_eq {τ} :
  ⟨ 0 ⊢ τ ⟩ → ∀ i : Ix, τ <> tvar i.
Proof.
  intros.
  intros contra.
  rewrite contra in H.
  exact (closed_implies_not_var H).
Qed.

Lemma closed_arr_implies_closed_argty {τ τ'} :
  ⟨ 0 ⊢ (tarr τ τ') ⟩ → ⟨ 0 ⊢ τ ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_arr_implies_closed_argty : cty.

Lemma closed_arr_implies_closed_retty {τ τ'} :
  ⟨ 0 ⊢ (tarr τ τ') ⟩ → ⟨ 0 ⊢ τ' ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_arr_implies_closed_retty : cty.

Lemma closed_arr_implies_closed_argty_eq {τ τ1 τ2} :
  ⟨ 0 ⊢ τ ⟩ →
  τ = tarr τ1 τ2 →
  ⟨ 0 ⊢ τ1 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_arr_implies_closed_argty H).
Qed.

Lemma closed_arr_implies_closed_retty_eq {τ τ1 τ2} :
  ⟨ 0 ⊢ τ ⟩ →
  τ = tarr τ1 τ2 →
  ⟨ 0 ⊢ τ2 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_arr_implies_closed_retty H).
Qed.

Lemma closed_sum_implies_closed_lhs {τ τ'} :
 ⟨ 0 ⊢ (tsum τ τ') ⟩ → ⟨ 0 ⊢ τ ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_sum_implies_closed_lhs : cty.

Lemma closed_sum_implies_closed_rhs {τ τ'} :
 ⟨ 0 ⊢ (tsum τ τ') ⟩ → ⟨ 0 ⊢ τ' ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_sum_implies_closed_rhs : cty.

Lemma closed_sum_implies_closed_lhs_eq {τ τ1 τ2} :
 ⟨ 0 ⊢ τ ⟩ →
  τ = tsum τ1 τ2 →
 ⟨ 0 ⊢ τ1 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_sum_implies_closed_lhs H).
Qed.


Lemma closed_sum_implies_closed_rhs_eq {τ τ1 τ2} :
 ⟨ 0 ⊢ τ ⟩ →
  τ = tsum τ1 τ2 →
 ⟨ 0 ⊢ τ2 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_sum_implies_closed_rhs H).
Qed.

(* Lemma closed_rec_implies_closed_unfold {τ} : *)
(*  ClosedTy (trec τ) →ClosedTy τ[beta1 (trec τ)]. *)
(* Proof. *)
(*   intros. *)
(*   inversion H. *)
(*   induction τ. *)
(*   inversion H1. *)
(*   assert (H6 :ClosedTy (trec τ1)). *)
(*   constructor. *)
(*   assumption. *)
(*   assert (H7 :ClosedTy (trec τ2)). *)
(*   constructor. *)
(*   assumption. *)
(*   assert (H8 :ClosedTy τ1[beta1 (trec τ1)]). *)
(*   apply IHτ1. *)
(*   assumption. *)
(*   assert (H9 :ClosedTy τ2[beta1 (trec τ2)]). *)
(*   apply IHτ2. *)
(*   assumption. *)
(* Admitted. *)

(* Lemma closed_rec_implies_closed_unfold_eq {τ τ'} : *)
(*  ClosedTy τ → *)
(*   τ = trec τ' → *)
(*  ClosedTy τ'[beta1 (trec τ')]. *)
(* Proof. *)
(*   intros. *)
(*   rewrite H0 in H. *)
(*   exact (closed_rec_implies_closed_unfold H). *)
(* Qed. *)

Lemma Closed_SimpleRec_SimpleContr {τ} : ⟨ 0 ⊢ τ ⟩ -> SimpleRec τ -> SimpleContr τ.
Proof.
  intros cty rty.
  destruct rty; [|assumption].
  exfalso; eauto with cty.
Qed.

Lemma Closed_SimpleRec_Valid {τ} : ⟨ 0 ⊢ τ ⟩ -> SimpleRec τ -> ValidTy τ.
Proof.
  split; eauto using Closed_SimpleRec_SimpleContr.
Qed.

Lemma ValidTy_arr {τ1 τ2} : ValidTy τ1 -> ValidTy τ2 -> ValidTy (tarr τ1 τ2).
Proof.
  intros [τ1_cl τ1_contr] [τ2_cl τ2_contr].
  split; eauto with simple_contr_rec.
  now constructor.
Qed.
#[export]
Hint Resolve ValidTy_arr : tyvalid.

Lemma ValidTy_invert_arr {τ1 τ2} : ValidTy (tarr τ1 τ2) -> ValidTy τ1 /\ ValidTy τ2.
Proof.
  intros [τ_cl τ_contr].
  inversion τ_cl; subst.
  inversion τ_contr; subst.
  eauto using Closed_SimpleRec_Valid.
Qed.

Lemma ValidTy_prod {τ1 τ2} : ValidTy τ1 -> ValidTy τ2 -> ValidTy (tprod τ1 τ2).
Proof.
  intros [τ1_cl τ1_contr] [τ2_cl τ2_contr].
  split; eauto with simple_contr_rec.
  now constructor.
Qed.
#[export]
Hint Resolve ValidTy_prod : tyvalid.

Lemma ValidTy_invert_prod {τ1 τ2} : ValidTy (tprod τ1 τ2) -> ValidTy τ1 /\ ValidTy τ2.
Proof.
  intros [τ_cl τ_contr].
  inversion τ_cl; subst.
  inversion τ_contr; subst.
  eauto using Closed_SimpleRec_Valid.
Qed.

Lemma ValidTy_sum {τ1 τ2} : ValidTy τ1 -> ValidTy τ2 -> ValidTy (tsum τ1 τ2).
Proof.
  intros [τ1_cl τ1_contr] [τ2_cl τ2_contr].
  split; eauto with simple_contr_rec.
  now constructor.
Qed.
#[export]
Hint Resolve ValidTy_sum : tyvalid.

Lemma ValidTy_invert_sum {τ1 τ2} : ValidTy (tsum τ1 τ2) -> ValidTy τ1 /\ ValidTy τ2.
Proof.
  intros [τ_cl τ_contr].
  inversion τ_cl; subst.
  inversion τ_contr; subst.
  eauto using Closed_SimpleRec_Valid.
Qed.

Lemma ValidTy_unit : ValidTy tunit.
Proof.
  split; now constructor.
Qed.
#[export]
Hint Resolve ValidTy_unit : tyvalid.

Lemma ValidTy_bool : ValidTy tbool.
Proof.
  split; now constructor.
Qed.
#[export]
Hint Resolve ValidTy_bool : tyvalid.

Lemma ValidTy_rec {τ} : ⟨ 1 ⊢ τ ⟩ -> SimpleContr τ -> ValidTy (trec τ).
Proof.
  intros τ_cl τ_contr.
  split; eauto with simple_contr_rec.
  now constructor.
Qed.
#[export]
Hint Resolve ValidTy_rec : tyvalid.

Lemma ValidTy_unfold_trec {τ} : ValidTy (trec τ) -> ValidTy (τ[beta1 (trec τ)]).
Proof.
  intros (clτ & crτ).
  inversion clτ; subst.
  inversion crτ; subst.
  split.
  - eauto using wsAp, wsSub_sub_beta1.
  - eauto using unfold_preserves_contr.
Qed.

Lemma unfold_trec_prerves_ws {i τ} : ⟨ i ⊢ trec τ ⟩ → ⟨ i ⊢ τ[beta1 (trec τ)] ⟩.
Proof.
  intros.
  pose proof wsSub_sub_beta1.
  eapply wsAp; eauto. inversion H; subst; assumption.
Qed.

Lemma ValidTy_unfoldOnce {τ} : ValidTy τ -> ValidTy (unfoldOnce τ).
Proof.
  destruct τ; cbn; eauto using ValidTy_unfold_trec.
Qed.
#[export]
Hint Resolve ValidTy_unfoldOnce : tyvalid.

Lemma ValidTy_unfoldn {n τ} : ValidTy τ -> ValidTy (unfoldn n τ).
Proof.
  revert τ;
  induction n; cbn; eauto using ValidTy_unfoldOnce.
Qed.

Lemma unfoldOnce_preserves_ws {i τ} : ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ unfoldOnce τ ⟩.
Proof.
  destruct τ; cbn; eauto using unfold_trec_prerves_ws.
Qed.

Lemma unfoldn_preserves_ws {i n τ} : ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ unfoldn n τ ⟩.
Proof.
  revert τ;
  induction n; cbn; eauto using unfoldOnce_preserves_ws.
Qed.

Lemma ValidTy_invert_rec {τ} : ValidTy (trec τ) -> ⟨ 1 ⊢ τ ⟩ /\ SimpleContr τ.
Proof.
  intros [clτ cτ].
  inversion clτ.
  now inversion cτ.
Qed.

Definition decideValidTy τ := decideClosed τ && checkContractive τ.
Arguments decideValidTy /τ.

Lemma decideValidTy_sound τ : Is_true (decideValidTy τ) -> ValidTy τ.
Proof.
  intros (clres & ctres)%andb_prop_elim.
  split; eauto using decideClosed_sound, checkContractive_sound.
Qed.


Lemma ValidEnv_invert_cons {Γ τ} : ValidEnv (Γ r▻ τ) -> ValidEnv Γ /\ ValidTy τ.
Proof.
  intros (cΓτ & crΓτ).
  inversion cΓτ; subst.
  inversion crΓτ; subst.
  split; split; assumption.
Qed.

Ltac crushValidTyMatch2 :=
  try assumption;
  match goal with
  | |- ValidTy (?τ [ beta1 (trec ?τ)]) => refine (ValidTy_unfoldOnce (τ := trec τ) _)
  | H: ⟨ _ ⊢ ?τ ⟩ |- ⟨ _ ⊢ ?τ ⟩ => refine (WsTy_mono _ H)
  | H : ValidTy ?τ |- SimpleContr ?τ => exact (proj2 H)
  | H : ValidTy ?τ |- SimpleRec ?τ => eapply SimpleRecContr
  | H : ValidTy ?τ |- ⟨ 0 ⊢ ?τ ⟩ => exact (proj1 H)
  | H : ValidTy ?τ |- ⟨ _ ⊢ ?τ ⟩ => refine (WsTy_mono _ (proj1 H))
  | H: ValidTy (_ r⇒ _) |- _ => eapply ValidTy_invert_arr in H; destruct H as (? & ?)
  | H: ValidTy (_ r× _) |- _ => eapply ValidTy_invert_prod in H; destruct H as (? & ?)
  | H: ValidTy (_ r⊎ _) |- _ => eapply ValidTy_invert_sum in H; destruct H as (? & ?)
  | H: ValidTy (trec _) |- _ => eapply ValidTy_invert_rec in H; destruct H as (? & ?)
  | H: ValidTy (tvar _) |- _ => now eapply proj1, closed_implies_not_var in H
  | |- ValidTy (_ r× _) => eapply ValidTy_prod
  | |- ValidTy (unfoldOnce _) => eapply ValidTy_unfoldOnce
  | |- ValidTy (_ r⇒ _) => eapply ValidTy_arr
  | |- ValidTy (_ r⊎ _) => eapply ValidTy_sum
  | |- ValidTy tunit => eapply ValidTy_unit
  | |- ValidTy tbool => eapply ValidTy_bool
  | |- SimpleContr (trec _) => constructor
  | |- SimpleContr (_ r× _) => constructor
  | |- SimpleContr (_ r⇒ _) => constructor
  | |- SimpleContr (_ r⊎ _) => constructor
  | |- SimpleContr tunit => constructor
  | |- SimpleContr tbool => constructor
  | |- SimpleContr (tvar _) => constructor
  | |- SimpleContr (?τ [beta1 (trec ?τ)]) => refine (unfold_preserves_contr _)
  | |- SimpleRec (trec _) => constructor
  | |- SimpleRec (_ r× _) => constructor
  | |- SimpleRec (_ r⇒ _) => constructor
  | |- SimpleRec (_ r⊎ _) => constructor
  | |- SimpleRec tunit => constructor
  | |- SimpleRec tbool => constructor
  | |- SimpleRec (tvar _) => constructor
  | |- ValidEnv empty => eapply ValidEnv_nil
  | |- ValidEnv (_ r▻ _) => eapply ValidEnv_cons
  | |- ⟨ _ ⊢ trec _ ⟩ => constructor
  | |- ⟨ _ ⊢ _ r× _ ⟩ => constructor
  | |- ⟨ _ ⊢ _ r⊎ _ ⟩ => constructor
  | |- ⟨ _ ⊢ _ r⇒ _ ⟩ => constructor
  | |- ⟨ _ ⊢ tunit ⟩ => constructor
  | |- ⟨ _ ⊢ tbool ⟩ => constructor
  | |- ⟨ _ ⊢ tvar _ ⟩ => constructor
  | |- ⟨ _ ⊢ ?τ [beta1 (trec ?τ)] ⟩ => refine (unfold_trec_prerves_ws _)
  | |- wsTy ?n ?τ => change (⟨ n ⊢ τ ⟩)
  | H: ⟨ 0 ⊢ ?τ ⟩ |- context [ ?τ [ ?σ ] ] => rewrite (wsClosed_invariant (x := τ))
  | H: SimpleContr ?τ |- SimpleRec ?τ => eapply SimpleRecContr
(* , H2: ⟨ 0 ⊢ ?τ ⟩  *)
  end.
Ltac crushValidTyMatch :=
  crushValidTyMatch2 +
    match goal with
    | |- ValidTy _ => split
    end.


Ltac crushValidTy :=
  repeat crushValidTyMatch; try lia; eauto with ws wsi.

#[export]
Hint Extern 20 (ValidTy _) =>
  crushValidTy : tyvalid2.

#[export]
Hint Extern 20 (Closed_SimpleRec_SimpleContr _) =>
  crushValidTy : tyvalid2.
