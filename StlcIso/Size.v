Require Export StlcIso.Inst.
Require Export Coq.Relations.Relation_Operators.
Require Export Common.Relations.
Require Export StlcIso.SpecEvaluation.
Require Export StlcIso.LemmasEvaluation.

Require Import Lia.

Fixpoint size (t : Tm) : nat :=
  match t with
  | var i => 1
  | abs τ t => 1
  | app t₁ t₂ => S (size t₁ + size t₂)
  | unit => 1
  | true => 1
  | false => 1
  | ite t₁ t₂ t₃ => S (size t₁ + size t₂ + size t₃)
  | pair t₁ t₂ => S (size t₁ + size t₂)
  | proj₁ t => S (size t)
  | proj₂ t => S (size t)
  | inl t => S (size t)
  | inr t => S (size t)
  | caseof t₁ t₂ t₃ => S (size t₁ + size t₂ + size t₃)
  | seq t₁ t₂ => S (size t₁ + size t₂)
  | fold_ t => S (size t)
  | unfold_ t => S (size t)
  end.

(* Hor is for horizon: no terms should be hidden behind the horizon n *)
Inductive evalHor (t1 : Tm) : Tm -> nat -> Prop :=
  | evalHor_term : forall n, size t1 <= n -> evalHor t1 t1 n
  | evalHor_step : forall t2 t3 n,
      size t1 <= n -> eval t1 t2 -> evalHor t2 t3 n -> evalHor t1 t3 (S n)
.
#[export]
Hint Constructors evalHor : eval.

Definition TermHor (t1 : Tm) (n : nat) :=
  exists v, Value v /\ evalHor t1 v n.

Lemma TermHor_size {t n} : TermHor t n -> size t <= n.
Proof.
  destruct 1 as (v & vv & eh).
  destruct eh as [n st|t2 t3 n st e eh]; lia.
Qed.

Lemma evalHor_lt {t1 t2 n} :
  evalHor t1 t2 n -> forall n', n <= n' -> evalHor t1 t2 n'.
Proof.
  induction 1; intros n' ineq.
  - eapply evalHor_term; [lia].
  - destruct n'; [exfalso;lia|].
    eapply evalHor_step; [lia|eauto|].
    eapply IHevalHor; lia.
Qed.

Lemma TermHor_lt {t n n'} :
  TermHor t n → n ≤ n' → TermHor t n'.
Proof.
  destruct 1 as (v & vv & eh).
  intros ineq.
  exists v; split; try assumption.
  eauto using evalHor_lt.
Qed.

Lemma termHor_closed_under_antireduction {t t' n} :
  eval t t' → size t <= n -> TermHor t' n → TermHor t (S n).
Proof.
  destruct 3 as (v & vv & steps).
  exists v; eauto using evalHor_step.
Qed.

Lemma TermHor_closed_under_reduction {t t' n} :
  t --> t' → TermHor t (S n) -> TermHor t' n.
Proof.
  intros step term.
  destruct term as (v & vv & steps).
  exists v; split; try assumption.
  remember (S n) as n'.
  destruct steps.
  + exfalso.
    eapply values_are_normal; eauto.
  + destruct (determinacy step H0).
    inversion Heqn'.
    now destruct H2.
Qed.

Lemma TermHor_eval_extend {t t' n} :
  t --> t' → size t <= n -> TermHor t' n <-> TermHor t (S n).
Proof.
  intros term.
  split; eauto using termHor_closed_under_antireduction, TermHor_closed_under_reduction.
Qed.


Lemma TermHor_evalHor {t t' n } :
  evalHor t t' n → forall n', TermHor t' n' -> TermHor t (n + n').
Proof.
  induction 1; intros n' term.
  - eapply (TermHor_lt term); lia.
  - change (S n + n') with (S (n + n')).
    eapply (termHor_closed_under_antireduction H0).
    + lia.
    + eauto using IHevalHor.
Qed.

Lemma TermHor_xor_evaln {t t' n} :
  TermHor t n → evaln t t' (S n) → False.
Proof.
  intros term esn.
  destruct term as (v & vv & steps).
  revert esn.
  induction steps; intros esn.
  - destruct (evaln_split1 esn) as (t2 & step & steps').
    exact (values_are_normal vv _ step).
  - destruct (evaln_split1 esn) as (t4 & step & steps').
    destruct (determinacy H0 step).
    exact (IHsteps vv steps').
Qed.

Lemma TermHor_evaln {t t' n } n' :
  evaln t t' n → TermHor t (n + n') -> TermHor t' n'.
Proof.
  intros steps term.
  induction steps; eauto.
  eapply IHsteps.
  now apply (TermHor_closed_under_reduction H term).
Qed.

Lemma evalHor_evaln {t t' n} :
  evalHor t t' n -> exists n', n' <= n /\ evaln t t' n'.
Proof.
  induction 1.
  exists 0; repeat split.
  - lia.
  - constructor.
  - destruct IHevalHor as (n' & ineq & es).
    exists (S n'); split.
    + lia.
    + now eapply (stepRel_step eval _ _ _ _ H0).
Qed.

Lemma TermHor_TerminatingN {t n} :
  TermHor t n -> TerminatingN t n.
Proof.
  destruct 1 as (v & vv & es).
  destruct (evalHor_evaln es) as (n' & ineq & es').
  exists v,n'; eauto.
Qed.

Lemma TermHor_Terminating {t n} :
  TermHor t n -> Terminating t.
Proof.
  eauto using TermHor_TerminatingN, TerminatingN_Terminating.
Qed.

Lemma evalStar_to_evalHor {t t'} : t -->* t' -> exists n, evalHor t t' n.
Proof.
  induction 1.
  - exists (size x).
    constructor; eauto.
  - destruct IHclos_refl_trans_1n as (n & es).
    exists (S (n + size x)).
    eapply evalHor_step.
    + lia.
    + eauto.
    + eapply evalHor_lt; eauto; lia.
Qed.

Lemma Terminating_TermHor {t : Tm} : t ⇓ -> ∃ n, TermHor t n.
Proof.
  destruct 1 as (v & vv & es).
  destruct (evalStar_to_evalHor es) as [n en].
  exists n; econstructor; eauto.
Qed.

Lemma size_value_gt_zero {t : Tm} : Value t -> size t > 0.
Proof.
  destruct t; cbn; intuition.
Qed.

Lemma size_ectx {t} C : ECtx C -> size t <= size (pctx_app t C).
Proof.
  induction C; try contradiction;
    try reflexivity;
    intros eC; try (cbn; specialize (IHC eC); lia);
  cbn; destruct eC as [vt eC];
  specialize (IHC eC); lia.
Qed.

(* convenience lemma *)
Lemma size_ectx' {t w} C : ECtx C -> size (pctx_app t C) <= w -> size t <= w.
Proof.
  eauto using size_ectx with arith.
Qed.

Lemma evalHor_ectx_inv C {t} (ec : ECtx C) {v n} :
  evalHor (pctx_app t C) v n → Value v →
  exists v', Value v' ∧ t -->* v' ∧ evalHor (pctx_app v' C) v n.
Proof.
  intros es vv; depind es.
  - exists t; eauto using value_ectx_inv with eval.
  - destruct (eval_ectx_inv C t ec H0 eq_refl) as [vt|[t'' [eq e]]].
    + exists t; eauto with eval.
    + subst.
      destruct (IHes t'' C ec eq_refl vv) as (v' & vv' & es1' & es2').
      eapply evalHor_lt in es2'.
      exists v'; eauto with eval.
      lia.
Qed.

Lemma TermHor_ectx_inv C {t} (ec : ECtx C) {n} :
  TermHor (pctx_app t C) n →
  exists v', Value v' ∧ t -->* v' ∧ TermHor (pctx_app v' C) n.
Proof.
  intros (v & vv & es).
  destruct (evalHor_ectx_inv C ec es vv) as (v' & vv' & es1 & es2).
  exists v'. repeat split; auto.
  exists v. eauto.
Qed.

Lemma TermHor_closed_under_reduction_star {t t' n} :
  t -->* t' → TermHor t n -> TermHor t' n.
Proof.
  induction 1;
  eauto using TermHor_closed_under_reduction, TermHor_lt.
Qed.
