Require Export Db.Lemmas.
Require Export StlcEqui.SpecSyntax.
Require Export StlcEqui.SpecEvaluation.
Require Export Coq.Program.Tactics.
Require Import Common.Common.
Require Import Common.Relations.

Require Import Lia.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     subst*);
  try discriminate;
  eauto with eval.

(* ** Evaluation contexts *)
Lemma ectx_cat (C₁ C₂: PCtx) :
  ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
Proof.
  induction C₂; simpl; intros; destruct_conjs; auto.
Qed.

Lemma pctx_cat_app (t : Tm) (C₁ C₂ : PCtx) :
  pctx_app t (pctx_cat C₁ C₂) = pctx_app (pctx_app t C₁) C₂.
Proof.
  induction C₂; crush.
Qed.

Lemma eval_ctx C t t' (eC : ECtx C) :
  t --> t' -> pctx_app t C --> pctx_app t' C.
Proof.
  induction 1.
  rewrite <- ?pctx_cat_app in *.
  eauto using ectx_cat with eval.
Qed.

Lemma evalstar_ctx {t t'} C (eC: ECtx C) :
  t -->* t' → pctx_app t C -->* pctx_app t' C.
Proof.
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma evalplus_ctx C t t' (eC: ECtx C) :
  t -->+ t' → pctx_app t C -->+ pctx_app t' C.
Proof.
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma evaln_ctx {C t t' n} :
  ECtx C → evaln t t' n -> evaln (pctx_app t C) (pctx_app t' C) n.
Proof.
  intros ec.
  induction 1; unfold evaln; eauto using eval_ctx with eval.
Qed.

Lemma termination_closed_under_antireduction {t t'} :
  t --> t' → t'⇓ → t⇓.
Proof.
  destruct 2 as [v ?].
  exists v; crush.
Qed.


Lemma terminationN_closed_under_antireduction {t t' n} :
  t --> t' → TerminatingN t' n → TerminatingN t (S n).
Proof.
  destruct 2 as (v & m & ? & ? & ?).
  exists v, (S m); repeat split.
  - crush.
  - lia.
  - eapply stepRel_step; crush.
Qed.


Lemma termination_closed_under_antireductionStar {t t'} :
  t -->* t' → t'⇓ → t⇓.
Proof.
  intros e m. induction e;
  eauto using termination_closed_under_antireduction.
Qed.

Lemma value_ectx_inv C t (ec : ECtx C) :
  Value (pctx_app t C) → Value t.
Proof.
  intros v; induction C; crush.
Qed.

Lemma eval₀_ectx_inv C t (ec : ECtx C) {t' t''} :
  t'' -->₀ t' → t'' = pctx_app t C →
  Value t ∨ C = phole.
Proof.
  induction 1;
  destruct C; crush;
  try match goal with
      [ H : _ = pctx_app t C |- _ ] =>
      (assert (Value (pctx_app t C)) by (rewrite <- H; crush))
  end; eauto using value_ectx_inv.
Qed.

Lemma pctx_cat_phole_leftzero {C} :
  pctx_cat phole C = C.
Proof.
  induction C; crush; f_equal; crush.
Qed.

Lemma pctx_cat_assoc {C C' C''} :
  pctx_cat C (pctx_cat C' C'') = pctx_cat (pctx_cat C C') C''.
Proof.
  induction C''; crush; f_equal; crush.
Qed.

Lemma values_terminate {v : Tm} : Value v → v ⇓.
Proof.
  intros vv. exists v; crush.
Qed.

Definition normal' (t : Tm) := ∀ t', ¬ (t --> t').
Lemma values_are_normal' {t : Tm} : Value t -> normal' t.
Proof. induction 2 using eval_ind'; crush. Qed.

Lemma values_are_normal {t : Tm} : Value t -> normal t.
Proof.
  generalize @values_are_normal'.
  unfold normal, normal', not.
  intros ? ? t'; destruct t'; eauto.
Qed.

Lemma normal_evalStar {v t} : normal v -> v -->* t -> v = t.
Proof.
  intros nv [|t' ev ets]; [reflexivity|].
  exfalso; eapply nv; eauto.
Qed.

Lemma value_evalStar {v t} : Value v -> v -->* t -> v = t.
Proof.
  eauto using normal_evalStar, values_are_normal.
Qed.

Lemma values_terminateN {t n} : Value t → t ⇓_ n.
Proof.
  intros v. exists t, 0; repeat split.
  - crush.
  - lia.
  - eapply stepRel_zero.
Qed.


Section InvertECtxEq.

  Inductive EctxAppEq : ∀ (t : Tm) (C : PCtx) (t' : Tm) (C' : PCtx),  Prop :=
    | EctxAppEqLeft : ∀ t C C', ECtx C → EctxAppEq (pctx_app t C) C' t (pctx_cat C C')
    | EctxAppEqRight : ∀ t C C', ECtx C → EctxAppEq t (pctx_cat C C') (pctx_app t C) C'
    | ECtxValueLeft : ∀ t t' C C', Value t → EctxAppEq t C t' C'
    | ECtxValueRight : ∀ t t' C C', Value t' → EctxAppEq t C t' C'
  .

  Lemma ectxAppEqExtend {t C t' C'} C'' :
    EctxAppEq t C t' C' →
    EctxAppEq t (pctx_cat C C'') t' (pctx_cat C' C'').
  Proof.
    induction 1; rewrite <- ?pctx_cat_assoc; constructor; assumption.
  Qed.

  Lemma ectxAppEqExtendPAbs {t C t' C' τ} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pabs τ C) t' (pabs τ C').
  Proof.
    eapply (ectxAppEqExtend (pabs τ phole)).
  Qed.

  Lemma ectxAppEqExtendPInl {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pinl C) t' (pinl C').
  Proof.
    eapply (ectxAppEqExtend (pinl phole)).
  Qed.

  Lemma ectxAppEqExtendPInr {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pinr C) t' (pinr C').
  Proof.
    eapply (ectxAppEqExtend (pinr phole)).
  Qed.

  Lemma ectxAppEqExtendPProj₁ {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pproj₁ C) t' (pproj₁ C').
  Proof.
    eapply (ectxAppEqExtend (pproj₁ phole)).
  Qed.

  Lemma ectxAppEqExtendPProj₂ {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pproj₂ C) t' (pproj₂ C').
  Proof.
    eapply (ectxAppEqExtend (pproj₂ phole)).
  Qed.

  Lemma ectxAppEqExtendPPair₁ {t C t' C' t₂} :
    EctxAppEq t C t' C' →
    EctxAppEq t (ppair₁ C t₂) t' (ppair₁ C' t₂).
  Proof.
    eapply (ectxAppEqExtend (ppair₁ phole t₂)).
  Qed.

  Lemma ectxAppEqExtendPPair₂ {t C t' C' t₁} :
    EctxAppEq t C t' C' →
    EctxAppEq t (ppair₂ t₁ C) t' (ppair₂ t₁ C').
  Proof.
    eapply (ectxAppEqExtend (ppair₂ t₁ phole)).
  Qed.

  Lemma ectxAppEqExtendPApp₁ {t C t' C' t₂} :
    EctxAppEq t C t' C' →
    EctxAppEq t (papp₁ C t₂) t' (papp₁ C' t₂).
  Proof.
    eapply (ectxAppEqExtend (papp₁ phole t₂)).
  Qed.

  Lemma ectxAppEqExtendPApp₂ {t C t' C' t₁} :
    EctxAppEq t C t' C' →
    EctxAppEq t (papp₂ t₁ C) t' (papp₂ t₁ C').
  Proof.
    eapply (ectxAppEqExtend (papp₂ t₁ phole)).
  Qed.

  Lemma ectxAppEqExtendPSeq₁ {t C t' C' t₂} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pseq₁ C t₂) t' (pseq₁ C' t₂).
  Proof.
    eapply (ectxAppEqExtend (pseq₁ phole t₂)).
  Qed.

  Lemma ectxAppEqExtendPIte₁ {t C t' C' t₂ t₃} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pite₁ C t₂ t₃) t' (pite₁ C' t₂ t₃).
  Proof.
    eapply (ectxAppEqExtend (pite₁ phole t₂ t₃)).
  Qed.

  Lemma ectxAppEqExtendPCaseof₁ {t C t' C' t₂ t₃} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pcaseof₁ C t₂ t₃) t' (pcaseof₁ C' t₂ t₃).
  Proof.
    eapply (ectxAppEqExtend (pcaseof₁ phole t₂ t₃)).
  Qed.

  Lemma ectxAppEqPHoleRight {t C} : ECtx C → EctxAppEq t C (pctx_app t C) phole.
  Proof.
    change C with (pctx_cat C phole); eauto using EctxAppEq.
  Qed.

  Lemma ectxAppEqPHoleLeft {t C} : ECtx C → EctxAppEq (pctx_app t C) phole t C.
  Proof.
    change C with (pctx_cat C phole); eauto using EctxAppEq.
  Qed.

  Lemma pctx_app_eq t C t' C' :
    ECtx C → ECtx C' →
    pctx_app t C = pctx_app t' C' →
    EctxAppEq t C t' C'.
  Proof.
    revert t' C';
    induction C; intros t' C' eC eC' eq';
    [simpl in *; subst;
     eauto using ectxAppEqPHoleLeft, ectxAppEqPHoleRight, EctxAppEq
    |idtac..];
    (destruct C';
      [change (pctx_app t' phole) with t' in *; subst;
       eauto using ectxAppEqPHoleLeft, ectxAppEqPHoleRight, EctxAppEq
      |idtac..]);
    crush;
    eauto using ectxAppEqExtendPAbs, ectxAppEqExtendPProj₂, ectxAppEqExtendPProj₁, ectxAppEqExtendPInr, ectxAppEqExtendPInl, ectxAppEqExtendPApp₁, ectxAppEqExtendPApp₂, ectxAppEqExtendPPair₁, ectxAppEqExtendPPair₂, ectxAppEqExtendPIte₁, ectxAppEqExtendPCaseof₁, ectxAppEqExtendPSeq₁;
    eauto using value_ectx_inv, ECtxValueRight, ECtxValueLeft.
  Qed.

End InvertECtxEq.

Lemma eval_ectx_inv C t (ec : ECtx C) {t' t''} :
  t'' --> t' → pctx_app t C = t'' →
  Value t ∨ exists t'', t' = pctx_app t'' C ∧ t --> t''.
Proof.
  induction 1.
  intros eq.
  pose proof (pctx_app_eq _ _ _ _ ec H0 eq) as inv.
  induction inv.
  - right.
    exists (pctx_app t' C).
    eauto using pctx_cat_app, eval_ctx₀.
  - destruct (eval₀_ectx_inv C t H1 H eq_refl); crush.
    right; exists t'.
    rewrite pctx_cat_phole_leftzero;
    eauto using (eval_ctx₀ phole).
  - left; crush.
  - exfalso.
    eapply (values_are_normal H1 t').
    eapply (eval_ctx₀ phole); crush.
Qed.

Lemma evalStar_ectx_inv C t (ec : ECtx C) v :
  pctx_app t C -->* v → Value v →
  exists v', Value v' ∧ t -->* v' ∧ pctx_app v' C -->* v.
Proof.
  intros es vv; depind es.
  - exists t; eauto using value_ectx_inv with eval.
  - destruct (eval_ectx_inv C t ec H eq_refl) as [vt|[t'' [eq e]]].
    + exists t; crush.
    + subst.
      destruct (IHes t'' C ec eq_refl vv) as (v' & vv' & es1' & es2').
      exists v'; crush.
Qed.

Lemma evaln_ectx_inv C t (ec : ECtx C) v n :
  evaln (pctx_app t C) v n → Value v →
  exists n' v', n' <= n /\ Value v' ∧ t -->* v' ∧ evaln (pctx_app v' C) v n'.
Proof.
  intros es vv; depind es.
  - exists 0, t; repeat split; eauto using value_ectx_inv, stepRel_zero with eval.
    eapply stepRel_zero.
  - destruct (eval_ectx_inv C t ec H eq_refl) as [vt|[t3 [eq e]]].
    + exists (S n), t; repeat split; eauto with eval.
      eapply stepRel_step; eauto.
    + subst.
      destruct (IHes t3 C ec eq_refl vv) as (n' & v' & nplen & vv' & es1' & es2').
      exists n', v'; repeat split; eauto with eval.
Qed.

Lemma inversion_termination_evalcontext C t (ec: ECtx C) :
  Terminating (pctx_app t C) → Terminating t.
Proof.
  destruct 1 as (v & vv & es).
  destruct (evalStar_ectx_inv C t ec v es) as (v' & vv' & es1 & es2); subst; crush.
  exists v'; crush.
Qed.

Corollary divergence_closed_under_evalcontext t :
  t⇑ → ∀ p, ECtx p → (pctx_app t p)⇑.
Proof. eauto using inversion_termination_evalcontext. Qed.

Corollary divergence_closed_under_evalcontext' {t C t'} :
  t⇑ → t' = pctx_app t C → ECtx C → t'⇑.
Proof. intros; subst; eauto using divergence_closed_under_evalcontext. Qed.

Ltac crushImpossibleEvals :=
  match goal with
          [ H : abs _ _ --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : true --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : false --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : unit --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : Value ?x, H' : ?x --> _ |- _ ] => exfalso; refine (values_are_normal' H _ H'); crush
        | [ Hx : Value ?x, Hy : Value ?y,  H' : pair ?x ?y --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
        | [ Hx : Value ?x,  H' : inl ?x --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
        | [ Hx : Value ?x,  H' : inr ?x --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
  end.

Lemma TerminatingN_Terminating {t : Tm} {n} : t ⇓_ n -> t ⇓.
Proof.
  destruct 1 as (v & m & vv & ineq & es).
  exists v; eauto using stepRel_to_evalStar.
Qed.

Lemma evalStar_to_evaln {t t'} : t -->* t' → exists n, evaln t t' n.
Proof.
  induction 1.
  - exists 0; apply stepRel_zero.
  - destruct (IHclos_refl_trans_1n) as (n & en).
    exists (S n); eapply stepRel_step; crush.
Qed.

Lemma evaln_to_evalStar {t t' n} :
  evaln t t' n → t -->* t'.
Proof.
  induction 1; crush.
Qed.

(* Lemma ctxevaln_to_ctxevalStar {t t' n} : *)
(*   ctxevaln t t' n → ctxevalStar t t'. *)
(* Proof. *)
(*   induction 1; crush. *)
(* Qed. *)

(* (* The following implication is actually an equivalence, but we don't need that. *) *)
(* Lemma ctxeval_eval_ctx {t t'} : ctxeval t t' → forall Cu, ECtx Cu → pctx_app t Cu --> pctx_app t' Cu. *)
(* Proof. *)
(*   destruct 1; intros; rewrite <- ?pctx_cat_app; eauto using ectx_cat with eval. *)
(* Qed. *)

(* Lemma ctxevaln_ctx {t t' n} : *)
(*   ctxevaln t t' n -> forall C, ECtx C → evaln (pctx_app t C) (pctx_app t' C) n. *)
(* Proof. *)
(*   intros ec C eC; unfold evaln. *)
(*   induction ec; eauto using ctxeval_eval_ctx with eval. *)
(* Qed. *)

(* Lemma ctxevaln_evaln_ctx {t t' n} : ctxevaln t t' n → forall Cu, ECtx Cu → evaln (pctx_app t Cu) (pctx_app t' Cu) n. *)
(* Proof. *)
(*   induction 1; unfold evaln in *; *)
(*   econstructor; eauto using ctxeval_eval_ctx with eval. *)
(* Qed. *)

(* Lemma extend_ctxeval tu tu' Cu : ECtx Cu → ctxeval tu tu' → ctxeval (pctx_app tu Cu) (pctx_app tu' Cu). *)
(* Proof. *)
(*   intros eCu ce.  *)
(*   induction ce. *)
(*   rewrite <- ?pctx_cat_app. *)
(*   eauto using ctxeval, ectx_cat. *)
(* Qed. *)

(* Lemma extend_ctxevalStar {tu tu'} Cu : ECtx Cu → ctxevalStar tu tu' → ctxevalStar (pctx_app tu Cu) (pctx_app tu' Cu). *)
(* Proof. *)
(*   intros eCu ce.  *)
(*   unfold ctxevalStar. *)
(*   induction ce; *)
(*   eauto using extend_ctxeval with eval. *)
(* Qed. *)

(* Lemma ctxevalStar_evalStar {tu tu'} : ctxevalStar tu tu' → tu -->* tu'. *)
(* Proof. *)
(*   unfold ctxevalStar. *)
(*   induction 1; *)
(*   eauto using ctxeval_eval with eval. *)
(* Qed. *)

(* Lemma evalStar_ctxevalStar {tu tu'} : tu -->* tu' -> ctxevalStar tu tu'. *)
(* Proof. *)
(*   unfold ctxevalStar. *)
(*   induction 1; *)
(*   eauto using eval_ctxeval with eval. *)
(* Qed. *)

(* Lemma ctxevalStar_normal {tu tu'} : normal tu -> ctxevalStar tu tu' -> tu = tu'. *)
(* Proof. *)
(*   intros ntu eu. *)
(*   destruct eu as [|tu'' tu' eu]; try reflexivity. *)
(*   eapply ctxeval_eval in eu. *)
(*   exfalso. exact (ntu _ eu). *)
(* Qed. *)



(* This should hold, but doesn't? *)
Lemma Terminating_TerminatingN {t : Tm} : t ⇓ -> ∃ n, t ⇓_ n.
Proof.
  destruct 1 as (v & vv & es).
  destruct (evalStar_to_evaln es) as [n en].
  exists n; econstructor; crush.
Qed.

Lemma determinacy' {t t' t'' t'''} : t --> t' → t'' --> t''' → t = t'' → t' = t'''.
Proof.
  intros e₁.
  revert t'' t'''.
  induction e₁ using eval_ind';
  induction 1 using eval_ind'; crush; try crushImpossibleEvals.
Qed.

Lemma determinacy {t t' t''} : t --> t' → t --> t'' → t' = t''.
Proof.
  eauto using determinacy'.
Qed.

Lemma determinacyStar' {t1 t2 t3 t4} : t1 -->* t2 -> t3 -->* t4 -> t1 = t3 -> normal t4 -> t2 -->* t4.
Proof.
  intros e12. revert t3.
  induction e12 as [|x t5 t2 e15 e52]; intros t3 e34 -> n4; eauto.
  destruct e34 as [|t6 t4 e26 e64].
  - exfalso. eapply (n4 _ e15).
  - refine (IHe52 t6 e64 _ n4).
    eapply determinacy; eauto.
Qed.

Lemma determinacyStar {t1 t2 t4} : t1 -->* t2 -> t1 -->* t4 -> normal t4 -> t2 -->* t4.
Proof.
  eauto using determinacyStar'.
Qed.

(* Lemma determinacyStar_ctxeval {t1 t2 t4} : ctxevalStar t1 t2 -> ctxevalStar t1 t4 -> normal t4 -> ctxevalStar t2 t4. *)
(* Proof. *)
(*   eauto using evalStar_ctxevalStar, determinacyStar, ctxevalStar_evalStar. *)
(* Qed. *)


Lemma TerminatingD (t: Tm) (m: t⇓) :
  ∀ t', t --> t' → Terminating t'.
Proof.
  destruct m as (v & vv & es).
  destruct es;
  intros t' e; try crushImpossibleEvals.
  destruct (determinacy H e).
  exists z; crush.
Qed.

Lemma TerminatingDN (t: Tm) n (term: t ⇓_ (S n)) :
  ∀ t', t --> t' → TerminatingN t' n.
Proof.
  destruct term as (v & m & vv & ineq & esn).
  intros t' e.
  destruct esn; try crushImpossibleEvals.
  destruct (determinacy H e).
  exists t'', n0; repeat split.
  - crush.
  - lia.
  - crush.
Qed.

Lemma termination_closed_under_evalplus {t t'} :
  t -->+ t' → t⇓ → t'⇓.
Proof. intros e m; induction e; eauto using TerminatingD. Qed.

Lemma termination_closed_under_evalstar {t t'} :
  t -->* t' → t⇓ → t'⇓.
Proof. intros e m; induction e; eauto using TerminatingD. Qed.

Corollary divergence_closed_under_eval {t t'} :
  t --> t' → t'⇑ → t⇑.
Proof. eauto using TerminatingD with eval. Qed.

Corollary divergence_closed_under_evalplus {t t'} :
  t -->+ t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalplus. Qed.

Corollary divergence_closed_under_evalstar {t t'} :
  t -->* t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalstar. Qed.

Lemma cycles_dont_terminate {t} :
  t -->+ t → t⇑.
Proof.
  intros cycle.
  destruct 1 as (v & vv & ?).
  enough (forall t', t' -->+ t → t' -->* v → False) by eauto with eval.
  intros ? cycle'.
  induction 1 as [?|? ? ? e' ? IHes''];
    destruct (inversion_evalPlus cycle') as (? & cycleStart & ?).
  - refine (values_are_normal vv _ cycleStart).
  - rewrite <- ?(determinacy e' cycleStart) in *.
    eauto using IHes'', evalStarPlusToPlus.
Qed.

Lemma TerminatingN_lt {t n n'} :
  TerminatingN t n → n ≤ n' → TerminatingN t n'.
Proof.
  destruct 1 as (v & m & vv & ineq & esm).
  intros ineq'.
  exists v, m; repeat split; crush.
  lia.
Qed.

(* Lemma TerminatingN_eval1 {t t' n} : *)
(*   t --> t' → TerminatingN t' n → TerminatingN t (S n). *)
(* Proof. *)
(*   intros e term. *)
(*   destruct term as [v m]. *)
(*   apply (TerminatingIN t (S n) v (S m)); crush; try omega. *)
(*   eapply stepRel_step; crush. *)
(* Qed. *)

Lemma TerminatingN_eval {t t' n} :
  t --> t' → TerminatingN t' n ↔ TerminatingN t (S n).
Proof.
  intros term.
  split; intros;
  [eapply terminationN_closed_under_antireduction | eapply TerminatingDN];
  crush.
Qed.

Lemma TerminatingN_evaln {t t' n } n' :
  evaln t t' n → TerminatingN t' n' ↔ TerminatingN t (n + n').
Proof.
  induction 1; constructor; auto; intro term;
  change (S n + n') with (S (n + n')) in *;
  [rewrite <- (TerminatingN_eval H) | rewrite <- (TerminatingN_eval H) in term];
  apply IHstepRel; auto.
Qed.

Lemma evaln_split1 {t t' n} :
  evaln t t' (S n) → exists t'', eval t t'' ∧ evaln t'' t' n.
Proof.
  remember (S n) as n'.
  destruct 1; inversion Heqn'.
  subst.
  now exists t'.
Qed.

Lemma evaln_split {t t' } n n':
  evaln t t' (n + n') → exists t'', evaln t t'' n ∧ evaln t'' t' n'.
Proof.
  revert t; induction n.
  - intros; exists t; simpl in *; split; [apply stepRel_zero|assumption].
  - intros t esn.
    destruct (evaln_split1 esn) as (t'' & es & esn').
    destruct (IHn t'' esn') as (t3 & es1 & es2).
    exists t3; split; try assumption.
    eapply stepRel_step; crush.
Qed.


Lemma TerminatingN_xor_evaln {t t' n} :
  TerminatingN t n → evaln t t' (S n) → False.
Proof.
  intros term esn.
  replace (S n) with (n + 1) in esn by lia.
  destruct (evaln_split n 1 esn) as (t'' & en & e1).
  replace n with (n + 0) in term by lia.
  rewrite <- (TerminatingN_evaln 0 en) in term.
  destruct term as (v & m & vv & ineq & esm).
  assert (m = 0) by lia; subst.
  inversion esm; subst.
  inversion e1.
  crushImpossibleEvals.
Qed.

Section EvalInContext.
  Lemma eval₀_to_eval {t t'} :
    t -->₀ t' →
    t --> t'.
  Proof.
    intros e₀.
    change (t --> t') with (pctx_app t phole --> pctx_app t' phole).
    eapply (eval_ctx₀ phole); crush.
  Qed.

  Lemma eval_from_eval₀ {t t' t₀ t₀' C} :
    t₀ -->₀ t₀' →
    t = pctx_app t₀ C →
    t' = pctx_app t₀' C →
    ECtx C →
    t --> t'.
  Proof.
    intros; subst; eauto using eval_ctx₀.
  Qed.

  Lemma evalstar_ctx' {t t' t₀ t₀' C} :
    t₀ -->* t₀' →
    t = pctx_app t₀ C →
    t' = pctx_app t₀' C →
    ECtx C →
    t -->* t'.
  Proof.
    intros; subst; eauto using evalstar_ctx.
  Qed.

End EvalInContext.

Ltac inferContext :=
  cbn; try reflexivity;
  let rec inferC acc t t₀ :=
      match t with
        | t₀ => instantiate (1 := acc)
        | app ?t1 ?t2 => inferC (pctx_cat (papp₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (papp₂ t1 phole) acc) t2 t₀
        | pair ?t1 ?t2 => inferC (pctx_cat (ppair₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (ppair₂ t1 phole) acc) t2 t₀
        | seq ?t1 ?t2 => inferC (pctx_cat (pseq₁ phole t2) acc) t1 t₀
        | inl ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | inr ?t1 => inferC (pctx_cat (pinr phole) acc) t1 t₀
        | ite ?t1 ?t2 ?t3 => inferC (pctx_cat (pite₁ phole t2 t3) acc) t1 t₀
        | caseof ?t1 ?t2 ?t3 => inferC (pctx_cat (pcaseof₁ phole t2 t3) acc) t1 t₀
        | proj₁ ?t1 => inferC (pctx_cat (pproj₁ phole) acc) t1 t₀
        | proj₂ ?t1 => inferC (pctx_cat (pproj₂ phole) acc) t1 t₀
        | pctx_app t₀ ?C => instantiate (1 := pctx_cat C acc)
        | pctx_app ?t1 (pctx_cat ?C1 ?C2) => inferC (pctx_app (pctx_app t1 C1) C2) t₀
        | pctx_app ?t1 ?C => inferC (pctx_cat C acc) t1 t₀
      end
  in repeat match goal with
              | [ |- ?t = pctx_app ?t₀ (pctx_cat ?C1 ?C2) ] => (rewrite -> ?pctx_cat_app)
              | [ |- pctx_app ?t0 ?C = pctx_app ?t' ?C ] => f_equal
              | [ |- ?t = pctx_app ?t₀ ?C ] => (inferC phole t t₀; rewrite -> ?pctx_cat_app; cbn; rewrite -> ?pctx_cat_app in *; reflexivity)
            end.

Lemma test_inferContext (t : Tm) (C' : PCtx): True.
Proof.
  assert (pctx_app (pair (inl t) (inr unit)) C' = pctx_app t (pctx_cat (ppair₁ (pinl phole) (inr unit)) C')).
  inferContext.
  trivial.
Qed.

Ltac crushStlcEval :=
  match goal with
      [ |- ECtx (pctx_cat _ _) ] => eapply ectx_cat
    | [ |- ECtx (papp₁ _ _) ] => unfold ECtx
    | [ |- ECtx (papp₂ _ _) ] => unfold ECtx
    | [ |- ECtx (pinl _) ] => unfold ECtx
    | [ |- ECtx (pinr _) ] => unfold ECtx
    | [ |- ECtx phole ] => unfold ECtx
    | [ |- ECtx (pcaseof₁ _ _ _) ] => unfold ECtx
  end.
