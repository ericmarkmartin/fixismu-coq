Require Import Common.Common.
Require Import UValFI.UVal.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LR.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.Size.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
(* Require Import StlcIso.LemmasScoping. *)
Require Import StlcIso.Inst.
Require Import StlcIso.Size.

Require Import Lia.
Require Import Min.

Lemma lev_lateri {i W} : lev (lateri i W) = lev W - i.
Proof.
  induction i; unfold lev in *; simpl in *; eauto with arith.
  rewrite IHi. lia.
Qed.


Section Obs.
  Lemma obs_zero {d ts tu} : Obs d 0 ts tu.
  Proof.
    destruct d; simpl; intuition.
  Qed.

  Lemma S_Observe_Terminating_value {n ts} :
    F.Value ts → Observe (S n) (F.TerminatingN ts).
  Proof.
    intros vts. simpl. eauto using F.values_terminateN.
  Qed.

  Lemma U_Observe_Terminating_value {n tu} :
    I.Value tu → Observe (S n) (I.TerminatingN tu).
  Proof.
    intros vtu. simpl. eauto using I.values_terminateN.
  Qed.

  Lemma obs_value {d n ts tu} :
    F.Value ts → I.Value tu → Obs d n ts tu.
  Proof.
    intros vs vu.
    destruct d; simpl; intros _;
    eauto using F.values_terminate, I.values_terminate.
  Qed.

  Lemma obs_mono {d W' W ts tu} :
    lev W' ≤ lev W →
    Obs d W ts tu →
    Obs d W' ts tu.
  Proof.
    intros fw obs.
    destruct d; destruct W';
    simpl in *; intuition;
    destruct (S_le fw) as [W'' [eq fw']];
    replace (lev W) with (S W'') in *; simpl in *;
    eauto using F.TermHor_lt, I.TermHor_lt.
  Qed.

  Lemma S_ObserveTerminatingN_xor_evaln {t t' n} :
    F.evaln t t' n → False ↔ Observe n (F.TerminatingN t).
  Proof.
    destruct n; simpl in *; intuition; eauto using F.TerminatingN_xor_evaln.
  Qed.

  Lemma S_Observe_TerminatingN_evaln {t t' n } n' :
    F.evaln t t' n → Observe n' (F.TerminatingN t') ↔ Observe (n + n') (F.TerminatingN t).
  Proof.
    destruct n';
      [ replace (n + 0) with n by lia
      | replace (n + S n') with (S n + n') by lia ];
    simpl in *; eauto using F.TerminatingN_evaln, S_ObserveTerminatingN_xor_evaln.
  Qed.

  Lemma S_ObserveTermHor_xor_evaln {t t' n} :
    F.evaln t t' n → False ↔ Observe n (F.TermHor t).
  Proof.
    destruct n; cbn; intuition. eauto using F.TermHor_xor_evaln.
  Qed.

  Lemma S_Observe_TermHor_evaln {t t' n } n' :
    F.evaln t t' n → Observe (n + n') (F.TermHor t) -> Observe n' (F.TermHor t').
  Proof.
    destruct n'; cbn; intros evals.
    - replace (n + 0) with n by lia.
      now rewrite <- (S_ObserveTermHor_xor_evaln evals).
    - replace (n + S n') with (S (n + n')) by lia.
      cbn.
      eauto using F.TermHor_evaln.
  Qed.

  Lemma S_Observe_TerminatingN_lt {t n n'} :
    n ≤ n' → Observe n (F.TerminatingN t) → Observe n' (F.TerminatingN t).
  Proof.
    intros ineq obs.
    destruct n; simpl; intuition.
    destruct (S_le ineq) as [n'' [eq ineq']]; subst; simpl in *.
    eauto using F.TerminatingN_lt.
  Qed.

  Lemma S_Observe_TermHor_lt {t n n'} :
    n ≤ n' → Observe n (F.TermHor t) → Observe n' (F.TermHor t).
  Proof.
    intros ineq obs.
    destruct n; simpl in *; [contradiction|].
    destruct (S_le ineq) as [n'' [-> ineq']]; cbn.
    eauto using F.TermHor_lt.
  Qed.

  Lemma U_Observe_TermHor_lt {t n n'} :
    n ≤ n' → Observe n (I.TermHor t) → Observe n' (I.TermHor t).
  Proof.
    intros ineq obs.
    destruct n; simpl in *; [contradiction|].
    destruct (S_le ineq) as [n'' [-> ineq']]; cbn.
    eauto using I.TermHor_lt.
  Qed.

  Lemma U_ObserveTerminatingN_xor_evaln {t t' n} :
    I.evaln t t' n → False ↔ Observe n (I.TerminatingN t).
  Proof.
    destruct n; simpl in *; intuition; eauto using I.TerminatingN_xor_evaln.
  Qed.

  Lemma U_Observe_TerminatingN_evaln {t t' n } n' :
    I.evaln t t' n → Observe n' (I.TerminatingN t') ↔ Observe (n + n') (I.TerminatingN t).
  Proof.
    destruct n';
      [ replace (n + 0) with n by lia
      | replace (n + S n') with (S n + n') by lia ];
    simpl in *; eauto using I.TerminatingN_evaln, U_ObserveTerminatingN_xor_evaln.
  Qed.

  Lemma U_Observe_TerminatingN_lt {t n n'} :
    n ≤ n' → Observe n (I.TerminatingN t) → Observe n' (I.TerminatingN t).
  Proof.
    intros ineq obs.
    destruct n; simpl; intuition.
    destruct (S_le ineq) as [n'' [eq ineq']]; subst; simpl; simpl in obs.
    eauto using I.TerminatingN_lt.
  Qed.

  Lemma U_ObserveTermHor_xor_evaln {t t' n} :
    I.evaln t t' n → False ↔ Observe n (I.TermHor t).
  Proof.
    destruct n; simpl in *; intuition; eauto using I.TermHor_xor_evaln.
  Qed.

  Lemma U_Observe_TermHor_evaln {t t' n } n' :
    I.evaln t t' n → Observe (n + n') (I.TermHor t) -> Observe n' (I.TermHor t').
  Proof.
    destruct n'; cbn; intros evals.
    - replace (n + 0) with n by lia.
      now rewrite <- (U_ObserveTermHor_xor_evaln evals).
    - replace (n + S n') with (S (n + n')) by lia.
      cbn.
      eauto using I.TermHor_evaln.
  Qed.

  Lemma obs_antired {ts ts' tu tu' W' W d i j} :
    F.evaln ts ts' i →
    I.evaln tu tu' j →
    (* W' ≤ W → *)
    lev W' + min i j ≥ lev W →
    Obs d W' ts' tu' →
    Obs d W ts tu.
  Proof.
    intros es eu (* fw *) sge obs.
    destruct d; destruct W; simpl; simpl in obs; intuition.
    - cut (tu'⇓).
      + refine (I.termination_closed_under_antireductionStar _).
        eauto using I.evaln_to_evalStar.
      + apply obs; clear obs.
        eapply (S_Observe_TermHor_evaln (lev W') es).
        assert (obs : Observe (S W) (F.TermHor ts)) by (simpl; intuition).
        refine (S_Observe_TermHor_lt _ obs).
        unfold lev in *.
        enough (min i j ≤ i) by lia.
        auto using le_min_l.
    - refine (F.termination_closed_under_antireductionStar _ _).
      + refine (stepRel_to_evalStar es).
      + apply obs; clear obs.
        assert (obs : Observe (S W) (I.TermHor tu)) by (simpl; intuition).
        apply (U_Observe_TermHor_evaln (lev W') eu).
        refine (U_Observe_TermHor_lt _ obs).
        unfold lev in *.
        lia.
  Qed.

  Lemma obs_antired_star {ts ts' tu tu' W d} :
    F.evalStar ts ts' →
    tu -->* tu' →
    Obs d W ts' tu' →
    Obs d W ts tu.
  Proof.
    intros es eu obs.
    destruct d.
    - intros term.
      destruct W; [contradiction|].
      eapply (F.TermHor_closed_under_reduction_star es) in term.
      eauto using I.termination_closed_under_antireductionStar.
    - intros term.
      destruct W; [contradiction|].
      cbn in term.
      eapply (I.TermHor_closed_under_reduction_star eu) in term.
      eauto using F.termination_closed_under_antireductionStar.
  Qed.

  (* Lemma obs_red {ts ts' tu tu' W' W d i j} : *)
  (*   F.evaln ts' ts i → *)
  (*   I.evaln tu' tu j → *)
  (*   lev W  + max i j <= lev W' → *)
  (*   Obs d W' ts' tu' → *)
  (*   Obs d W ts tu. *)
  (* Proof. *)
  (*   intros es eu sge obs. *)
  (*   destruct d; simpl; simpl in obs; intuition. *)
  (*   - eapply evaln_to_evalStar in eu. *)
  (*     eapply (termination_closed_under_evalstar eu). *)
  (*     eapply obs. *)
  (*     assert (i + lev W <= lev W') as sgei by lia. *)
  (*     eapply (S_Observe_TermHor_lt sgei). *)
  (*     now eapply (S_Observe_TermHor_evaln (lev W) es). *)
  (*   - eapply F.evaln_to_evalStar in es. *)
  (*     eapply (F.termination_closed_under_evalstar es). *)
  (*     eapply obs. *)
  (*     assert (j + lev W <= lev W') as sgej by lia. *)
  (*     eapply (U_Observe_TerminatingN_lt sgej). *)
  (*     now eapply (U_Observe_TerminatingN_evaln (lev W) eu). *)
  (* Qed. *)

  Lemma S_ObserveTerminating_Value {w vs} :
    F.Value vs →
    Observe (S w) (F.TerminatingN vs).
  Proof.
    intros vvs; simpl.
    apply F.values_terminateN; trivial.
  Qed.

  Lemma Diverge_Obs_lt {w ts tu} : not (F.Terminating ts) → Obs dir_lt w ts tu.
  Proof.
    intros div termobs.
    destruct w; try contradiction.
    apply F.TermHor_Terminating in termobs.
    exfalso; eauto.
  Qed.

  Lemma Diverge_Wrong_Obs {d w ts tu} :
    not (F.Terminating ts) →
    not (I.Terminating tu) →
    Obs d w ts tu.
  Proof.
    intros div divw.
    destruct d; intros termobs.
    - destruct w; try contradiction.
      apply F.TermHor_Terminating in termobs.
      exfalso; eauto.
    - destruct w; try contradiction.
      apply I.TermHor_Terminating in termobs.
      exfalso. eauto.
  Qed.

End Obs.

Section ClosedLR.
  Lemma valrel_implies_OfType {d W τ ts tu} :
    valrel d W τ ts tu → OfType τ ts tu.
  Proof.
    rewrite -> valrel_fixp. unfold valrel'. intuition.
  Qed.

  Lemma envrel_triv {d w γs γu} :
    envrel d w pempty γs γu.
  Proof.
    unfold envrel.
    intros i τ i_τ.
    depind i_τ.
  Qed.

  Lemma envrel_implies_WtSub {d W Γ γs γu} :
    envrel d W Γ γs γu → WtSub (repEmulCtx Γ) F.empty γs.
  Proof.
    intros er i τ vi_τ.
    destruct (getevar_repEmulCtx vi_τ) as [pτ [vi_pτ ?]].
    assert (vr : valrel d W pτ (γs i) (γu i)) by refine (er _ _ vi_pτ).
    destruct (valrel_implies_OfType vr) as [[_ ots] _].
    unfold OfTypeStlcFix in ots.
    subst. exact ots.
  Qed.

  Lemma envrel_implies_WtSub_iso {d W Γ γs γu} :
    envrel d W Γ γs γu → I.WtSub (fxToIsCtx Γ) I.empty γu.
  Proof.
    intros er i τ vu_τ.
    destruct (getevar_fxToIsCtx vu_τ) as [pτ [vu_pτ ?]].
    assert (vr : valrel d W pτ (γs i) (γu i)) by refine (er _ _ vu_pτ).
    destruct (valrel_implies_OfType vr) as [_ [_ ots]].
    subst. exact ots.
  Qed.

  (* Lemma envrel_implies_WsSub {d W Γ γs γu}: *)
  (*   envrel d W Γ γs γu → WsSub (pdom Γ) 0 γu. *)
  (* Proof. *)
  (*   intros er i wsi. *)
  (*   destruct (pdom_works_inv wsi) as (τ & τinΓ). *)
  (*   specialize (er i τ τinΓ). *)
  (*   destruct (valrel_implies_OfType er) as (_ & ws & _). *)
  (*   exact ws. *)
  (* Qed. *)

  Local Ltac crush :=
    crushOfType;
    repeat
      (cbn in *;
       subst*;
       repeat F.crushStlcSyntaxMatchH;
       repeat I.crushStlcSyntaxMatchH;
       destruct_conjs);
       eauto 20 using lt_le with arith.

  Lemma valrel_mono {d W τ ts tu W'} :
    W' ≤ W → valrel d W τ ts tu → valrel d W' τ ts tu.
  Proof with subst; intuition.
    rewrite -> ?valrel_fixp.
    revert ts tu W' W.
    induction τ;  unfold valrel';
    intros ts tu W' W fw [ot hyp];
    split; eauto; cbn in *.
    - (* ptarr _ _ *)
      destruct hyp as (tsb & tub & τ₁' & τ₂' & -> & -> & hyp).
      exists tsb, tub, τ₁', τ₂'.
      repeat split; try reflexivity.
      intros W'' fw'.
      apply hyp; lia.
    - (* ptprod *)
      crush.
    - (* ptsum *)
      crush.
      destruct H0 as [(-> & -> & ot')|[ (-> & -> )|[( -> & -> )|( -> & -> & ot')]]]; crush.
    - (* pEmulDV n p *)
      destruct n; [ assumption | idtac ].
      destruct hyp as [[eqs eqp]|[ts' hyp]];
        [ now left
        | right; exists ts'].
      destruct τ.
      + (* tarr *)
        destruct hyp as (-> & tsb & tub & τ₁' & τ₂' & -> & -> & hyp).
        split; [reflexivity|].
        exists tsb, tub, τ₁', τ₂'.
        crush.
      + (* tunit *)
        assumption.
      + (* tbool *)
        assumption.
      + (* tprod *)
        intuition.
        destruct ts'; crush.
        destruct tu; crush.
      + (* tsum *)
        intuition.
        destruct ts'; crush.
        destruct tu; crush.
        unfold sum_rel in *.
        destruct tu; crush.
      + (* trec *)
        crush.
      + (* tvar *)
        assumption.
  Qed.

  Lemma envrel_mono {d W Γ γs γu W'} :
    W' ≤ W → envrel d W Γ γs γu → envrel d W' Γ γs γu.
  Proof.
    intros fw er i τ viτ.
    refine (valrel_mono fw _).
    apply er; auto.
  Qed.

  Lemma contrel_mono {d W τ Cs Cu W'} :
    W' ≤ W → contrel d W τ Cs Cu → contrel d W' τ Cs Cu.
  Proof.
    intros fw cr. simpl.
    intros W'' fw' vs vu vr.
    apply cr; eauto with arith.
  Qed.

  Lemma termrel_zero {d τ ts tu} : termrel d 0 τ ts tu.
  Proof.
    intros Cs Cu cr eCs eCu. eauto using obs_zero.
  Qed.

  Lemma termrel_antired_step {ts ts' tu tu' W d τ} :
    F.eval ts ts' →
    I.eval tu tu' →
    (forall W', W = S W' -> termrel d W' τ ts' tu') →
    termrel d W τ ts tu.
  Proof.
    intros es eu tr.
    unfold termrel, termrel'.
    intros Cs Cu ecs ecu cr.
    destruct W.
    - eapply obs_zero.
    - refine (obs_antired (W' := W) _ _ _ _).
      eapply stepRel_step.
      refine (F.eval_ctx Cs _ _ ecs es).
      eapply stepRel_zero.
      eapply stepRel_step.
      refine (I.eval_ctx Cu _ _ ecu eu).
      eapply stepRel_zero.
      unfold lev; lia.
      apply tr; auto.
      refine (contrel_mono _ cr).
      lia.
  Qed.

  Lemma termrel_antired {ts ts' tu tu' W d τ i j} W' :
    F.evaln ts ts' i →
    I.evaln tu tu' j →
    W' ≤ W →
    lev W' + min i j ≥ lev W →
    termrel d W' τ ts' tu' →
    termrel d W τ ts tu.
  Proof.
    intros es eu fw sge tr.
    unfold termrel, termrel'.
    intros Cs Cu ecs ecu cr.
    refine (obs_antired _ _ sge _); eauto using F.evaln_ctx, I.evaln_ctx.
    apply tr; auto.
    refine (contrel_mono fw cr).
  Qed.

  Lemma termrel_antired_star {ts ts' tu tu' W d τ} :
    clos_refl_trans_1n F.Tm F.eval ts ts' →
    tu -->* tu' →
    termrel d W τ ts' tu' →
    termrel d W τ ts tu.
  Proof.
    intros es eu tr.
    destruct (evalTrans_to_stepRel es) as [i esi].
    destruct (evalTrans_to_stepRel eu) as [j euj].
    refine (termrel_antired W esi euj _ _ tr); lia.
  Qed.

  Lemma termrel_antired_star_left {ts ts' tu W d τ} :
    clos_refl_trans_1n F.Tm F.eval ts ts' →
    termrel d W τ ts' tu →
    termrel d W τ ts tu.
  Proof.
    assert (tu -->* tu) by (eauto with eval).
    eauto using termrel_antired_star.
  Qed.

  Lemma termrel_antired_eval_left {ts ts' tu W d τ} :
    F.eval ts ts' →
    termrel d W τ ts' tu →
    termrel d W τ ts tu.
  Proof.
    eauto using termrel_antired_star_left with eval.
  Qed.


  (* Lemma termrel_antired' {ts ts' tu tu' W d τ i j} W' : *)
  (*   S.evaln ts ts' i → *)
  (*   U.evaln tu tu' j →  *)
  (*   tu' ≠ wrong → *)
  (*   W' ≤ W → *)
  (*   lev W' + min i j ≥ lev W → *)
  (*   termrel d W' τ ts' tu' → *)
  (*   termrel d W τ ts tu. *)
  (* Proof. *)
  (*   intros es eu nw. *)
  (*   apply termrel_antired; try assumption. *)
  (*   induction eu; eauto using evaln; econstructor; eauto using evaln. *)
  (*   apply eval_ctx; try assumption. *)
  (*   intro eq; depind eu; intuition. *)
  (*   destruct H0 as [C'|C' eq']; destruct C'; simpl in eq; destruct H0; inversion eq; intuition. *)
  (* Qed. *)

  Lemma valrel_in_termrel {ts tu W d τ} :
    valrel d W τ ts tu → termrel d W τ ts tu.
  Proof.
    intros vr Cs Cu eCs eCu contrel.
    apply contrel; auto.
  Qed.

  Lemma valrel_implies_Value {d w τ ts tu} :
    valrel d w τ ts tu →
    F.Value ts ∧ I.Value tu.
  Proof.
    intros vr.
    rewrite -> valrel_fixp in vr.
    destruct vr as [ot _].
    exact (OfType_implies_Value ot).
  Qed.

  Lemma contrel_triv {d w τ} :
    contrel d w τ F.phole I.phole.
  Proof.
    unfold contrel, contrel'; intros w' fw ts tu vr; simpl.
    destruct (valrel_implies_Value vr).
    apply obs_value; trivial.
  Qed.

  Lemma extend_envrel {d w Γ γs γu τ ts tu} :
    valrel d w τ ts tu →
    envrel d w Γ γs γu →
    envrel d w (Γ p▻ τ) (γs↑ >=> beta1 ts) (γu↑ >=> beta1 tu).
  Proof.
    intros vr er x τ' xτ'.
    depind xτ'; intuition. 
    replace ((γs↑ >=> beta1 ts) (S i)) with (γs i). 
    replace ((γu↑ >=> beta1 tu) (S i)) with (γu i).
    now refine (er _ _ xτ').
    + cbn; rewrite <- ap_liftSub; 
      rewrite -> liftSub_wkm;
      rewrite -> apply_wkm_beta1_cancel; intuition.
    + cbn; rewrite <- ap_liftSub; 
      rewrite -> liftSub_wkm;
      rewrite -> apply_wkm_beta1_cancel; intuition.
  Qed.

  Lemma termrel_adequacy_lt {w m ts tu τ} :
    termrel dir_lt w τ ts tu →
    F.TermHor ts m →
    lev w > m →
    I.Terminating tu.
  Proof.
    intros tr term ineq.
    specialize (tr F.phole I.phole I I contrel_triv).
    simpl in tr. unfold lev in *.
    destruct (le_inv_plus ineq) as [r eq]; subst.
    apply tr.
    change (S m + r) with (S (m + r)) in *.
    apply (F.TermHor_lt term); lia.
  Qed.

  Lemma termrel_adequacy_gt {w m tu ts τ} :
    termrel dir_gt w τ ts tu →
    I.TermHor tu m →
    lev w > m →
    F.Terminating ts.
  Proof.
    intros tr term ineq.
    specialize (tr F.phole I.phole I I contrel_triv).
    simpl in tr. unfold lev in *.
    destruct (le_inv_plus ineq) as [r eq]; subst.
    apply tr.
    change (S m + r) with (S (m + r)) in *.
    apply (I.TermHor_lt term); lia.
  Qed.

  Lemma termrel_div_lt {w τ ts tu} : not (F.Terminating ts) → termrel dir_lt w τ ts tu.
  Proof.
    intros div Cs Cu eCs eCu contrel.
    eauto using Diverge_Obs_lt, F.divergence_closed_under_evalcontext.
  Qed.

  Lemma termrel_div_wrong {d w τ ts tu} : 
    not (F.Terminating ts) →
    not (I.Terminating tu) →
    termrel d w τ ts tu.
  Proof.
    intros div divw Cs Cu eCs eCu _.
    eauto using Diverge_Wrong_Obs, F.divergence_closed_under_evalcontext.
    eapply Diverge_Wrong_Obs.
    - eauto using F.divergence_closed_under_evalcontext.
    - eapply I.divergence_closed_under_evalcontext; assumption.
  Qed.

  Lemma termrel_size_left {w τ ts tu} :
    (S (F.size ts) <= w -> termrel dir_lt w τ ts tu) -> termrel dir_lt w τ ts tu.
  Proof.
    intros hyp Cs Cu eCs eCu Cr.
    destruct w; try (cbn; contradiction).
    intros term.
    pose proof (sz := F.TermHor_size term).
    eapply F.size_ectx' in sz; [|assumption].
    eapply hyp; eauto.
    lia.
  Qed.

  Lemma termrel_size_right {w τ ts tu} :
    (S (I.size tu) <= w -> termrel dir_gt w τ ts tu) -> termrel dir_gt w τ ts tu.
  Proof.
    intros hyp Cs Cu eCs eCu Cr.
    destruct w; try (cbn; contradiction).
    intros term.
    pose proof (sz := I.TermHor_size term).
    eapply I.size_ectx' in sz; [|assumption].
    eapply hyp; eauto.
    lia.
  Qed.

  Lemma termrel_size_right' {d w τ ts tu} :
    ((d = dir_gt -> S (I.size tu) <= w) -> termrel d w τ ts tu) -> termrel d w τ ts tu.
  Proof.
    destruct d.
    - intros hyp. apply hyp. intros [=].
    - eauto using termrel_size_right.
  Qed.

End ClosedLR.



Section OpenLR.

  Lemma compat_var {Γ d n τ i} :
    ⟪ i : τ p∈ Γ ⟫ →
    ⟪ Γ ⊩ F.var i ⟦ d , n ⟧ I.var i : τ ⟫.
  Proof.
    intros iτ. unfold OpenLRN.
    split;[|split].
    - crushTyping.
      eauto using repEmulCtx_works.
    - I.crushTyping.
      eauto using fxToIsCtx_works.
    - intros ? _ ? ? er.
      apply valrel_in_termrel.
      refine (er _ _ iτ).
  Qed.

  Lemma adequacy_lt {n m ts tu τ} :
    ⟪ pempty ⊩ ts ⟦ dir_lt , n ⟧ tu : τ ⟫ →
    F.TermHor ts m →
    n > m →
    I.Terminating tu.
  Proof.
    intros lr term ineq.
    destruct lr as (tsty & tuscp & lr).
    set (w := n).
    assert (le_w : lev w ≤ n) by (unfold lev, w; lia).
    assert (er : envrel dir_lt w pempty (idm F.Tm) (idm I.Tm)) by apply envrel_triv.
    pose proof (lr w le_w (idm F.Tm) (idm I.Tm) er) as tr.
    rewrite -> ?ap_id in tr.
    eapply (termrel_adequacy_lt tr term); trivial.
  Qed.

  Lemma adequacy_gt {n m tu ts τ} :
    ⟪ pempty ⊩ ts ⟦ dir_gt , n ⟧ tu : τ ⟫ →
    I.TermHor tu m →
    n > m →
    F.Terminating ts.
  Proof.
    intros lr term ineq.
    destruct lr as (tsty & tuscp & lr).
    set (w := n).
    assert (le_w : lev w ≤ n) by (unfold lev, w; lia).
    assert (er : envrel dir_gt w pempty (idm F.Tm) (idm I.Tm)) by apply envrel_triv.
    (* assert (er : envrel dir_lt w pempty (idm F.Tm) (idm I.Tm)) by apply envrel_triv. *)
    pose proof (lr w le_w (idm F.Tm) (idm I.Tm) er) as tr.
    (* pose proof (lr w le_w (idm F.Tm) (idm I.Tm) er) as tr. *)
    rewrite -> ?ap_id in tr.
    eapply (termrel_adequacy_gt tr term); trivial.
  Qed.

End OpenLR.

Section TermRelZero.

  Lemma valrel_in_termreli₀ {d dfc w τ ts tu} :
    valrel d w τ ts tu → termreli₀ d dfc w τ ts tu.
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] ?].
    unfold termrel₀. simpl.
    left. exists ts, tu.
    (* why isn't this enough? *)
    (* eauto using clos_refl_trans_1n with eval. *)
    split; [|split]; eauto using clos_refl_trans_1n with eval; constructor.
  Qed.

  Lemma valrel_in_termrel₀ {d w τ ts tu} :
    valrel d w τ ts tu → termrel₀ d  w τ ts tu.
  Proof.
    unfold termrel₀.
    eauto using valrel_in_termreli₀.
  Qed.

  Lemma termrel₀_in_termrel {d w τ ts tu} :
    termrel₀ d w τ ts tu → termrel d w τ ts tu.
  Proof.
    destruct 1 as [(vs & vu & ess & esu & vr)|div].
    - eauto using termrel_antired_star, valrel_in_termrel.
    - unfold termrel, termrel'; eauto.
  Qed.

  Lemma termreli₀_antired {ts ts' tu tu' W d dfc τ i j} dfc' :
    dfc' + min i j ≥ dfc  →
    F.evaln ts ts' i →
    I.evaln tu tu' j →
    termreli₀ d dfc W τ ts' tu' →
    termreli₀ d dfc' W τ ts tu.
  Proof.
    intros ineq es eu tzi.
    destruct tzi as [(vs & vu & es' & eu' & vr)|?].
    - left. exists vs, vu.
      eapply stepRel_to_evalStar in es.
      eapply stepRel_to_evalStar in eu.
      eauto using evalStepTrans with eval.
    - right. intros Cs Cu eCs eCu.
      specialize (H Cs Cu eCs eCu).

      pose proof (evaln_ctx eCu eu) as eu'.
      pose proof (F.evaln_ctx eCs es) as es'.
      enough (lev (lateri dfc W) + Nat.min i j ≥ lev (lateri dfc' W)) as ineq' by
          eapply (obs_antired es' eu' ineq' H).
      rewrite ?lev_lateri; unfold lev.
      lia.
  Qed.

  Lemma termreli₀_antired_star {ts ts' tu tu' W d dfc τ} :
    clos_refl_trans_1n F.Tm F.eval ts ts' →
    tu -->* tu' →
    termreli₀ d dfc W τ ts' tu' →
    termreli₀ d dfc W τ ts tu.
  Proof.
    intros es eu tr.
    destruct tr as [(vs & vu & ess & esu & vr)|div].
    - left; exists vs, vu.
      simpl in *.
      eauto using evalStepTrans.
    - right. intros Cs Cu eCs eCu.
      destruct (evalTrans_to_stepRel (F.evalstar_ctx Cs eCs es)) as (? & es').
      destruct (evalTrans_to_stepRel eu) as (? & eu').
      pose proof (evaln_ctx eCu eu') as eu''.
      specialize (div Cs Cu eCs eCu).
      eapply (obs_antired (W' := (lateri dfc W)) es' eu''); try assumption.
      rewrite ?lev_lateri.
      lia.
  Qed.

  Lemma termreli₀_div_lt {w dfc τ ts tu} : not (F.Terminating ts) → termreli₀ dir_lt dfc w τ ts tu.
  Proof.
    intros div. right. intros  Cs Cu eCs eCu.
    eauto using Diverge_Obs_lt, F.divergence_closed_under_evalcontext.
  Qed.

  Lemma termreli₀_div_wrong {d dfc w τ ts tu} : 
    not (F.Terminating ts) →
    not (I.Terminating tu) →
    termreli₀ d dfc w τ ts tu.
  Proof.
    intros div divw. right. intros Cs Cu eCs eCu.
    eauto using Diverge_Wrong_Obs, F.divergence_closed_under_evalcontext.
    eapply Diverge_Wrong_Obs.
    - eauto using F.divergence_closed_under_evalcontext.
    - eapply I.divergence_closed_under_evalcontext; assumption.
  Qed.
  Lemma termrel₀_antired_star {ts ts' tu tu' W d τ} :
    clos_refl_trans_1n F.Tm F.eval ts ts' →
    tu -->* tu' →
    termrel₀ d W τ ts' tu' →
    termrel₀ d W τ ts tu.
  Proof.
    eapply termreli₀_antired_star.
  Qed.

  Lemma termrel₀_antired_star_left {ts ts' tu W d τ} :
    clos_refl_trans_1n F.Tm F.eval ts ts' →
    termrel₀ d W τ ts' tu →
    termrel₀ d W τ ts tu.
  Proof.
    assert (tu -->* tu) by (simpl; eauto with eval).
    eauto using termrel₀_antired_star.
  Qed.

  Lemma termrel₀_ectx {d dfc w τ₁ τ₂ ts Cs tu Cu} (eCs : F.ECtx Cs) (eCu : I.ECtx Cu) :
    termreli₀ d dfc w τ₁ ts tu →
    (∀ vs vu, valrel d w τ₁ vs vu → termreli₀ d dfc w τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    termreli₀ d dfc w τ₂ (F.pctx_app ts Cs) (I.pctx_app tu Cu).
  Proof.
    intros trtm trcont.
    destruct trtm as [(vs & vu & ess & esu & vr)|div].
    - specialize (trcont vs vu vr).
      refine (termreli₀_antired_star _ _ trcont);
        eauto using F.evalstar_ctx, evalstar_ctx.
    - right.
      intros Cs' Cu' eCs' eC'.
      rewrite <- F.pctx_cat_app.
      rewrite <- I.pctx_cat_app.
      eauto using F.ectx_cat, I.ectx_cat.
  Qed.

  Lemma termrel₀_ectx' {d dfc w τ₁ τ₂ ts Cs tu ts' tu' Cu} :
    termreli₀ d dfc w τ₁ ts tu →
    (∀ vs vu, valrel d w τ₁ vs vu → termreli₀ d dfc w τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    ts' = F.pctx_app ts Cs →
    tu' = I.pctx_app tu Cu →
    F.ECtx Cs → I.ECtx Cu →
    termreli₀ d dfc w τ₂ ts' tu'.
  Proof.
    intros. subst.
    eauto using termrel₀_ectx.
  Qed.

  Lemma termrel₀_zero {d τ ts tu} :
    termrel₀ d 0 τ ts tu.
  Proof.
    right.
    intros Cs Cu eCs eCu.
    eapply obs_zero.
  Qed.

  Lemma termrel₀_ectx'' {d w' w τ₁ τ₂ ts Cs tu Cu} (eCs : F.ECtx Cs) (eCu : I.ECtx Cu) :
    termrel₀ d w' τ₁ ts tu →
    (∀ vs vu, valrel d w' τ₁ vs vu → termrel₀ d w τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    w ≤ w' →
    termrel₀ d w τ₂ (F.pctx_app ts Cs) (I.pctx_app tu Cu).
  Proof.
    intros trtm trcont ineq.
    destruct trtm as [(vs & vu & ess & esu & vr)|div].
    - specialize (trcont vs vu vr).
      refine (termrel₀_antired_star _ _ trcont);
        eauto using F.evalstar_ctx, evalstar_ctx.
    - right.
      intros Cs' Cu' eCs' eC'.
      rewrite <- F.pctx_cat_app.
      rewrite <- I.pctx_cat_app.
      eauto using F.ectx_cat, I.ectx_cat, obs_mono.
  Qed.

  Lemma termrel₀_ectx''' {d w w' τ₁ τ₂ ts Cs tu ts' tu' Cu} :
    termrel₀ d w' τ₁ ts tu →
    (∀ vs vu, valrel d w' τ₁ vs vu → termrel₀ d w τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    ts' = F.pctx_app ts Cs →
    tu' = I.pctx_app tu Cu →
    F.ECtx Cs → I.ECtx Cu →
    w ≤ w' →
    termrel₀ d w τ₂ ts' tu'.
  Proof.
    intros. subst.
    eauto using termrel₀_ectx''.
  Qed.

  Lemma termreli₀_dfc_mono {d dfc dfc' w τ ts tu}:
    termreli₀ d dfc w τ ts tu →
    dfc ≤ dfc' →
    termreli₀ d dfc' w τ ts tu.
  Proof.
    destruct 1 as [(vs & vu & ess & esu & vr)|div]; intros ineq.
    - left. exists vs, vu. eauto. 
    - right. intros Cs Cu eCs eCu.
      specialize (div Cs Cu eCs eCu).
      refine (obs_mono _ div).
      rewrite ?lev_lateri.
      lia.
  Qed.

  Lemma termreli₀_ectx {d dfc w τ₁ τ₂ ts Cs tu Cu} (eCs : F.ECtx Cs) (eCu : I.ECtx Cu) :
    termrel₀ d (lateri dfc w) τ₁ ts tu →
    lev w ≥ dfc →
    (∀ vs vu, valrel d (lateri dfc w) τ₁ vs vu → termreli₀ d dfc w τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    termreli₀ d dfc w τ₂ (F.pctx_app ts Cs) (I.pctx_app tu Cu).
  Proof.
    intros trtm ineq trcont.
    destruct trtm as [(vs & vu & ess & esu & vr)|div].
    - specialize (trcont vs vu vr).
      eapply termreli₀_antired_star in trcont;
        eauto using F.evalstar_ctx, evalstar_ctx.
    - right.
      intros Cs' Cu' eCs' eC'.
      rewrite <- F.pctx_cat_app.
      rewrite <- I.pctx_cat_app.
      eauto using F.ectx_cat, I.ectx_cat.
  Qed.

  Lemma termreli₀_ectx' {d dfc w τ₁ τ₂ ts Cs tu ts' tu' Cu} :
    termrel₀ d (lateri dfc w) τ₁ ts tu →
    lev w ≥ dfc →
    (∀ vs vu, valrel d (lateri dfc w) τ₁ vs vu → termreli₀ d dfc w τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    ts' = F.pctx_app ts Cs →
    tu' = I.pctx_app tu Cu →
    F.ECtx Cs → I.ECtx Cu →
    termreli₀ d dfc w τ₂ ts' tu'.
  Proof.
    intros. subst.
    eauto using termreli₀_ectx.
  Qed.

End TermRelZero.

Section TermRelZeroNoDiv.
  Lemma valrel_termrelnd₀ {d w τ ts tu} :
    valrel d w τ ts tu -> termrelnd₀ d w τ ts tu.
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[vts ots] [vtu otu]].
    destruct d.
    - intros vs vvs es.
      destruct (F.value_evalStar vts es).
      exists tu; split; [assumption|]; split; eauto with eval.
    - intros vu vvu eu.
      destruct (I.value_evalStar vtu eu).
      exists ts; split; [assumption|]; split; eauto with eval.
  Qed.

  Lemma termrelnd₀_termrel {d w τ ts tu} :
    termrelnd₀ d w τ ts tu -> termrel d w τ ts tu.
  Proof.
    destruct d; cbn; intros tr.
    - intros Cs Cu eCs eCu cr term.
      destruct w; cbn in term; try contradiction.
      destruct term as (v & vv & es).
      destruct (F.evalHor_ectx_inv Cs eCs es vv) as (v' & vv' & es' & es'').
      destruct (tr v' vv' es') as (vu & vvu & eu & vr').
      eapply (evalstar_ctx Cu) in eu; eauto.
      eapply (termination_closed_under_antireductionStar eu).
      refine (cr _ _ _ _ vr' _); [lia|].
      exists v; eauto.
    - intros Cs Cu eCs eCu cr term.
      destruct w; cbn in term; try contradiction.
      destruct (I.TermHor_ectx_inv Cu eCu term) as (v' & vv' & es' & v'' & vv'' & es'').
      destruct (tr v' vv' es') as (vu & vvu & eu & vr').
      eapply (F.evalstar_ctx Cs) in eu; eauto.
      eapply (F.termination_closed_under_antireductionStar eu).
      refine (cr _ _ _ _ vr' _); [lia|].
      exists v''; repeat split; eauto with arith.
  Qed.

  Lemma termrelnd₀_antired {d w τ ts ts' tu tu'} :
    F.evalStar ts' ts -> tu' -->* tu ->
    termrelnd₀ d w τ ts tu -> termrelnd₀ d w τ ts' tu'.
  Proof.
    intros es eu tr.
    destruct d.
    - intros vs vvs es'.
      assert (es'' := F.determinacyStar es es' (F.values_are_normal vvs)).
      destruct (tr vs vvs es'') as (vu & vvu & eu' & vr).
      exists vu; repeat (split; eauto).
      refine (evalStepTrans _ eu eu').
    - intros vu vvu eu'.
      assert (eu'' := I.determinacyStar eu eu' (I.values_are_normal vvu)).
      destruct (tr vu vvu eu'') as (vs & vvs & es' & vr).
      exists vs; repeat (split; eauto).
      refine (evalStepTrans _ es es').
  Qed.

  Lemma termrelnd₀_antired_left {d w τ ts ts' tu} :
    F.evalStar ts' ts ->
    termrelnd₀ d w τ ts tu -> termrelnd₀ d w τ ts' tu.
  Proof.
    eauto using termrelnd₀_antired with eval.
  Qed.

  Lemma termrelnd₀_red {d w τ ts ts' tu tu'} :
    F.evalStar ts ts' -> tu -->* tu' ->
    termrelnd₀ d w τ ts tu -> termrelnd₀ d w τ ts' tu'.
  Proof.
    intros es eu tr.
    destruct d.
    - intros vs vvs es'.
      destruct (tr vs vvs (evalStepTrans _ es es')) as (vu & vvu & eu' & vr).
      exists vu; repeat (split; eauto).
      refine (I.determinacyStar eu eu' (I.values_are_normal vvu)).
    - intros vu vvu eu'.
      destruct (tr vu vvu (evalStepTrans _ eu eu')) as (vs & vvs & es' & vr).
      exists vs; repeat (split; eauto).
      refine (F.determinacyStar es es' (F.values_are_normal vvs)).
  Qed.

  Lemma termrelnd₀_ectx {d w w' τ₁ τ₂ ts Cs tu Cu} (eCs : F.ECtx Cs) (eCu : I.ECtx Cu) :
    termrelnd₀ d w τ₁ ts tu →
    (∀ vs vu, valrel d w τ₁ vs vu → termrelnd₀ d w' τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    termrelnd₀ d w' τ₂ (F.pctx_app ts Cs) (I.pctx_app tu Cu).
  Proof.
    intros tr cr.
    destruct d.
    - intros vs vvs es.
      destruct (F.evalStar_ectx_inv Cs ts eCs vs es vvs) as (vs' & vvs' & es1 & es2).
      destruct (tr vs' vvs' es1) as (vu & vvu & eu & vr2).
      specialize (cr vs' vu vr2).
      destruct (cr vs vvs es2) as (vu2 & vvu2 & eu2 & vr3).
      exists vu2.
      eapply (evalstar_ctx Cu eCu) in eu.
      split; [|split]; eauto using evalStepTrans.
    - intros vu vvu eu.
      destruct (I.evalStar_ectx_inv Cu tu eCu vu eu vvu) as (vu' & vvu' & eu1 & eu2).
      destruct (tr vu' vvu' eu1) as (vs & vvs & es & vr2).
      specialize (cr vs vu' vr2).
      destruct (cr vu vvu eu2) as (vs2 & vvs2 & es2 & vr3).
      exists vs2.
      eapply (F.evalstar_ctx Cs eCs) in es.
      split; [|split]; eauto using evalStepTrans.
  Qed.

  Lemma termrelnd₀_ectx' {d w w' τ₁ τ₂ ts Cs tu ts' tu' Cu} :
    termrelnd₀ d w τ₁ ts tu →
    ts' = F.pctx_app ts Cs →
    tu' = I.pctx_app tu Cu →
    (∀ vs vu, valrel d w τ₁ vs vu → termrelnd₀ d w' τ₂ (F.pctx_app vs Cs) (I.pctx_app vu Cu)) →
    F.ECtx Cs → I.ECtx Cu →
    termrelnd₀ d w' τ₂ ts' tu'.
  Proof.
    intros; subst; eauto using termrelnd₀_ectx.
  Qed.


  (* interestingly, the following doesn't seem to hold with termrel instead of termrelnd₀. *)
  Lemma termrelnd₀_ectx_sub {d w τ₁ τ₂ ts vu tub} Cs (eCs : F.ECtx Cs) {vvu : I.Value vu} :
    (* termrel d (S w) τ₁ ts vu → *)
    termrelnd₀ d w τ₁ ts vu →
    (∀ {vs}, valrel d w τ₁ vs vu → termrel d w τ₂ (F.pctx_app vs Cs) (tub [beta1 vu])) →
    termrel d w τ₂ (F.pctx_app ts Cs) (tub [beta1 vu]).
  Proof.
    intros tr contr.
    intros Cs' Cu' eCs' eCu' cr'.
    destruct d.
    - destruct w; try (cbn; contradiction).
      intros term.
      rewrite <-F.pctx_cat_app in term.
      destruct (F.TermHor_ectx_inv (F.pctx_cat Cs Cs') (F.ectx_cat Cs Cs' eCs eCs') term) as (vs' & vvs' & es' & term').
      destruct (tr vs' vvs' es') as (vu' & vvu' & eu' & vr').
      destruct (I.normal_evalStar (I.values_are_normal vvu) eu').
      clear vvu' tr eu' term.
      rewrite F.pctx_cat_app in term'.
      refine (contr _ vr' Cs' Cu' eCs' eCu' cr' term'); lia.
    - destruct w; try (cbn; contradiction).
      destruct (tr vu vvu (rt1n_refl _ _ _)) as (vs' & vvs' & es' & vr).
      eapply obs_antired_star.
      + eapply (F.evalstar_ctx _ eCs').
        refine (F.evalstar_ctx _ eCs es').
      + eapply rt1n_refl.
      + refine (contr vs' vr Cs' Cu' eCs' eCu' cr').
  Qed.

  Lemma termrelnd₀_div_lt {ts tu W τ} :
    not (F.Terminating ts) ->
    termrelnd₀ dir_lt W τ ts tu.
  Proof.
    intros div vs vvs es.
    contradict div.
    now exists vs.
  Qed.

End TermRelZeroNoDiv.


Ltac crushLRMatch :=
  match goal with
      [ |- _ ∧ _ ] => split
    | [ |- context[ lev ]] => unfold lev
    | [ H : context[ lev ] |- _ ] => unfold lev in *
    | [ |- ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => (unfold OpenLRN; split)
    | [ H : ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ |- _ ] => (unfold OpenLRN in H; destruct_conjs)
    | [ H : valrel ?d _ ?τ ?ts ?tu |- termrel ?d _ ?τ ?ts ?tu ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ (F.abs _ _) (I.abs _ _) ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ F.unit I.unit ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ F.false I.false ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ F.true I.true ] => apply valrel_in_termrel
    | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => (refine (valrel_mono _ H); try lia)
    | [ H : envrel ?d ?w ?τ ?ts ?tu |- envrel ?d ?w' ?τ ?ts ?tu ] => (refine (envrel_mono _ H); try lia)
    | [ |- envrel ?d ?w (?Γ p▻ ?τ) (?γs↑ >=> beta1 ?ts) (?γu↑ >=> beta1 ?tu) ] => refine (extend_envrel _ _)
    | [ H : valrel _ _ ?τ ?ts ?tu |- OfType ?τ ?ts ?tu ] => refine (valrel_implies_OfType H)
    | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp in |- *; unfold valrel' in |- *
    | [ |- F.ECtx (F.pctx_cat _ _) ] => apply F.ectx_cat
    | [ |- I.ECtx (I.pctx_cat _ _) ] => apply I.ectx_cat
  end.
