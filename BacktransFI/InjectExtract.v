Require StlcFix.SpecSyntax.
Require StlcIso.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.Size.
Require Import StlcIso.SpecEvaluation.
Require Import StlcFix.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.TypeSafety.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.StlcOmega.
Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LR.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import LogRelFI.LemmasInversion.
Require Import Lia.
Require Import Db.Lemmas.

Require Import LogRelFI.LR.
(* Require Import CompilerFI.ProtectConfine. *)
Require Import CompilerFI.CompilerFI.

Require Import BacktransFI.UValHelpers.
Require Import BacktransFI.UValHelpers2.

Require Import UValFI.UVal.

Local Ltac crush :=
  cbn in * |-;
  repeat
    (repeat F.crushStlcSyntaxMatchH;
     repeat I.crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushRepEmulEmbed;
     repeat F.crushStlcEval;
     repeat I.crushStlcEval;
     F.crushTyping;
     I.crushTyping;
     crushOfType;
     try split;
     trivial;
     subst*);
  try discriminate; try lia;
  eauto with eval;
  repeat F.crushStlcSyntaxMatchH; (* remove apTm's again *)
  repeat I.crushStlcSyntaxMatchH. (* remove apTm's again *)

Fixpoint injectA (n : nat) (τ : F.Ty) {struct n} : F.TmA :=
       F.a_abs τ (UValFI n (compfi_ty τ))
             (match n with
              | O => F.a_unit
              | S n => (match τ with
                       | F.tarr τ₁ τ₂ => F.a_inl (F.tarr (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))) F.tunit
                                          (F.a_abs (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))
                                              (F.a_app τ₂ (UValFI n (compfi_ty τ₂))
                                                       (injectA n τ₂)
                                                       (F.a_app τ₁ τ₂ (F.a_var 1)
                                                                (F.a_app (UValFI n (compfi_ty τ₁)) τ₁
                                                                         (extractA n τ₁)
                                                                         (F.a_var 0)))))
                       | F.tunit => F.a_inl F.tunit F.tunit (F.a_var 0)
                       | F.tbool => F.a_inl F.tbool F.tunit (F.a_var 0)
                       | F.tprod τ₁ τ₂ => F.a_inl (F.tprod (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))) F.tunit
                                                 (F.a_pair (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))
                                                           (F.a_app τ₁ (UValFI n (compfi_ty τ₁)) (injectA n τ₁)
                                                                    (F.a_proj₁ τ₁ τ₂ (F.a_var 0)))
                                                           (F.a_app τ₂ (UValFI n (compfi_ty τ₂)) (injectA n τ₂)
                                                                    (F.a_proj₂ τ₁ τ₂ (F.a_var 0))))
                       | F.tsum τ₁ τ₂ => F.a_inl (F.tsum (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))) F.tunit (F.a_caseof τ₁ τ₂ (F.tsum (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))) (F.a_var 0)
                                                 (F.a_inl (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))
                                                          (F.a_app τ₁ (UValFI n (compfi_ty τ₁)) (injectA n τ₁)
                                                                 (F.a_var 0)))
                                                 (F.a_inr (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))
                                                          (F.a_app τ₂ (UValFI n (compfi_ty τ₂)) (injectA n τ₂)
                                                               (F.a_var 0))))
                       end)
                end)
  with extractA (n : nat) (τ : F.Ty) {struct n} : F.TmA :=
         let caseτ : F.Tm → F.Tm := caseUVal (UValFI n (compfi_ty τ)) in
         F.a_abs (UValFI n (compfi_ty τ)) τ
               (match n with
                   | O => stlcOmegaA τ
                   | S n => match τ with
                           | F.tarr τ₁ τ₂ => F.a_abs τ₁ τ₂ (F.a_app (UValFI n (compfi_ty τ₂)) τ₂
                                                                (extractA n τ₂)
                                                                (F.a_app (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂))
                                                                         (caseArrA n (F.a_var 1)
                                                                                   (compfi_ty τ₁)
                                                                                   (compfi_ty τ₂))
                                                                         (F.a_app τ₁ (UValFI n (compfi_ty τ₁)) (injectA n τ₁)
                                                                                  (F.a_var 0))))
                           | F.tunit => caseUnitA n (F.a_var 0)
                           | F.tbool => caseBoolA n (F.a_var 0)
                           | F.tprod τ₁ τ₂ => F.a_pair τ₁ τ₂
                                                      (F.a_app (UValFI n (compfi_ty τ₁)) τ₁ (extractA n τ₁)
                                                               (F.a_proj₁ (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂)) (caseProdA n (F.a_var 0) (compfi_ty τ₁) (compfi_ty τ₂))))
                                                      (F.a_app (UValFI n (compfi_ty τ₂)) τ₂ (extractA n τ₂)
                                                               (F.a_proj₂ (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂)) (caseProdA n (F.a_var 0) (compfi_ty τ₁) (compfi_ty τ₂))))
                           | F.tsum τ₁ τ₂ => F.a_caseof (UValFI n (compfi_ty τ₁)) (UValFI n (compfi_ty τ₂)) (F.tsum τ₁ τ₂)
                                                       (caseSumA n (F.a_var 0) (compfi_ty τ₁) (compfi_ty τ₂))
                                                       (F.a_inl τ₁ τ₂ (F.a_app (UValFI n (compfi_ty τ₁)) τ₁ (extractA n τ₁) (F.a_var 0)))
                                                       (F.a_inr τ₁ τ₂ (F.a_app (UValFI n (compfi_ty τ₂)) τ₂ (extractA n τ₂) (F.a_var 0)))
                           end
               end).
Definition inject n τ := eraseAnnot (injectA n τ).
Definition extract n τ := eraseAnnot (extractA n τ).

Arguments injectA n τ : simpl never.
Arguments extractA n τ : simpl never.
Arguments inject n τ : simpl never.
Arguments extract n τ : simpl never.

Lemma inject_value {n τ} : F.Value (inject n τ).
Proof.
  (* exact I. *)
  (* Should be doable without the induction, but I don't see how *)
  destruct n; destruct τ; simpl; eauto with eval.
Qed.

Lemma injectAT {n τ Γ} : ⟪ Γ a⊢ injectA n τ : F.tarr τ (UValFI n (compfi_ty τ)) ⟫
with extractAT {n τ Γ} : ⟪ Γ a⊢ extractA n τ : F.tarr (UValFI n (compfi_ty τ)) τ ⟫.
Proof.
  - destruct n, τ; unfold injectA; eauto with typing uval_typing.
  - destruct n, τ; unfold extractA; eauto with typing uval_typing.
Qed.

Lemma injectT {n τ Γ} : ⟪ Γ ⊢ inject n τ : F.tarr τ (UValFI n (compfi_ty τ)) ⟫.
Proof.
  eauto using eraseAnnotT, injectAT.
Qed.
Lemma extractT {n τ Γ} : ⟪ Γ ⊢ extract n τ : F.tarr (UValFI n (compfi_ty τ)) τ ⟫.
Proof.
  eauto using eraseAnnotT, extractAT.
Qed.

Hint Resolve injectT : uval_typing.
Hint Resolve extractT : uval_typing.
Hint Resolve injectAT : uval_typing.
Hint Resolve extractAT : uval_typing.

Lemma inject_closed {n τ} :
  ⟨ 0 ⊢ inject n τ ⟩.
Proof.
  eapply (wt_implies_ws (Γ := F.empty)).
  eapply injectT.
Qed.

Lemma extract_value {n τ} : F.Value (extract n τ).
Proof.
  (* exact I. *)
  (* Should be doable without the induction, but I don't see how *)
  destruct n; destruct τ; simpl; eauto with eval.
Qed.

Lemma extract_closed {n τ} :
  ⟨ 0 ⊢ extract n τ ⟩.
Proof.
  eapply (wt_implies_ws (Γ := F.empty)).
  eapply extractT.
Qed.

Lemma inject_sub {n τ γ} : (inject n τ)[γ] = inject n τ.
Proof.
  apply wsClosed_invariant.
  eapply inject_closed.
Qed.

Lemma extract_sub {n τ γ} : (extract n τ)[γ] = extract n τ.
Proof.
  apply wsClosed_invariant.
  eapply extract_closed.
Qed.

Lemma inject_terminates n {τ vs}:
  OfTypeStlcFix (embed τ) vs ->
  Terminating (F.app (inject n τ) vs).
Proof.
  revert n vs.
  induction τ; intros n vs [vvs vty];
    (destruct n;
    (eapply F.termination_closed_under_antireduction;
     [ now eapply eval_eval₀, eval_beta |]);
    [eapply values_terminate; now cbn|]
    );
    cbn; fold inject extract.
  - eapply values_terminate.
    now cbn.
  - eapply values_terminate.
    now cbn.
  - inversion vty; subst; cbn in vvs; try contradiction;
      eapply values_terminate; now cbn.
  - inversion vty; subst; cbn in vvs; try contradiction.
    F.crushTyping.
    fold eraseAnnot.
    change (app _ ?t2) with (app (inject n τ1)[beta1 (pair t₁ t₂)] t2) at 1.
    change (app _ ?t2) with (app (inject n τ2)[beta1 (pair t₁ t₂)] t2) at 2.
    rewrite ?inject_sub.
    subst.
    eapply F.termination_closed_under_antireduction.
    { eapply (eval_ctx₀' (eval_proj₁ H H0)); F.inferContext; cbn; eauto using inject_value with eval. }
    cbn.
    destruct (IHτ1 n t₁ (conj H H2)) as (vs' & vvs' & es).
    eapply F.termination_closed_under_antireductionStar.
    { eapply (evalstar_ctx' es); F.inferContext; now cbn. }
    cbn.
    eapply F.termination_closed_under_antireduction.
    { eapply (eval_ctx₀' (eval_proj₂ H H0)); F.inferContext; cbn; eauto using inject_value with eval. }
    cbn.
    destruct (IHτ2 n t₂ (conj H0 H3)) as (vs2' & vvs2' & es2).
    eapply F.termination_closed_under_antireductionStar.
    { eapply (evalstar_ctx' es2); F.inferContext; now cbn. }
    cbn.
    eapply values_terminate; now cbn.
  - inversion vty; subst; cbn in vvs; try contradiction.
    (eapply F.termination_closed_under_antireduction;
    [eapply (eval_ctx₀ (pinl phole)); [|now cbn]; now eauto with eval|]);
    cbn;
    repeat change (apTm ?ξ ?t) with t[ξ];
    rewrite ?inject_sub.
    + destruct (IHτ1 n t (conj vvs H1)) as (vs' & vvs' & es).
      exists (inl (inl vs')); split; cbn; eauto.
      repeat change (inl (inl ?x)) with (pctx_app x (pinl (pinl phole))).
      fold eraseAnnot.
      change (eraseAnnot _) with (inject n τ1).
      rewrite ?inject_sub.
      eapply F.evalstar_ctx; now cbn.
    + destruct (IHτ2 n t (conj vvs H1)) as (vs' & vvs' & es).
      exists (inl (inr vs')); split; cbn; eauto.
      repeat change (inl (inr ?x)) with (pctx_app x (pinl (pinr phole))).
      fold eraseAnnot.
      change (eraseAnnot _) with (inject n τ1) at 1.
      change (eraseAnnot _) with (inject n τ2) at 1.
      crushTyping.
      rewrite ?inject_sub.
      eapply evalStepStar.
      { eapply (eval_ctx₀' (eval_case_inr vvs)); F.inferContext; now cbn. }
      crushTyping.
      rewrite ?inject_sub.
      eapply (F.evalstar_ctx' es); F.inferContext; now cbn.
Qed.


Definition inject_works_prop (n : nat) (w : World) (d : Direction) (p : Prec) (vs : F.Tm) (vu : I.Tm) (τ : F.Ty) : Prop :=
  dir_world_prec n w d p →
  valrel d w (embed τ) vs vu →
  termrelnd₀ d w (pEmulDV n p (compfi_ty τ)) (F.app (inject n τ) vs) vu.
  (* ECtx Cs → I.ECtx Cu → *)
  (* contrel d w (embed τ) Cs Cu → *)
  (* (exists vs', F.pctx_app (F.app (inject n τ) vs) Cs -->* F.pctx_app vs' Cs *)
  (*        ∧ valrel d w (pEmulDV n p (compfi_ty τ)) vs' vu) *)
  (* ∨ Obs d w (F.pctx_app (F.app (inject n τ) vs) Cs) (I.pctx_app vu Cu). *)

Definition extract_works_prop (n : nat) (w : World) (d : Direction) (p : Prec) (vs : F.Tm) (vu : I.Tm) (τ : F.Ty) : Prop :=
  dir_world_prec n w d p →
  (d = dir_gt -> I.size vu <= w) ->
  valrel d w (pEmulDV n p (compfi_ty τ)) vs vu →
  termrelnd₀ d w (embed τ) (F.app (extract n τ) vs) vu.
  (* ECtx Cs → I.ECtx Cu → *)
  (* contrel d w (embed τ) Cs Cu → *)
  (* (exists vs', F.pctx_app (F.app (extract n τ) vs) Cs -->* F.pctx_app vs' Cs *)
  (*        ∧ valrel d w (embed τ) vs' vu) *)
  (* ∨ Obs d w (F.pctx_app (F.app (extract n τ) vs) Cs) (I.pctx_app vu Cu). *)

Lemma inject_zero_works {w d p vs vu τ} :
  inject_works_prop 0 w d p vs vu τ.
Proof.
  intros dwp vr.
  destruct (dwp_zero dwp); subst.
  rewrite compiler_is_fxToIs_embed.
  destruct (valrel_implies_OfType vr) as [[vvs ovs] [vvu ovu]].
  eapply termrelnd₀_antired.
  - eapply evalToStar, eval₀_to_eval, eval_beta.
    assumption.
  - eapply rt1n_refl.
  - eapply valrel_termrelnd₀.
    crush.
Qed.

Lemma extract_zero_works {w d p vs vu τ} :
  extract_works_prop 0 w d p vs vu τ.
Proof.
  intros dwp _ vr.
  destruct (dwp_zero dwp); subst.
  intros vs0 vvs0 es.
  exfalso.
  cbn in es.
  eapply stlcOmega_div.
  exists vs0; split; [assumption|].
  refine (determinacyStar1 _ es _).
  - eapply eval_eval₀.
    destruct (valrel_implies_Value vr).
    erewrite <-stlcOmega_sub.
    unfold extract, extractA; cbn.
    eauto using eval_beta.
  - eauto using values_are_normal.
Qed.

Lemma inject_unit_works {n w d p vs vu} :
  inject_works_prop (S n) w d p vs vu F.tunit.
Proof.
  intros dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  simpl in tyvs, tyvu.
  eapply termrelnd₀_antired.
  - eapply evalToStar.
    refine (eval_ctx₀ phole (eval_beta _) I); eauto.
  - eapply rt1n_refl.
  - cbn.
    eapply valrel_termrelnd₀.
    apply valrel_inUnit; split;
      [F.stlcCanForm | I.stlcCanForm]; trivial.
Qed.

Lemma extract_unit_works {n w d p vs vu} :
  extract_works_prop (S n) w d p vs vu F.tunit.
Proof.
  intros dwp sz vr.
  simpl in vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  destruct (invert_valrel_pEmulDV_unit vr) as [(? & ?) | (vs' & ? & ?)];
    unfold unkUVal in H;
    subst.
  - apply dwp_invert_imprecise in dwp; subst.
    cbn.
    intros vs vvs' es.
    exfalso.
    refine (divergence_closed_under_eval _ _ (ex_intro _ vs (conj vvs' es))).
    + refine (eval_ctx₀ phole (eval_beta _) I).
      exact I.
    + (* note: choice of n = 0 doesn't actually matter *)
      eapply (caseUnit_eval_unk_diverges (n := 0)).
  - eapply termrelnd₀_antired.
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      unfold caseUnit, caseUnit_pctx, caseUVal_pctx.
      eapply evalStepStar.
      * eapply eval_eval₀.
        eapply eval_case_inl.
        exact vvs.
      * eapply rt1n_refl.
    + eapply rt1n_refl.
    + eapply valrel_termrelnd₀.
      assumption.
Qed.

Lemma inject_bool_works {n w d p vs vu} :
  inject_works_prop (S n) w d p vs vu F.tbool.
Proof.
  intros dwp vr.
  rewrite valrel_fixp in vr; unfold valrel' in vr; cbn in vr.
  destruct vr as [[[vvs tyvs] [vvu tyvu]] vr]; subst.
  simpl in tyvs, tyvu.
  eapply termrelnd₀_antired.
  - eapply evalToStar.
    refine (eval_ctx₀ phole (eval_beta _) I); eauto.
  - eapply rt1n_refl.
  - cbn.
    eapply valrel_termrelnd₀.
    eapply valrel_inBool; eauto.
Qed.

Lemma extract_bool_works {n w d p vs vu} :
  extract_works_prop (S n) w d p vs vu F.tbool.
Proof.
  intros dwp sz vr.
  simpl in vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  destruct (invert_valrel_pEmulDV_bool vr) as [(? & ?) | (vs' & ? & ?)];
    unfold unkUVal in H;
    subst.
  - apply dwp_invert_imprecise in dwp; subst.
    cbn.
    intros vs vvs' es.
    exfalso.
    refine (divergence_closed_under_eval _ _ (ex_intro _ vs (conj vvs' es))).
    + refine (eval_ctx₀ phole (eval_beta _) I).
      exact I.
    + cbn.
      eapply F.divergence_closed_under_eval.
      eapply (eval_ctx₀' (eval_case_inr (I : Value F.unit))); F.inferContext; now cbn.
      cbn.
      eapply stlcOmega_div.
  - eapply termrelnd₀_antired.
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      unfold caseBool, caseBool_pctx, caseUVal_pctx.
      eapply evalStepStar.
      * eapply eval_eval₀.
        eapply eval_case_inl.
        exact vvs.
      * eapply rt1n_refl.
    + eapply rt1n_refl.
    + eapply valrel_termrelnd₀.
      assumption.
Qed.

Lemma fizzbuzz {n p τ} : fxToIs (pEmulDV n p (compfi_ty τ)) = fxToIs (embed τ).
Proof.
  induction τ; cbn; now f_equal.
Qed.

Lemma value_sub t (v: F.Value t) :
  ∀ (ζ: Sub F.Tm), Value t[ζ].
Proof.
  induction t; crush; cbn; apply IHt;
  assumption.
Qed.
Hint Resolve value_sub.

Lemma inject_tarr_works {n w d p vs vu τ1 τ2} :
  (forall n' w' vs1 vu1, n' <= n → inject_works_prop n' w' d p vs1 vu1 τ2) →
  (forall n' w' vs1 vu1, n' <= n → extract_works_prop n' w' d p vs1 vu1 τ1) →
  inject_works_prop (S n) w d p vs vu (F.tarr τ1 τ2).
Proof.
  intros IHinj IHext dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  eapply termrelnd₀_antired.
  - eapply evalToStar.
    unfold inject, injectA; cbn.
    eapply (F.eval_ctx₀ F.phole); simpl;
      eauto using F.eval_beta.
  - apply rt1n_refl.
  - crushTyping.
    change (eraseAnnot _) with (inject n τ2) at 1.
    change (eraseAnnot _) with (extract n τ1) at 1.
    rewrite inject_sub, extract_sub.
    destruct (valrel_ptarr_inversion vr) as (tsb & tub & tslam & tulam & tytsb & tytub & trtsub).

    eapply valrel_termrelnd₀.
    eapply valrel_inArr.
    rewrite tulam.
    erewrite <- fizzbuzz.
    change (UValFI n (compfi_ty τ1)) with (repEmul (pEmulDV n p (compfi_ty τ1))).
    apply valrel_lambda.
    crushOfType; crush; eauto using injectT, extractT.
    rewrite ?compiler_is_fxToIs_embed; eauto using tytub.

    intros w' vs' vu' fw' szvu vr'.
    destruct (valrel_implies_Value vr') as (vvs' & vvu').
    cbn.
    crush.
    rewrite inject_sub, extract_sub.

    rewrite <-ap_liftSub, <-up_liftSub, liftSub_wkm, apply_wkm_beta1_up_cancel.
    assert (dir_world_prec n w' d p) as dwp' by apply (dwp_invert_S' dwp _ fw').
    assert (n <= n) as obv_leq by lia.
    destruct d.
    + (* eapply termrel_size_left. *)
      (* intros sz. *)
      (* cbn in sz. *)
      (* assert (szvs' : (size vs') <= w') by lia. *)
      assert (nsz : forall A, dir_lt = dir_gt -> A) by (intros _ [=]).
      pose proof (IHext _ _ _ _ obv_leq dwp' (nsz _) vr') as extr_tr.
      (* clear sz szvs'. *)
      refine (termrelnd₀_ectx_sub (F.papp₂ (inject n τ2) (F.papp₂ _ F.phole)) _ extr_tr _);
        cbn; eauto using inject_value.
      intros vs2 vr2.
      destruct (valrel_implies_Value vr2) as (vvs2 & _).
      clear extr_tr IHext.
      cbn.
      refine (termrel_antired_star_left _ _).
      eapply evalToStar.
      refine (eval_ctx₀ (F.papp₂ (inject n τ2) F.phole) (F.eval_beta _) _); cbn; eauto using inject_value.

      rewrite valrel_fixp in vr.
      destruct vr as [_ vr].
      destruct vr as (tsb' & tub' & τ₁' & τ₂' & eq1 & eq2 & vr).
      inversion eq1; inversion eq2; subst.
      specialize (vr w' fw' vs2 vu' (nsz _) vr2).
      eapply (termrel_ectx' vr); F.inferContext; I.inferContext;
        cbn; eauto using inject_value.
      intros w3 fw3 vs3 vu3 vr3.
      eapply termrelnd₀_termrel.
      refine (IHinj n w3 vs3 vu3 _ _ vr3); try lia; eauto using dwp_mono.
    + destruct (dwp_invert_gt dwp) as (-> & ineq).
      pose proof (IHext _ _ _ _ obv_leq dwp' (fun _ => szvu eq_refl) vr') as extr_tr.
      refine (termrelnd₀_ectx_sub (F.papp₂ (inject n τ2) (F.papp₂ _ F.phole)) _ extr_tr _);
        cbn; eauto using inject_value.
      intros vs2 vr2.
      destruct (valrel_implies_Value vr2) as (vvs2 & _).
      clear extr_tr IHext.
      cbn.
      refine (termrel_antired_star_left _ _).
      eapply evalToStar.
      refine (eval_ctx₀ (F.papp₂ (inject n τ2) F.phole) (F.eval_beta _) _); cbn; eauto using inject_value.

      rewrite valrel_fixp in vr.
      destruct vr as [_ vr].
      destruct vr as (tsb' & tub' & τ₁' & τ₂' & eq1 & eq2 & vr).
      inversion eq1; inversion eq2; subst.
      specialize (vr w' fw' vs2 vu' (fun _ => szvu eq_refl) vr2).
      eapply (termrel_ectx' vr); F.inferContext; I.inferContext;
        cbn; eauto using inject_value.
      intros w3 fw3 vs3 vu3 vr3.
      eapply termrelnd₀_termrel.
      refine (IHinj n w3 vs3 vu3 _ _ vr3); try lia; eauto using dwp_mono.
Qed.

Lemma inject_tprod_works {n w d p τ₁ τ₂ vs vu} :
  (forall n' w' vs1 vu1, n' <= n → inject_works_prop n' w' d p vs1 vu1 τ₁) →
  (forall n' w' vs1 vu1, n' <= n → inject_works_prop n' w' d p vs1 vu1 τ₂) →
  inject_works_prop (S n) w d p vs vu (F.tprod τ₁ τ₂).
Proof.
  intros inj₁ inj₂ dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].

  destruct (valrel_ptprod_inversion vr) as (vs1 & vs2 & vu1 & vu2 & -> & -> & ot1 & ot2 & vr').
  destruct ot1 as [tvs1 tvu1].
  destruct ot2 as [tvs2 tvu2].
  cbn in vvs.
  eapply termrelnd₀_antired_left.
  { (* beta-reduce *)
    eapply evalStepStar.
    apply eval₀_to_eval.
    unfold inject, injectA; cbn.
    eapply eval_beta; now cbn.
    eapply rt1n_refl.
  }
  change (eraseAnnot _) with (inject n τ₁) at 1.
  change (eraseAnnot _) with (inject n τ₂).

  destruct vvs as (vvs1 & vvs2).
  destruct w.
  - destruct (inject_terminates n tvs1) as (vs1' & vvs1' & es1).
    destruct (inject_terminates n tvs2) as (vs2' & vvs2' & es2).
    eapply termrelnd₀_antired_left.
    { crushTyping.
      rewrite ?inject_sub; cbn.
      eapply evalStepStar.
      { eapply (eval_ctx₀' (eval_proj₁ vvs1 vvs2)); F.inferContext; cbn; eauto using inject_value. }
      eapply evalStepTrans.
      { eapply (evalstar_ctx' es1); F.inferContext; cbn; eauto using inject_value. }
      eapply evalStepStar.
      { eapply (eval_ctx₀' (eval_proj₂ vvs1 vvs2)); F.inferContext; cbn; eauto using inject_value. }
      eapply evalStepTrans.
      { eapply (evalstar_ctx' es2); F.inferContext; cbn; eauto using inject_value. }
      eapply rt1n_refl.
    }
    cbn.
    eapply valrel_termrelnd₀.
    destruct tvu1 as (vvu1 & tvu1).
    destruct tvu2 as (vvu2 & tvu2).
    rewrite <- compiler_is_fxToIs_embed in *.
    eapply valrel_inProd''.
    rewrite valrel_fixp; unfold valrel'; cbn.
    split; [|split].
    split; split; cbn; crushTyping; eauto.
    + eapply (F.preservation_star es1).
      crushTyping.
      rewrite repEmul_embed_leftinv.
      eauto with typing uval_typing.
    + eapply (F.preservation_star es2).
      crushTyping.
      rewrite repEmul_embed_leftinv.
      eauto with typing uval_typing.
    + intros w' fw; exfalso; lia.
    + intros w' fw; exfalso; lia.
  -  assert (fw : w < S w) by lia.
     destruct (vr' w fw) as (vr1 & vr2).
     fold embed in *.
     assert (nlen : n <= n) by lia.
     eapply dwp_invert_S in dwp.
     specialize (inj₁ n w vs1 vu1 nlen dwp vr1).
     specialize (inj₂ n w vs2 vu2 nlen dwp vr2).
     unfold inject, injectA; cbn.
     change (eraseAnnot _) with (inject n τ₁) at 1.
     change (eraseAnnot _) with (inject n τ₂).
     eapply termrelnd₀_antired_left.
     {crushTyping.
      rewrite ?inject_sub; cbn.
      eapply evalStepStar.
      { eapply (eval_ctx₀' (eval_proj₁ vvs1 vvs2)); F.inferContext; cbn; eauto using inject_value. }
      cbn.
      eapply rt1n_refl.
     }
     eapply (termrelnd₀_ectx' inj₁); F.inferContext; I.inferContext; [|now cbn].
     intros vs3 vu3 vr3.
     destruct (valrel_implies_Value vr3) as (vvs3 & vvu3).
     cbn.
     eapply termrelnd₀_antired_left.
     { (* beta-reduce *)
      eapply evalStepStar.
      { eapply (eval_ctx₀' (eval_proj₂ vvs1 vvs2)); F.inferContext; cbn; eauto using inject_value. }
      cbn.
      eapply rt1n_refl.
     }
     eapply (termrelnd₀_ectx' inj₂); F.inferContext; I.inferContext; cbn; eauto.
     intros vs4 vu4 vr4.
     now eapply valrel_termrelnd₀, valrel_inProd'', valrel_pair'.
Qed.

Lemma inject_tsum_works {n w d p τ₁ τ₂ vs vu} :
  (forall n' w' vs1 vu1, n' <= n → inject_works_prop n' w' d p vs1 vu1 τ₁) →
  (forall n' w' vs1 vu1, n' <= n → inject_works_prop n' w' d p vs1 vu1 τ₂) →
  inject_works_prop (S n) w d p vs vu (F.tsum τ₁ τ₂).
Proof.
  intros inj₁ inj₂ dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].

  (* assert (w < S w) as fw by lia. *)
  (* assert (dir_world_prec n w d p) as dwp' by eauto using dwp_invert_S. *)

  destruct (valrel_ptsum_inversion vr) as (vs' & vu' & [(? & ? & ot' & vrs)|(? & ? & ot' & vrs) ]);
    (* specialize (vrs w fw); *)
    subst; cbn in vvs.
  - eapply termrelnd₀_antired_left.
    { (* beta-reduce *)
      eapply evalStepStar.
      apply eval₀_to_eval.
      unfold inject, injectA; cbn.
      eauto with eval.
      change (eraseAnnot _) with (inject n τ₁) at 1.
      change (eraseAnnot _) with (inject n τ₂).
      rewrite ?inject_sub; cbn.
      eapply evalToStar.
      refine (eval_ctx₀ (F.pinl F.phole) _ I).
      repeat change (apTm ?ξ ?t) with t[ξ].
      rewrite ?inject_sub.
      crush.
    }
    cbn.
    repeat change (apTm ?ξ ?t) with t[ξ].
    rewrite ?inject_sub.

    destruct w.
    + inversion tvs; subst.
      inversion tvu; subst.
      rewrite <-compiler_is_fxToIs_embed in H2.
      destruct (inject_terminates n (conj vvs H1)) as (vs2 & vvs2 & es2).
      eapply termrelnd₀_antired_left.
      { change (inl (inl ?x)) with (pctx_app x (pinl (pinl phole))).
        refine (evalstar_ctx _ _ es2); now cbn. }
      cbn.
      eapply valrel_termrelnd₀.
      eapply valrel_inSum''.
      eapply valrel_inl''.
      assert (tyvs2 : ⟪ PseudoTypeFI.F.empty ⊢ vs2 : repEmul (pEmulDV n p (compfi_ty τ₁)) ⟫).
      * eapply (F.preservation_star es2).
        crushTyping.
        rewrite repEmul_embed_leftinv.
        eapply injectT.
      * now repeat split.
      * intros w' fw; exfalso; lia.
    + assert (fw : w < S w) by lia.
      specialize (vrs w fw).
      fold embed in vrs.
      assert (nlen : n <= n) by lia.
      eapply dwp_invert_S in dwp.
      specialize (inj₁ n w vs' vu' nlen dwp vrs).
      change (inl (inl ?t)) with (pctx_app t (pinl (pinl phole))).
      change (I.inl ?t) with (I.pctx_app t (I.pinl I.phole)).
      eapply termrelnd₀_ectx; cbn; eauto.
      intros vs2 vu2 vr2.
      cbn.
      eapply valrel_termrelnd₀.
      eauto using valrel_inSum'', valrel_inl'.
  - eapply termrelnd₀_antired_left.
    { (* beta-reduce *)
      eapply evalStepStar.
      apply eval₀_to_eval.
      unfold inject, injectA; cbn.
      eauto with eval.
      change (eraseAnnot _) with (inject n τ₁) at 1.
      change (eraseAnnot _) with (inject n τ₂).
      rewrite ?inject_sub; cbn.
      eapply evalToStar.
      refine (eval_ctx₀ (F.pinl F.phole) _ I).
      repeat change (apTm ?ξ ?t) with t[ξ].
      rewrite ?inject_sub.
      crush.
    }
    cbn.
    repeat change (apTm ?ξ ?t) with t[ξ].
    rewrite ?inject_sub.

    destruct w.
    + inversion tvs; subst.
      inversion tvu; subst.
      rewrite <-compiler_is_fxToIs_embed in H2.
      destruct (inject_terminates n (conj vvs H1)) as (vs2 & vvs2 & es2).
      eapply termrelnd₀_antired_left.
      { change (inl (inr ?x)) with (pctx_app x (pinl (pinr phole))).
        refine (evalstar_ctx _ _ es2); now cbn. }
      cbn.
      eapply valrel_termrelnd₀.
      eapply valrel_inSum''.
      eapply valrel_inr''.
      assert (tyvs2 : ⟪ PseudoTypeFI.F.empty ⊢ vs2 : repEmul (pEmulDV n p (compfi_ty τ₂)) ⟫).
      * eapply (F.preservation_star es2).
        crushTyping.
        rewrite repEmul_embed_leftinv.
        eapply injectT.
      * now repeat split.
      * intros w' fw; exfalso; lia.
    + assert (fw : w < S w) by lia.
      specialize (vrs w fw).
      fold embed in vrs.
      assert (nlen : n <= n) by lia.
      eapply dwp_invert_S in dwp.
      specialize (inj₂ n w vs' vu' nlen dwp vrs).
      change (inl (inr ?t)) with (pctx_app t (pinl (pinr phole))).
      change (I.inr ?t) with (I.pctx_app t (I.pinr I.phole)).
      eapply termrelnd₀_ectx; cbn; eauto.
      intros vs2 vu2 vr2.
      cbn.
      eapply valrel_termrelnd₀.
      eauto using valrel_inSum'', valrel_inr'.
Qed.


Lemma extract_tarr_works {n w d p τ₁ τ₂ vs vu} :
  (forall w' vs' vu', w' < w → inject_works_prop n w' d p vs' vu' τ₁) →
  (forall w' vs' vu', w' < w → extract_works_prop n w' d p vs' vu' τ₂) →
  extract_works_prop (S n) w d p vs vu (F.tarr τ₁ τ₂).
Proof.
  intros inj1 extr2 dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].
  eapply termrelnd₀_antired_left.
  { now eapply evalToStar, eval_eval₀, eval_beta. }
  fold stlcOmega.
  cbn. fold inject extract.
  repeat change (apTm ?x ?t) with (ap x t).
  fold eraseAnnot.
  change (eraseAnnot _) with (inject n τ₁) at 3.
  change (eraseAnnot _) with (caseArr n (F.var 1) (compfi_ty τ₁) (compfi_ty τ₂)) at 2.
  change (eraseAnnot _) with (extract n τ₂).
  rewrite inject_sub, extract_sub, caseArr_sub.
  cbn.
  rewrite (wsClosed_invariant (wt_implies_ws tvs)).
  destruct (invert_valrel_pEmulDV_for_caseUValArr vr) as [(vs2 & -> & es2 & vr2) | (-> & div)].
  - fold compfi_ty in *.
    destruct (valrel_implies_OfType vr2) as [[vvs2 tvs2] _].
    cbn in tvs2.
    eapply valrel_termrelnd₀.
    replace τ₁ with (repEmul (embed τ₁)) at 2 by eapply repEmul_embed_leftinv.
    inversion tvu; subst; cbn in vvu; try contradiction.
    rewrite compiler_is_fxToIs_embed.
    pose proof (tvs2w := typing_sub tvs2 _ wkm (wtSub_wkm _ τ₁)).
    rewrite (wsClosed_invariant (wt_implies_ws tvs2)) in tvs2w.
    refine (valrel_lambda _ _); crushOfType; rewrite <-?compiler_is_fxToIs_embed, ?repEmul_embed_leftinv; eauto;
      crushTyping; eauto with typing uval_typing.
    subst.

    destruct (valrel_implies_Value H2) as [vvs3 vvu3].
    rewrite inject_sub, extract_sub, caseArr_sub.
    cbn.
    repeat change (apTm ?x ?t) with (ap x t).
    rewrite (wsClosed_invariant (wt_implies_ws tvs2)).
    pose proof (dwp3 := dwp_invert_S' dwp w' H).
    specialize (inj1 w' vs vu H dwp3 H2).

    refine (termrel_antired_star_left _ _).
    { unfold caseArr, caseArr_pctx, caseUVal_pctx; cbn.
      change (app ?t1 (app ?t2 ?t3)) with (F.pctx_app t2 (F.papp₂ t1 (F.papp₁ F.phole t3))).
      eapply evalToStar, eval_ctx₀; [eapply eval_case_inl|]; cbn; eauto using extract_value.
    }
    cbn.

    refine (termrelnd₀_ectx_sub (F.papp₂ _ (F.papp₂ _ F.phole)) _ inj1 _);
      cbn; eauto using extract_value.

    intros vs4 vr4.
    destruct (valrel_implies_Value vr4) as [vvs4 _].

    cbn in vr.
    destruct (valrel_ptarr_inversion vr2) as (tsb & tub & -> & [=] & ttsb & ttub & trb); subst.

    refine (termrel_antired_star_left _ _).
    { change (app ?t1 ?t2) with (F.pctx_app t2 (F.papp₂ t1 F.phole)).
      eapply evalToStar, eval_ctx₀; [eapply eval_beta|]; cbn; eauto using extract_value.
    }
    cbn.

    specialize (trb w' vs4 vu H H0 vr4).
    eapply (termrel_ectx' trb); F.inferContext; I.inferContext; eauto using extract_value.

    intros w5 fw5 vs5 vu5 vr5.
    cbn.
    eapply termrel_size_right'.
    intros sz5.
    pose proof (dwp5 := dwp_mono dwp3 _ fw5).
    eapply termrelnd₀_termrel.
    eapply extr2; eauto using extract_value.
    lia.
    intros eq; specialize (sz5 eq); lia.
  - fold compfi_ty in div.
    eapply dwp_invert_imprecise in dwp.
    subst.
    eapply valrel_termrelnd₀.
    cbn in tvu.
    inversion tvu; subst; cbn in vvu; try contradiction.
    replace τ₁ with (repEmul (embed τ₁)) at 2 by eapply repEmul_embed_leftinv.
    rewrite ?compiler_is_fxToIs_embed in *.
    refine (valrel_lambda _ _).
    { pose proof (tvsw := typing_sub tvs _ wkm (wtSub_wkm _ τ₁)).
      rewrite (wsClosed_invariant (wt_implies_ws tvs)) in tvsw.
      rewrite <-compiler_is_fxToIs_embed in tvsw.
      crushOfType;
        crushTyping;
      rewrite ?repEmul_embed_leftinv, <-?compiler_is_fxToIs_embed;
        eauto with typing uval_typing.
    }
    intros w2 vs2 vu2 fw2 _ vr2.
    eapply termrel_div_lt.
    cbn.
    repeat change (apTm ?x ?t) with (ap x t).
    rewrite inject_sub, extract_sub, caseArr_sub.
    rewrite (wsClosed_invariant (wt_implies_ws tvs)).
    refine (divergence_closed_under_evalcontext _ div (F.papp₂ _ (F.papp₁ F.phole _)) _).
    cbn.
    eauto using extract_value.
Qed.

Lemma extract_tprod_works {n w d p τ₁ τ₂ vs vu} :
  (forall n' w' vs1 vu1, n' <= n → extract_works_prop n' w' d p vs1 vu1 τ₁) →
  (forall n' w' vs1 vu1, n' <= n → extract_works_prop n' w' d p vs1 vu1 τ₂) →
  extract_works_prop (S n) w d p vs vu (F.tprod τ₁ τ₂).
Proof.
  intros extr₁ extr₂ dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].

  eapply termrelnd₀_antired_left.
  { (* beta-reduce *)
    eapply evalToStar.
    apply eval₀_to_eval.
    eapply eval_beta; now cbn.
  }
  cbn.
  crushTyping.
  repeat fold eraseAnnot.
  change (eraseAnnot _) with (extract n τ₁) at 1.
  change (eraseAnnot _) with (extract n τ₂).
  rewrite ?extract_sub.

  destruct (invert_valrel_pEmulDV_for_caseUValProd vr) as [(vs1 & -> & es1 & vr1)|(-> & div)].
  - destruct (valrel_implies_Value vr1) as (vvs1 & _).
    destruct (valrel_ptprod_inversion vr1) as (vs11 & vs12 & vu11 & vu12 & -> & -> & ot11 & ot12 & vr1').
    destruct (OfType_implies_Value ot11) as (vvs11 & _).
    destruct (OfType_implies_Value ot12) as (vvs12 & _).
    eapply termrelnd₀_antired_left.
    { eapply evalStepStar.
      eapply (F.eval_ctx₀' (F.eval_case_inl (conj vvs11 vvs12 : Value (pair vs11 vs12)))); F.inferContext; cbn; eauto using extract_value.
      cbn.
      eapply evalToStar.
      eapply (F.eval_ctx₀' (F.eval_proj₁ vvs11 vvs12)); F.inferContext; cbn; eauto using extract_value.
    }
    cbn.
    destruct d.
    * clear sz.
      intros vs2 vvs2 es2.
      exists (I.pair vu11 vu12).
      split; [|split]; eauto with eval.
      destruct (evalStar_ectx_inv (F.ppair₁ F.phole _) _ I _ es2 vvs2) as (vs11' & vvs11' & es11' & es3).
      cbn in es3.
      assert (es4 : F.evalStar (pair vs11' (app (extract n τ₂) vs12)) vs2).
      { refine (determinacyStar _ es3 (values_are_normal vvs2)).
        eapply evalStepStar.
        eapply (eval_ctx₀' (eval_case_inl (conj vvs11 vvs12 : Value (F.pair vs11 vs12)))); F.inferContext; cbn; eauto using extract_value.
        eapply evalToStar.
        eapply (eval_ctx₀' (eval_proj₂ vvs11 vvs12)); F.inferContext; cbn; eauto using extract_value.
      }
      assert (eC3 : ECtx (F.ppair₂ vs11' F.phole)) by now cbn.
      destruct (evalStar_ectx_inv (F.ppair₂ _ F.phole) _ eC3 _ es4 vvs2) as (vs12' & vvs12' & es12' & es5); clear eC3.
      cbn in es5.
      eapply value_evalStar in es5; [|now cbn];subst.
      destruct ot11 as (ots11 & otu11).
      destruct ot12 as (ots12 & otu12).
      eapply valrel_pair''.
      { split.
        split; [assumption|].
        eapply (F.preservation_star es11').
        rewrite repEmul_embed_leftinv.
        eauto using extractT with typing uval_typing.
        refine (OfTypeStlcIso_fxToIs _ otu11);
        cbn; now apply compiler_is_fxToIs_embed.
      }
      { split.
        split; [assumption|].
        eapply (F.preservation_star es12').
        rewrite repEmul_embed_leftinv.
        eauto using extractT with typing uval_typing.
        refine (OfTypeStlcIso_fxToIs _ otu12);
        cbn; now apply compiler_is_fxToIs_embed.
      }
      { intros w' fw.
        destruct (vr1' w' fw) as (vr11 & vr12).
        destruct w; [exfalso;lia|].
        eapply dwp_invert_S in dwp.
        assert (nlen : n <= n) by lia.
        assert (dwp' : dir_world_prec n w' dir_lt p) by eauto using dwp_mono with arith.
        assert (szabs : forall A, dir_lt=dir_gt -> A) by intros _ [=].
        specialize (extr₁ n w' vs11 vu11 nlen dwp' (szabs _) vr11).
        destruct (extr₁ _ vvs11' es11') as (vu3 & vvu3 & eu3 & vr3).
        destruct (valrel_implies_Value vr11) as (_ & vvu11).
        eapply I.value_evalStar in eu3; now subst.
      }
      { intros w' fw.
        destruct (vr1' w' fw) as (vr11 & vr12).
        destruct w; [exfalso;lia|].
        eapply dwp_invert_S in dwp.
        assert (nlen : n <= n) by lia.
        assert (dwp' : dir_world_prec n w' dir_lt p) by eauto using dwp_mono with arith.
        assert (szabs : forall A, dir_lt=dir_gt -> A) by intros _ [=].
        specialize (extr₂ n w' _ _ nlen dwp' (szabs _) vr12).
        destruct (extr₂ _ vvs12' es12') as (vu3 & vvu3 & eu3 & vr3).
        destruct (valrel_implies_Value vr12) as (_ & vvu12).
        eapply I.value_evalStar in eu3; now subst.
      }
    * specialize (sz eq_refl).
      cbn in sz.
      assert (nlen : n <= n) by lia.
      destruct w; [exfalso; lia|].
      eapply dwp_invert_S in dwp.
      assert (sz1 : I.size vu11 <= w) by lia.
      assert (sz2 : I.size vu12 <= w) by lia.
      assert (fw : w < S w) by lia.
      destruct (vr1' w fw) as (vr11 & vr12).
      specialize (extr₁ n w _ _ nlen dwp (fun _ => sz1) vr11).
      specialize (extr₂ n w _ _ nlen dwp (fun _ => sz2) vr12).
      eapply (termrelnd₀_ectx' extr₁); [F.inferContext|I.inferContext|idtac|now cbn|now cbn].
      intros vs21 vu21 vr21.
      destruct (valrel_implies_Value vr21) as [vvs21 vvu21].
      eapply termrelnd₀_antired_left.
      { cbn.
        eapply evalStepStar.
        eapply (eval_ctx₀' (eval_case_inl (conj vvs11 vvs12 : Value (F.pair vs11 vs12)))); F.inferContext; cbn; eauto using extract_value.
        eapply evalToStar.
        eapply (eval_ctx₀' (eval_proj₂ vvs11 vvs12)); F.inferContext; cbn; eauto using extract_value.
      }
      eapply (termrelnd₀_ectx' extr₂); [F.inferContext| I.inferContext|idtac|now cbn|now cbn].
      intros vs31 vu31 vr31.
      eapply valrel_termrelnd₀.
      now eapply valrel_pair'.
  - eapply dwp_invert_imprecise in dwp; subst.
    eapply termrelnd₀_div_lt.
    unfold caseProd,caseProd_pctx, caseUVal_pctx, stlcOmega in div.
    cbn in div.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext.
    cbn; eauto using extract_value.
Qed.

Lemma extract_tsum_works {n w d p τ₁ τ₂ vs vu} :
  (forall n' w' vs1 vu1, n' <= n → extract_works_prop n' w' d p vs1 vu1 τ₁) →
  (forall n' w' vs2 vu2, n' <= n → extract_works_prop n' w' d p vs2 vu2 τ₂) →
  extract_works_prop (S n) w d p vs vu (F.tsum τ₁ τ₂).
Proof.
  intros extr1 extr2 dwp szvs vr.
  (* destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]]. *)

  rewrite valrel_fixp in vr.
  destruct vr as [ot [(-> & ->)|(vs' & -> & vr)]].
  - rewrite (dwp_invert_imprecise dwp) in *.
    intros vs' vvs' es.
    assert (term : (F.app (extract (S n) (τ₁ ⊎ τ₂)) (unkUVal (S n))) ⇓) by (now exists vs').
    contradict term.
    eapply divergence_closed_under_eval.
    eapply eval_eval₀.
    eapply eval_beta; now cbn.
    refine (divergence_closed_under_evalcontext _ _ (pcaseof₁ phole _ _) _); [|now cbn].
    fold apTm.
    repeat change (apTm ?x ?t) with (ap x t).
    fold eraseAnnot.
    rewrite eraseAnnot_stlcOmegaA, stlcOmega_sub.
    cbn.
    eapply divergence_closed_under_eval.
    eapply eval_eval₀.
    eapply eval_case_inr; now cbn.
    rewrite stlcOmega_sub.
    eapply stlcOmega_div.
  - cbn in vr.
    destruct (OfType_implies_Value ot) as [vvs' vvu].
    eapply termrelnd₀_antired_left.
    { eapply evalStepStar.
      unfold extract, extractA; cbn.
      eapply (F.eval_ctx₀ F.phole); [|now cbn].
      eauto using F.eval_beta.
      crushTyping.
      change (eraseAnnot _) with (extract n τ₂) at 3.
      change (eraseAnnot _) with (extract n τ₁) at 2.
      rewrite eraseAnnot_caseSumA.
      rewrite ?extract_sub, caseSum_sub; cbn.
      eapply evalToStar.
      eapply (F.eval_ctx₀ (F.pcaseof₁ F.phole _ _)); [|now cbn].
      eapply F.eval_case_inl; now cbn in *.
    }
    destruct vs'; destruct vu; try contradiction;
    cbn in vr.
    + clear extr2.
      eapply termrelnd₀_antired_left.
      { eapply evalToStar.
        eapply (F.eval_ctx₀ F.phole); [|now cbn].
        eapply F.eval_case_inl; now cbn in *.
      }
      cbn.
      repeat change (apTm ?x ?t) with (ap x t).
      repeat rewrite extract_sub.
      destruct d.
      * clear szvs.
        intros vs2 vvs2 es2.
        exists (I.inl vu).
        split; [|split]; eauto with eval.
        destruct (evalStar_ectx_inv (F.pinl F.phole) _ I _ es2 vvs2) as (vs3 & vvs3 & es3 & es3').
        cbn in es3'.
        assert (vivs3 : Value (F.inl vs3)) by (now cbn).
        eapply (value_evalStar vivs3) in es3'; subst.
        eapply valrel_inl''.
        { destruct (OfType_inversion_pEmulDV ot) as (_ & _ & tyvs' & tyvu).
          inversion tyvu; subst.
          inversion tyvs'; subst.
          inversion H2; clear H2; subst.
          fold UValFI in H3.
          split; split;
            try rewrite <-compiler_is_fxToIs_embed;
            eauto.
          rewrite repEmul_embed_leftinv.
          refine (F.preservation_star es3 _);
            eauto with typing uval_typing.
        }
        intros w' fw.
        destruct w; [exfalso; lia|].
        eapply dwp_invert_S in dwp.
        assert (dwp' : dir_world_prec n w' dir_lt p) by (eauto using dwp_mono with arith).
        specialize (vr w' fw).
        assert (nlen : n <= n) by lia.
        assert (szvs' : forall A, dir_lt = dir_gt -> A) by (intros _ [=]).
        destruct (extr1 n w' vs' vu nlen dwp' (szvs' _) vr vs3 vvs3 es3) as (vu' & vvu' & eu' & vr').
        cbn in vvu.
        now destruct (I.value_evalStar vvu eu').
      * specialize (szvs eq_refl).
        cbn in szvs.
        (* domi: this is where we use the size vu <= w requirement! *)
        destruct w; [exfalso; lia|].
        assert (fw : w < S w) by lia.
        specialize (vr w fw).
        assert (nlen : n <= n) by lia.
        eapply dwp_invert_S in dwp.
        assert (szvs' : I.size vu <= w) by lia.
        specialize (extr1 n w vs' vu nlen dwp (fun _ => szvs') vr).
        refine (termrelnd₀_ectx (Cs := F.pinl F.phole) (Cu := I.pinl I.phole) I I extr1 _).
        intros vs2 vu2 vr2.
        eapply valrel_termrelnd₀.
        now eapply valrel_inl'.
    + clear extr1.
      eapply termrelnd₀_antired_left.
      { eapply evalToStar.
        eapply (F.eval_ctx₀ F.phole); [|now cbn].
        eapply F.eval_case_inr; now cbn in *.
      }
      cbn.
      repeat change (apTm ?x ?t) with (ap x t).
      repeat rewrite extract_sub.
      destruct d.
      * clear szvs.
        intros vs2 vvs2 es2.
        exists (I.inr vu).
        split; [|split]; eauto with eval.
        destruct (evalStar_ectx_inv (F.pinr F.phole) _ I _ es2 vvs2) as (vs3 & vvs3 & es3 & es3').
        cbn in es3'.
        assert (vivs3 : F.Value (F.inr vs3)) by (now cbn).
        eapply (value_evalStar vivs3) in es3'; subst.
        eapply valrel_inr''.
        { destruct (OfType_inversion_pEmulDV ot) as (_ & _ & tyvs' & tyvu).
          inversion tyvu; subst.
          inversion tyvs'; subst.
          inversion H2; clear H2; subst.
          fold UValFI in H3.
          split; split;
            try rewrite <-compiler_is_fxToIs_embed;
            eauto.
          rewrite repEmul_embed_leftinv.
          refine (F.preservation_star es3 _);
            eauto using extractT with typing.
        }
        intros w' fw.
        destruct w; [exfalso; lia|].
        eapply dwp_invert_S in dwp.
        assert (dwp' : dir_world_prec n w' dir_lt p) by (eauto using dwp_mono with arith).
        specialize (vr w' fw).
        assert (nlen : n <= n) by lia.
        assert (szvs' : forall A, dir_lt = dir_gt -> A) by (intros _ [=]).
        destruct (extr2 n w' vs' vu nlen dwp' (szvs' _) vr vs3 vvs3 es3) as (vu' & vvu' & eu' & vr').
        cbn in vvu.
        now destruct (I.value_evalStar vvu eu').
      * specialize (szvs eq_refl).
        cbn in szvs.
        destruct w; [exfalso; lia|].
        assert (fw : w < S w) by lia.
        specialize (vr w fw).
        assert (nlen : n <= n) by lia.
        eapply dwp_invert_S in dwp.
        assert (szvs' : I.size vu <= w) by lia.
        specialize (extr2 n w vs' vu nlen dwp (fun _ => szvs') vr).
        refine (termrelnd₀_ectx (Cs := F.pinr F.phole) (Cu := I.pinr I.phole) I I extr2 _).
        intros vs2 vu2 vr2.
        eapply valrel_termrelnd₀.
        now eapply valrel_inr'.
Qed.

Lemma inject_works {n w d p τ vs vu} :
  inject_works_prop n w d p vs vu τ
with extract_works {n w d p τ vs vu} :
  extract_works_prop n w d p vs vu τ.
Proof.
  - revert n w vs vu.
    induction τ;
      intros n w vs vu dwp vr;
      destruct (valrel_implies_OfType vr) as ((_ & tvs) & (closed_vu & _));
      destruct (valrel_implies_Value vr) as (vvs & vvu);
      simpl.
    + (* τ₁ ⇒ τ₂ *)
      destruct n; [refine (inject_zero_works dwp vr)|].
      eapply inject_tarr_works;
        eauto using dwp_mono.
    + (* tunit *)
      destruct n; [refine (inject_zero_works dwp vr)|].
      eapply inject_unit_works; now assumption.
    + (* tbool *)
      destruct n; [refine (inject_zero_works dwp vr)|].
      eapply inject_bool_works; now assumption.
    (* + (* tprod τ₁ τ₂ *) *)
    (*   eapply inject_tprod_works; *)
    (*     eauto using dwp_mono. *)
    + (* τ₁ × τ₂ *)
      destruct n; [refine (inject_zero_works dwp vr)|].
      eapply inject_tprod_works;
        eauto using dwp_mono.
    + (* τ₁ ⊎ τ₂ *)
      destruct n; [refine (inject_zero_works dwp vr)|].
      eapply inject_tsum_works;
        eauto using dwp_mono.
  - (* extract *)
    revert n w vs vu.
    induction τ;
      intros n w vs vu dwp sz vr;
      destruct (valrel_implies_OfType vr) as ((_ & tvs) & (closed_vu & _));
      destruct (valrel_implies_Value vr) as (vvs & vvu);
      simpl.
    + (* τ₁ ⇒ τ₂ *)
      destruct n; [refine (extract_zero_works dwp sz vr)|].
      eapply extract_tarr_works;
        eauto using dwp_mono.
    + (* tunit *)
      destruct n; [refine (extract_zero_works dwp sz vr)|].
      eapply extract_unit_works;
        eauto using dwp_mono.
    (* + (* tbool *) *)
    (*   eapply extract_tbool_works; *)
    (*     eauto using dwp_mono. *)
    (* + (* tprod τ₁ τ₂ *) *)
    (*   eapply extract_tprod_works; *)
    (*     eauto using dwp_mono. *)

    + (* tbool *)
      destruct n; [refine (extract_zero_works dwp sz vr)|].
      eapply extract_bool_works;
        eauto using dwp_mono.
    + (* τ₁ × τ₂ *)
      destruct n; [refine (extract_zero_works dwp sz vr)|].
      eapply extract_tprod_works;
        eauto using dwp_mono.
    + (* τ₁ ⊎ τ₂ *)
      destruct n; [refine (extract_zero_works dwp sz vr)|].
      eapply extract_tsum_works;
        eauto using dwp_mono.
Qed.

Lemma inject_works_open {d n m τ ts tu Γ p} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : embed τ ⟫ →
  ⟪ Γ ⊩ F.app (inject n τ) ts ⟦ d , m ⟧ tu : pEmulDV n p (compfi_ty τ) ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & lr).
  unfold OpenLRCtxN; split; [|split].
  - crushTyping.
    rewrite repEmul_embed_leftinv.
    eauto using injectT.
  - cbn.
    rewrite compiler_is_fxToIs_embed.
    assumption.
  - intros w wm γs γu envrel.
    specialize (lr w wm γs γu envrel).

    cbn; crushTyping.
    rewrite inject_sub.

    eapply (termrel_ectx' lr); F.inferContext; I.inferContext;
      crush; eauto using inject_value.

    cbn.
    eapply termrel_size_right'.
    intros sz.
    eapply termrelnd₀_termrel.
    eapply inject_works; eauto using dwp_mono.
Qed.
