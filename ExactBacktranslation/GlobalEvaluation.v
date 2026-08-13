Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import ExactBacktranslation.CastCommon.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.Fix.
Require Import StlcIso.TypeSafety.
Require Import StlcIso.CanForm.
Require Import Db.Lemmas.

Lemma global_bundle_functional_closed {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall zeta,
    (global_bundle_functional d)[zeta] = global_bundle_functional d.
Proof.
  intros VA VB zeta.
  pose proof (@global_bundle_functional_typing empty A B d VA VB) as Hty.
  pose proof (StlcIso.LemmasTyping.wt_implies_ws Hty) as Hws.
  cbn in Hws.
  exact (wsClosed_invariant Hws zeta).
Qed.

Lemma apply_wkm_beta1_up4_cancel (t x : StlcIso.SpecSyntax.Tm) :
  t[wkm↑↑↑↑][(beta1 x)↑↑↑↑] = t.
Proof.
  change (t[wkm ↑⋆ 4][beta1 x ↑⋆ 4] = t).
  apply apply_wkm_beta1_ups_cancel.
Qed.

Lemma recursive_bundle_loop_closed {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall zeta,
    (ufix₁ (global_bundle_functional d) tunit
      (certificate_bundle_ty d))[zeta] =
    ufix₁ (global_bundle_functional d) tunit
      (certificate_bundle_ty d).
Proof.
  intros VA VB zeta.
  assert (Hty : StlcIso.SpecTyping.Typing empty
    (ufix₁ (global_bundle_functional d) tunit
      (certificate_bundle_ty d))
    (tarr tunit (certificate_bundle_ty d))).
  { eapply ufix₁_typing.
    - eauto with tyvalid cty simple_contr_rec.
    - eapply certificate_bundle_ty_valid;
        eauto using pair_env_valid_nil.
    - now apply global_bundle_functional_typing. }
  pose proof (StlcIso.LemmasTyping.wt_implies_ws Hty) as Hws.
  cbn in Hws. exact (wsClosed_invariant Hws zeta).
Qed.

Lemma iso_value_substitution t :
  StlcIso.SpecEvaluation.Value t ->
  forall ζ, StlcIso.SpecEvaluation.Value t[ζ].
Proof.
  induction t; cbn; intros Hval ζ; try contradiction; try exact I.
  - destruct Hval as [H1 H2]. split.
    + now apply IHt1.
    + now apply IHt2.
  - now apply IHt.
  - now apply IHt.
  - now apply IHt.
Qed.

Lemma global_node_cast_value {H A B} (node : CastNode H A B) self rho :
  StlcIso.SpecEvaluation.Value (global_node_cast node self rho).
Proof.
  destruct node; cbn; repeat split; exact I.
Qed.

Lemma build_certificate_bundle_value {H A B} (d : CastEq H A B) self rho :
  StlcIso.SpecEvaluation.Value (build_certificate_bundle d self rho)
with build_node_bundle_value {H A B} (node : CastNode H A B) self rho :
  StlcIso.SpecEvaluation.Value (build_node_bundle node self rho).
Proof.
  - destruct d; cbn.
    + exact I.
    + split.
      * apply global_node_cast_value.
      * apply build_node_bundle_value.
  - destruct node; cbn; try exact I.
    all: try (split; apply build_certificate_bundle_value).
    all: apply build_certificate_bundle_value.
Qed.

Lemma global_bundle_functional_value {A B} (d : ClosedCastEq A B) :
  StlcIso.SpecEvaluation.Value (global_bundle_functional d).
Proof. exact I. Qed.

(** Bundle construction itself is finite even for cyclic equality: recursive
    bundle selectors occur only underneath the cast lambdas. *)
Lemma global_bundle_body_value {A B} (d : ClosedCastEq A B) self :
  StlcIso.SpecEvaluation.Value
    (build_certificate_bundle d self cast_terms_nil).
Proof. apply build_certificate_bundle_value. Qed.

Lemma tied_certificate_bundle_step {A B} (d : ClosedCastEq A B) :
  StlcIso.SpecEvaluation.eval
    (tied_certificate_bundle d)
    (recursive_certificate_bundle d).
Proof.
  unfold tied_certificate_bundle, recursive_certificate_bundle.
  eapply StlcIso.LemmasEvaluation.eval_ctx
    with (C := StlcIso.SpecSyntax.papp₁ StlcIso.SpecSyntax.phole
      StlcIso.SpecSyntax.unit).
  - exact I.
  - apply ufix_eval₁. apply global_bundle_functional_value.
Qed.

Lemma recursive_certificate_bundle_unfolds {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  StlcIso.SpecEvaluation.evalStar
    (recursive_certificate_bundle d)
    (build_certificate_bundle d (delayed_recursive_certificate_bundle d)
      cast_terms_nil).
Proof.
  intros VA VB.
  unfold recursive_certificate_bundle, delayed_recursive_certificate_bundle,
    global_bundle_functional.
  set (BT := certificate_bundle_ty d).
  set (body := build_certificate_bundle d
    (tm_app (StlcIso.SpecSyntax.var 1) StlcIso.SpecSyntax.unit)
    cast_terms_nil).
  change (StlcIso.SpecEvaluation.evalStar
    (StlcIso.SpecSyntax.app
      (ufix₁ (StlcIso.SpecSyntax.abs (tarr tunit BT)
        (StlcIso.SpecSyntax.abs tunit body)) tunit BT)
      StlcIso.SpecSyntax.unit)
    (build_certificate_bundle d
      (StlcIso.SpecSyntax.app
        (StlcIso.SpecSyntax.abs tunit
          (StlcIso.SpecSyntax.app
            (ufix₁ (StlcIso.SpecSyntax.abs (tarr tunit BT)
              (StlcIso.SpecSyntax.abs tunit body)) tunit BT)
            (StlcIso.SpecSyntax.var 0)))
        StlcIso.SpecSyntax.unit)
      cast_terms_nil)).
  pose proof (@ufix₁_evaln'
    (StlcIso.SpecSyntax.abs tunit body) tunit BT) as Hunfold.
  pose proof (global_bundle_functional_closed d VA VB wkm) as HFclosed.
  unfold global_bundle_functional in HFclosed.
  change ((StlcIso.SpecSyntax.abs (tarr tunit BT)
    (StlcIso.SpecSyntax.abs tunit body))[wkm] =
    StlcIso.SpecSyntax.abs (tarr tunit BT)
      (StlcIso.SpecSyntax.abs tunit body)) in HFclosed.
  cbn in HFclosed.
  assert (HFshift :
    StlcIso.SpecSyntax.abs (tarr tunit BT)
      ((StlcIso.SpecSyntax.abs tunit body)[wkm↑]) =
    StlcIso.SpecSyntax.abs (tarr tunit BT)
      (StlcIso.SpecSyntax.abs tunit body)).
  { cbn. exact HFclosed. }
  rewrite HFshift in Hunfold.
  apply evaln_to_evalStar in Hunfold.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (StlcIso.SpecSyntax.papp₁ StlcIso.SpecSyntax.phole
        StlcIso.SpecSyntax.unit) I Hunfold).
  - unfold body.
    cbn -[build_certificate_bundle ufix₁].
    setoid_rewrite build_certificate_bundle_subst.
    repeat crushDbLemmasRewriteH.
    apply evalToStar, StlcIso.SpecEvaluation.eval_eval₀.
    lazymatch goal with
    | |- StlcIso.SpecEvaluation.eval₀
        (StlcIso.SpecSyntax.app
          (StlcIso.SpecSyntax.abs ?tau ?t) ?v) ?rhs =>
        replace rhs with t[beta1 v]
    end.
    + apply StlcIso.SpecEvaluation.eval_beta. exact I.
    + setoid_rewrite build_certificate_bundle_subst.
      unfold ufix₁.
      cbn -[build_certificate_bundle].
      try setoid_rewrite build_certificate_bundle_subst.
      repeat change (apTm ?xi ?term) with term[xi].
      rewrite <-?ap_liftSub, <-?up_liftSub, ?liftSub_wkm.
      repeat crushDbSyntaxMatchH.
      repeat crushDbLemmasMatchH.
      repeat crushDbLemmasRewriteH.
      repeat crushDbSyntaxMatchH.
      repeat crushDbLemmasMatchH.
      cbn -[build_certificate_bundle].
      setoid_rewrite apply_wkm_beta1_up4_cancel.
      reflexivity.
Qed.

Lemma delayed_recursive_certificate_bundle_step {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  StlcIso.SpecEvaluation.eval
    (delayed_recursive_certificate_bundle d)
    (recursive_certificate_bundle d).
Proof.
  intros VA VB.
  unfold delayed_recursive_certificate_bundle,
    recursive_certificate_bundle.
  unfold tm_app.
  apply StlcIso.SpecEvaluation.eval_eval₀.
  lazymatch goal with
  | |- StlcIso.SpecEvaluation.eval₀
      (StlcIso.SpecSyntax.app
        (StlcIso.SpecSyntax.abs ?tau ?t) ?v) ?rhs =>
      replace rhs with t[beta1 v]
  end.
  - apply StlcIso.SpecEvaluation.eval_beta. exact I.
  - cbn. setoid_rewrite (recursive_bundle_loop_closed d VA VB (beta1 unit)).
    reflexivity.
Qed.

Lemma terminating_app_after_evaln_abs {f τ body arg n} :
  StlcIso.SpecEvaluation.evaln f (abs τ body) n ->
  StlcIso.SpecEvaluation.Value arg ->
  StlcIso.SpecEvaluation.Value body[beta1 arg] ->
  StlcIso.SpecEvaluation.Terminating (app f arg).
Proof.
  intros Hef Harg Hbody.
  exists body[beta1 arg]. split; [exact Hbody|].
  eapply evalStepTrans.
  - pose proof (stepRel_to_evalStar Hef) as Hefstar.
    exact (StlcIso.LemmasEvaluation.evalstar_ctx (papp₁ phole arg) I Hefstar).
  - apply evalToStar, StlcIso.SpecEvaluation.eval_eval₀.
    now apply StlcIso.SpecEvaluation.eval_beta.
Qed.

Theorem tied_certificate_bundle_terminates {A B} (d : ClosedCastEq A B) :
  StlcIso.SpecEvaluation.Terminating (tied_certificate_bundle d).
Proof.
  unfold tied_certificate_bundle, global_bundle_functional.
  set (BT := certificate_bundle_ty d).
  set (body := build_certificate_bundle d (tm_app (var 1) unit)
                    cast_terms_nil).
  change (StlcIso.SpecEvaluation.Terminating
    (app (app (ufix tunit BT)
          (abs (tarr tunit BT) (abs tunit body))) unit)).
  assert (VF : StlcIso.SpecEvaluation.Value
    (abs (tarr tunit BT) (abs tunit body))) by exact I.
  pose proof (@ufix_eval₁ (abs (tarr tunit BT) (abs tunit body)) VF
                tunit BT)
    as Hfirst.
  pose proof (@ufix₁_evaln' (abs tunit body) tunit BT) as Hbody.
  cbn in Hbody.
  eapply StlcIso.LemmasEvaluation.termination_closed_under_antireduction.
  - eapply StlcIso.LemmasEvaluation.eval_ctx
      with (C := papp₁ phole unit); [exact I|exact Hfirst].
  - eapply terminating_app_after_evaln_abs.
    + exact Hbody.
    + exact I.
    + apply iso_value_substitution, iso_value_substitution.
      apply global_bundle_body_value.
Qed.

Lemma terminating_proj1_closed {t A B} :
  ⟪ empty i⊢ t : tprod A B ⟫ ->
  StlcIso.SpecEvaluation.Terminating t ->
  StlcIso.SpecEvaluation.Terminating (proj₁ t).
Proof.
  intros Htyped (v & Hv & Heval).
  pose proof (preservation_star Heval ValidEnv_nil Htyped) as Hvt.
  destruct (can_form_tprod Hv Hvt) as (v1 & v2 & -> & Hv1t & Hv2t).
  cbn in Hv. destruct Hv as [Hv1 Hv2].
  exists v1. split; [exact Hv1|].
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx (pproj₁ phole) I Heval).
  - apply evalToStar, StlcIso.SpecEvaluation.eval_eval₀.
    now apply StlcIso.SpecEvaluation.eval_proj₁.
Qed.

Lemma terminating_proj2_closed {t A B} :
  ⟪ empty i⊢ t : tprod A B ⟫ ->
  StlcIso.SpecEvaluation.Terminating t ->
  StlcIso.SpecEvaluation.Terminating (proj₂ t).
Proof.
  intros Htyped (v & Hv & Heval).
  pose proof (preservation_star Heval ValidEnv_nil Htyped) as Hvt.
  destruct (can_form_tprod Hv Hvt) as (v1 & v2 & -> & Hv1t & Hv2t).
  cbn in Hv. destruct Hv as [Hv1 Hv2].
  exists v2. split; [exact Hv2|].
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx (pproj₂ phole) I Heval).
  - apply evalToStar, StlcIso.SpecEvaluation.eval_eval₀.
    now apply StlcIso.SpecEvaluation.eval_proj₂.
Qed.

Theorem compile_global_pair_terminates {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  StlcIso.SpecEvaluation.Terminating (compile_global_pair d).
Proof.
  intros VA VB.
  destruct (casteq_view d) as [m|node].
  - exact (False_rect _ (assumed_nil_absurd m)).
  - cbn [compile_global_pair certificate_root].
    eapply (@terminating_proj1_closed _ (cast_pair_ty A B)
              (node_bundle_ty node)).
    + exact (@tied_certificate_bundle_typing empty A B (ce_step node) VA VB).
    + apply tied_certificate_bundle_terminates.
Qed.

Theorem compile_global_up_terminates {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  StlcIso.SpecEvaluation.Terminating (compile_global_up d).
Proof.
  intros VA VB. unfold compile_global_up, pair_up.
  eapply (@terminating_proj1_closed _ (tarr A B) (tarr B A)).
  - now apply compile_global_pair_typing.
  - now apply compile_global_pair_terminates.
Qed.

Theorem compile_global_down_terminates {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  StlcIso.SpecEvaluation.Terminating (compile_global_down d).
Proof.
  intros VA VB. unfold compile_global_down, pair_down.
  eapply (@terminating_proj2_closed _ (tarr A B) (tarr B A)).
  - now apply compile_global_pair_typing.
  - now apply compile_global_pair_terminates.
Qed.
