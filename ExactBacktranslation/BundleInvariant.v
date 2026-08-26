Require Import ExactBacktranslation.HeterogeneousLR.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.GlobalEvaluation.
Require Import ExactBacktranslation.CastCommon.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import StlcIso.Inst.
Require Import StlcIso.CanForm.
Require Import StlcIso.TypeSafety.
Require Import StlcIso.Size.
Require Import StlcEqui.CanForm.
Require Import Db.Lemmas.
Require Import Common.Relations.
Require Import CompilerIE.Compiler.
From Stdlib Require Import Lia Lists.List.
Import ListNotations.

Module BI := StlcIso.SpecSyntax.
Module BIE := StlcIso.SpecEvaluation.

Lemma compie_preserves_value t :
  BIE.Value t -> HEE.Value (CompilerIE.Compiler.compie t).
Proof. induction t; cbn; intuition. Qed.

Lemma equi_typing_unfold {body t} :
  ValidTy (trec body) ->
  StlcEqui.SpecTyping.Typing empty t (trec body) ->
  StlcEqui.SpecTyping.Typing empty t (body[beta1 (trec body)]).
Proof.
  intros Vrec Ht. eapply StlcEqui.SpecTyping.WtEq.
  - exact (@EqMuL body (body[beta1 (trec body)]) tyeq_refl).
  - exact Vrec.
  - now apply ValidTy_unfold_trec.
  - exact Ht.
Qed.



Lemma equi_typing_fold {body t} :
  ValidTy (trec body) ->
  StlcEqui.SpecTyping.Typing empty t (body[beta1 (trec body)]) ->
  StlcEqui.SpecTyping.Typing empty t (trec body).
Proof.
  intros Vrec Ht. eapply StlcEqui.SpecTyping.WtEq.
  - exact (@EqMuR (body[beta1 (trec body)]) body tyeq_refl).
  - now apply ValidTy_unfold_trec.
  - exact Vrec.
  - exact Ht.
Qed.

Lemma pair_first_abs_app_eval {A body other vi} :
  BIE.Value other ->
  BIE.Value vi ->
  BIE.evalStar
    (BI.app (BI.proj₁ (BI.pair (BI.abs A body) other)) vi)
    (BI.apTm (beta1 vi) body).
Proof.
  intros Hother Hvi.
  eapply evalStepTrans.
  - apply evalToStar.
    eapply BIE.eval_ctx₀ with (C := BI.papp₁ BI.phole vi).
    + now apply BIE.eval_proj₁.
    + exact I.
  - apply evalToStar, BIE.eval_eval₀.
    now apply BIE.eval_beta.
Qed.




Lemma pair_second_abs_app_eval {A body other vi} :
  BIE.Value other ->
  BIE.Value vi ->
  BIE.evalStar
    (BI.app (BI.proj₂ (BI.pair other (BI.abs A body))) vi)
    (BI.apTm (beta1 vi) body).
Proof.
  intros Hother Hvi.
  eapply evalStepTrans.
  - apply evalToStar.
    eapply BIE.eval_ctx₀ with (C := BI.papp₁ BI.phole vi).
    + now apply BIE.eval_proj₂.
    + exact I.
  - apply evalToStar, BIE.eval_eval₀.
    now apply BIE.eval_beta.
Qed.

Lemma app_argument_antired {f arg arg' vo} :
  BIE.evalStar arg arg' ->
  BIE.Value arg' ->
  BIE.evalStar (BI.app f arg') vo ->
  BIE.Value vo ->
  BIE.evalStar (BI.app f arg) vo.
Proof.
  intros Harg Harg' Happ Hvo.
  destruct (StlcIso.LemmasEvaluation.evalStar_ectx_inv
    (BI.papp₁ BI.phole arg') f I vo Happ Hvo)
    as (vf & Hvf & Hf & Hvfapp).
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.papp₁ BI.phole arg) I Hf).
  - eapply evalStepTrans.
    + exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.papp₂ vf BI.phole) (conj Hvf I) Harg).
    + exact Hvfapp.
Qed.

Lemma value_action_map_term
  {R S : BI.Tm -> HE.Tm -> Prop} {f ti te} :
  (forall vi ve,
    BIE.Value vi -> HEE.Value ve -> R vi ve ->
    exists vo, BIE.Value vo /\ BIE.evalStar (BI.app f vi) vo /\ S vo ve) ->
  term_lift R ti te ->
  term_lift S (BI.app f ti) te.
Proof.
  intros Haction [HL HR]. split.
  - intros vo Hvo Happ.
    destruct (StlcIso.LemmasEvaluation.evalStar_ectx_inv
      (BI.papp₁ BI.phole ti) f I vo Happ Hvo)
      as (vf & Hvf & Hf & Hvfapp).
    destruct (StlcIso.LemmasEvaluation.evalStar_ectx_inv
      (BI.papp₂ vf BI.phole) ti (conj Hvf I) vo Hvfapp Hvo)
      as (vi & Hvi & Hti & Hfinal).
    destruct (HL vi Hvi Hti) as (ve & Hve & Hte & HRvi).
    destruct (Haction vi ve Hvi Hve HRvi)
      as (vo' & Hvo' & Happ' & HSvo).
    assert (Hwhole' : BIE.evalStar (BI.app f ti) vo').
    { exact (app_argument_antired Hti Hvi Happ' Hvo'). }
    assert (Hvo_vo' : BIE.evalStar vo vo').
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Happ Hwhole'
        (StlcIso.LemmasEvaluation.values_are_normal Hvo')). }
    assert (vo = vo').
    { now apply StlcIso.LemmasEvaluation.value_evalStar. }
    subst vo'. exists ve. repeat split; assumption.
  - intros ve Hve Hte.
    destruct (HR ve Hve Hte) as (vi & Hvi & Hti & HRvi).
    destruct (Haction vi ve Hvi Hve HRvi)
      as (vo & Hvo & Happ & HSvo).
    exists vo. repeat split; try assumption.
    exact (app_argument_antired Hti Hvi Happ Hvo).
Qed.

Lemma term_lift_values {R : BI.Tm -> HE.Tm -> Prop} vi ve :
  BIE.Value vi -> HEE.Value ve -> R vi ve -> term_lift R vi ve.
Proof.
  intros Hvi Hve Hrel. split.
  - intros vi' Hvi' Heval.
    assert (vi = vi') by
      (eapply StlcIso.LemmasEvaluation.value_evalStar; eauto).
    subst vi'. exists ve. repeat split; try assumption. constructor.
  - intros ve' Hve' Heval.
    assert (ve = ve') by
      (eapply StlcEqui.LemmasEvaluation.value_evalStar; eauto).
    subst ve'. exists vi. repeat split; try assumption. constructor.
Qed.

Lemma forward_action_map_term {n m A B} (foc : Focus A B) up ti te :
  forward_value_action n foc up -> m <= n ->
  endpoint_term_left m foc ti te ->
  cast_term_up m foc (BI.app up ti) te.
Proof.
  intros Hact Hmn Hterm. eapply value_action_map_term; [|exact Hterm].
  intros vi ve Hvi Hve Hrel. exact (Hact m Hmn vi ve Hvi Hve Hrel).
Qed.

Lemma reverse_action_map_term {n m A B} (foc : Focus A B) down ti te :
  reverse_value_action n foc down -> m <= n ->
  endpoint_term_right m foc ti te ->
  cast_term m foc (BI.app down ti) te.
Proof.
  intros Hact Hmn Hterm. eapply value_action_map_term; [|exact Hterm].
  intros vi ve Hvi Hve Hrel. exact (Hact m Hmn vi ve Hvi Hve Hrel).
Qed.

Lemma forward_recovery_map_term {n m A B} (foc : Focus A B) up ti te :
  forward_recovery_action n foc up -> m <= n ->
  cast_term m foc ti te ->
  endpoint_term_right m foc (BI.app up ti) te.
Proof.
  intros Hact Hmn Hterm. eapply value_action_map_term; [|exact Hterm].
  intros vi ve Hvi Hve Hrel. exact (Hact m Hmn vi ve Hvi Hve Hrel).
Qed.

Lemma reverse_recovery_map_term {n m A B} (foc : Focus A B) down ti te :
  reverse_recovery_action n foc down -> m <= n ->
  cast_term_up m foc ti te ->
  endpoint_term_left m foc (BI.app down ti) te.
Proof.
  intros Hact Hmn Hterm. eapply value_action_map_term; [|exact Hterm].
  intros vi ve Hvi Hve Hrel. exact (Hact m Hmn vi ve Hvi Hve Hrel).
Qed.

Lemma generated_arrow_value_eq {B domcast codcast vf} :
  BI.apTm (beta1 vf)
    (BI.abs B
      (BI.app codcast[wkm][wkm]
        (BI.app (BI.var 1)
          (BI.app domcast[wkm][wkm] (BI.var 0))))) =
  BI.abs B
    (BI.app codcast[wkm]
      (BI.app vf[wk]
        (BI.app domcast[wkm] (BI.var 0)))).
Proof.
  cbn. repeat crushDbLemmasRewriteH.
  replace (BI.apTm (beta1 vf)↑ codcast[wkm][wkm↑]) with codcast[wkm].
  2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ codcast[wkm] vf). }
  replace (BI.apTm (beta1 vf)↑ domcast[wkm][wkm↑]) with domcast[wkm].
  2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ domcast[wkm] vf). }
  reflexivity.
Qed.

Lemma generated_arrow_body_subst {domcast codcast vf va} :
  BI.apTm (beta1 va)
    (BI.app codcast[wkm]
      (BI.app vf[wk]
        (BI.app domcast[wkm] (BI.var 0)))) =
  BI.app codcast (BI.app vf (BI.app domcast va)).
Proof.
  cbn. repeat crushDbLemmasRewriteH.
  replace (BI.apTm (beta1 va) codcast[wkm]) with codcast.
  2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ codcast va). }
  replace (BI.apTm (beta1 va) domcast[wkm]) with domcast.
  2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ domcast va). }
  replace (BI.apTm (beta1 va) vf[wk]) with vf.
  2:{ assert (Hwk : vf[wk] = vf[wkm]).
      { rewrite <- ap_liftSub, liftSub_wkm. reflexivity. }
      rewrite Hwk.
      symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ vf va). }
  reflexivity.
Qed.

Lemma generated_arrow_application_eval {B domcast codcast vf va} :
  BIE.Value va ->
  BIE.evalStar
    (BI.app
      (BI.apTm (beta1 vf)
        (BI.abs B
          (BI.app codcast[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app domcast[wkm][wkm] (BI.var 0))))))
      va)
    (BI.app codcast (BI.app vf (BI.app domcast va))).
Proof.
  intros Hva. cbn. repeat crushDbLemmasRewriteH.
  replace (BI.apTm (beta1 vf)↑ codcast[wkm][wkm↑]) with codcast[wkm].
  2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ codcast[wkm] vf). }
  replace (BI.apTm (beta1 vf)↑ domcast[wkm][wkm↑]) with domcast[wkm].
  2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ domcast[wkm] vf). }
  apply evalToStar, BIE.eval_eval₀.
  replace (BI.app codcast (BI.app vf (BI.app domcast va))) with
    (BI.apTm (beta1 va)
      (BI.app codcast[wkm]
        (BI.app vf[wk] (BI.app domcast[wkm] (BI.var 0))))).
  2:{ exact (@generated_arrow_body_subst
        domcast codcast vf va). }
  eapply BIE.eval_beta''; [exact Hva|reflexivity].
Qed.

Lemma global_arrow_forward_application_eval
  {H A1 A2 B1 B2}
  {dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1}
  {cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2}
  {payload rho vf} :
  BIE.Value vf ->
  BIE.evalStar
    (BI.app
      (pair_up
        (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho))
      vf)
    (BI.abs B1
      (BI.app
        (pair_up (certificate_root cod (BI.proj₂ payload) rho))[wkm]
        (BI.app vf[wk]
          (BI.app
            (pair_down (certificate_root dom (BI.proj₁ payload) rho))[wkm]
            (BI.var 0))))).
Proof.
  intros Hvf. cbn [global_node_cast].
  rewrite <- (@generated_arrow_value_eq B1
    (pair_down (certificate_root dom (BI.proj₁ payload) rho))
    (pair_up (certificate_root cod (BI.proj₂ payload) rho)) vf).
  eapply pair_first_abs_app_eval; [exact I|exact Hvf].
Qed.

Lemma global_arrow_reverse_application_eval
  {H A1 A2 B1 B2}
  {dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1}
  {cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2}
  {payload rho vf} :
  BIE.Value vf ->
  BIE.evalStar
    (BI.app
      (pair_down
        (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho))
      vf)
    (BI.abs A1
      (BI.app
        (pair_down (certificate_root cod (BI.proj₂ payload) rho))[wkm]
        (BI.app vf[wk]
          (BI.app
            (pair_up (certificate_root dom (BI.proj₁ payload) rho))[wkm]
            (BI.var 0))))).
Proof.
  intros Hvf. cbn [global_node_cast].
  rewrite <- (@generated_arrow_value_eq A1
    (pair_up (certificate_root dom (BI.proj₁ payload) rho))
    (pair_down (certificate_root cod (BI.proj₂ payload) rho)) vf).
  eapply pair_second_abs_app_eval; [exact I|exact Hvf].
Qed.

Lemma pair_first_mu_l_app_eval {body B up down vi vo} :
  BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app up vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₁
        (BI.pair
          (BI.abs (trec body)
            (BI.app up[wkm] (BI.unfold_ (BI.var 0))))
          (BI.abs B (BI.fold_ (BI.app down[wkm] (BI.var 0))))))
      (BI.fold_ vi)) vo.
Proof.
  intros Hvi Hvo Happ. eapply evalStepTrans.
  - eapply pair_first_abs_app_eval; [exact I|exact Hvi].
  - cbn. repeat crushDbLemmasRewriteH.
    replace (BI.apTm (beta1 (BI.fold_ vi)) up[wkm]) with up.
    2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ up (BI.fold_ vi)). }
    eapply app_argument_antired.
    + apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_fold_unfold.
    + exact Hvi.
    + exact Happ.
    + exact Hvo.
Qed.

Lemma pair_second_mu_l_app_eval {body B up down vi vo} :
  BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app down vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₂
        (BI.pair
          (BI.abs (trec body)
            (BI.app up[wkm] (BI.unfold_ (BI.var 0))))
          (BI.abs B (BI.fold_ (BI.app down[wkm] (BI.var 0))))))
      vi) (BI.fold_ vo).
Proof.
  intros Hvi Hvo Happ. eapply evalStepTrans.
  - eapply pair_second_abs_app_eval; [exact I|exact Hvi].
  - cbn. repeat crushDbLemmasRewriteH.
    replace (BI.apTm (beta1 vi) down[wkm]) with down.
    2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ down vi). }
    exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.pfold BI.phole) I Happ).
Qed.

Lemma pair_first_mu_r_app_eval {A body up down vi vo} :
  BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app up vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₁
        (BI.pair
          (BI.abs A (BI.fold_ (BI.app up[wkm] (BI.var 0))))
          (BI.abs (trec body)
            (BI.app down[wkm] (BI.unfold_ (BI.var 0))))))
      vi) (BI.fold_ vo).
Proof.
  intros Hvi Hvo Happ. eapply evalStepTrans.
  - eapply pair_first_abs_app_eval; [exact I|exact Hvi].
  - cbn. repeat crushDbLemmasRewriteH.
    replace (BI.apTm (beta1 vi) up[wkm]) with up.
    2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ up vi). }
    exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.pfold BI.phole) I Happ).
Qed.

Lemma pair_second_mu_r_app_eval {A body up down vi vo} :
  BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app down vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₂
        (BI.pair
          (BI.abs A (BI.fold_ (BI.app up[wkm] (BI.var 0))))
          (BI.abs (trec body)
            (BI.app down[wkm] (BI.unfold_ (BI.var 0))))))
      (BI.fold_ vi)) vo.
Proof.
  intros Hvi Hvo Happ. eapply evalStepTrans.
  - eapply pair_second_abs_app_eval; [exact I|exact Hvi].
  - cbn. repeat crushDbLemmasRewriteH.
    replace (BI.apTm (beta1 (BI.fold_ vi)) down[wkm]) with down.
    2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ down (BI.fold_ vi)). }
    eapply app_argument_antired.
    + apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_fold_unfold.
    + exact Hvi.
    + exact Happ.
    + exact Hvo.
Qed.

Lemma pair_app_projections_eval {f g vi1 vi2 vo1 vo2} :
  BIE.Value vi1 -> BIE.Value vi2 ->
  BIE.Value vo1 -> BIE.Value vo2 ->
  BIE.evalStar (BI.app f vi1) vo1 ->
  BIE.evalStar (BI.app g vi2) vo2 ->
  BIE.evalStar
    (BI.pair
      (BI.app f (BI.proj₁ (BI.pair vi1 vi2)))
      (BI.app g (BI.proj₂ (BI.pair vi1 vi2))))
    (BI.pair vo1 vo2).
Proof.
  intros Hvi1 Hvi2 Hvo1 Hvo2 Hf Hg.
  assert (Hp1 : BIE.evalStar (BI.proj₁ (BI.pair vi1 vi2)) vi1).
  { apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_proj₁. }
  assert (Hp2 : BIE.evalStar (BI.proj₂ (BI.pair vi1 vi2)) vi2).
  { apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_proj₂. }
  assert (Hleft :
    BIE.evalStar
      (BI.app f (BI.proj₁ (BI.pair vi1 vi2))) vo1).
  { eapply app_argument_antired; eauto. }
  assert (Hright :
    BIE.evalStar
      (BI.app g (BI.proj₂ (BI.pair vi1 vi2))) vo2).
  { eapply app_argument_antired; eauto. }
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.ppair₁ BI.phole
        (BI.app g (BI.proj₂ (BI.pair vi1 vi2)))) I Hleft).
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.ppair₂ vo1 BI.phole) (conj Hvo1 I) Hright).
Qed.

Lemma global_product_forward_application_eval
  {H A1 A2 B1 B2}
  {fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1}
  {sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2}
  {payload rho vi1 vi2 vo1 vo2} :
  BIE.Value vi1 -> BIE.Value vi2 ->
  BIE.Value vo1 -> BIE.Value vo2 ->
  BIE.evalStar
    (BI.app (pair_up (certificate_root fstc (BI.proj₁ payload) rho)) vi1)
    vo1 ->
  BIE.evalStar
    (BI.app (pair_up (certificate_root sndc (BI.proj₂ payload) rho)) vi2)
    vo2 ->
  BIE.evalStar
    (BI.app
      (pair_up
        (global_node_cast (cn_prod H A1 A2 B1 B2 fstc sndc) payload rho))
      (BI.pair vi1 vi2))
    (BI.pair vo1 vo2).
Proof.
  intros Hvi1 Hvi2 Hvo1 Hvo2 Heval1 Heval2.
  cbn [global_node_cast]. eapply evalStepTrans.
  - eapply pair_first_abs_app_eval; [exact I|now split].
  - cbn.
    assert (Hcancel1 :
      BI.apTm (beta1 (BI.pair vi1 vi2))
        (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
      certificate_root fstc (BI.proj₁ payload) rho)
      by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
    assert (Hcancel2 :
      BI.apTm (beta1 (BI.pair vi1 vi2))
        (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
      certificate_root sndc (BI.proj₂ payload) rho)
      by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
    rewrite Hcancel1, Hcancel2.
    eapply pair_app_projections_eval; eauto.
Qed.

Lemma global_product_reverse_application_eval
  {H A1 A2 B1 B2}
  {fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1}
  {sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2}
  {payload rho vi1 vi2 vo1 vo2} :
  BIE.Value vi1 -> BIE.Value vi2 ->
  BIE.Value vo1 -> BIE.Value vo2 ->
  BIE.evalStar
    (BI.app (pair_down (certificate_root fstc (BI.proj₁ payload) rho)) vi1)
    vo1 ->
  BIE.evalStar
    (BI.app (pair_down (certificate_root sndc (BI.proj₂ payload) rho)) vi2)
    vo2 ->
  BIE.evalStar
    (BI.app
      (pair_down
        (global_node_cast (cn_prod H A1 A2 B1 B2 fstc sndc) payload rho))
      (BI.pair vi1 vi2))
    (BI.pair vo1 vo2).
Proof.
  intros Hvi1 Hvi2 Hvo1 Hvo2 Heval1 Heval2.
  cbn [global_node_cast]. eapply evalStepTrans.
  - eapply pair_second_abs_app_eval; [exact I|now split].
  - cbn.
    assert (Hcancel1 :
      BI.apTm (beta1 (BI.pair vi1 vi2))
        (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
      certificate_root fstc (BI.proj₁ payload) rho)
      by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
    assert (Hcancel2 :
      BI.apTm (beta1 (BI.pair vi1 vi2))
        (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
      certificate_root sndc (BI.proj₂ payload) rho)
      by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
        _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
    rewrite Hcancel1, Hcancel2.
    eapply pair_app_projections_eval; eauto.
Qed.

Lemma pair_first_sum_inl_app_eval {T f g other vi vo} :
  BIE.Value other -> BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app f vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₁
        (BI.pair
          (BI.abs T
            (BI.caseof (BI.var 0)
              (BI.inl (BI.app f[wkm][wkm] (BI.var 0)))
              (BI.inr (BI.app g[wkm][wkm] (BI.var 0)))))
          other))
      (BI.inl vi))
    (BI.inl vo).
Proof.
  intros Hother Hvi Hvo Happ.
  eapply evalStepTrans.
  - eapply pair_first_abs_app_eval; [exact Hother|exact Hvi].
  - cbn.
    eapply evalStepTrans.
    + apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_case_inl.
    + cbn.
      repeat crushDbLemmasRewriteH.
      replace (BI.apTm (beta1 (BI.inl vi))↑ f[wkm][wkm↑])
        with f[wkm].
      2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ _ f[wkm] (BI.inl vi)). }
      replace (BI.apTm (beta1 vi) f[wkm]) with f.
      2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ f vi). }
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pinl BI.phole) I Happ).
Qed.

Lemma pair_first_sum_inr_app_eval {T f g other vi vo} :
  BIE.Value other -> BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app g vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₁
        (BI.pair
          (BI.abs T
            (BI.caseof (BI.var 0)
              (BI.inl (BI.app f[wkm][wkm] (BI.var 0)))
              (BI.inr (BI.app g[wkm][wkm] (BI.var 0)))))
          other))
      (BI.inr vi))
    (BI.inr vo).
Proof.
  intros Hother Hvi Hvo Happ.
  eapply evalStepTrans.
  - eapply pair_first_abs_app_eval; [exact Hother|exact Hvi].
  - cbn. eapply evalStepTrans.
    + apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_case_inr.
    + cbn. repeat crushDbLemmasRewriteH.
      replace (BI.apTm (beta1 (BI.inr vi))↑ g[wkm][wkm↑])
        with g[wkm].
      2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ _ g[wkm] (BI.inr vi)). }
      replace (BI.apTm (beta1 vi) g[wkm]) with g.
      2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ g vi). }
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pinr BI.phole) I Happ).
Qed.

Lemma pair_second_sum_inl_app_eval {T f g other vi vo} :
  BIE.Value other -> BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app f vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₂
        (BI.pair other
          (BI.abs T
            (BI.caseof (BI.var 0)
              (BI.inl (BI.app f[wkm][wkm] (BI.var 0)))
              (BI.inr (BI.app g[wkm][wkm] (BI.var 0)))))))
      (BI.inl vi))
    (BI.inl vo).
Proof.
  intros Hother Hvi Hvo Happ.
  eapply evalStepTrans.
  - eapply pair_second_abs_app_eval; [exact Hother|exact Hvi].
  - cbn. eapply evalStepTrans.
    + apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_case_inl.
    + cbn. repeat crushDbLemmasRewriteH.
      replace (BI.apTm (beta1 (BI.inl vi))↑ f[wkm][wkm↑])
        with f[wkm].
      2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ _ f[wkm] (BI.inl vi)). }
      replace (BI.apTm (beta1 vi) f[wkm]) with f.
      2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ f vi). }
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pinl BI.phole) I Happ).
Qed.

Lemma pair_second_sum_inr_app_eval {T f g other vi vo} :
  BIE.Value other -> BIE.Value vi -> BIE.Value vo ->
  BIE.evalStar (BI.app g vi) vo ->
  BIE.evalStar
    (BI.app
      (BI.proj₂
        (BI.pair other
          (BI.abs T
            (BI.caseof (BI.var 0)
              (BI.inl (BI.app f[wkm][wkm] (BI.var 0)))
              (BI.inr (BI.app g[wkm][wkm] (BI.var 0)))))))
      (BI.inr vi))
    (BI.inr vo).
Proof.
  intros Hother Hvi Hvo Happ.
  eapply evalStepTrans.
  - eapply pair_second_abs_app_eval; [exact Hother|exact Hvi].
  - cbn. eapply evalStepTrans.
    + apply evalToStar, BIE.eval_eval₀. now apply BIE.eval_case_inr.
    + cbn. repeat crushDbLemmasRewriteH.
      replace (BI.apTm (beta1 (BI.inr vi))↑ g[wkm][wkm↑])
        with g[wkm].
      2:{ symmetry. exact (@apply_wkm_beta1_up_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ _ g[wkm] (BI.inr vi)). }
      replace (BI.apTm (beta1 vi) g[wkm]) with g.
      2:{ symmetry. exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _ g vi). }
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pinr BI.phole) I Happ).
Qed.

Lemma unit_left_to_up n H fs vi ve :
  endpoint_value_left n
    (focus (ce_step (cn_unit H)) fs) vi ve ->
  cast_value_up n
    (focus (ce_step (cn_unit H)) fs) vi ve.
Proof.
  induction n; cbn; intuition.
Qed.

Lemma unit_right_to_down n H fs vi ve :
  endpoint_value_right n
    (focus (ce_step (cn_unit H)) fs) vi ve ->
  cast_value n
    (focus (ce_step (cn_unit H)) fs) vi ve.
Proof.
  induction n; cbn; intuition.
Qed.

Lemma unit_cross_down_to_right n H fs vi ve :
  cast_value n (focus (ce_step (cn_unit H)) fs) vi ve ->
  endpoint_value_right n (focus (ce_step (cn_unit H)) fs) vi ve.
Proof. induction n; cbn; intuition. Qed.

Lemma unit_cross_up_to_left n H fs vi ve :
  cast_value_up n (focus (ce_step (cn_unit H)) fs) vi ve ->
  endpoint_value_left n (focus (ce_step (cn_unit H)) fs) vi ve.
Proof. induction n; cbn; intuition. Qed.

Lemma bool_left_to_up n H fs vi ve :
  endpoint_value_left n
    (focus (ce_step (cn_bool H)) fs) vi ve ->
  cast_value_up n
    (focus (ce_step (cn_bool H)) fs) vi ve.
Proof.
  induction n; cbn; intuition.
Qed.

Lemma bool_right_to_down n H fs vi ve :
  endpoint_value_right n
    (focus (ce_step (cn_bool H)) fs) vi ve ->
  cast_value n
    (focus (ce_step (cn_bool H)) fs) vi ve.
Proof.
  induction n; cbn; intuition.
Qed.

Lemma bool_cross_down_to_right n H fs vi ve :
  cast_value n (focus (ce_step (cn_bool H)) fs) vi ve ->
  endpoint_value_right n (focus (ce_step (cn_bool H)) fs) vi ve.
Proof. induction n; cbn; intuition. Qed.

Lemma bool_cross_up_to_left n H fs vi ve :
  cast_value_up n (focus (ce_step (cn_bool H)) fs) vi ve ->
  endpoint_value_left n (focus (ce_step (cn_bool H)) fs) vi ve.
Proof. induction n; cbn; intuition. Qed.

Lemma var_left_to_up n H x fs vi ve :
  endpoint_value_left n
    (focus (ce_step (cn_var H x)) fs) vi ve ->
  cast_value_up n
    (focus (ce_step (cn_var H x)) fs) vi ve.
Proof.
  induction n; cbn; intuition.
Qed.

Lemma var_right_to_down n H x fs vi ve :
  endpoint_value_right n
    (focus (ce_step (cn_var H x)) fs) vi ve ->
  cast_value n
    (focus (ce_step (cn_var H x)) fs) vi ve.
Proof.
  induction n; cbn; intuition.
Qed.

Lemma var_cross_down_to_right n H x fs vi ve :
  cast_value n (focus (ce_step (cn_var H x)) fs) vi ve ->
  endpoint_value_right n (focus (ce_step (cn_var H x)) fs) vi ve.
Proof. induction n; cbn; intuition. Qed.

Lemma var_cross_up_to_left n H x fs vi ve :
  cast_value_up n (focus (ce_step (cn_var H x)) fs) vi ve ->
  endpoint_value_left n (focus (ce_step (cn_var H x)) fs) vi ve.
Proof. induction n; cbn; intuition. Qed.

Lemma cast_value_up_prod_intro n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi1 vi2 ve1 ve2 :
  cast_value_up n
    (focus fstc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
    vi1 ve1 ->
  cast_value_up n
    (focus sndc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
    vi2 ve2 ->
  cast_value_up (S n)
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs)
    (BI.pair vi1 vi2) (HE.pair ve1 ve2).
Proof.
  revert vi1 vi2 ve1 ve2.
  induction n as [|n IH]; intros vi1 vi2 ve1 ve2 Hfst Hsnd; cbn in *.
  - split.
    + split.
      * apply StlcIso.SpecTyping.WtPair;
          [exact (proj1 Hfst)|exact (proj1 Hsnd)].
      * apply StlcEqui.SpecTyping.WtPair;
          [exact (proj2 Hfst)|exact (proj2 Hsnd)].
    + exists vi1, vi2, ve1, ve2.
      split; [reflexivity|]. split; [reflexivity|].
      split; assumption.
  - split.
    + apply (proj2 (cast_value_up_normalize (S n)
        (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs)
        (BI.pair vi1 vi2) (HE.pair ve1 ve2))).
      apply IH.
      * exact (cast_value_up_mono (S n) n A1 B1 _ vi1 ve1
          (le_S n n (le_n n)) Hfst).
      * exact (cast_value_up_mono (S n) n A2 B2 _ vi2 ve2
          (le_S n n (le_n n)) Hsnd).
    + exists vi1, vi2, ve1, ve2.
      split; [reflexivity|]. split; [reflexivity|].
      split; assumption.
Qed.

Lemma cast_value_prod_intro n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi1 vi2 ve1 ve2 :
  cast_value n
    (focus fstc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
    vi1 ve1 ->
  cast_value n
    (focus sndc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
    vi2 ve2 ->
  cast_value (S n)
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs)
    (BI.pair vi1 vi2) (HE.pair ve1 ve2).
Proof.
  revert vi1 vi2 ve1 ve2.
  induction n as [|n IH]; intros vi1 vi2 ve1 ve2 Hfst Hsnd; cbn in *.
  - split.
    + split.
      * apply StlcIso.SpecTyping.WtPair;
          [exact (proj1 Hfst)|exact (proj1 Hsnd)].
      * apply StlcEqui.SpecTyping.WtPair;
          [exact (proj2 Hfst)|exact (proj2 Hsnd)].
    + exists vi1, vi2, ve1, ve2.
      split; [reflexivity|]. split; [reflexivity|].
      split; assumption.
  - split.
    + apply (proj2 (cast_value_normalize (S n)
        (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs)
        (BI.pair vi1 vi2) (HE.pair ve1 ve2))).
      apply IH.
      * exact (cast_value_mono (S n) n A1 B1 _ vi1 ve1
          (le_S n n (le_n n)) Hfst).
      * exact (cast_value_mono (S n) n A2 B2 _ vi2 ve2
          (le_S n n (le_n n)) Hsnd).
    + exists vi1, vi2, ve1, ve2.
      split; [reflexivity|]. split; [reflexivity|].
      split; assumption.
Qed.

Lemma endpoint_value_left_prod_inv n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A1 -> ValidTy A2 ->
  BIE.Value vi -> HEE.Value ve ->
  endpoint_value_left n
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs) vi ve ->
  exists vi1 vi2 ve1 ve2,
    vi = BI.pair vi1 vi2 /\ ve = HE.pair ve1 ve2
    /\ BIE.Value vi1 /\ BIE.Value vi2
    /\ HEE.Value ve1 /\ HEE.Value ve2
    /\ endpoint_value_left (Nat.pred n)
      (focus fstc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
      vi1 ve1
    /\ endpoint_value_left (Nat.pred n)
      (focus sndc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
      vi2 ve2.
Proof.
  intros VA1 VA2 Hvi Hve Hrel.
  destruct n as [|n].
  - cbn in Hrel.
    destruct (StlcIso.CanForm.can_form_tprod Hvi (proj1 Hrel))
      as (vi1 & vi2 & -> & Hti1 & Hti2).
    destruct (StlcEqui.CanForm.can_form_tprod Hve (proj2 Hrel)
      tyeq_refl ValidEnv_nil VA1 VA2)
      as (ve1 & ve2 & -> & Hte1 & Hte2).
    cbn in Hvi, Hve. destruct Hvi as [Hvi1 Hvi2].
    destruct Hve as [Hve1 Hve2].
    exists vi1, vi2, ve1, ve2. repeat split; try assumption;
      try reflexivity.
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as
      (vi1 & vi2 & ve1 & ve2 & -> & -> & Hfst & Hsnd).
    cbn in Hvi, Hve. destruct Hvi as [Hvi1 Hvi2].
    destruct Hve as [Hve1 Hve2].
    exists vi1, vi2, ve1, ve2. repeat split; try assumption;
      try reflexivity.
Qed.

Lemma endpoint_value_right_prod_inv n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy B1 -> ValidTy B2 ->
  BIE.Value vi -> HEE.Value ve ->
  endpoint_value_right n
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs) vi ve ->
  exists vi1 vi2 ve1 ve2,
    vi = BI.pair vi1 vi2 /\ ve = HE.pair ve1 ve2
    /\ BIE.Value vi1 /\ BIE.Value vi2
    /\ HEE.Value ve1 /\ HEE.Value ve2
    /\ endpoint_value_right (Nat.pred n)
      (focus fstc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
      vi1 ve1
    /\ endpoint_value_right (Nat.pred n)
      (focus sndc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs))
      vi2 ve2.
Proof.
  intros VB1 VB2 Hvi Hve Hrel.
  destruct n as [|n].
  - cbn in Hrel.
    destruct (StlcIso.CanForm.can_form_tprod Hvi (proj1 Hrel))
      as (vi1 & vi2 & -> & Hti1 & Hti2).
    destruct (StlcEqui.CanForm.can_form_tprod Hve (proj2 Hrel)
      tyeq_refl ValidEnv_nil VB1 VB2)
      as (ve1 & ve2 & -> & Hte1 & Hte2).
    cbn in Hvi, Hve. destruct Hvi as [Hvi1 Hvi2].
    destruct Hve as [Hve1 Hve2].
    exists vi1, vi2, ve1, ve2. repeat split; try assumption;
      try reflexivity.
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as
      (vi1 & vi2 & ve1 & ve2 & -> & -> & Hfst & Hsnd).
    cbn in Hvi, Hve. destruct Hvi as [Hvi1 Hvi2].
    destruct Hve as [Hve1 Hve2].
    exists vi1, vi2, ve1, ve2. repeat split; try assumption;
      try reflexivity.
Qed.

Lemma cast_value_prod_inv n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy B1 -> ValidTy B2 ->
  BIE.Value vi -> HEE.Value ve ->
  cast_value n
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs) vi ve ->
  exists vi1 vi2 ve1 ve2,
    vi = BI.pair vi1 vi2 /\ ve = HE.pair ve1 ve2
    /\ BIE.Value vi1 /\ BIE.Value vi2
    /\ HEE.Value ve1 /\ HEE.Value ve2
    /\ cast_value (Nat.pred n)
      (focus fstc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi1 ve1
    /\ cast_value (Nat.pred n)
      (focus sndc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi2 ve2.
Proof.
  intros VB1 VB2 Hvi Hve Hrel. destruct n as [|n].
  - cbn in Hrel.
    destruct (StlcIso.CanForm.can_form_tprod Hvi (proj1 Hrel))
      as (vi1 & vi2 & -> & Hti1 & Hti2).
    destruct (StlcEqui.CanForm.can_form_tprod Hve (proj2 Hrel)
      tyeq_refl ValidEnv_nil VB1 VB2)
      as (ve1 & ve2 & -> & Hte1 & Hte2).
    cbn in Hvi, Hve. exists vi1, vi2, ve1, ve2.
    repeat split; try assumption; try reflexivity.
    + exact (proj1 Hvi).
    + exact (proj2 Hvi).
    + exact (proj1 Hve).
    + exact (proj2 Hve).
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as
      (vi1 & vi2 & ve1 & ve2 & -> & -> & Hfst & Hsnd).
    cbn in Hvi, Hve. exists vi1, vi2, ve1, ve2.
    repeat split; try assumption; try reflexivity.
    + exact (proj1 Hvi).
    + exact (proj2 Hvi).
    + exact (proj1 Hve).
    + exact (proj2 Hve).
Qed.

Lemma cast_value_up_prod_inv n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A1 -> ValidTy A2 ->
  BIE.Value vi -> HEE.Value ve ->
  cast_value_up n
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs) vi ve ->
  exists vi1 vi2 ve1 ve2,
    vi = BI.pair vi1 vi2 /\ ve = HE.pair ve1 ve2
    /\ BIE.Value vi1 /\ BIE.Value vi2
    /\ HEE.Value ve1 /\ HEE.Value ve2
    /\ cast_value_up (Nat.pred n)
      (focus fstc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi1 ve1
    /\ cast_value_up (Nat.pred n)
      (focus sndc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi2 ve2.
Proof.
  intros VA1 VA2 Hvi Hve Hrel. destruct n as [|n].
  - cbn in Hrel.
    destruct (StlcIso.CanForm.can_form_tprod Hvi (proj1 Hrel))
      as (vi1 & vi2 & -> & Hti1 & Hti2).
    destruct (StlcEqui.CanForm.can_form_tprod Hve (proj2 Hrel)
      tyeq_refl ValidEnv_nil VA1 VA2)
      as (ve1 & ve2 & -> & Hte1 & Hte2).
    cbn in Hvi, Hve. exists vi1, vi2, ve1, ve2.
    repeat split; try assumption; try reflexivity.
    + exact (proj1 Hvi).
    + exact (proj2 Hvi).
    + exact (proj1 Hve).
    + exact (proj2 Hve).
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as
      (vi1 & vi2 & ve1 & ve2 & -> & -> & Hfst & Hsnd).
    cbn in Hvi, Hve. exists vi1, vi2, ve1, ve2.
    repeat split; try assumption; try reflexivity.
    + exact (proj1 Hvi).
    + exact (proj2 Hvi).
    + exact (proj1 Hve).
    + exact (proj2 Hve).
Qed.

Lemma endpoint_value_left_prod_intro n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi1 vi2 ve1 ve2 :
  endpoint_value_left n
    (focus fstc (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi1 ve1 ->
  endpoint_value_left n
    (focus sndc (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi2 ve2 ->
  endpoint_value_left (S n)
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs)
    (BI.pair vi1 vi2) (HE.pair ve1 ve2).
Proof.
  revert vi1 vi2 ve1 ve2. induction n as [|n IH];
    intros vi1 vi2 ve1 ve2 Hfst Hsnd; cbn in *.
  - split.
    + split; constructor; [exact (proj1 Hfst)|exact (proj1 Hsnd)
                          |exact (proj2 Hfst)|exact (proj2 Hsnd)].
    + exists vi1, vi2, ve1, ve2. split; [reflexivity|].
      split; [reflexivity|]. split; assumption.
  - split.
    + change (endpoint_value_left (S n)
        (normalize_focus
          (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs))
        (BI.pair vi1 vi2) (HE.pair ve1 ve2)).
      apply (proj2 (endpoint_value_left_normalize (S n) _ _ _)).
      apply IH.
      * exact (proj1 (endpoint_value_left_normalize n _ _ _) (proj1 Hfst)).
      * exact (proj1 (endpoint_value_left_normalize n _ _ _) (proj1 Hsnd)).
    + exists vi1, vi2, ve1, ve2. split; [reflexivity|].
      split; [reflexivity|]. split; assumption.
Qed.

Lemma endpoint_value_right_prod_intro n H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  fs vi1 vi2 ve1 ve2 :
  endpoint_value_right n
    (focus fstc (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi1 ve1 ->
  endpoint_value_right n
    (focus sndc (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)) vi2 ve2 ->
  endpoint_value_right (S n)
    (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs)
    (BI.pair vi1 vi2) (HE.pair ve1 ve2).
Proof.
  revert vi1 vi2 ve1 ve2. induction n as [|n IH];
    intros vi1 vi2 ve1 ve2 Hfst Hsnd; cbn in *.
  - split.
    + split; constructor; [exact (proj1 Hfst)|exact (proj1 Hsnd)
                          |exact (proj2 Hfst)|exact (proj2 Hsnd)].
    + exists vi1, vi2, ve1, ve2. split; [reflexivity|].
      split; [reflexivity|]. split; assumption.
  - split.
    + change (endpoint_value_right (S n)
        (normalize_focus
          (focus (ce_step (cn_prod H A1 A2 B1 B2 fstc sndc)) fs))
        (BI.pair vi1 vi2) (HE.pair ve1 ve2)).
      apply (proj2 (endpoint_value_right_normalize (S n) _ _ _)).
      apply IH.
      * exact (proj1 (endpoint_value_right_normalize n _ _ _) (proj1 Hfst)).
      * exact (proj1 (endpoint_value_right_normalize n _ _ _) (proj1 Hsnd)).
    + exists vi1, vi2, ve1, ve2. split; [reflexivity|].
      split; [reflexivity|]. split; assumption.
Qed.

Lemma cast_value_up_sum_inl_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A2 -> ValidTy B2 ->
  cast_value_up n
    (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  cast_value_up (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inl vi) (HE.inl ve).
Proof.
  intros VA2 VB2 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split.
      * now apply StlcIso.SpecTyping.WtInl.
      * now apply StlcEqui.SpecTyping.WtInl.
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + apply (proj2 (cast_value_up_normalize (S n)
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
        (BI.inl vi) (HE.inl ve))).
      apply IH. exact (proj1 (cast_value_up_normalize n _ vi ve)
        (proj1 Hchild)).
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma cast_value_up_sum_inr_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A1 -> ValidTy B1 ->
  cast_value_up n
    (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  cast_value_up (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inr vi) (HE.inr ve).
Proof.
  intros VA1 VB1 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split.
      * now apply StlcIso.SpecTyping.WtInr.
      * now apply StlcEqui.SpecTyping.WtInr.
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + apply (proj2 (cast_value_up_normalize (S n)
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
        (BI.inr vi) (HE.inr ve))).
      apply IH. exact (proj1 (cast_value_up_normalize n _ vi ve)
        (proj1 Hchild)).
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma cast_value_sum_inl_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A2 -> ValidTy B2 ->
  cast_value n
    (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  cast_value (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inl vi) (HE.inl ve).
Proof.
  intros VA2 VB2 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split.
      * now apply StlcIso.SpecTyping.WtInl.
      * now apply StlcEqui.SpecTyping.WtInl.
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + apply (proj2 (cast_value_normalize (S n)
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
        (BI.inl vi) (HE.inl ve))).
      apply IH. exact (proj1 (cast_value_normalize n _ vi ve)
        (proj1 Hchild)).
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma cast_value_sum_inr_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A1 -> ValidTy B1 ->
  cast_value n
    (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  cast_value (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inr vi) (HE.inr ve).
Proof.
  intros VA1 VB1 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split.
      * now apply StlcIso.SpecTyping.WtInr.
      * now apply StlcEqui.SpecTyping.WtInr.
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + apply (proj2 (cast_value_normalize (S n)
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
        (BI.inr vi) (HE.inr ve))).
      apply IH. exact (proj1 (cast_value_normalize n _ vi ve)
        (proj1 Hchild)).
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma endpoint_value_left_sum_inv n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy A1 -> ValidTy A2 ->
  BIE.Value vi -> HEE.Value ve ->
  endpoint_value_left (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs) vi ve ->
  (exists vii vee,
    vi = BI.inl vii /\ ve = HE.inl vee /\
    BIE.Value vii /\ HEE.Value vee /\
    endpoint_value_left n
      (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee)
  \/ (exists vii vee,
    vi = BI.inr vii /\ ve = HE.inr vee /\
    BIE.Value vii /\ HEE.Value vee /\
    endpoint_value_left n
      (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee).
Proof.
  intros VA1 VA2 Hvi Hve Hrel. cbn in Hrel.
  destruct Hrel as [Hprev Hlayer].
  destruct Hlayer as
    [(vii & vee & -> & -> & Hchild)|(vii & vee & -> & -> & Hchild)].
  - cbn in Hvi, Hve. left. exists vii, vee.
    repeat split; try reflexivity; try assumption.
  - cbn in Hvi, Hve. right. exists vii, vee.
    repeat split; try reflexivity; try assumption.
Qed.

Lemma endpoint_value_right_sum_inv n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  ValidTy B1 -> ValidTy B2 ->
  BIE.Value vi -> HEE.Value ve ->
  endpoint_value_right (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs) vi ve ->
  (exists vii vee,
    vi = BI.inl vii /\ ve = HE.inl vee /\
    BIE.Value vii /\ HEE.Value vee /\
    endpoint_value_right n
      (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee)
  \/ (exists vii vee,
    vi = BI.inr vii /\ ve = HE.inr vee /\
    BIE.Value vii /\ HEE.Value vee /\
    endpoint_value_right n
      (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee).
Proof.
  intros VB1 VB2 Hvi Hve Hrel. cbn in Hrel.
  destruct Hrel as [Hprev Hlayer].
  destruct Hlayer as
    [(vii & vee & -> & -> & Hchild)|(vii & vee & -> & -> & Hchild)].
  - cbn in Hvi, Hve. left. exists vii, vee.
    repeat split; try reflexivity; try assumption.
  - cbn in Hvi, Hve. right. exists vii, vee.
    repeat split; try reflexivity; try assumption.
Qed.

Lemma cast_value_sum_inv n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  BIE.Value vi -> HEE.Value ve ->
  cast_value (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs) vi ve ->
  (exists vii vee, vi = BI.inl vii /\ ve = HE.inl vee /\
    BIE.Value vii /\ HEE.Value vee /\
    cast_value n
      (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee)
  \/ (exists vii vee, vi = BI.inr vii /\ ve = HE.inr vee /\
    BIE.Value vii /\ HEE.Value vee /\
    cast_value n
      (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee).
Proof.
  intros Hvi Hve [Hprev Hlayer]. destruct Hlayer as
    [(vii & vee & -> & -> & Hchild)|(vii & vee & -> & -> & Hchild)].
  - cbn in Hvi, Hve. left. exists vii, vee.
    repeat split; try reflexivity; try assumption.
  - cbn in Hvi, Hve. right. exists vii, vee.
    repeat split; try reflexivity; try assumption.
Qed.

Lemma cast_value_up_sum_inv n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  fs vi ve :
  BIE.Value vi -> HEE.Value ve ->
  cast_value_up (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs) vi ve ->
  (exists vii vee, vi = BI.inl vii /\ ve = HE.inl vee /\
    BIE.Value vii /\ HEE.Value vee /\
    cast_value_up n
      (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee)
  \/ (exists vii vee, vi = BI.inr vii /\ ve = HE.inr vee /\
    BIE.Value vii /\ HEE.Value vee /\
    cast_value_up n
      (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vii vee).
Proof.
  intros Hvi Hve [Hprev Hlayer]. destruct Hlayer as
    [(vii & vee & -> & -> & Hchild)|(vii & vee & -> & -> & Hchild)].
  - cbn in Hvi, Hve. left. exists vii, vee.
    repeat split; try reflexivity; try assumption.
  - cbn in Hvi, Hve. right. exists vii, vee.
    repeat split; try reflexivity; try assumption.
Qed.

Lemma endpoint_value_left_sum_inl_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2) fs vi ve :
  ValidTy A2 ->
  endpoint_value_left n
    (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  endpoint_value_left (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inl vi) (HE.inl ve).
Proof.
  intros VA2 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split; now apply StlcIso.SpecTyping.WtInl
             || now apply StlcEqui.SpecTyping.WtInl.
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + change (endpoint_value_left (S n) (normalize_focus
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs))
        (BI.inl vi) (HE.inl ve)).
      apply (proj2 (endpoint_value_left_normalize (S n) _ _ _)), IH.
      exact (proj1 (endpoint_value_left_normalize n _ _ _) (proj1 Hchild)).
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma endpoint_value_left_sum_inr_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2) fs vi ve :
  ValidTy A1 ->
  endpoint_value_left n
    (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  endpoint_value_left (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inr vi) (HE.inr ve).
Proof.
  intros VA1 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split; now apply StlcIso.SpecTyping.WtInr
             || now apply StlcEqui.SpecTyping.WtInr.
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + change (endpoint_value_left (S n) (normalize_focus
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs))
        (BI.inr vi) (HE.inr ve)).
      apply (proj2 (endpoint_value_left_normalize (S n) _ _ _)), IH.
      exact (proj1 (endpoint_value_left_normalize n _ _ _) (proj1 Hchild)).
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma endpoint_value_right_sum_inl_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2) fs vi ve :
  ValidTy B2 ->
  endpoint_value_right n
    (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  endpoint_value_right (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inl vi) (HE.inl ve).
Proof.
  intros VB2 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split; now apply StlcIso.SpecTyping.WtInl
             || now apply StlcEqui.SpecTyping.WtInl.
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + change (endpoint_value_right (S n) (normalize_focus
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs))
        (BI.inl vi) (HE.inl ve)).
      apply (proj2 (endpoint_value_right_normalize (S n) _ _ _)), IH.
      exact (proj1 (endpoint_value_right_normalize n _ _ _) (proj1 Hchild)).
    + left. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

Lemma endpoint_value_right_sum_inr_intro n H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2) fs vi ve :
  ValidTy B1 ->
  endpoint_value_right n
    (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)) vi ve ->
  endpoint_value_right (S n)
    (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs)
    (BI.inr vi) (HE.inr ve).
Proof.
  intros VB1 Hchild. induction n as [|n IH]; cbn in *.
  - split.
    + split; now apply StlcIso.SpecTyping.WtInr
             || now apply StlcEqui.SpecTyping.WtInr.
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
  - split.
    + change (endpoint_value_right (S n) (normalize_focus
        (focus (ce_step (cn_sum H A1 A2 B1 B2 lc rc)) fs))
        (BI.inr vi) (HE.inr ve)).
      apply (proj2 (endpoint_value_right_normalize (S n) _ _ _)), IH.
      exact (proj1 (endpoint_value_right_normalize n _ _ _) (proj1 Hchild)).
    + right. exists vi, ve. split; [reflexivity|].
      split; [reflexivity|]. exact Hchild.
Qed.

(** Semantic interpretation of the run-time ancestor environment.  Stating it
    extensionally at the exact membership focus avoids equality transports
    between an ancestor step and a backreference to that step. *)
Fixpoint cast_terms_action n {H} : Frames H -> CastTerms H -> Prop :=
  match H as H0 return Frames H0 -> CastTerms H0 -> Prop with
  | nil => fun _ _ => True
  | (A, B) :: tail => fun fs rho =>
      cast_pair_full_action n (focus (ce_back assumed_here) fs) (fst rho)
      /\ cast_terms_action n (frames_tail_any fs) (snd rho)
  end.

(** A proper cell is used in two definitionally different ways: as the root
    step itself and, by its children, as the immediate ancestor backreference.
    Keeping both views makes cyclic lookup transport-free. *)
Definition node_pair_value_action n {H A B}
  (node : CastNode H A B) (fs : Frames H) (p : BI.Tm) : Prop :=
  cast_pair_full_action n (focus (ce_step node) fs) p
  /\ cast_pair_full_action n
       (focus (ce_back assumed_here) (frames_cons node fs)) p.

Lemma node_pair_value_action_intro {n H A B}
  (node : CastNode H A B) fs p :
  cast_pair_full_action n (focus (ce_step node) fs) p ->
  node_pair_value_action n node fs p.
Proof.
  intros Hstep. split; [exact Hstep|].
  now apply (proj2 (cast_pair_full_action_back_here n node fs p)).
Qed.

Lemma identity_cast_pair_action n T {A B} (f : Focus A B) :
  (forall m vi ve,
    endpoint_value_left m f vi ve -> cast_value_up m f vi ve) ->
  (forall m vi ve,
    endpoint_value_right m f vi ve -> cast_value m f vi ve) ->
  (forall m vi ve,
    cast_value m f vi ve -> endpoint_value_right m f vi ve) ->
  (forall m vi ve,
    cast_value_up m f vi ve -> endpoint_value_left m f vi ve) ->
  cast_pair_full_action n f (BI.pair (id_cast T) (id_cast T)).
Proof.
  intros Hup Hdown Hrecover_up Hrecover_down.
  unfold cast_pair_full_action, cast_pair_value_action.
  split.
  - split.
    + intros m Hmn vi ve Hvi Hve Hrel.
      exists vi. repeat split; try assumption.
      * change (BIE.evalStar
          (BI.app (BI.proj₁
            (BI.pair (BI.abs T (BI.var 0))
                     (BI.abs T (BI.var 0)))) vi)
          (BI.apTm (beta1 vi) (BI.var 0))).
        eapply pair_first_abs_app_eval; exact I || exact Hvi.
      * now apply Hup.
    + intros m Hmn vi ve Hvi Hve Hrel.
      exists vi. repeat split; try assumption.
      * change (BIE.evalStar
          (BI.app (BI.proj₂
            (BI.pair (BI.abs T (BI.var 0))
                     (BI.abs T (BI.var 0)))) vi)
          (BI.apTm (beta1 vi) (BI.var 0))).
        eapply pair_second_abs_app_eval; exact I || exact Hvi.
      * now apply Hdown.
  - split.
    + intros m Hmn vi ve Hvi Hve Hrel.
      exists vi. repeat split; try assumption.
      * change (BIE.evalStar
          (BI.app (BI.proj₁
            (BI.pair (BI.abs T (BI.var 0))
                     (BI.abs T (BI.var 0)))) vi)
          (BI.apTm (beta1 vi) (BI.var 0))).
        eapply pair_first_abs_app_eval; exact I || exact Hvi.
      * now apply Hrecover_up.
    + intros m Hmn vi ve Hvi Hve Hrel.
      exists vi. repeat split; try assumption.
      * change (BIE.evalStar
          (BI.app (BI.proj₂
            (BI.pair (BI.abs T (BI.var 0))
                     (BI.abs T (BI.var 0)))) vi)
          (BI.apTm (beta1 vi) (BI.var 0))).
        eapply pair_second_abs_app_eval; exact I || exact Hvi.
      * now apply Hrecover_down.
Qed.

Lemma cast_terms_action_nil n :
  cast_terms_action n frames_nil cast_terms_nil.
Proof. exact I. Qed.

Lemma cast_terms_action_cons {n H A B}
  (node : CastNode H A B) (fs : Frames H) p rho :
  node_pair_value_action n node fs p ->
  cast_terms_action n fs rho ->
  cast_terms_action n (frames_cons node fs) (cast_terms_cons p rho).
Proof.
  intros Hnode Htail. cbn. split.
  - exact (proj2 Hnode).
  - exact Htail.
Qed.

(** Every proper node contributes a semantic cast-pair cell.  Payloads mirror
    [certificate_bundle_ty]; a backreference contributes no cell because its
    action is supplied by [cast_terms_action]. *)
Fixpoint certificate_bundle_action n {H A B} (d : CastEq H A B)
  (fs : Frames H) (self : BI.Tm) : Prop :=
  match d in CastEq H0 A0 B0
        return Frames H0 -> BI.Tm -> Prop with
  | ce_back _ => fun _ _ => True
  | ce_step node => fun fs0 self0 =>
      node_pair_value_action n node fs0 (BI.proj₁ self0)
      /\ node_bundle_action n node fs0 (BI.proj₂ self0)
  end fs self
with node_bundle_action n {H A B} (node : CastNode H A B)
  (fs : Frames H) (payload : BI.Tm) : Prop :=
  match node in CastNode H0 A0 B0
        return Frames H0 -> BI.Tm -> Prop with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ _ => True
  | cn_arr H0 A1 A2 B1 B2 l r => fun fs0 payload0 =>
      certificate_bundle_action n l
        (frames_cons (cn_arr H0 A1 A2 B1 B2 l r) fs0)
        (BI.proj₁ payload0)
      /\ certificate_bundle_action n r
        (frames_cons (cn_arr H0 A1 A2 B1 B2 l r) fs0)
        (BI.proj₂ payload0)
  | cn_prod H0 A1 A2 B1 B2 l r => fun fs0 payload0 =>
      certificate_bundle_action n l
        (frames_cons (cn_prod H0 A1 A2 B1 B2 l r) fs0)
        (BI.proj₁ payload0)
      /\ certificate_bundle_action n r
        (frames_cons (cn_prod H0 A1 A2 B1 B2 l r) fs0)
        (BI.proj₂ payload0)
  | cn_sum H0 A1 A2 B1 B2 l r => fun fs0 payload0 =>
      certificate_bundle_action n l
        (frames_cons (cn_sum H0 A1 A2 B1 B2 l r) fs0)
        (BI.proj₁ payload0)
      /\ certificate_bundle_action n r
        (frames_cons (cn_sum H0 A1 A2 B1 B2 l r) fs0)
        (BI.proj₂ payload0)
  | cn_mu_l H0 body B0 child => fun fs0 payload0 =>
      certificate_bundle_action n child
        (frames_cons (cn_mu_l H0 body B0 child) fs0) payload0
  | cn_mu_r H0 A0 body nm child => fun fs0 payload0 =>
      certificate_bundle_action n child
        (frames_cons (cn_mu_r H0 A0 body nm child) fs0) payload0
  end fs payload.

Lemma cast_terms_action_lookup {n H A B}
  (m : Assumed H A B) (fs : Frames H) rho :
  cast_terms_action n fs rho ->
  cast_pair_full_action n (focus (ce_back m) fs) (lookup_cast m rho).
Proof.
  revert fs rho. induction m; intros fs rho Hrho; cbn in Hrho |- *.
  - exact (proj1 Hrho).
  - apply (proj1 (cast_pair_full_action_normalize n
      (focus (ce_back (assumed_there m)) fs)
      (lookup_cast m (snd rho)))).
    change (cast_pair_full_action n
      (normalize_focus
        (focus (ce_back m) (frames_tail_any fs)))
      (lookup_cast m (snd rho))).
    apply (proj2 (cast_pair_full_action_normalize n
      (focus (ce_back m) (frames_tail_any fs))
      (lookup_cast m (snd rho)))).
    now apply IHm, Hrho.
Qed.

Lemma certificate_root_action {n H A B} (d : CastEq H A B)
  (fs : Frames H) self rho :
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  cast_pair_full_action n (focus d fs) (certificate_root d self rho).
Proof.
  destruct d; cbn; intros Hself Hrho.
  - now apply cast_terms_action_lookup.
  - exact (proj1 (proj1 Hself)).
Qed.

Lemma certificate_up_action {n H A B} (d : CastEq H A B)
  (fs : Frames H) self rho :
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  forward_value_action n (focus d fs) (certificate_up d self rho).
Proof.
  intros Hself Hrho.
  exact (proj1 (proj1
    (certificate_root_action d fs self rho Hself Hrho))).
Qed.

Lemma certificate_down_action {n H A B} (d : CastEq H A B)
  (fs : Frames H) self rho :
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  reverse_value_action n (focus d fs) (certificate_down d self rho).
Proof.
  intros Hself Hrho.
  exact (proj2 (proj1
    (certificate_root_action d fs self rho Hself Hrho))).
Qed.

Lemma certificate_up_recovery_action {n H A B} (d : CastEq H A B)
  (fs : Frames H) self rho :
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  forward_recovery_action n (focus d fs) (certificate_up d self rho).
Proof.
  intros Hself Hrho.
  exact (proj1 (proj2
    (certificate_root_action d fs self rho Hself Hrho))).
Qed.

Lemma certificate_down_recovery_action {n H A B} (d : CastEq H A B)
  (fs : Frames H) self rho :
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  reverse_recovery_action n (focus d fs) (certificate_down d self rho).
Proof.
  intros Hself Hrho.
  exact (proj2 (proj2
    (certificate_root_action d fs self rho Hself Hrho))).
Qed.

Lemma cast_terms_action_mono {n m H} (fs : Frames H) rho :
  m <= n ->
  cast_terms_action n fs rho ->
  cast_terms_action m fs rho.
Proof.
  revert fs rho. induction H as [|[A B] H IH];
    intros fs rho Hmn Henv; cbn in *.
  - exact I.
  - split.
    + eapply cast_pair_full_action_mono; [exact Hmn|exact (proj1 Henv)].
    + eapply IH; [exact Hmn|exact (proj2 Henv)].
Qed.

Lemma node_pair_value_action_mono {n m H A B}
  (node : CastNode H A B) fs p :
  m <= n ->
  node_pair_value_action n node fs p ->
  node_pair_value_action m node fs p.
Proof.
  intros Hmn [Hstep Hback]. split;
    eapply cast_pair_full_action_mono; eauto.
Qed.

Scheme BundleCastEq_ind_mut := Induction for CastEq Sort Prop
with BundleCastNode_ind_mut := Induction for CastNode Sort Prop.
Combined Scheme BundleCastEq_CastNode_ind_mut
  from BundleCastEq_ind_mut, BundleCastNode_ind_mut.

Lemma bundle_action_mono_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall n m fs self,
      m <= n ->
      certificate_bundle_action n d fs self ->
      certificate_bundle_action m d fs self)
  (forall H A B (node : CastNode H A B),
    forall n m fs payload,
      m <= n ->
      node_bundle_action n node fs payload ->
      node_bundle_action m node fs payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH n m fs self Hmn [Hroot Hpayload].
    split.
    + exact (@node_pair_value_action_mono n m H A B node fs
        (BI.proj₁ self) Hmn Hroot).
    + exact (IH n m fs (BI.proj₂ self) Hmn Hpayload).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr n m fs payload Hmn [Hl Hr].
    split; [exact (IHl n m _ _ Hmn Hl)|exact (IHr n m _ _ Hmn Hr)].
  - intros H A1 A2 B1 B2 l IHl r IHr n m fs payload Hmn [Hl Hr].
    split; [exact (IHl n m _ _ Hmn Hl)|exact (IHr n m _ _ Hmn Hr)].
  - intros H A1 A2 B1 B2 l IHl r IHr n m fs payload Hmn [Hl Hr].
    split; [exact (IHl n m _ _ Hmn Hl)|exact (IHr n m _ _ Hmn Hr)].
  - intros H body B child IH n m fs payload Hmn Hchild.
    exact (IH n m _ _ Hmn Hchild).
  - intros H A body nm child IH n m fs payload Hmn Hchild.
    exact (IH n m _ _ Hmn Hchild).
Qed.

Lemma certificate_bundle_action_mono {n m H A B}
  (d : CastEq H A B) fs self :
  m <= n ->
  certificate_bundle_action n d fs self ->
  certificate_bundle_action m d fs self.
Proof.
  exact ((proj1 bundle_action_mono_mut) H A B d n m fs self).
Qed.

Lemma node_bundle_action_mono {n m H A B}
  (node : CastNode H A B) fs payload :
  m <= n ->
  node_bundle_action n node fs payload ->
  node_bundle_action m node fs payload.
Proof.
  exact ((proj2 bundle_action_mono_mut) H A B node n m fs payload).
Qed.

Lemma unit_node_pair_action n H (fs : Frames H) payload rho :
  node_pair_value_action n (cn_unit H) fs
    (global_node_cast (cn_unit H) payload rho).
Proof.
  apply node_pair_value_action_intro.
  change (cast_pair_full_action n
    (focus (ce_step (cn_unit H)) fs)
    (BI.pair (id_cast tunit) (id_cast tunit))).
  apply identity_cast_pair_action.
  - intros. now apply unit_left_to_up.
  - intros. now apply unit_right_to_down.
  - intros. now apply unit_cross_down_to_right.
  - intros. now apply unit_cross_up_to_left.
Qed.

Lemma bool_node_pair_action n H (fs : Frames H) payload rho :
  node_pair_value_action n (cn_bool H) fs
    (global_node_cast (cn_bool H) payload rho).
Proof.
  apply node_pair_value_action_intro.
  change (cast_pair_full_action n
    (focus (ce_step (cn_bool H)) fs)
    (BI.pair (id_cast tbool) (id_cast tbool))).
  apply identity_cast_pair_action.
  - intros. now apply bool_left_to_up.
  - intros. now apply bool_right_to_down.
  - intros. now apply bool_cross_down_to_right.
  - intros. now apply bool_cross_up_to_left.
Qed.

Lemma var_node_pair_action n H x (fs : Frames H) payload rho :
  node_pair_value_action n (cn_var H x) fs
    (global_node_cast (cn_var H x) payload rho).
Proof.
  apply node_pair_value_action_intro.
  change (cast_pair_full_action n
    (focus (ce_step (cn_var H x)) fs)
    (BI.pair (id_cast (tvar x)) (id_cast (tvar x)))).
  apply identity_cast_pair_action.
  - intros. now apply var_left_to_up.
  - intros. now apply var_right_to_down.
  - intros. now apply var_cross_down_to_right.
  - intros. now apply var_cross_up_to_left.
Qed.

Lemma prod_node_pair_action n k H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  node_bundle_action n (cn_prod H A1 A2 B1 B2 fstc sndc) fs payload ->
  cast_terms_action n
    (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs) rho ->
  k <= S n ->
  node_pair_value_action k (cn_prod H A1 A2 B1 B2 fstc sndc) fs
    (global_node_cast (cn_prod H A1 A2 B1 B2 fstc sndc) payload rho).
Proof.
  intros VA1 VA2 VB1 VB2 [Hfstbundle Hsndbundle] Hrho Hkn.
  apply node_pair_value_action_intro.
  unfold cast_pair_full_action. split.
  - unfold cast_pair_value_action. split.
    { intros m Hmn vi ve Hvi Hve Hrel.
    destruct (endpoint_value_left_prod_inv m H A1 A2 B1 B2
      fstc sndc fs vi ve VA1 VA2 Hvi Hve Hrel)
      as (vi1 & vi2 & ve1 & ve2 & -> & -> & Hvi1 & Hvi2
          & Hve1 & Hve2 & Hfst & Hsnd).
    pose proof (certificate_up_action fstc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
      (BI.proj₁ payload) rho Hfstbundle Hrho) as Hfstact.
    pose proof (certificate_up_action sndc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
      (BI.proj₂ payload) rho Hsndbundle Hrho) as Hsndact.
    destruct (Hfstact (Nat.pred m) ltac:(lia)
      vi1 ve1 Hvi1 Hve1 Hfst) as (vo1 & Hvo1 & Heval1 & Hout1).
    destruct (Hsndact (Nat.pred m) ltac:(lia)
      vi2 ve2 Hvi2 Hve2 Hsnd) as (vo2 & Hvo2 & Heval2 & Hout2).
    exists (BI.pair vo1 vo2). split; [now split|]. split.
    + cbn [global_node_cast].
      eapply evalStepTrans.
      * eapply pair_first_abs_app_eval; [exact I|now split].
      * cbn.
        assert (Hcancel1 :
          BI.apTm (beta1 (BI.pair vi1 vi2))
            (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
          certificate_root fstc (BI.proj₁ payload) rho).
        { exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _
            (certificate_root fstc (BI.proj₁ payload) rho)
            (BI.pair vi1 vi2)). }
        assert (Hcancel2 :
          BI.apTm (beta1 (BI.pair vi1 vi2))
            (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
          certificate_root sndc (BI.proj₂ payload) rho).
        { exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _
            (certificate_root sndc (BI.proj₂ payload) rho)
            (BI.pair vi1 vi2)). }
        rewrite Hcancel1, Hcancel2.
        eapply pair_app_projections_eval; eauto.
    + destruct m as [|m].
      * apply cast_value_up_zero.
        -- apply StlcIso.SpecTyping.WtPair.
           ++ exact (cast_value_up_iso_typing 0 _ vo1 ve1 Hout1).
           ++ exact (cast_value_up_iso_typing 0 _ vo2 ve2 Hout2).
        -- apply StlcEqui.SpecTyping.WtPair.
           ++ exact (endpoint_value_left_equi_typing 0 _ vi1 ve1 Hfst).
           ++ exact (endpoint_value_left_equi_typing 0 _ vi2 ve2 Hsnd).
      * now apply cast_value_up_prod_intro. }
    { intros m Hmn vi ve Hvi Hve Hrel.
    destruct (endpoint_value_right_prod_inv m H A1 A2 B1 B2
      fstc sndc fs vi ve VB1 VB2 Hvi Hve Hrel)
      as (vi1 & vi2 & ve1 & ve2 & -> & -> & Hvi1 & Hvi2
          & Hve1 & Hve2 & Hfst & Hsnd).
    pose proof (certificate_down_action fstc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
      (BI.proj₁ payload) rho Hfstbundle Hrho) as Hfstact.
    pose proof (certificate_down_action sndc
      (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
      (BI.proj₂ payload) rho Hsndbundle Hrho) as Hsndact.
    destruct (Hfstact (Nat.pred m) ltac:(lia)
      vi1 ve1 Hvi1 Hve1 Hfst) as (vo1 & Hvo1 & Heval1 & Hout1).
    destruct (Hsndact (Nat.pred m) ltac:(lia)
      vi2 ve2 Hvi2 Hve2 Hsnd) as (vo2 & Hvo2 & Heval2 & Hout2).
    exists (BI.pair vo1 vo2). split; [now split|]. split.
    + cbn [global_node_cast].
      eapply evalStepTrans.
      * eapply pair_second_abs_app_eval; [exact I|now split].
      * cbn.
        assert (Hcancel1 :
          BI.apTm (beta1 (BI.pair vi1 vi2))
            (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
          certificate_root fstc (BI.proj₁ payload) rho).
        { exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _
            (certificate_root fstc (BI.proj₁ payload) rho)
            (BI.pair vi1 vi2)). }
        assert (Hcancel2 :
          BI.apTm (beta1 (BI.pair vi1 vi2))
            (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
          certificate_root sndc (BI.proj₂ payload) rho).
        { exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
            _ _ _ _ _ _
            (certificate_root sndc (BI.proj₂ payload) rho)
            (BI.pair vi1 vi2)). }
        rewrite Hcancel1, Hcancel2.
        eapply pair_app_projections_eval; eauto.
    + destruct m as [|m].
      * apply cast_value_zero.
        -- apply StlcIso.SpecTyping.WtPair.
           ++ exact (cast_value_iso_typing 0 _ vo1 ve1 Hout1).
           ++ exact (cast_value_iso_typing 0 _ vo2 ve2 Hout2).
        -- apply StlcEqui.SpecTyping.WtPair.
           ++ exact (endpoint_value_right_equi_typing 0 _ vi1 ve1 Hfst).
           ++ exact (endpoint_value_right_equi_typing 0 _ vi2 ve2 Hsnd).
      * now apply cast_value_prod_intro. }
  - split.
    + intros m Hmn vi ve Hvi Hve Hrel.
      destruct (cast_value_prod_inv m H A1 A2 B1 B2
        fstc sndc fs vi ve VB1 VB2 Hvi Hve Hrel)
        as (vi1 & vi2 & ve1 & ve2 & -> & -> & Hvi1 & Hvi2
            & Hve1 & Hve2 & Hfst & Hsnd).
      pose proof (certificate_up_recovery_action fstc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
        (BI.proj₁ payload) rho Hfstbundle Hrho) as Hfstact.
      pose proof (certificate_up_recovery_action sndc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
        (BI.proj₂ payload) rho Hsndbundle Hrho) as Hsndact.
      destruct (Hfstact (Nat.pred m) ltac:(lia)
        vi1 ve1 Hvi1 Hve1 Hfst) as (vo1 & Hvo1 & Heval1 & Hout1).
      destruct (Hsndact (Nat.pred m) ltac:(lia)
        vi2 ve2 Hvi2 Hve2 Hsnd) as (vo2 & Hvo2 & Heval2 & Hout2).
      exists (BI.pair vo1 vo2). split; [now split|]. split.
      * cbn [global_node_cast]. eapply evalStepTrans.
        -- eapply pair_first_abs_app_eval; [exact I|now split].
        -- cbn.
           assert (Hcancel1 : BI.apTm (beta1 (BI.pair vi1 vi2))
             (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
             certificate_root fstc (BI.proj₁ payload) rho)
             by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
               _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
           assert (Hcancel2 : BI.apTm (beta1 (BI.pair vi1 vi2))
             (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
             certificate_root sndc (BI.proj₂ payload) rho)
             by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
               _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
           rewrite Hcancel1, Hcancel2.
           eapply pair_app_projections_eval; eauto.
      * destruct m as [|m].
        -- split.
           ++ apply StlcIso.SpecTyping.WtPair.
              ** exact (endpoint_value_right_iso_typing 0 _ vo1 ve1 Hout1).
              ** exact (endpoint_value_right_iso_typing 0 _ vo2 ve2 Hout2).
           ++ exact (cast_value_equi_typing 0 _
                (BI.pair vi1 vi2) (HE.pair ve1 ve2) Hrel).
        -- now apply endpoint_value_right_prod_intro.
    + intros m Hmn vi ve Hvi Hve Hrel.
      destruct (cast_value_up_prod_inv m H A1 A2 B1 B2
        fstc sndc fs vi ve VA1 VA2 Hvi Hve Hrel)
        as (vi1 & vi2 & ve1 & ve2 & -> & -> & Hvi1 & Hvi2
            & Hve1 & Hve2 & Hfst & Hsnd).
      pose proof (certificate_down_recovery_action fstc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
        (BI.proj₁ payload) rho Hfstbundle Hrho) as Hfstact.
      pose proof (certificate_down_recovery_action sndc
        (frames_cons (cn_prod H A1 A2 B1 B2 fstc sndc) fs)
        (BI.proj₂ payload) rho Hsndbundle Hrho) as Hsndact.
      destruct (Hfstact (Nat.pred m) ltac:(lia)
        vi1 ve1 Hvi1 Hve1 Hfst) as (vo1 & Hvo1 & Heval1 & Hout1).
      destruct (Hsndact (Nat.pred m) ltac:(lia)
        vi2 ve2 Hvi2 Hve2 Hsnd) as (vo2 & Hvo2 & Heval2 & Hout2).
      exists (BI.pair vo1 vo2). split; [now split|]. split.
      * cbn [global_node_cast]. eapply evalStepTrans.
        -- eapply pair_second_abs_app_eval; [exact I|now split].
        -- cbn.
           assert (Hcancel1 : BI.apTm (beta1 (BI.pair vi1 vi2))
             (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
             certificate_root fstc (BI.proj₁ payload) rho)
             by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
               _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
           assert (Hcancel2 : BI.apTm (beta1 (BI.pair vi1 vi2))
             (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
             certificate_root sndc (BI.proj₂ payload) rho)
             by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
               _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
           rewrite Hcancel1, Hcancel2.
           eapply pair_app_projections_eval; eauto.
      * destruct m as [|m].
        -- split.
           ++ apply StlcIso.SpecTyping.WtPair.
              ** exact (endpoint_value_left_iso_typing 0 _ vo1 ve1 Hout1).
              ** exact (endpoint_value_left_iso_typing 0 _ vo2 ve2 Hout2).
           ++ exact (cast_value_up_equi_typing 0 _
                (BI.pair vi1 vi2) (HE.pair ve1 ve2) Hrel).
        -- now apply endpoint_value_left_prod_intro.
Qed.

Lemma sum_node_pair_action n k H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  node_bundle_action n (cn_sum H A1 A2 B1 B2 lc rc) fs payload ->
  cast_terms_action n
    (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs) rho ->
  k <= S n ->
  node_pair_value_action k (cn_sum H A1 A2 B1 B2 lc rc) fs
    (global_node_cast (cn_sum H A1 A2 B1 B2 lc rc) payload rho).
Proof.
  intros VA1 VA2 VB1 VB2 [Hlcbundle Hrcbundle] Hrho Hkn.
  apply node_pair_value_action_intro.
  unfold cast_pair_full_action. split.
  - unfold cast_pair_value_action. split.
    { intros m Hmn vi ve Hvi Hve Hrel.
    pose proof (certificate_up_action lc
      (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
      (BI.proj₁ payload) rho Hlcbundle Hrho) as Hlcact.
    pose proof (certificate_up_action rc
      (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
      (BI.proj₂ payload) rho Hrcbundle Hrho) as Hrcact.
    destruct m as [|m].
    + destruct (StlcIso.CanForm.can_form_tsum Hvi (proj1 Hrel))
        as [(vii & -> & Htii)|(vii & -> & Htii)]; cbn in Hvi.
      * assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
          by now apply compie_preserves_value.
        assert (Hchild : endpoint_value_left 0
          (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
          vii (CompilerIE.Compiler.compie vii)).
        { split; [exact Htii|]. now apply CompilerIE.Compiler.compie_typing_works. }
        destruct (Hlcact 0 ltac:(lia) vii
          (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inl vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_first_sum_inl_app_eval;
             [exact I|exact Hvi|exact Hvo|exact Heval].
        -- apply cast_value_up_zero.
           ++ apply StlcIso.SpecTyping.WtInl.
              ** exact (cast_value_up_iso_typing 0 _ vo
                   (CompilerIE.Compiler.compie vii) Hout).
              ** exact VB2.
           ++ exact (proj2 Hrel).
      * assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
          by now apply compie_preserves_value.
        assert (Hchild : endpoint_value_left 0
          (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
          vii (CompilerIE.Compiler.compie vii)).
        { split; [exact Htii|]. now apply CompilerIE.Compiler.compie_typing_works. }
        destruct (Hrcact 0 ltac:(lia) vii
          (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inr vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_first_sum_inr_app_eval;
             [exact I|exact Hvi|exact Hvo|exact Heval].
        -- apply cast_value_up_zero.
           ++ apply StlcIso.SpecTyping.WtInr.
              ** exact (cast_value_up_iso_typing 0 _ vo
                   (CompilerIE.Compiler.compie vii) Hout).
              ** exact VB1.
           ++ exact (proj2 Hrel).
    + destruct (endpoint_value_left_sum_inv m H A1 A2 B1 B2
        lc rc fs vi ve VA1 VA2 Hvi Hve Hrel)
        as [(vii & vee & -> & -> & Hvii & Hvee & Hchild)
           |(vii & vee & -> & -> & Hvii & Hvee & Hchild)].
      * destruct (Hlcact m ltac:(lia) vii vee Hvii Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inl vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_first_sum_inl_app_eval;
             [exact I|exact Hvii|exact Hvo|exact Heval].
        -- now apply cast_value_up_sum_inl_intro.
      * destruct (Hrcact m ltac:(lia) vii vee Hvii Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inr vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_first_sum_inr_app_eval;
             [exact I|exact Hvii|exact Hvo|exact Heval].
        -- now apply cast_value_up_sum_inr_intro. }
    { intros m Hmn vi ve Hvi Hve Hrel.
    pose proof (certificate_down_action lc
      (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
      (BI.proj₁ payload) rho Hlcbundle Hrho) as Hlcact.
    pose proof (certificate_down_action rc
      (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
      (BI.proj₂ payload) rho Hrcbundle Hrho) as Hrcact.
    destruct m as [|m].
    + destruct (StlcIso.CanForm.can_form_tsum Hvi (proj1 Hrel))
        as [(vii & -> & Htii)|(vii & -> & Htii)]; cbn in Hvi.
      * assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
          by now apply compie_preserves_value.
        assert (Hchild : endpoint_value_right 0
          (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
          vii (CompilerIE.Compiler.compie vii)).
        { split; [exact Htii|]. now apply CompilerIE.Compiler.compie_typing_works. }
        destruct (Hlcact 0 ltac:(lia) vii
          (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inl vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_second_sum_inl_app_eval;
             [exact I|exact Hvi|exact Hvo|exact Heval].
        -- apply cast_value_zero.
           ++ apply StlcIso.SpecTyping.WtInl.
              ** exact (cast_value_iso_typing 0 _ vo
                   (CompilerIE.Compiler.compie vii) Hout).
              ** exact VA2.
           ++ exact (proj2 Hrel).
      * assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
          by now apply compie_preserves_value.
        assert (Hchild : endpoint_value_right 0
          (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
          vii (CompilerIE.Compiler.compie vii)).
        { split; [exact Htii|]. now apply CompilerIE.Compiler.compie_typing_works. }
        destruct (Hrcact 0 ltac:(lia) vii
          (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inr vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_second_sum_inr_app_eval;
             [exact I|exact Hvi|exact Hvo|exact Heval].
        -- apply cast_value_zero.
           ++ apply StlcIso.SpecTyping.WtInr.
              ** exact (cast_value_iso_typing 0 _ vo
                   (CompilerIE.Compiler.compie vii) Hout).
              ** exact VA1.
           ++ exact (proj2 Hrel).
    + destruct (endpoint_value_right_sum_inv m H A1 A2 B1 B2
        lc rc fs vi ve VB1 VB2 Hvi Hve Hrel)
        as [(vii & vee & -> & -> & Hvii & Hvee & Hchild)
           |(vii & vee & -> & -> & Hvii & Hvee & Hchild)].
      * destruct (Hlcact m ltac:(lia) vii vee Hvii Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inl vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_second_sum_inl_app_eval;
             [exact I|exact Hvii|exact Hvo|exact Heval].
        -- now apply cast_value_sum_inl_intro.
      * destruct (Hrcact m ltac:(lia) vii vee Hvii Hvee Hchild)
          as (vo & Hvo & Heval & Hout).
        exists (BI.inr vo). split; [exact Hvo|]. split.
        -- cbn [global_node_cast].
           eapply pair_second_sum_inr_app_eval;
             [exact I|exact Hvii|exact Hvo|exact Heval].
        -- now apply cast_value_sum_inr_intro. }
  - split.
    + intros m Hmn vi ve Hvi Hve Hrel.
      pose proof (certificate_up_action lc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₁ payload) rho Hlcbundle Hrho) as Hlcordinary.
      pose proof (certificate_up_action rc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₂ payload) rho Hrcbundle Hrho) as Hrcordinary.
      pose proof (certificate_up_recovery_action lc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₁ payload) rho Hlcbundle Hrho) as Hlcrecover.
      pose proof (certificate_up_recovery_action rc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₂ payload) rho Hrcbundle Hrho) as Hrcrecover.
      destruct m as [|m].
      * destruct (StlcIso.CanForm.can_form_tsum Hvi (proj1 Hrel))
          as [(vii & -> & Htii)|(vii & -> & Htii)]; cbn in Hvi.
        -- assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
             by now apply compie_preserves_value.
           assert (Hchild : endpoint_value_left 0
             (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
             vii (CompilerIE.Compiler.compie vii)).
           { split; [exact Htii|].
             now apply CompilerIE.Compiler.compie_typing_works. }
           destruct (Hlcordinary 0 ltac:(lia) vii
             (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inl vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_first_sum_inl_app_eval;
                [exact I|exact Hvi|exact Hvo|exact Heval].
           ++ split.
              ** apply StlcIso.SpecTyping.WtInl.
                 --- exact (cast_value_up_iso_typing 0 _ vo
                       (CompilerIE.Compiler.compie vii) Hout).
                 --- exact VB2.
              ** exact (proj2 Hrel).
        -- assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
             by now apply compie_preserves_value.
           assert (Hchild : endpoint_value_left 0
             (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
             vii (CompilerIE.Compiler.compie vii)).
           { split; [exact Htii|].
             now apply CompilerIE.Compiler.compie_typing_works. }
           destruct (Hrcordinary 0 ltac:(lia) vii
             (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inr vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_first_sum_inr_app_eval;
                [exact I|exact Hvi|exact Hvo|exact Heval].
           ++ split.
              ** apply StlcIso.SpecTyping.WtInr.
                 --- exact (cast_value_up_iso_typing 0 _ vo
                       (CompilerIE.Compiler.compie vii) Hout).
                 --- exact VB1.
              ** exact (proj2 Hrel).
      * destruct (cast_value_sum_inv m H A1 A2 B1 B2
          lc rc fs vi ve Hvi Hve Hrel)
          as [(vii & vee & -> & -> & Hvii & Hvee & Hchild)
             |(vii & vee & -> & -> & Hvii & Hvee & Hchild)].
        -- destruct (Hlcrecover m ltac:(lia) vii vee Hvii Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inl vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_first_sum_inl_app_eval;
                [exact I|exact Hvii|exact Hvo|exact Heval].
           ++ now apply endpoint_value_right_sum_inl_intro.
        -- destruct (Hrcrecover m ltac:(lia) vii vee Hvii Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inr vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_first_sum_inr_app_eval;
                [exact I|exact Hvii|exact Hvo|exact Heval].
           ++ now apply endpoint_value_right_sum_inr_intro.
    + intros m Hmn vi ve Hvi Hve Hrel.
      pose proof (certificate_down_action lc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₁ payload) rho Hlcbundle Hrho) as Hlcordinary.
      pose proof (certificate_down_action rc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₂ payload) rho Hrcbundle Hrho) as Hrcordinary.
      pose proof (certificate_down_recovery_action lc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₁ payload) rho Hlcbundle Hrho) as Hlcrecover.
      pose proof (certificate_down_recovery_action rc
        (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs)
        (BI.proj₂ payload) rho Hrcbundle Hrho) as Hrcrecover.
      destruct m as [|m].
      * destruct (StlcIso.CanForm.can_form_tsum Hvi (proj1 Hrel))
          as [(vii & -> & Htii)|(vii & -> & Htii)]; cbn in Hvi.
        -- assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
             by now apply compie_preserves_value.
           assert (Hchild : endpoint_value_right 0
             (focus lc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
             vii (CompilerIE.Compiler.compie vii)).
           { split; [exact Htii|].
             now apply CompilerIE.Compiler.compie_typing_works. }
           destruct (Hlcordinary 0 ltac:(lia) vii
             (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inl vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_second_sum_inl_app_eval;
                [exact I|exact Hvi|exact Hvo|exact Heval].
           ++ split.
              ** apply StlcIso.SpecTyping.WtInl.
                 --- exact (cast_value_iso_typing 0 _ vo
                       (CompilerIE.Compiler.compie vii) Hout).
                 --- exact VA2.
              ** exact (proj2 Hrel).
        -- assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
             by now apply compie_preserves_value.
           assert (Hchild : endpoint_value_right 0
             (focus rc (frames_cons (cn_sum H A1 A2 B1 B2 lc rc) fs))
             vii (CompilerIE.Compiler.compie vii)).
           { split; [exact Htii|].
             now apply CompilerIE.Compiler.compie_typing_works. }
           destruct (Hrcordinary 0 ltac:(lia) vii
             (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inr vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_second_sum_inr_app_eval;
                [exact I|exact Hvi|exact Hvo|exact Heval].
           ++ split.
              ** apply StlcIso.SpecTyping.WtInr.
                 --- exact (cast_value_iso_typing 0 _ vo
                       (CompilerIE.Compiler.compie vii) Hout).
                 --- exact VA1.
              ** exact (proj2 Hrel).
      * destruct (cast_value_up_sum_inv m H A1 A2 B1 B2
          lc rc fs vi ve Hvi Hve Hrel)
          as [(vii & vee & -> & -> & Hvii & Hvee & Hchild)
             |(vii & vee & -> & -> & Hvii & Hvee & Hchild)].
        -- destruct (Hlcrecover m ltac:(lia) vii vee Hvii Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inl vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_second_sum_inl_app_eval;
                [exact I|exact Hvii|exact Hvo|exact Heval].
           ++ now apply endpoint_value_left_sum_inl_intro.
        -- destruct (Hrcrecover m ltac:(lia) vii vee Hvii Hvee Hchild)
             as (vo & Hvo & Heval & Hout).
           exists (BI.inr vo). split; [exact Hvo|]. split.
           ++ cbn [global_node_cast].
              eapply pair_second_sum_inr_app_eval;
                [exact I|exact Hvii|exact Hvo|exact Heval].
           ++ now apply endpoint_value_left_sum_inr_intro.
Qed.
Lemma arr_forward_action n k H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  PairEnvValid H ->
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_arr H A1 A2 B1 B2 dom cod)) ->
  CastTermsTyping empty ((tarr A1 A2, tarr B1 B2) :: H) rho ->
  node_bundle_action n (cn_arr H A1 A2 B1 B2 dom cod) fs payload ->
  cast_terms_action n
    (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs) rho ->
  k <= S n ->
  forward_value_action k
    (focus (ce_step (cn_arr H A1 A2 B1 B2 dom cod)) fs)
    (pair_up
      (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)).
Proof.
  intros VH VA1 VA2 VB1 VB2 Hpayload Htyrho
    [Hdombundle Hcodbundle] Hrho Hkn m.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - set (vo := BI.apTm (beta1 vi)
        (BI.abs B1
          (BI.app
            (certificate_up cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_down dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_up
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi) vo).
    { cbn [pair_up global_node_cast].
      eapply pair_first_abs_app_eval; [exact I|exact Hvi].
    }
    exists vo. split; [exact I|]. split.
    + exact Heval.
    + apply cast_value_up_zero.
      * assert (Hpair : StlcIso.SpecTyping.Typing empty
          (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)
          (cast_pair_ty (tarr A1 A2) (tarr B1 B2))).
        { eapply global_node_cast_typing; eauto;
            now apply ValidTy_arr. }
        assert (Happ : StlcIso.SpecTyping.Typing empty
          (BI.app
            (pair_up
              (global_node_cast
                (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi)
          (tarr B1 B2)).
        { eapply StlcIso.SpecTyping.WtApp.
          - exact (pair_up_typing Hpair).
          - exact (proj1 Hrel). }
        exact (StlcIso.TypeSafety.preservation_star
          Heval ValidEnv_nil Happ).
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as (ti & te & -> & -> & Hfun).
    set (vo := BI.apTm (beta1 (BI.abs A1 ti))
        (BI.abs B1
          (BI.app
            (certificate_up cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_down dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_up
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho))
        (BI.abs A1 ti)) vo).
    { cbn [pair_up global_node_cast].
      eapply pair_first_abs_app_eval; [exact I|exact I]. }
    assert (Hprev_parent : endpoint_value_left m
      (focus (ce_step (cn_arr H A1 A2 B1 B2 dom cod)) fs)
      (BI.abs A1 ti) (HE.abs A1 te)).
    { exact Hprev. }
    destruct (IH ltac:(lia) (BI.abs A1 ti) (HE.abs A1 te)
      I I Hprev_parent) as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Heval
        (StlcIso.LemmasEvaluation.values_are_normal (t := vo) I)). }
    assert (vop = vo).
    { now apply StlcIso.LemmasEvaluation.value_evalStar. }
    subst vop. exists vo. split; [exact I|]. split; [exact Heval|].
    cbn. split.
    + exact (proj2 (cast_value_up_normalize m _ _ _) Houtp).
    + eexists. exists te. split; [reflexivity|].
      split; [reflexivity|].
      intros vai vae Hvai Hvae Harg.
      pose proof (certificate_down_recovery_action dom
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₁ payload) rho Hdombundle Hrho) as Hdomact.
      pose proof (certificate_up_action cod
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₂ payload) rho Hcodbundle Hrho) as Hcodact.
      destruct (Hdomact m ltac:(lia) vai vae Hvai Hvae Harg)
        as (vad & Hvad & Hdeval & Hendpoint).
      assert (Hsource : endpoint_term_left m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (BI.abs A1 ti)
          (BI.app (certificate_down dom (BI.proj₁ payload) rho) vai))
        (HE.app (HE.abs A1 te) vae)).
      { eapply term_lift_antired.
        - exact (StlcIso.LemmasEvaluation.evalstar_ctx
            (BI.papp₂ (BI.abs A1 ti) BI.phole) (conj I I) Hdeval).
        - constructor.
        - exact (Hfun vad vae Hvad Hvae Hendpoint). }
      assert (Hmapped : cast_term_up m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (certificate_up cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs A1 ti)
            (BI.app (certificate_down dom (BI.proj₁ payload) rho) vai)))
        (HE.app (HE.abs A1 te) vae)).
      { eapply forward_action_map_term.
        - exact Hcodact.
        - lia.
        - exact Hsource. }
      assert (Houtereval : BIE.evalStar (BI.app vo vai)
        (BI.app (certificate_up cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs A1 ti)
            (BI.app (certificate_down dom (BI.proj₁ payload) rho) vai)))).
      { unfold vo. apply generated_arrow_application_eval. exact Hvai. }
      eapply term_lift_antired.
      * exact Houtereval.
      * constructor.
      * exact Hmapped.
Qed.
Lemma arr_forward_recovery_action n k H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  PairEnvValid H ->
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_arr H A1 A2 B1 B2 dom cod)) ->
  CastTermsTyping empty ((tarr A1 A2, tarr B1 B2) :: H) rho ->
  node_bundle_action n (cn_arr H A1 A2 B1 B2 dom cod) fs payload ->
  cast_terms_action n
    (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs) rho ->
  k <= S n ->
  forward_recovery_action k
    (focus (ce_step (cn_arr H A1 A2 B1 B2 dom cod)) fs)
    (pair_up
      (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)).
Proof.
  intros VH VA1 VA2 VB1 VB2 Hpayload Htyrho
    [Hdombundle Hcodbundle] Hrho Hkn m.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - set (vo := BI.apTm (beta1 vi)
        (BI.abs B1
          (BI.app
            (certificate_up cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_down dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_up
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi) vo).
    { cbn [pair_up global_node_cast].
      eapply pair_first_abs_app_eval; [exact I|exact Hvi].
    }
    exists vo. split; [exact I|]. split.
    + exact Heval.
    + split.
      * assert (Hpair : StlcIso.SpecTyping.Typing empty
          (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)
          (cast_pair_ty (tarr A1 A2) (tarr B1 B2))).
        { eapply global_node_cast_typing; eauto;
            now apply ValidTy_arr. }
        assert (Happ : StlcIso.SpecTyping.Typing empty
          (BI.app
            (pair_up
              (global_node_cast
                (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi)
          (tarr B1 B2)).
        { eapply StlcIso.SpecTyping.WtApp.
          - exact (pair_up_typing Hpair).
          - exact (proj1 Hrel). }
        exact (StlcIso.TypeSafety.preservation_star
          Heval ValidEnv_nil Happ).
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as (ti & te & -> & -> & Hfun).
    set (vo := BI.apTm (beta1 (BI.abs A1 ti))
        (BI.abs B1
          (BI.app
            (certificate_up cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_down dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_up
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho))
        (BI.abs A1 ti)) vo).
    { cbn [pair_up global_node_cast].
      eapply pair_first_abs_app_eval; [exact I|exact I]. }
    assert (Hprev_parent : cast_value m
      (focus (ce_step (cn_arr H A1 A2 B1 B2 dom cod)) fs)
      (BI.abs A1 ti) (HE.abs B1 te)).
    { exact Hprev. }
    destruct (IH ltac:(lia) (BI.abs A1 ti) (HE.abs B1 te)
      I I Hprev_parent) as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Heval
        (StlcIso.LemmasEvaluation.values_are_normal (t := vo) I)). }
    assert (vop = vo).
    { now apply StlcIso.LemmasEvaluation.value_evalStar. }
    subst vop. exists vo. split; [exact I|]. split; [exact Heval|].
    cbn. split.
    + exact (proj2 (endpoint_value_right_normalize m _ _ _) Houtp).
    + eexists. exists te. split; [reflexivity|].
      split; [reflexivity|].
      intros vai vae Hvai Hvae Harg.
      pose proof (certificate_down_action dom
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₁ payload) rho Hdombundle Hrho) as Hdomact.
      pose proof (certificate_up_recovery_action cod
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₂ payload) rho Hcodbundle Hrho) as Hcodact.
      destruct (Hdomact m ltac:(lia) vai vae Hvai Hvae Harg)
        as (vad & Hvad & Hdeval & Hendpoint).
      assert (Hsource : cast_term m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (BI.abs A1 ti)
          (BI.app (certificate_down dom (BI.proj₁ payload) rho) vai))
        (HE.app (HE.abs B1 te) vae)).
      { eapply term_lift_antired.
        - exact (StlcIso.LemmasEvaluation.evalstar_ctx
            (BI.papp₂ (BI.abs A1 ti) BI.phole) (conj I I) Hdeval).
        - constructor.
        - exact (Hfun vad vae Hvad Hvae Hendpoint). }
      assert (Hmapped : endpoint_term_right m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (certificate_up cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs A1 ti)
            (BI.app (certificate_down dom (BI.proj₁ payload) rho) vai)))
        (HE.app (HE.abs B1 te) vae)).
      { eapply forward_recovery_map_term.
        - exact Hcodact.
        - lia.
        - exact Hsource. }
      assert (Houtereval : BIE.evalStar (BI.app vo vai)
        (BI.app (certificate_up cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs A1 ti)
            (BI.app (certificate_down dom (BI.proj₁ payload) rho) vai)))).
      { unfold vo. apply generated_arrow_application_eval. exact Hvai. }
      eapply term_lift_antired.
      * exact Houtereval.
      * constructor.
      * exact Hmapped.
Qed.

Lemma arr_reverse_recovery_action n k H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  PairEnvValid H ->
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_arr H A1 A2 B1 B2 dom cod)) ->
  CastTermsTyping empty ((tarr A1 A2, tarr B1 B2) :: H) rho ->
  node_bundle_action n (cn_arr H A1 A2 B1 B2 dom cod) fs payload ->
  cast_terms_action n
    (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs) rho ->
  k <= S n ->
  reverse_recovery_action k
    (focus (ce_step (cn_arr H A1 A2 B1 B2 dom cod)) fs)
    (pair_down
      (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)).
Proof.
  intros VH VA1 VA2 VB1 VB2 Hpayload Htyrho
    [Hdombundle Hcodbundle] Hrho Hkn m.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - set (vo := BI.apTm (beta1 vi)
        (BI.abs A1
          (BI.app
            (certificate_down cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_up dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_down
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi) vo).
    { cbn [pair_down global_node_cast].
      eapply pair_second_abs_app_eval; [exact I|exact Hvi]. }
    exists vo. split; [exact I|]. split; [exact Heval|].
    split.
    + assert (Hpair : StlcIso.SpecTyping.Typing empty
        (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)
        (cast_pair_ty (tarr A1 A2) (tarr B1 B2))).
      { eapply global_node_cast_typing; eauto; now apply ValidTy_arr. }
      assert (Happ : StlcIso.SpecTyping.Typing empty
        (BI.app
          (pair_down
            (global_node_cast
              (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi)
        (tarr A1 A2)).
      { eapply StlcIso.SpecTyping.WtApp.
        - exact (pair_down_typing Hpair).
        - exact (proj1 Hrel). }
      exact (StlcIso.TypeSafety.preservation_star Heval ValidEnv_nil Happ).
    + exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as (ti & te & -> & -> & Hfun).
    set (vo := BI.apTm (beta1 (BI.abs B1 ti))
        (BI.abs A1
          (BI.app
            (certificate_down cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_up dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_down
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho))
        (BI.abs B1 ti)) vo).
    { cbn [pair_down global_node_cast].
      eapply pair_second_abs_app_eval; [exact I|exact I]. }
    destruct (IH ltac:(lia) (BI.abs B1 ti) (HE.abs A1 te)
      I I Hprev) as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Heval
        (StlcIso.LemmasEvaluation.values_are_normal (t := vo) I)). }
    assert (vop = vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists vo. split; [exact I|]. split; [exact Heval|].
    cbn. split.
    + exact (proj2 (endpoint_value_left_normalize m _ _ _) Houtp).
    + eexists. exists te. split; [reflexivity|].
      split; [reflexivity|].
      intros vai vae Hvai Hvae Harg.
      pose proof (certificate_up_action dom
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₁ payload) rho Hdombundle Hrho) as Hdomact.
      pose proof (certificate_down_recovery_action cod
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₂ payload) rho Hcodbundle Hrho) as Hcodact.
      destruct (Hdomact m ltac:(lia) vai vae Hvai Hvae Harg)
        as (vad & Hvad & Hdeval & Hendpoint).
      assert (Hsource : cast_term_up m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (BI.abs B1 ti)
          (BI.app (certificate_up dom (BI.proj₁ payload) rho) vai))
        (HE.app (HE.abs A1 te) vae)).
      { eapply term_lift_antired.
        - exact (StlcIso.LemmasEvaluation.evalstar_ctx
            (BI.papp₂ (BI.abs B1 ti) BI.phole) (conj I I) Hdeval).
        - constructor.
        - exact (Hfun vad vae Hvad Hvae Hendpoint). }
      assert (Hmapped : endpoint_term_left m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (certificate_down cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs B1 ti)
            (BI.app (certificate_up dom (BI.proj₁ payload) rho) vai)))
        (HE.app (HE.abs A1 te) vae)).
      { eapply reverse_recovery_map_term.
        - exact Hcodact.
        - lia.
        - exact Hsource. }
      assert (Houtereval : BIE.evalStar (BI.app vo vai)
        (BI.app (certificate_down cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs B1 ti)
            (BI.app (certificate_up dom (BI.proj₁ payload) rho) vai)))).
      { unfold vo. apply generated_arrow_application_eval. exact Hvai. }
      eapply term_lift_antired.
      * exact Houtereval.
      * constructor.
      * exact Hmapped.
Qed.
Lemma arr_reverse_action n k H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  PairEnvValid H ->
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_arr H A1 A2 B1 B2 dom cod)) ->
  CastTermsTyping empty ((tarr A1 A2, tarr B1 B2) :: H) rho ->
  node_bundle_action n (cn_arr H A1 A2 B1 B2 dom cod) fs payload ->
  cast_terms_action n
    (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs) rho ->
  k <= S n ->
  reverse_value_action k
    (focus (ce_step (cn_arr H A1 A2 B1 B2 dom cod)) fs)
    (pair_down
      (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)).
Proof.
  intros VH VA1 VA2 VB1 VB2 Hpayload Htyrho
    [Hdombundle Hcodbundle] Hrho Hkn m.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - set (vo := BI.apTm (beta1 vi)
        (BI.abs A1
          (BI.app
            (certificate_down cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_up dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_down
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi) vo).
    { cbn [pair_down global_node_cast].
      eapply pair_second_abs_app_eval; [exact I|exact Hvi]. }
    exists vo. split; [exact I|]. split; [exact Heval|].
    apply cast_value_zero.
    + assert (Hpair : StlcIso.SpecTyping.Typing empty
        (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho)
        (cast_pair_ty (tarr A1 A2) (tarr B1 B2))).
      { eapply global_node_cast_typing; eauto; now apply ValidTy_arr. }
      assert (Happ : StlcIso.SpecTyping.Typing empty
        (BI.app
          (pair_down
            (global_node_cast
              (cn_arr H A1 A2 B1 B2 dom cod) payload rho)) vi)
        (tarr A1 A2)).
      { eapply StlcIso.SpecTyping.WtApp.
        - exact (pair_down_typing Hpair).
        - exact (proj1 Hrel). }
      exact (StlcIso.TypeSafety.preservation_star Heval ValidEnv_nil Happ).
    + exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct Hlayer as (ti & te & -> & -> & Hfun).
    set (vo := BI.apTm (beta1 (BI.abs B1 ti))
        (BI.abs A1
          (BI.app
            (certificate_down cod (BI.proj₂ payload) rho)[wkm][wkm]
            (BI.app (BI.var 1)
              (BI.app
                (certificate_up dom (BI.proj₁ payload) rho)[wkm][wkm]
                (BI.var 0)))))).
    assert (Heval : BIE.evalStar
      (BI.app
        (pair_down
          (global_node_cast
            (cn_arr H A1 A2 B1 B2 dom cod) payload rho))
        (BI.abs B1 ti)) vo).
    { cbn [pair_down global_node_cast].
      eapply pair_second_abs_app_eval; [exact I|exact I]. }
    destruct (IH ltac:(lia) (BI.abs B1 ti) (HE.abs B1 te)
      I I Hprev) as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Heval
        (StlcIso.LemmasEvaluation.values_are_normal (t := vo) I)). }
    assert (vop = vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists vo. split; [exact I|]. split; [exact Heval|].
    cbn. split.
    + exact (proj2 (cast_value_normalize m _ _ _) Houtp).
    + eexists. exists te. split; [reflexivity|].
      split; [reflexivity|].
      intros vai vae Hvai Hvae Harg.
      pose proof (certificate_up_recovery_action dom
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₁ payload) rho Hdombundle Hrho) as Hdomact.
      pose proof (certificate_down_action cod
        (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs)
        (BI.proj₂ payload) rho Hcodbundle Hrho) as Hcodact.
      destruct (Hdomact m ltac:(lia) vai vae Hvai Hvae Harg)
        as (vad & Hvad & Hdeval & Hendpoint).
      assert (Hsource : endpoint_term_right m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (BI.abs B1 ti)
          (BI.app (certificate_up dom (BI.proj₁ payload) rho) vai))
        (HE.app (HE.abs B1 te) vae)).
      { eapply term_lift_antired.
        - exact (StlcIso.LemmasEvaluation.evalstar_ctx
            (BI.papp₂ (BI.abs B1 ti) BI.phole) (conj I I) Hdeval).
        - constructor.
        - exact (Hfun vad vae Hvad Hvae Hendpoint). }
      assert (Hmapped : cast_term m
        (focus cod
          (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs))
        (BI.app (certificate_down cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs B1 ti)
            (BI.app (certificate_up dom (BI.proj₁ payload) rho) vai)))
        (HE.app (HE.abs B1 te) vae)).
      { eapply reverse_action_map_term.
        - exact Hcodact.
        - lia.
        - exact Hsource. }
      assert (Houtereval : BIE.evalStar (BI.app vo vai)
        (BI.app (certificate_down cod (BI.proj₂ payload) rho)
          (BI.app (BI.abs B1 ti)
            (BI.app (certificate_up dom (BI.proj₁ payload) rho) vai)))).
      { unfold vo. apply generated_arrow_application_eval. exact Hvai. }
      eapply term_lift_antired.
      * exact Houtereval.
      * constructor.
      * exact Hmapped.
Qed.

Lemma arr_node_pair_action n k H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  PairEnvValid H ->
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_arr H A1 A2 B1 B2 dom cod)) ->
  CastTermsTyping empty ((tarr A1 A2, tarr B1 B2) :: H) rho ->
  node_bundle_action n (cn_arr H A1 A2 B1 B2 dom cod) fs payload ->
  cast_terms_action n
    (frames_cons (cn_arr H A1 A2 B1 B2 dom cod) fs) rho ->
  k <= S n ->
  node_pair_value_action k (cn_arr H A1 A2 B1 B2 dom cod) fs
    (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho).
Proof.
  intros VH VA1 VA2 VB1 VB2 Hpayload Htyrho Hbundle Hrho Hkn.
  apply node_pair_value_action_intro.
  unfold cast_pair_full_action, cast_pair_value_action. split.
  - split.
    + exact (arr_forward_action n k H A1 A2 B1 B2 dom cod fs payload rho
        VH VA1 VA2 VB1 VB2 Hpayload Htyrho Hbundle Hrho Hkn).
    + exact (arr_reverse_action n k H A1 A2 B1 B2 dom cod fs payload rho
        VH VA1 VA2 VB1 VB2 Hpayload Htyrho Hbundle Hrho Hkn).
  - split.
    + exact (arr_forward_recovery_action n k H A1 A2 B1 B2 dom cod fs
        payload rho VH VA1 VA2 VB1 VB2 Hpayload Htyrho Hbundle Hrho Hkn).
    + exact (arr_reverse_recovery_action n k H A1 A2 B1 B2 dom cod fs
        payload rho VH VA1 VA2 VB1 VB2 Hpayload Htyrho Hbundle Hrho Hkn).
Qed.
Lemma mu_l_forward_action n k H body B
  (child : CastEq ((trec body, B) :: H) body[beta1 (trec body)] B)
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy (trec body) -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_l H body B child)) ->
  CastTermsTyping empty ((trec body, B) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_l H body B child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_l H body B child) fs) rho ->
  k <= S n ->
  forward_value_action k
    (focus (ce_step (cn_mu_l H body B child)) fs)
    (pair_up (global_node_cast (cn_mu_l H body B child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_up_action child
    (frames_cons (cn_mu_l H body B child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - destruct (StlcIso.CanForm.can_form_trec Hvi (proj1 Hrel))
      as (vii & -> & Hvii_ty). cbn in Hvi.
    assert (Hvee : HEE.Value (CompilerIE.Compiler.compie vii))
      by now apply compie_preserves_value.
    assert (Hchild : endpoint_value_left 0
      (focus child (frames_cons (cn_mu_l H body B child) fs))
      vii (CompilerIE.Compiler.compie vii)).
    { split; [exact Hvii_ty|].
      now apply CompilerIE.Compiler.compie_typing_works. }
    destruct (Hchildact 0 ltac:(lia) vii
      (CompilerIE.Compiler.compie vii) Hvi Hvee Hchild)
      as (vo & Hvo & Heval & Hout).
    exists vo. split; [exact Hvo|]. split.
    + cbn [pair_up global_node_cast].
      eapply pair_first_mu_l_app_eval; eauto.
    + apply cast_value_up_zero.
      * exact (cast_value_up_iso_typing 0 _ vo
          (CompilerIE.Compiler.compie vii) Hout).
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev (vii & -> & Hchild)].
    cbn in Hvi.
    destruct (Hchildact m ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_up (global_node_cast (cn_mu_l H body B child) payload rho))
        (BI.fold_ vii)) vo).
    { cbn [pair_up global_node_cast].
      eapply pair_first_mu_l_app_eval; eauto. }
    destruct (IH ltac:(lia) (BI.fold_ vii) ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal Hvo)). }
    assert (vop = vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists vo. repeat split; try assumption.
Qed.

Lemma mu_l_reverse_action n k H body B
  (child : CastEq ((trec body, B) :: H) body[beta1 (trec body)] B)
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy (trec body) -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_l H body B child)) ->
  CastTermsTyping empty ((trec body, B) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_l H body B child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_l H body B child) fs) rho ->
  k <= S n ->
  reverse_value_action k
    (focus (ce_step (cn_mu_l H body B child)) fs)
    (pair_down (global_node_cast (cn_mu_l H body B child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_down_action child
    (frames_cons (cn_mu_l H body B child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - assert (Hchild : endpoint_value_right 0
      (focus child (frames_cons (cn_mu_l H body B child) fs)) vi ve)
      by exact Hrel.
    destruct (Hchildact 0 ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists (BI.fold_ vo). split; [exact Hvo|]. split.
    + cbn [pair_down global_node_cast].
      eapply pair_second_mu_l_app_eval; eauto.
    + apply cast_value_zero.
      * apply StlcIso.SpecTyping.WtFold.
        -- exact (cast_value_iso_typing 0 _ vo ve Hout).
        -- exact VA.
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hchild].
    destruct (Hchildact m ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_down (global_node_cast (cn_mu_l H body B child) payload rho))
        vi) (BI.fold_ vo)).
    { cbn [pair_down global_node_cast].
      eapply pair_second_mu_l_app_eval; eauto. }
    destruct (IH ltac:(lia) vi ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop (BI.fold_ vo)).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal
          (t := BI.fold_ vo) Hvo)). }
    assert (vop = BI.fold_ vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists (BI.fold_ vo). split; [exact Hvo|].
    split; [exact Hwhole|]. cbn. split.
    + exact (proj2 (cast_value_normalize m _ _ _) Houtp).
    + exists vo. split; [reflexivity|exact Hout].
Qed.

Lemma mu_l_forward_recovery_action n k H body B
  (child : CastEq ((trec body, B) :: H) body[beta1 (trec body)] B)
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy (trec body) -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_l H body B child)) ->
  CastTermsTyping empty ((trec body, B) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_l H body B child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_l H body B child) fs) rho ->
  k <= S n ->
  forward_recovery_action k
    (focus (ce_step (cn_mu_l H body B child)) fs)
    (pair_up (global_node_cast (cn_mu_l H body B child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_up_recovery_action child
    (frames_cons (cn_mu_l H body B child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - destruct (StlcIso.CanForm.can_form_trec Hvi (proj1 Hrel))
      as (vii & -> & Hvii_ty). cbn in Hvi.
    assert (Hchild : cast_value 0
      (focus child (frames_cons (cn_mu_l H body B child) fs)) vii ve).
    { split; [exact Hvii_ty|exact (proj2 Hrel)]. }
    destruct (Hchildact 0 ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists vo. split; [exact Hvo|]. split.
    + cbn [pair_up global_node_cast].
      eapply pair_first_mu_l_app_eval; eauto.
    + exact Hout.
  - cbn in Hrel. destruct Hrel as [Hprev (vii & -> & Hchild)].
    cbn in Hvi.
    destruct (Hchildact m ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_up (global_node_cast (cn_mu_l H body B child) payload rho))
        (BI.fold_ vii)) vo).
    { cbn [pair_up global_node_cast].
      eapply pair_first_mu_l_app_eval; eauto. }
    destruct (IH ltac:(lia) (BI.fold_ vii) ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal Hvo)). }
    assert (vop = vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists vo. repeat split; try assumption.
Qed.

Lemma mu_l_reverse_recovery_action n k H body B
  (child : CastEq ((trec body, B) :: H) body[beta1 (trec body)] B)
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy (trec body) -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_l H body B child)) ->
  CastTermsTyping empty ((trec body, B) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_l H body B child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_l H body B child) fs) rho ->
  k <= S n ->
  reverse_recovery_action k
    (focus (ce_step (cn_mu_l H body B child)) fs)
    (pair_down (global_node_cast (cn_mu_l H body B child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_down_recovery_action child
    (frames_cons (cn_mu_l H body B child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - assert (Hchild : cast_value_up 0
      (focus child (frames_cons (cn_mu_l H body B child) fs)) vi ve).
    { split; [exact (proj1 Hrel)|].
      exact (equi_typing_unfold VA (proj2 Hrel)). }
    destruct (Hchildact 0 ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists (BI.fold_ vo). split; [exact Hvo|]. split.
    + cbn [pair_down global_node_cast].
      eapply pair_second_mu_l_app_eval; eauto.
    + split.
      * apply StlcIso.SpecTyping.WtFold.
        -- exact (endpoint_value_left_iso_typing 0 _ vo ve Hout).
        -- exact VA.
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hchild].
    destruct (Hchildact m ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_down (global_node_cast (cn_mu_l H body B child) payload rho))
        vi) (BI.fold_ vo)).
    { cbn [pair_down global_node_cast].
      eapply pair_second_mu_l_app_eval; eauto. }
    destruct (IH ltac:(lia) vi ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop (BI.fold_ vo)).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal
          (t := BI.fold_ vo) Hvo)). }
    assert (vop = BI.fold_ vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists (BI.fold_ vo). split; [exact Hvo|].
    split; [exact Hwhole|]. cbn. split.
    + exact (proj2 (endpoint_value_left_normalize m _ _ _) Houtp).
    + exists vo. split; [reflexivity|exact Hout].
Qed.

Lemma mu_l_node_pair_action n k H body B
  (child : CastEq ((trec body, B) :: H) body[beta1 (trec body)] B)
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy (trec body) -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_l H body B child)) ->
  CastTermsTyping empty ((trec body, B) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_l H body B child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_l H body B child) fs) rho ->
  k <= S n ->
  node_pair_value_action k (cn_mu_l H body B child) fs
    (global_node_cast (cn_mu_l H body B child) payload rho).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn.
  apply node_pair_value_action_intro.
  unfold cast_pair_full_action, cast_pair_value_action. split.
  - split.
    + exact (mu_l_forward_action n k H body B child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
    + exact (mu_l_reverse_action n k H body B child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
  - split.
    + exact (mu_l_forward_recovery_action n k H body B child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
    + exact (mu_l_reverse_recovery_action n k H body B child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
Qed.

Lemma mu_r_forward_action n k H A body nm
  (child : CastEq ((A, trec body) :: H) A body[beta1 (trec body)])
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy (trec body) ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_r H A body nm child)) ->
  CastTermsTyping empty ((A, trec body) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_r H A body nm child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_r H A body nm child) fs) rho ->
  k <= S n ->
  forward_value_action k
    (focus (ce_step (cn_mu_r H A body nm child)) fs)
    (pair_up (global_node_cast (cn_mu_r H A body nm child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_up_action child
    (frames_cons (cn_mu_r H A body nm child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - assert (Hchild : endpoint_value_left 0
      (focus child (frames_cons (cn_mu_r H A body nm child) fs)) vi ve)
      by exact Hrel.
    destruct (Hchildact 0 ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists (BI.fold_ vo). split; [exact Hvo|]. split.
    + cbn [pair_up global_node_cast].
      eapply pair_first_mu_r_app_eval; eauto.
    + apply cast_value_up_zero.
      * apply StlcIso.SpecTyping.WtFold.
        -- exact (cast_value_up_iso_typing 0 _ vo ve Hout).
        -- exact VB.
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hchild].
    destruct (Hchildact m ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_up (global_node_cast (cn_mu_r H A body nm child) payload rho))
        vi) (BI.fold_ vo)).
    { cbn [pair_up global_node_cast].
      eapply pair_first_mu_r_app_eval; eauto. }
    destruct (IH ltac:(lia) vi ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop (BI.fold_ vo)).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal
          (t := BI.fold_ vo) Hvo)). }
    assert (vop = BI.fold_ vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists (BI.fold_ vo). split; [exact Hvo|].
    split; [exact Hwhole|]. cbn. split.
    + exact (proj2 (cast_value_up_normalize m _ _ _) Houtp).
    + exists vo. split; [reflexivity|exact Hout].
Qed.

Lemma mu_r_reverse_action n k H A body nm
  (child : CastEq ((A, trec body) :: H) A body[beta1 (trec body)])
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy (trec body) ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_r H A body nm child)) ->
  CastTermsTyping empty ((A, trec body) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_r H A body nm child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_r H A body nm child) fs) rho ->
  k <= S n ->
  reverse_value_action k
    (focus (ce_step (cn_mu_r H A body nm child)) fs)
    (pair_down (global_node_cast (cn_mu_r H A body nm child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_down_action child
    (frames_cons (cn_mu_r H A body nm child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - destruct (StlcIso.CanForm.can_form_trec Hvi (proj1 Hrel))
      as (vii & -> & Hvii_ty). cbn in Hvi.
    assert (Hchild : endpoint_value_right 0
      (focus child (frames_cons (cn_mu_r H A body nm child) fs)) vii ve).
    { split; [exact Hvii_ty|].
      exact (equi_typing_unfold VB (proj2 Hrel)). }
    destruct (Hchildact 0 ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists vo. split; [exact Hvo|]. split.
    + cbn [pair_down global_node_cast].
      eapply pair_second_mu_r_app_eval; eauto.
    + apply cast_value_zero.
      * exact (cast_value_iso_typing 0 _ vo ve Hout).
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev (vii & -> & Hchild)].
    cbn in Hvi.
    destruct (Hchildact m ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_down (global_node_cast (cn_mu_r H A body nm child) payload rho))
        (BI.fold_ vii)) vo).
    { cbn [pair_down global_node_cast].
      eapply pair_second_mu_r_app_eval; eauto. }
    destruct (IH ltac:(lia) (BI.fold_ vii) ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal Hvo)). }
    assert (vop = vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists vo. repeat split; try assumption.
Qed.

Lemma mu_r_forward_recovery_action n k H A body nm
  (child : CastEq ((A, trec body) :: H) A body[beta1 (trec body)])
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy (trec body) ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_r H A body nm child)) ->
  CastTermsTyping empty ((A, trec body) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_r H A body nm child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_r H A body nm child) fs) rho ->
  k <= S n ->
  forward_recovery_action k
    (focus (ce_step (cn_mu_r H A body nm child)) fs)
    (pair_up (global_node_cast (cn_mu_r H A body nm child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_up_recovery_action child
    (frames_cons (cn_mu_r H A body nm child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - assert (Hchild : cast_value 0
      (focus child (frames_cons (cn_mu_r H A body nm child) fs)) vi ve).
    { split; [exact (proj1 Hrel)|].
      exact (equi_typing_unfold VB (proj2 Hrel)). }
    destruct (Hchildact 0 ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists (BI.fold_ vo). split; [exact Hvo|]. split.
    + cbn [pair_up global_node_cast].
      eapply pair_first_mu_r_app_eval; eauto.
    + split.
      * apply StlcIso.SpecTyping.WtFold.
        -- exact (endpoint_value_right_iso_typing 0 _ vo ve Hout).
        -- exact VB.
      * exact (proj2 Hrel).
  - cbn in Hrel. destruct Hrel as [Hprev Hchild].
    destruct (Hchildact m ltac:(lia) vi ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_up (global_node_cast (cn_mu_r H A body nm child) payload rho))
        vi) (BI.fold_ vo)).
    { cbn [pair_up global_node_cast].
      eapply pair_first_mu_r_app_eval; eauto. }
    destruct (IH ltac:(lia) vi ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop (BI.fold_ vo)).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal
          (t := BI.fold_ vo) Hvo)). }
    assert (vop = BI.fold_ vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists (BI.fold_ vo). split; [exact Hvo|].
    split; [exact Hwhole|]. cbn. split.
    + exact (proj2 (endpoint_value_right_normalize m _ _ _) Houtp).
    + exists vo. split; [reflexivity|exact Hout].
Qed.

Lemma mu_r_reverse_recovery_action n k H A body nm
  (child : CastEq ((A, trec body) :: H) A body[beta1 (trec body)])
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy (trec body) ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_r H A body nm child)) ->
  CastTermsTyping empty ((A, trec body) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_r H A body nm child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_r H A body nm child) fs) rho ->
  k <= S n ->
  reverse_recovery_action k
    (focus (ce_step (cn_mu_r H A body nm child)) fs)
    (pair_down (global_node_cast (cn_mu_r H A body nm child) payload rho)).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn m.
  pose proof (certificate_down_recovery_action child
    (frames_cons (cn_mu_r H A body nm child) fs)
    payload rho Hbundle Hrho) as Hchildact.
  induction m as [|m IH]; intros Hmn vi ve Hvi Hve Hrel.
  - destruct (StlcIso.CanForm.can_form_trec Hvi (proj1 Hrel))
      as (vii & -> & Hvii_ty). cbn in Hvi.
    assert (Hchild : cast_value_up 0
      (focus child (frames_cons (cn_mu_r H A body nm child) fs)) vii ve).
    { split; [exact Hvii_ty|exact (proj2 Hrel)]. }
    destruct (Hchildact 0 ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    exists vo. split; [exact Hvo|]. split.
    + cbn [pair_down global_node_cast].
      eapply pair_second_mu_r_app_eval; eauto.
    + exact Hout.
  - cbn in Hrel. destruct Hrel as [Hprev (vii & -> & Hchild)].
    cbn in Hvi.
    destruct (Hchildact m ltac:(lia) vii ve Hvi Hve Hchild)
      as (vo & Hvo & Heval & Hout).
    assert (Hwhole : BIE.evalStar
      (BI.app
        (pair_down (global_node_cast (cn_mu_r H A body nm child) payload rho))
        (BI.fold_ vii)) vo).
    { cbn [pair_down global_node_cast].
      eapply pair_second_mu_r_app_eval; eauto. }
    destruct (IH ltac:(lia) (BI.fold_ vii) ve Hvi Hve Hprev)
      as (vop & Hvop & Hevalp & Houtp).
    assert (Hvop_vo : BIE.evalStar vop vo).
    { exact (StlcIso.LemmasEvaluation.determinacyStar
        Hevalp Hwhole
        (StlcIso.LemmasEvaluation.values_are_normal Hvo)). }
    assert (vop = vo) by
      now apply StlcIso.LemmasEvaluation.value_evalStar.
    subst vop. exists vo. repeat split; try assumption.
Qed.

Lemma mu_r_node_pair_action n k H A body nm
  (child : CastEq ((A, trec body) :: H) A body[beta1 (trec body)])
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy (trec body) ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_mu_r H A body nm child)) ->
  CastTermsTyping empty ((A, trec body) :: H) rho ->
  certificate_bundle_action n child
    (frames_cons (cn_mu_r H A body nm child) fs) payload ->
  cast_terms_action n (frames_cons (cn_mu_r H A body nm child) fs) rho ->
  k <= S n ->
  node_pair_value_action k (cn_mu_r H A body nm child) fs
    (global_node_cast (cn_mu_r H A body nm child) payload rho).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn.
  apply node_pair_value_action_intro.
  unfold cast_pair_full_action, cast_pair_value_action. split.
  - split.
    + exact (mu_r_forward_action n k H A body nm child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
    + exact (mu_r_reverse_action n k H A body nm child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
  - split.
    + exact (mu_r_forward_recovery_action n k H A body nm child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
    + exact (mu_r_reverse_recovery_action n k H A body nm child fs payload rho
        VH VA VB Hpayload Htyrho Hbundle Hrho Hkn).
Qed.

Lemma generated_node_pair_action n k H A B (node : CastNode H A B)
  (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
  CastTermsTyping empty ((A, B) :: H) rho ->
  node_bundle_action n node fs payload ->
  cast_terms_action n (frames_cons node fs) rho ->
  k <= S n ->
  node_pair_value_action k node fs (global_node_cast node payload rho).
Proof.
  destruct node as
    [H|H|H x
    |H A1 A2 B1 B2 dom cod
    |H A1 A2 B1 B2 fstc sndc
    |H A1 A2 B1 B2 lc rc
    |H body B child
    |H A body nm child];
    intros VH VA VB Hpayload Htyrho Hbundle Hrho Hkn.
  - now apply unit_node_pair_action.
  - now apply bool_node_pair_action.
  - now apply var_node_pair_action.
  - apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    eapply arr_node_pair_action; eauto.
  - apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    eapply prod_node_pair_action; eauto.
  - apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    eapply sum_node_pair_action; eauto.
  - eapply mu_l_node_pair_action; eauto.
  - eapply mu_r_node_pair_action; eauto.
Qed.

Lemma forward_value_action_antired n {A B} (foc : Focus A B) up up' :
  BIE.evalStar up up' ->
  forward_value_action n foc up' ->
  forward_value_action n foc up.
Proof.
  intros Heval Hact m Hmn vi ve Hvi Hve Hrel.
  destruct (Hact m Hmn vi ve Hvi Hve Hrel)
    as (vo & Hvo & Happ & Hout).
  exists vo. repeat split; try assumption.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.papp₁ BI.phole vi) I Heval).
  - exact Happ.
Qed.

Lemma reverse_value_action_antired n {A B} (foc : Focus A B) down down' :
  BIE.evalStar down down' ->
  reverse_value_action n foc down' ->
  reverse_value_action n foc down.
Proof.
  intros Heval Hact m Hmn vi ve Hvi Hve Hrel.
  destruct (Hact m Hmn vi ve Hvi Hve Hrel)
    as (vo & Hvo & Happ & Hout).
  exists vo. repeat split; try assumption.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.papp₁ BI.phole vi) I Heval).
  - exact Happ.
Qed.

Lemma forward_recovery_action_antired n {A B} (foc : Focus A B) up up' :
  BIE.evalStar up up' ->
  forward_recovery_action n foc up' ->
  forward_recovery_action n foc up.
Proof.
  intros Heval Hact m Hmn vi ve Hvi Hve Hrel.
  destruct (Hact m Hmn vi ve Hvi Hve Hrel)
    as (vo & Hvo & Happ & Hout).
  exists vo. repeat split; try assumption.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.papp₁ BI.phole vi) I Heval).
  - exact Happ.
Qed.

Lemma reverse_recovery_action_antired n {A B} (foc : Focus A B) down down' :
  BIE.evalStar down down' ->
  reverse_recovery_action n foc down' ->
  reverse_recovery_action n foc down.
Proof.
  intros Heval Hact m Hmn vi ve Hvi Hve Hrel.
  destruct (Hact m Hmn vi ve Hvi Hve Hrel)
    as (vo & Hvo & Happ & Hout).
  exists vo. repeat split; try assumption.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.papp₁ BI.phole vi) I Heval).
  - exact Happ.
Qed.

Lemma cast_pair_full_action_antired n {A B} (foc : Focus A B) p p' :
  BIE.evalStar p p' ->
  cast_pair_full_action n foc p' ->
  cast_pair_full_action n foc p.
Proof.
  intros Heval [[Hup Hdown] [Huprec Hdownrec]].
  assert (Hproj1 : BIE.evalStar (BI.proj₁ p) (BI.proj₁ p')).
  { exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.pproj₁ BI.phole) I Heval). }
  assert (Hproj2 : BIE.evalStar (BI.proj₂ p) (BI.proj₂ p')).
  { exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (BI.pproj₂ BI.phole) I Heval). }
  split; [split|split].
  - eapply forward_value_action_antired; [exact Hproj1|exact Hup].
  - eapply reverse_value_action_antired; [exact Hproj2|exact Hdown].
  - eapply forward_recovery_action_antired; [exact Hproj1|exact Huprec].
  - eapply reverse_recovery_action_antired; [exact Hproj2|exact Hdownrec].
Qed.

Lemma node_pair_value_action_antired n {H A B}
  (node : CastNode H A B) fs p p' :
  BIE.evalStar p p' ->
  node_pair_value_action n node fs p' ->
  node_pair_value_action n node fs p.
Proof.
  intros Heval [Hstep Hback]. split;
    eapply cast_pair_full_action_antired; eauto.
Qed.

Lemma bundle_action_antired_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall n fs self self',
      BIE.evalStar self self' ->
      certificate_bundle_action n d fs self' ->
      certificate_bundle_action n d fs self)
  (forall H A B (node : CastNode H A B),
    forall n fs payload payload',
      BIE.evalStar payload payload' ->
      node_bundle_action n node fs payload' ->
      node_bundle_action n node fs payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH n fs self self' Heval [Hroot Hpayload].
    split.
    + eapply node_pair_value_action_antired; [|exact Hroot].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IH; [|exact Hpayload].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr n fs payload payload'
      Heval [Hl Hr]. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr n fs payload payload'
      Heval [Hl Hr]. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr n fs payload payload'
      Heval [Hl Hr]. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros H body B child IH n fs payload payload' Heval Hchild.
    exact (IH n _ _ _ Heval Hchild).
  - intros H A body nm child IH n fs payload payload' Heval Hchild.
    exact (IH n _ _ _ Heval Hchild).
Qed.

Lemma certificate_bundle_action_antired n {H A B} (d : CastEq H A B)
  fs self self' :
  BIE.evalStar self self' ->
  certificate_bundle_action n d fs self' ->
  certificate_bundle_action n d fs self.
Proof.
  exact ((proj1 bundle_action_antired_mut) H A B d n fs self self').
Qed.

Lemma node_bundle_action_antired n {H A B} (node : CastNode H A B)
  fs payload payload' :
  BIE.evalStar payload payload' ->
  node_bundle_action n node fs payload' ->
  node_bundle_action n node fs payload.
Proof.
  exact ((proj2 bundle_action_antired_mut) H A B node
    n fs payload payload').
Qed.

Lemma build_bundle_action_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall n k fs self rho,
      PairEnvValid H -> ValidTy A -> ValidTy B ->
      StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
      CastTermsTyping empty H rho ->
      certificate_bundle_action n d fs self ->
      cast_terms_action n fs rho ->
      k <= S n ->
      certificate_bundle_action k d fs
        (build_certificate_bundle d self rho))
  (forall H A B (node : CastNode H A B),
    forall n k fs payload rho,
      PairEnvValid H -> ValidTy A -> ValidTy B ->
      StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
      CastTermsTyping empty ((A, B) :: H) rho ->
      node_bundle_action n node fs payload ->
      cast_terms_action n (frames_cons node fs) rho ->
      k <= S n ->
      node_bundle_action k node fs (build_node_bundle node payload rho)).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH n k fs self rho VH VA VB Hself Htyrho
      [Hroot Hpayload] Hrho Hkn.
    cbn.
    assert (Hrootty : StlcIso.SpecTyping.Typing empty
      (BI.proj₁ self) (cast_pair_ty A B)).
    { eapply StlcIso.SpecTyping.WtProj1. exact Hself. }
    assert (Hpayloadty : StlcIso.SpecTyping.Typing empty
      (BI.proj₂ self) (node_bundle_ty node)).
    { eapply StlcIso.SpecTyping.WtProj2. exact Hself. }
    assert (Htyrho' : CastTermsTyping empty ((A, B) :: H)
      (cast_terms_cons (BI.proj₁ self) rho)).
    { now apply cast_terms_typing_cons. }
    assert (Hrho' : cast_terms_action n (frames_cons node fs)
      (cast_terms_cons (BI.proj₁ self) rho)).
    { now apply cast_terms_action_cons. }
    pose proof (generated_node_pair_action n k H A B node fs
      (BI.proj₂ self) (cast_terms_cons (BI.proj₁ self) rho)
      VH VA VB Hpayloadty Htyrho' Hpayload Hrho' Hkn) as Hglobal.
    pose proof (IH n k fs (BI.proj₂ self)
      (cast_terms_cons (BI.proj₁ self) rho)
      VH VA VB Hpayloadty Htyrho' Hpayload Hrho' Hkn) as Hbuilt.
    assert (Hglobalv : BIE.Value
      (global_node_cast node (BI.proj₂ self)
        (cast_terms_cons (BI.proj₁ self) rho)))
      by apply global_node_cast_value.
    assert (Hbuiltv : BIE.Value
      (build_node_bundle node (BI.proj₂ self)
        (cast_terms_cons (BI.proj₁ self) rho)))
      by apply build_node_bundle_value.
    split.
    + eapply node_pair_value_action_antired; [|exact Hglobal].
      apply evalToStar, BIE.eval_eval₀.
      now apply BIE.eval_proj₁.
    + eapply node_bundle_action_antired; [|exact Hbuilt].
      apply evalToStar, BIE.eval_eval₀.
      now apply BIE.eval_proj₂.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr n k fs payload rho
      VH VA VB Hpayload Htyrho [Hl Hr] Hrho Hkn.
    apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H)).
    { apply pair_env_valid_cons; [now apply ValidTy_arr|now apply ValidTy_arr|exact VH]. }
    assert (Hleft := IHl n k
      (frames_cons (cn_arr H A1 A2 B1 B2 l r) fs)
      (BI.proj₁ payload) rho VH' VA1 VB1 ltac:(eapply StlcIso.SpecTyping.WtProj1; exact Hpayload)
      Htyrho Hl Hrho Hkn).
    assert (Hright := IHr n k
      (frames_cons (cn_arr H A1 A2 B1 B2 l r) fs)
      (BI.proj₂ payload) rho VH' VA2 VB2 ltac:(eapply StlcIso.SpecTyping.WtProj2; exact Hpayload)
      Htyrho Hr Hrho Hkn).
    cbn. split.
    + eapply certificate_bundle_action_antired; [|exact Hleft].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_action_antired; [|exact Hright].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr n k fs payload rho
      VH VA VB Hpayload Htyrho [Hl Hr] Hrho Hkn.
    apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H)).
    { apply pair_env_valid_cons; [now apply ValidTy_prod|now apply ValidTy_prod|exact VH]. }
    assert (Hleft := IHl n k
      (frames_cons (cn_prod H A1 A2 B1 B2 l r) fs)
      (BI.proj₁ payload) rho VH' VA1 VB1 ltac:(eapply StlcIso.SpecTyping.WtProj1; exact Hpayload)
      Htyrho Hl Hrho Hkn).
    assert (Hright := IHr n k
      (frames_cons (cn_prod H A1 A2 B1 B2 l r) fs)
      (BI.proj₂ payload) rho VH' VA2 VB2 ltac:(eapply StlcIso.SpecTyping.WtProj2; exact Hpayload)
      Htyrho Hr Hrho Hkn).
    cbn. split.
    + eapply certificate_bundle_action_antired; [|exact Hleft].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_action_antired; [|exact Hright].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr n k fs payload rho
      VH VA VB Hpayload Htyrho [Hl Hr] Hrho Hkn.
    apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H)).
    { apply pair_env_valid_cons; [now apply ValidTy_sum|now apply ValidTy_sum|exact VH]. }
    assert (Hleft := IHl n k
      (frames_cons (cn_sum H A1 A2 B1 B2 l r) fs)
      (BI.proj₁ payload) rho VH' VA1 VB1 ltac:(eapply StlcIso.SpecTyping.WtProj1; exact Hpayload)
      Htyrho Hl Hrho Hkn).
    assert (Hright := IHr n k
      (frames_cons (cn_sum H A1 A2 B1 B2 l r) fs)
      (BI.proj₂ payload) rho VH' VA2 VB2 ltac:(eapply StlcIso.SpecTyping.WtProj2; exact Hpayload)
      Htyrho Hr Hrho Hkn).
    cbn. split.
    + eapply certificate_bundle_action_antired; [|exact Hleft].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_action_antired; [|exact Hright].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H body B child IH n k fs payload rho VH VA VB
      Hpayload Htyrho Hchild Hrho Hkn.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((trec body, B) :: H))
      by now apply pair_env_valid_cons.
    cbn in Hpayload |- *. eapply IH; eauto.
  - intros H A body nm child IH n k fs payload rho VH VA VB
      Hpayload Htyrho Hchild Hrho Hkn.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((A, trec body) :: H))
      by now apply pair_env_valid_cons.
    cbn in Hpayload |- *. eapply IH; eauto.
Qed.

Lemma build_certificate_bundle_action n H A B (d : CastEq H A B)
  fs self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
  CastTermsTyping empty H rho ->
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  certificate_bundle_action n d fs (build_certificate_bundle d self rho).
Proof.
  intros VH VA VB Hself Htyrho Hbundle Hrho.
  eapply ((proj1 build_bundle_action_mut) H A B d n n fs self rho);
    eauto; lia.
Qed.

Lemma build_certificate_bundle_action_guarded n H A B (d : CastEq H A B)
  fs self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
  CastTermsTyping empty H rho ->
  certificate_bundle_action n d fs self ->
  cast_terms_action n fs rho ->
  certificate_bundle_action (S n) d fs
    (build_certificate_bundle d self rho).
Proof.
  intros VH VA VB Hself Htyrho Hbundle Hrho.
  eapply ((proj1 build_bundle_action_mut) H A B d n (S n)
    fs self rho); eauto.
Qed.

Lemma build_node_bundle_action n H A B (node : CastNode H A B)
  fs payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
  CastTermsTyping empty ((A, B) :: H) rho ->
  node_bundle_action n node fs payload ->
  cast_terms_action n (frames_cons node fs) rho ->
  node_bundle_action n node fs (build_node_bundle node payload rho).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho.
  eapply ((proj2 build_bundle_action_mut) H A B node n n
    fs payload rho); eauto; lia.
Qed.

Lemma build_node_bundle_action_guarded n H A B (node : CastNode H A B)
  fs payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
  CastTermsTyping empty ((A, B) :: H) rho ->
  node_bundle_action n node fs payload ->
  cast_terms_action n (frames_cons node fs) rho ->
  node_bundle_action (S n) node fs (build_node_bundle node payload rho).
Proof.
  intros VH VA VB Hpayload Htyrho Hbundle Hrho.
  eapply ((proj2 build_bundle_action_mut) H A B node n (S n)
    fs payload rho); eauto.
Qed.

(** World zero of the heterogeneous value relations records only endpoint
    typing, but the action predicates intentionally still record CBV
    termination.  This lemma isolates that operational base obligation from
    all higher-world structural reasoning. *)
Definition cast_pair_application_terminates (A B : Ty) (p : BI.Tm) : Prop :=
  (forall vi,
    BIE.Value vi ->
    StlcIso.SpecTyping.Typing empty vi A ->
    BIE.Terminating (BI.app (BI.proj₁ p) vi))
  /\
  (forall vi,
    BIE.Value vi ->
    StlcIso.SpecTyping.Typing empty vi B ->
    BIE.Terminating (BI.app (BI.proj₂ p) vi)).

Lemma cast_pair_application_terminates_action_zero {A B}
  (foc : Focus A B) p :
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  cast_pair_application_terminates A B p ->
  cast_pair_full_action 0 foc p.
Proof.
  intros Hp [Hupterm Hdownterm].
  assert (Hup : StlcIso.SpecTyping.Typing empty
    (BI.proj₁ p) (tarr A B)).
  { eapply StlcIso.SpecTyping.WtProj1. exact Hp. }
  assert (Hdown : StlcIso.SpecTyping.Typing empty
    (BI.proj₂ p) (tarr B A)).
  { eapply StlcIso.SpecTyping.WtProj2. exact Hp. }
  unfold cast_pair_full_action, cast_pair_value_action.
  split; [split|split].
  - intros m Hm vi ve Hvi Hve Hrel.
    assert (m = 0) by lia. subst m. cbn in Hrel |- *.
    destruct (Hupterm vi Hvi (proj1 Hrel)) as (vo & Hvo & Heval).
    exists vo. repeat split; try assumption.
    + assert (Happ : StlcIso.SpecTyping.Typing empty
        (BI.app (BI.proj₁ p) vi) B)
        by (eapply StlcIso.SpecTyping.WtApp;
            [exact Hup|exact (proj1 Hrel)]).
      pose proof (StlcIso.TypeSafety.preservation_star Heval
        ValidEnv_nil Happ) as HvoTy.
      exact HvoTy.
    + exact (proj2 Hrel).
  - intros m Hm vi ve Hvi Hve Hrel.
    assert (m = 0) by lia. subst m. cbn in Hrel |- *.
    destruct (Hdownterm vi Hvi (proj1 Hrel)) as (vo & Hvo & Heval).
    exists vo. repeat split; try assumption.
    + assert (Happ : StlcIso.SpecTyping.Typing empty
        (BI.app (BI.proj₂ p) vi) A)
        by (eapply StlcIso.SpecTyping.WtApp;
            [exact Hdown|exact (proj1 Hrel)]).
      pose proof (StlcIso.TypeSafety.preservation_star Heval
        ValidEnv_nil Happ) as HvoTy.
      exact HvoTy.
    + exact (proj2 Hrel).
  - intros m Hm vi ve Hvi Hve Hrel.
    assert (m = 0) by lia. subst m. cbn in Hrel |- *.
    destruct (Hupterm vi Hvi (proj1 Hrel)) as (vo & Hvo & Heval).
    exists vo. repeat split; try assumption.
    + assert (Happ : StlcIso.SpecTyping.Typing empty
        (BI.app (BI.proj₁ p) vi) B)
        by (eapply StlcIso.SpecTyping.WtApp;
            [exact Hup|exact (proj1 Hrel)]).
      pose proof (StlcIso.TypeSafety.preservation_star Heval
        ValidEnv_nil Happ) as HvoTy.
      exact HvoTy.
    + exact (proj2 Hrel).
  - intros m Hm vi ve Hvi Hve Hrel.
    assert (m = 0) by lia. subst m. cbn in Hrel |- *.
    destruct (Hdownterm vi Hvi (proj1 Hrel)) as (vo & Hvo & Heval).
    exists vo. repeat split; try assumption.
    + assert (Happ : StlcIso.SpecTyping.Typing empty
        (BI.app (BI.proj₂ p) vi) A)
        by (eapply StlcIso.SpecTyping.WtApp;
            [exact Hdown|exact (proj1 Hrel)]).
      pose proof (StlcIso.TypeSafety.preservation_star Heval
        ValidEnv_nil Happ) as HvoTy.
      exact HvoTy.
    + exact (proj2 Hrel).
Qed.

Fixpoint certificate_bundle_application_terminates {H A B}
  (d : CastEq H A B) (self : BI.Tm) : Prop :=
  match d in CastEq H0 A0 B0 return BI.Tm -> Prop with
  | ce_back _ => fun _ => True
  | @ce_step H0 A0 B0 node => fun self0 =>
      cast_pair_application_terminates A0 B0 (BI.proj₁ self0)
      /\ node_bundle_application_terminates node (BI.proj₂ self0)
  end self
with node_bundle_application_terminates {H A B}
  (node : CastNode H A B) (payload : BI.Tm) : Prop :=
  match node in CastNode H0 A0 B0 return BI.Tm -> Prop with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ => True
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => fun payload0 =>
      certificate_bundle_application_terminates l (BI.proj₁ payload0)
      /\ certificate_bundle_application_terminates r (BI.proj₂ payload0)
  | cn_mu_l _ _ _ child => fun payload0 =>
      certificate_bundle_application_terminates child payload0
  | cn_mu_r _ _ _ _ child => fun payload0 =>
      certificate_bundle_application_terminates child payload0
  end payload.

Lemma bundle_application_termination_action_zero_mut :
  and
  (forall H A B (d : CastEq H A B), forall fs self,
    PairEnvValid H -> ValidTy A -> ValidTy B ->
    StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
    certificate_bundle_application_terminates d self ->
    certificate_bundle_action 0 d fs self)
  (forall H A B (node : CastNode H A B), forall fs payload,
    PairEnvValid H -> ValidTy A -> ValidTy B ->
    StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
    node_bundle_application_terminates node payload ->
    node_bundle_action 0 node fs payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH fs self VH VA VB Hself [Hroot Hpayload].
    assert (Hrootty : StlcIso.SpecTyping.Typing empty
      (BI.proj₁ self) (cast_pair_ty A B))
      by (eapply StlcIso.SpecTyping.WtProj1; exact Hself).
    assert (Hpayloadty : StlcIso.SpecTyping.Typing empty
      (BI.proj₂ self) (node_bundle_ty node))
      by (eapply StlcIso.SpecTyping.WtProj2; exact Hself).
    cbn. split.
    + split; eapply cast_pair_application_terminates_action_zero;
        eauto.
    + eapply IH; eauto.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr fs payload VH VA VB
      Hpayload [Hl Hr].
    apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H)).
    { apply pair_env_valid_cons;
        [now apply ValidTy_arr|now apply ValidTy_arr|exact VH]. }
    cbn. split.
    + eapply IHl; eauto. eapply StlcIso.SpecTyping.WtProj1; exact Hpayload.
    + eapply IHr; eauto. eapply StlcIso.SpecTyping.WtProj2; exact Hpayload.
  - intros H A1 A2 B1 B2 l IHl r IHr fs payload VH VA VB
      Hpayload [Hl Hr].
    apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H)).
    { apply pair_env_valid_cons;
        [now apply ValidTy_prod|now apply ValidTy_prod|exact VH]. }
    cbn. split.
    + eapply IHl; eauto. eapply StlcIso.SpecTyping.WtProj1; exact Hpayload.
    + eapply IHr; eauto. eapply StlcIso.SpecTyping.WtProj2; exact Hpayload.
  - intros H A1 A2 B1 B2 l IHl r IHr fs payload VH VA VB
      Hpayload [Hl Hr].
    apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H)).
    { apply pair_env_valid_cons;
        [now apply ValidTy_sum|now apply ValidTy_sum|exact VH]. }
    cbn. split.
    + eapply IHl; eauto. eapply StlcIso.SpecTyping.WtProj1; exact Hpayload.
    + eapply IHr; eauto. eapply StlcIso.SpecTyping.WtProj2; exact Hpayload.
  - intros H body B child IH fs payload VH VA VB Hpayload Hterm.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((trec body, B) :: H))
      by now apply pair_env_valid_cons.
    cbn. eapply IH; eauto.
  - intros H A body nm child IH fs payload VH VA VB Hpayload Hterm.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((A, trec body) :: H))
      by now apply pair_env_valid_cons.
    cbn. eapply IH; eauto.
Qed.

Lemma certificate_bundle_application_termination_action_zero
  {H A B} (d : CastEq H A B) fs self :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
  certificate_bundle_application_terminates d self ->
  certificate_bundle_action 0 d fs self.
Proof.
  exact ((proj1 bundle_application_termination_action_zero_mut)
    H A B d fs self).
Qed.

Theorem recursive_certificate_bundle_action_all_worlds
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  certificate_bundle_application_terminates d
    (recursive_certificate_bundle d) ->
  forall n,
    certificate_bundle_action n d frames_nil
      (recursive_certificate_bundle d).
Proof.
  intros VA VB Hterminates n. induction n as [|n IH].
  - eapply certificate_bundle_application_termination_action_zero.
    + apply pair_env_valid_nil.
    + exact VA.
    + exact VB.
    + now apply recursive_certificate_bundle_typing.
    + exact Hterminates.
  - assert (Hdelayed : certificate_bundle_action n d frames_nil
      (delayed_recursive_certificate_bundle d)).
    { eapply certificate_bundle_action_antired; [|exact IH].
      apply evalToStar. now apply delayed_recursive_certificate_bundle_step. }
    assert (Hbuild : certificate_bundle_action (S n) d frames_nil
      (build_certificate_bundle d
        (delayed_recursive_certificate_bundle d) cast_terms_nil)).
    { eapply build_certificate_bundle_action_guarded.
      - apply pair_env_valid_nil.
      - exact VA.
      - exact VB.
      - now apply delayed_recursive_certificate_bundle_typing.
      - apply cast_terms_typing_nil.
      - exact Hdelayed.
      - apply cast_terms_action_nil. }
    eapply certificate_bundle_action_antired; [|exact Hbuild].
    now apply recursive_certificate_bundle_unfolds.
Qed.

Theorem tied_certificate_bundle_action_all_worlds
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  certificate_bundle_application_terminates d
    (recursive_certificate_bundle d) ->
  forall n,
    certificate_bundle_action n d frames_nil
      (tied_certificate_bundle d).
Proof.
  intros VA VB Hterminates n.
  eapply certificate_bundle_action_antired.
  - apply evalToStar. apply tied_certificate_bundle_step.
  - now apply recursive_certificate_bundle_action_all_worlds.
Qed.

Corollary compile_global_pair_action_all_worlds
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  certificate_bundle_application_terminates d
    (recursive_certificate_bundle d) ->
  forall n,
    cast_pair_full_action n (focus d frames_nil) (compile_global_pair d).
Proof.
  intros VA VB Hterminates n. unfold compile_global_pair.
  eapply certificate_root_action.
  - now apply tied_certificate_bundle_action_all_worlds.
  - apply cast_terms_action_nil.
Qed.

(** A numerical potential for the operational termination proof.  The value
    size is the primary component; the sum of leading-mu counts is the
    secondary component.  [certificate_lmc_bound] supplies one finite radix
    large enough for every cell and backedge in the certificate. *)
Fixpoint certificate_lmc_bound {H A B} (d : CastEq H A B) : nat :=
  Nat.max (LMC A + LMC B)
    (match d with
     | ce_back _ => 0
     | ce_step node => node_lmc_bound node
     end)
with node_lmc_bound {H A B} (node : CastNode H A B) : nat :=
  match node with
  | cn_unit _ | cn_bool _ | cn_var _ _ => 0
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r =>
      Nat.max (certificate_lmc_bound l) (certificate_lmc_bound r)
  | cn_mu_l _ _ _ child => certificate_lmc_bound child
  | cn_mu_r _ _ _ _ child => certificate_lmc_bound child
  end.

Definition cast_application_measure (radix : nat) (A B : Ty)
  (vi : BI.Tm) : nat :=
  StlcIso.Size.size vi * radix + LMC A + LMC B.

Definition cast_pair_terminates_below (radix budget : nat)
  (A B : Ty) (p : BI.Tm) : Prop :=
  (forall vi,
    BIE.Value vi ->
    StlcIso.SpecTyping.Typing empty vi A ->
    cast_application_measure radix A B vi < budget ->
    BIE.Terminating (BI.app (BI.proj₁ p) vi))
  /\
  (forall vi,
    BIE.Value vi ->
    StlcIso.SpecTyping.Typing empty vi B ->
    cast_application_measure radix A B vi < budget ->
    BIE.Terminating (BI.app (BI.proj₂ p) vi)).

Fixpoint certificate_bundle_terminates_below radix budget {H A B}
  (d : CastEq H A B) (self : BI.Tm) : Prop :=
  match d in CastEq H0 A0 B0 return BI.Tm -> Prop with
  | ce_back _ => fun _ => True
  | @ce_step H0 A0 B0 node => fun self0 =>
      cast_pair_terminates_below radix budget A0 B0 (BI.proj₁ self0)
      /\ node_bundle_terminates_below radix budget node (BI.proj₂ self0)
  end self
with node_bundle_terminates_below radix budget {H A B}
  (node : CastNode H A B) (payload : BI.Tm) : Prop :=
  match node in CastNode H0 A0 B0 return BI.Tm -> Prop with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ => True
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => fun payload0 =>
      certificate_bundle_terminates_below radix budget l
        (BI.proj₁ payload0)
      /\ certificate_bundle_terminates_below radix budget r
        (BI.proj₂ payload0)
  | cn_mu_l _ _ _ child => fun payload0 =>
      certificate_bundle_terminates_below radix budget child payload0
  | cn_mu_r _ _ _ _ child => fun payload0 =>
      certificate_bundle_terminates_below radix budget child payload0
  end payload.

Fixpoint cast_terms_terminate_below radix budget {H} :
    CastTerms H -> Prop :=
  match H return CastTerms H -> Prop with
  | nil => fun _ => True
  | (A, B) :: tail => fun rho =>
      cast_pair_terminates_below radix budget A B (fst rho)
      /\ cast_terms_terminate_below radix budget (snd rho)
  end.

Lemma cast_pair_terminates_below_zero radix A B p :
  cast_pair_terminates_below radix 0 A B p.
Proof. split; intros vi Hvi Hty Hlt; exfalso; lia. Qed.

Lemma bundle_terminates_below_zero_mut radix :
  and
  (forall H A B (d : CastEq H A B), forall self,
    certificate_bundle_terminates_below radix 0 d self)
  (forall H A B (node : CastNode H A B), forall payload,
    node_bundle_terminates_below radix 0 node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH self. cbn. split.
    + apply cast_pair_terminates_below_zero.
    + apply IH.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr payload. cbn.
    split; [apply IHl|apply IHr].
  - intros H A1 A2 B1 B2 l IHl r IHr payload. cbn.
    split; [apply IHl|apply IHr].
  - intros H A1 A2 B1 B2 l IHl r IHr payload. cbn.
    split; [apply IHl|apply IHr].
  - intros H body B child IH payload. cbn. apply IH.
  - intros H A body nm child IH payload. cbn. apply IH.
Qed.

Lemma certificate_bundle_terminates_below_zero radix {H A B}
  (d : CastEq H A B) self :
  certificate_bundle_terminates_below radix 0 d self.
Proof.
  exact ((proj1 (bundle_terminates_below_zero_mut radix)) H A B d self).
Qed.

Lemma cast_terms_terminate_below_zero radix {H} (rho : CastTerms H) :
  cast_terms_terminate_below radix 0 rho.
Proof.
  induction H as [|[A B] H IH]; cbn in *.
  - exact I.
  - split; [apply cast_pair_terminates_below_zero|exact (IH (snd rho))].
Qed.

Lemma endpoint_lmc_bounded_by_certificate {H A B}
  (d : CastEq H A B) :
  LMC A + LMC B <= certificate_lmc_bound d.
Proof.
  destruct d; cbn [certificate_lmc_bound];
    apply PeanoNat.Nat.le_max_l.
Qed.

Lemma cast_terms_terminate_below_lookup radix budget {H A B}
  (m : Assumed H A B) rho :
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix budget A B (lookup_cast m rho).
Proof.
  revert rho. induction m; intros rho Hrho; cbn in *.
  - exact (proj1 Hrho).
  - now apply IHm, Hrho.
Qed.

Lemma cast_terms_terminate_below_cons radix budget {H A B}
  p (rho : CastTerms H) :
  cast_pair_terminates_below radix budget A B p ->
  cast_terms_terminate_below radix budget rho ->
  cast_terms_terminate_below radix budget
    (@cast_terms_cons H A B p rho).
Proof.
  intros Hp Hrho. now split.
Qed.

Lemma certificate_root_terminates_below radix budget {H A B}
  (d : CastEq H A B) self rho :
  certificate_bundle_terminates_below radix budget d self ->
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix budget A B
    (certificate_root d self rho).
Proof.
  destruct d; cbn; intros Hself Hrho.
  - now apply cast_terms_terminate_below_lookup.
  - exact (proj1 Hself).
Qed.

Lemma cast_pair_terminates_below_antired radix budget A B p p' :
  BIE.evalStar p p' ->
  cast_pair_terminates_below radix budget A B p' ->
  cast_pair_terminates_below radix budget A B p.
Proof.
  intros Heval [Hup Hdown]. split; intros vi Hvi Hty Hmeasure.
  - eapply StlcIso.LemmasEvaluation.termination_closed_under_antireductionStar.
    + exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.papp₁ BI.phole vi) I
        (StlcIso.LemmasEvaluation.evalstar_ctx
          (BI.pproj₁ BI.phole) I Heval)).
    + exact (Hup vi Hvi Hty Hmeasure).
  - eapply StlcIso.LemmasEvaluation.termination_closed_under_antireductionStar.
    + exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.papp₁ BI.phole vi) I
        (StlcIso.LemmasEvaluation.evalstar_ctx
          (BI.pproj₂ BI.phole) I Heval)).
    + exact (Hdown vi Hvi Hty Hmeasure).
Qed.

Lemma bundle_terminates_below_antired_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall radix budget self self',
      BIE.evalStar self self' ->
      certificate_bundle_terminates_below radix budget d self' ->
      certificate_bundle_terminates_below radix budget d self)
  (forall H A B (node : CastNode H A B),
    forall radix budget payload payload',
      BIE.evalStar payload payload' ->
      node_bundle_terminates_below radix budget node payload' ->
      node_bundle_terminates_below radix budget node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH radix budget self self' Heval
      [Hroot Hpayload]. cbn. split.
    + eapply cast_pair_terminates_below_antired; [|exact Hroot].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IH; [|exact Hpayload].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget
      payload payload' Heval [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget
      payload payload' Heval [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget
      payload payload' Heval [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₁ BI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (BI.pproj₂ BI.phole) I Heval).
  - intros H body B child IH radix budget payload payload' Heval Hterm.
    cbn. eapply IH; eauto.
  - intros H A body nm child IH radix budget payload payload' Heval Hterm.
    cbn. eapply IH; eauto.
Qed.

Lemma certificate_bundle_terminates_below_antired radix budget
  {H A B} (d : CastEq H A B) self self' :
  BIE.evalStar self self' ->
  certificate_bundle_terminates_below radix budget d self' ->
  certificate_bundle_terminates_below radix budget d self.
Proof.
  exact ((proj1 bundle_terminates_below_antired_mut)
    H A B d radix budget self self').
Qed.

Lemma node_bundle_terminates_below_antired radix budget
  {H A B} (node : CastNode H A B) payload payload' :
  BIE.evalStar payload payload' ->
  node_bundle_terminates_below radix budget node payload' ->
  node_bundle_terminates_below radix budget node payload.
Proof.
  exact ((proj2 bundle_terminates_below_antired_mut)
    H A B node radix budget payload payload').
Qed.

Lemma cast_measure_smaller_value radix budget A B A' B' vi vi' :
  LMC A' + LMC B' < radix ->
  StlcIso.Size.size vi' < StlcIso.Size.size vi ->
  cast_application_measure radix A B vi < S budget ->
  cast_application_measure radix A' B' vi' < budget.
Proof. unfold cast_application_measure. nia. Qed.

Lemma cast_measure_smaller_lmc radix budget A B A' B' vi :
  LMC A' + LMC B' < LMC A + LMC B ->
  cast_application_measure radix A B vi < S budget ->
  cast_application_measure radix A' B' vi < budget.
Proof. unfold cast_application_measure. lia. Qed.

Lemma LMC_unfold_trec_lt body :
  SimpleContr (trec body) ->
  LMC body[beta1 (trec body)] < LMC (trec body).
Proof.
  intros Hcontr.
  change (LMC (unfoldOnce (trec body)) < LMC (trec body)).
  rewrite LMC_unfoldOnce; [cbn; lia|exact Hcontr|cbn; lia].
Qed.

Lemma identity_pair_terminates_below radix budget T :
  cast_pair_terminates_below radix budget T T
    (BI.pair (id_cast T) (id_cast T)).
Proof.
  split.
  - intros vi Hvi Hty Hmeasure. exists vi. split; [exact Hvi|].
    change (BIE.evalStar
      (BI.app (BI.proj₁
        (BI.pair (BI.abs T (BI.var 0)) (BI.abs T (BI.var 0)))) vi)
      (BI.apTm (beta1 vi) (BI.var 0))).
    eapply pair_first_abs_app_eval; [exact I|exact Hvi].
  - intros vi Hvi Hty Hmeasure. exists vi. split; [exact Hvi|].
    change (BIE.evalStar
      (BI.app (BI.proj₂
        (BI.pair (BI.abs T (BI.var 0)) (BI.abs T (BI.var 0)))) vi)
      (BI.apTm (beta1 vi) (BI.var 0))).
    eapply pair_second_abs_app_eval; [exact I|exact Hvi].
Qed.

Lemma arrow_node_pair_terminates_below radix budget H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  payload rho :
  cast_pair_terminates_below radix budget (tarr A1 A2) (tarr B1 B2)
    (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho).
Proof.
  split; intros vf Hvf Hty Hmeasure.
  - cbn [global_node_cast].
    lazymatch goal with
    | |- BIE.Terminating
        (BI.app (BI.proj₁ (BI.pair (BI.abs ?T ?body) ?other)) vf) =>
        exists (BI.apTm (beta1 vf) body)
    end.
    split; [exact I|].
    eapply pair_first_abs_app_eval; [exact I|exact Hvf].
  - cbn [global_node_cast].
    lazymatch goal with
    | |- BIE.Terminating
        (BI.app (BI.proj₂ (BI.pair ?other (BI.abs ?T ?body))) vf) =>
        exists (BI.apTm (beta1 vf) body)
    end.
    split; [exact I|].
    eapply pair_second_abs_app_eval; [exact I|exact Hvf].
Qed.

Lemma prod_node_pair_terminates_below radix budget H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  payload rho :
  certificate_lmc_bound fstc < radix ->
  certificate_lmc_bound sndc < radix ->
  certificate_bundle_terminates_below radix budget fstc
    (BI.proj₁ payload) ->
  certificate_bundle_terminates_below radix budget sndc
    (BI.proj₂ payload) ->
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix (S budget)
    (tprod A1 A2) (tprod B1 B2)
    (global_node_cast (cn_prod H A1 A2 B1 B2 fstc sndc) payload rho).
Proof.
  intros Hfstbound Hsndbound Hfstbundle Hsndbundle Hrho.
  pose proof (certificate_root_terminates_below
    radix budget fstc (BI.proj₁ payload) rho Hfstbundle Hrho) as Hfstroot.
  pose proof (certificate_root_terminates_below
    radix budget sndc (BI.proj₂ payload) rho Hsndbundle Hrho) as Hsndroot.
  assert (Hfstlmc : LMC A1 + LMC B1 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate fstc). lia. }
  assert (Hsndlmc : LMC A2 + LMC B2 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate sndc). lia. }
  split.
  - intros vi Hvi Hty Hmeasure.
    destruct (StlcIso.CanForm.can_form_tprod Hvi Hty)
      as (vi1 & vi2 & -> & Hty1 & Hty2).
    cbn in Hvi. destruct Hvi as [Hvi1 Hvi2].
    assert (Hm1 : cast_application_measure radix A1 B1 vi1 < budget).
    { eapply cast_measure_smaller_value; eauto. cbn. lia. }
    assert (Hm2 : cast_application_measure radix A2 B2 vi2 < budget).
    { eapply cast_measure_smaller_value; eauto. cbn. lia. }
    destruct (proj1 Hfstroot vi1 Hvi1 Hty1 Hm1)
      as (vo1 & Hvo1 & Heval1).
    destruct (proj1 Hsndroot vi2 Hvi2 Hty2 Hm2)
      as (vo2 & Hvo2 & Heval2).
    exists (BI.pair vo1 vo2). split; [now split|].
    cbn [global_node_cast]. eapply evalStepTrans.
    + eapply pair_first_abs_app_eval; [exact I|now split].
    + cbn.
      assert (Hcancel1 :
        BI.apTm (beta1 (BI.pair vi1 vi2))
          (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
        certificate_root fstc (BI.proj₁ payload) rho)
        by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
      assert (Hcancel2 :
        BI.apTm (beta1 (BI.pair vi1 vi2))
          (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
        certificate_root sndc (BI.proj₂ payload) rho)
        by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
      rewrite Hcancel1, Hcancel2.
      eapply pair_app_projections_eval; eauto.
  - intros vi Hvi Hty Hmeasure.
    destruct (StlcIso.CanForm.can_form_tprod Hvi Hty)
      as (vi1 & vi2 & -> & Hty1 & Hty2).
    cbn in Hvi. destruct Hvi as [Hvi1 Hvi2].
    assert (Hm1 : cast_application_measure radix A1 B1 vi1 < budget).
    { eapply cast_measure_smaller_value; eauto. cbn. lia. }
    assert (Hm2 : cast_application_measure radix A2 B2 vi2 < budget).
    { eapply cast_measure_smaller_value; eauto. cbn. lia. }
    destruct (proj2 Hfstroot vi1 Hvi1 Hty1 Hm1)
      as (vo1 & Hvo1 & Heval1).
    destruct (proj2 Hsndroot vi2 Hvi2 Hty2 Hm2)
      as (vo2 & Hvo2 & Heval2).
    exists (BI.pair vo1 vo2). split; [now split|].
    cbn [global_node_cast]. eapply evalStepTrans.
    + eapply pair_second_abs_app_eval; [exact I|now split].
    + cbn.
      assert (Hcancel1 :
        BI.apTm (beta1 (BI.pair vi1 vi2))
          (BI.apTm wkm (certificate_root fstc (BI.proj₁ payload) rho)) =
        certificate_root fstc (BI.proj₁ payload) rho)
        by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
      assert (Hcancel2 :
        BI.apTm (beta1 (BI.pair vi1 vi2))
          (BI.apTm wkm (certificate_root sndc (BI.proj₂ payload) rho)) =
        certificate_root sndc (BI.proj₂ payload) rho)
        by exact (@apply_wkm_beta1_cancel BI.Tm BI.Tm
          _ _ _ _ _ _ _ (BI.pair vi1 vi2)).
      rewrite Hcancel1, Hcancel2.
      eapply pair_app_projections_eval; eauto.
Qed.

Lemma sum_node_pair_terminates_below radix budget H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  payload rho :
  certificate_lmc_bound lc < radix ->
  certificate_lmc_bound rc < radix ->
  certificate_bundle_terminates_below radix budget lc
    (BI.proj₁ payload) ->
  certificate_bundle_terminates_below radix budget rc
    (BI.proj₂ payload) ->
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix (S budget)
    (tsum A1 A2) (tsum B1 B2)
    (global_node_cast (cn_sum H A1 A2 B1 B2 lc rc) payload rho).
Proof.
  intros Hlbound Hrbound Hlbundle Hrbundle Hrho.
  pose proof (certificate_root_terminates_below
    radix budget lc (BI.proj₁ payload) rho Hlbundle Hrho) as Hlroot.
  pose proof (certificate_root_terminates_below
    radix budget rc (BI.proj₂ payload) rho Hrbundle Hrho) as Hrroot.
  assert (Hllmc : LMC A1 + LMC B1 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate lc). lia. }
  assert (Hrlmc : LMC A2 + LMC B2 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate rc). lia. }
  split.
  - intros vi Hvi Hty Hmeasure.
    destruct (StlcIso.CanForm.can_form_tsum Hvi Hty)
      as [(v & -> & Hvty)|(v & -> & Hvty)]; cbn in Hvi.
    + assert (Hm : cast_application_measure radix A1 B1 v < budget).
      { eapply cast_measure_smaller_value; eauto. cbn. lia. }
      destruct (proj1 Hlroot v Hvi Hvty Hm) as (vo & Hvo & Heval).
      exists (BI.inl vo). split; [exact Hvo|].
      cbn [global_node_cast].
      eapply pair_first_sum_inl_app_eval; eauto; exact I.
    + assert (Hm : cast_application_measure radix A2 B2 v < budget).
      { eapply cast_measure_smaller_value; eauto. cbn. lia. }
      destruct (proj1 Hrroot v Hvi Hvty Hm) as (vo & Hvo & Heval).
      exists (BI.inr vo). split; [exact Hvo|].
      cbn [global_node_cast].
      eapply pair_first_sum_inr_app_eval; eauto; exact I.
  - intros vi Hvi Hty Hmeasure.
    destruct (StlcIso.CanForm.can_form_tsum Hvi Hty)
      as [(v & -> & Hvty)|(v & -> & Hvty)]; cbn in Hvi.
    + assert (Hm : cast_application_measure radix A1 B1 v < budget).
      { eapply cast_measure_smaller_value; eauto. cbn. lia. }
      destruct (proj2 Hlroot v Hvi Hvty Hm) as (vo & Hvo & Heval).
      exists (BI.inl vo). split; [exact Hvo|].
      cbn [global_node_cast].
      eapply pair_second_sum_inl_app_eval; eauto; exact I.
    + assert (Hm : cast_application_measure radix A2 B2 v < budget).
      { eapply cast_measure_smaller_value; eauto. cbn. lia. }
      destruct (proj2 Hrroot v Hvi Hvty Hm) as (vo & Hvo & Heval).
      exists (BI.inr vo). split; [exact Hvo|].
      cbn [global_node_cast].
      eapply pair_second_sum_inr_app_eval; eauto; exact I.
Qed.

Lemma mu_l_node_pair_terminates_below radix budget H body B
  (child : CastEq ((trec body, B) :: H) body[beta1 (trec body)] B)
  payload rho :
  ValidTy (trec body) ->
  certificate_lmc_bound child < radix ->
  certificate_bundle_terminates_below radix budget child payload ->
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix (S budget) (trec body) B
    (global_node_cast (cn_mu_l H body B child) payload rho).
Proof.
  intros VA Hbound Hbundle Hrho.
  pose proof (certificate_root_terminates_below
    radix budget child payload rho Hbundle Hrho) as Hroot.
  assert (Hchildlmc : LMC body[beta1 (trec body)] + LMC B < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate child). lia. }
  assert (Hunfoldlmc :
    LMC body[beta1 (trec body)] + LMC B < LMC (trec body) + LMC B).
  { pose proof (LMC_unfold_trec_lt body (proj2 VA)). lia. }
  split.
  - intros vi Hvi Hty Hmeasure.
    destruct (StlcIso.CanForm.can_form_trec Hvi Hty)
      as (v & -> & Hvty). cbn in Hvi.
    assert (Hm : cast_application_measure radix
      body[beta1 (trec body)] B v < budget).
    { eapply cast_measure_smaller_value; eauto. cbn. lia. }
    destruct (proj1 Hroot v Hvi Hvty Hm) as (vo & Hvo & Heval).
    exists vo. split; [exact Hvo|].
    cbn [global_node_cast]. eapply pair_first_mu_l_app_eval; eauto.
  - intros vi Hvi Hty Hmeasure.
    assert (Hm : cast_application_measure radix
      body[beta1 (trec body)] B vi < budget).
    { eapply cast_measure_smaller_lmc; eauto. }
    destruct (proj2 Hroot vi Hvi Hty Hm) as (vo & Hvo & Heval).
    exists (BI.fold_ vo). split; [exact Hvo|].
    cbn [global_node_cast]. eapply pair_second_mu_l_app_eval; eauto.
Qed.

Lemma mu_r_node_pair_terminates_below radix budget H A body nm
  (child : CastEq ((A, trec body) :: H) A body[beta1 (trec body)])
  payload rho :
  ValidTy (trec body) ->
  certificate_lmc_bound child < radix ->
  certificate_bundle_terminates_below radix budget child payload ->
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix (S budget) A (trec body)
    (global_node_cast (cn_mu_r H A body nm child) payload rho).
Proof.
  intros VB Hbound Hbundle Hrho.
  pose proof (certificate_root_terminates_below
    radix budget child payload rho Hbundle Hrho) as Hroot.
  assert (Hchildlmc : LMC A + LMC body[beta1 (trec body)] < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate child). lia. }
  assert (Hunfoldlmc :
    LMC A + LMC body[beta1 (trec body)] < LMC A + LMC (trec body)).
  { pose proof (LMC_unfold_trec_lt body (proj2 VB)). lia. }
  split.
  - intros vi Hvi Hty Hmeasure.
    assert (Hm : cast_application_measure radix A
      body[beta1 (trec body)] vi < budget).
    { eapply cast_measure_smaller_lmc; eauto. }
    destruct (proj1 Hroot vi Hvi Hty Hm) as (vo & Hvo & Heval).
    exists (BI.fold_ vo). split; [exact Hvo|].
    cbn [global_node_cast]. eapply pair_first_mu_r_app_eval; eauto.
  - intros vi Hvi Hty Hmeasure.
    destruct (StlcIso.CanForm.can_form_trec Hvi Hty)
      as (v & -> & Hvty). cbn in Hvi.
    assert (Hm : cast_application_measure radix A
      body[beta1 (trec body)] v < budget).
    { eapply cast_measure_smaller_value; eauto. cbn. lia. }
    destruct (proj2 Hroot v Hvi Hvty Hm) as (vo & Hvo & Heval).
    exists vo. split; [exact Hvo|].
    cbn [global_node_cast]. eapply pair_second_mu_r_app_eval; eauto.
Qed.

Lemma generated_node_pair_terminates_below radix budget H A B
  (node : CastNode H A B) payload rho :
  ValidTy A -> ValidTy B ->
  node_lmc_bound node < radix ->
  node_bundle_terminates_below radix budget node payload ->
  cast_terms_terminate_below radix budget rho ->
  cast_pair_terminates_below radix (S budget) A B
    (global_node_cast node payload rho).
Proof.
  destruct node as
    [H|H|H x
    |H A1 A2 B1 B2 dom cod
    |H A1 A2 B1 B2 fstc sndc
    |H A1 A2 B1 B2 lc rc
    |H body B child
    |H A body nm child];
    intros VA VB Hbound Hbundle Hrho; cbn in Hbound, Hbundle.
  - apply identity_pair_terminates_below.
  - apply identity_pair_terminates_below.
  - apply identity_pair_terminates_below.
  - apply arrow_node_pair_terminates_below.
  - destruct Hbundle as [Hfst Hsnd].
    eapply prod_node_pair_terminates_below; eauto; lia.
  - destruct Hbundle as [Hl Hr].
    eapply sum_node_pair_terminates_below; eauto; lia.
  - eapply mu_l_node_pair_terminates_below; eauto.
  - eapply mu_r_node_pair_terminates_below; eauto.
Qed.

Lemma build_bundle_terminates_below_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall radix budget self rho,
      PairEnvValid H -> ValidTy A -> ValidTy B ->
      certificate_lmc_bound d < radix ->
      certificate_bundle_terminates_below radix budget d self ->
      cast_terms_terminate_below radix budget rho ->
      certificate_bundle_terminates_below radix (S budget) d
        (build_certificate_bundle d self rho))
  (forall H A B (node : CastNode H A B),
    forall radix budget payload rho,
      PairEnvValid H -> ValidTy A -> ValidTy B ->
      node_lmc_bound node < radix ->
      node_bundle_terminates_below radix budget node payload ->
      cast_terms_terminate_below radix budget rho ->
      node_bundle_terminates_below radix (S budget) node
        (build_node_bundle node payload rho)).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH radix budget self rho VH VA VB Hbound
      [Hroot Hpayload] Hrho.
    assert (Hnodebound : node_lmc_bound node < radix).
    { cbn [certificate_lmc_bound] in Hbound. lia. }
    assert (VH' : PairEnvValid ((A, B) :: H))
      by now apply pair_env_valid_cons.
    assert (Hrho' : cast_terms_terminate_below radix budget
      (@cast_terms_cons H A B (BI.proj₁ self) rho)).
    { now apply cast_terms_terminate_below_cons. }
    pose proof (generated_node_pair_terminates_below
      radix budget H A B node (BI.proj₂ self)
      (@cast_terms_cons H A B (BI.proj₁ self) rho)
      VA VB Hnodebound Hpayload Hrho') as Hglobal.
    pose proof (IH radix budget (BI.proj₂ self)
      (@cast_terms_cons H A B (BI.proj₁ self) rho)
      VH VA VB Hnodebound Hpayload Hrho') as Hbuilt.
    cbn. split.
    + eapply cast_pair_terminates_below_antired; [|exact Hglobal].
      apply evalToStar, BIE.eval_eval₀.
      apply BIE.eval_proj₁;
        [apply global_node_cast_value|apply build_node_bundle_value].
    + eapply node_bundle_terminates_below_antired; [|exact Hbuilt].
      apply evalToStar, BIE.eval_eval₀.
      apply BIE.eval_proj₂;
        [apply global_node_cast_value|apply build_node_bundle_value].
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget payload rho
      VH VA VB Hbound [Hl Hr] Hrho.
    apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H)).
    { apply pair_env_valid_cons;
        [now apply ValidTy_arr|now apply ValidTy_arr|exact VH]. }
    assert (Hlbound : certificate_lmc_bound l < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    assert (Hrbound : certificate_lmc_bound r < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    pose proof (IHl radix budget (BI.proj₁ payload) rho
      VH' VA1 VB1 Hlbound Hl Hrho) as Hleft.
    pose proof (IHr radix budget (BI.proj₂ payload) rho
      VH' VA2 VB2 Hrbound Hr Hrho) as Hright.
    cbn. split.
    + eapply certificate_bundle_terminates_below_antired; [|exact Hleft].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_terminates_below_antired; [|exact Hright].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget payload rho
      VH VA VB Hbound [Hl Hr] Hrho.
    apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H)).
    { apply pair_env_valid_cons;
        [now apply ValidTy_prod|now apply ValidTy_prod|exact VH]. }
    assert (Hlbound : certificate_lmc_bound l < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    assert (Hrbound : certificate_lmc_bound r < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    pose proof (IHl radix budget (BI.proj₁ payload) rho
      VH' VA1 VB1 Hlbound Hl Hrho) as Hleft.
    pose proof (IHr radix budget (BI.proj₂ payload) rho
      VH' VA2 VB2 Hrbound Hr Hrho) as Hright.
    cbn. split.
    + eapply certificate_bundle_terminates_below_antired; [|exact Hleft].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_terminates_below_antired; [|exact Hright].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget payload rho
      VH VA VB Hbound [Hl Hr] Hrho.
    apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H)).
    { apply pair_env_valid_cons;
        [now apply ValidTy_sum|now apply ValidTy_sum|exact VH]. }
    assert (Hlbound : certificate_lmc_bound l < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    assert (Hrbound : certificate_lmc_bound r < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    pose proof (IHl radix budget (BI.proj₁ payload) rho
      VH' VA1 VB1 Hlbound Hl Hrho) as Hleft.
    pose proof (IHr radix budget (BI.proj₂ payload) rho
      VH' VA2 VB2 Hrbound Hr Hrho) as Hright.
    cbn. split.
    + eapply certificate_bundle_terminates_below_antired; [|exact Hleft].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_terminates_below_antired; [|exact Hright].
      apply evalToStar, BIE.eval_eval₀, BIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H body B child IH radix budget payload rho VH VA VB
      Hbound Hterm Hrho.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((trec body, B) :: H))
      by now apply pair_env_valid_cons.
    cbn in Hbound |- *. eapply IH; eauto.
  - intros H A body nm child IH radix budget payload rho VH VA VB
      Hbound Hterm Hrho.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((A, trec body) :: H))
      by now apply pair_env_valid_cons.
    cbn in Hbound |- *. eapply IH; eauto.
Qed.

Lemma build_certificate_bundle_terminates_below radix budget
  {H A B} (d : CastEq H A B) self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  certificate_lmc_bound d < radix ->
  certificate_bundle_terminates_below radix budget d self ->
  cast_terms_terminate_below radix budget rho ->
  certificate_bundle_terminates_below radix (S budget) d
    (build_certificate_bundle d self rho).
Proof.
  exact ((proj1 build_bundle_terminates_below_mut)
    H A B d radix budget self rho).
Qed.

Lemma cast_terms_terminate_below_nil radix budget :
  cast_terms_terminate_below radix budget cast_terms_nil.
Proof. exact I. Qed.

Theorem recursive_certificate_bundle_terminates_below_all
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall budget,
    certificate_bundle_terminates_below
      (S (certificate_lmc_bound d)) budget d
      (recursive_certificate_bundle d).
Proof.
  intros VA VB budget. induction budget as [|budget IH].
  - apply certificate_bundle_terminates_below_zero.
  - assert (Hdelayed : certificate_bundle_terminates_below
      (S (certificate_lmc_bound d)) budget d
      (delayed_recursive_certificate_bundle d)).
    { eapply certificate_bundle_terminates_below_antired; [|exact IH].
      apply evalToStar. now apply delayed_recursive_certificate_bundle_step. }
    assert (Hbuild : certificate_bundle_terminates_below
      (S (certificate_lmc_bound d)) (S budget) d
      (build_certificate_bundle d
        (delayed_recursive_certificate_bundle d) cast_terms_nil)).
    { eapply build_certificate_bundle_terminates_below.
      - apply pair_env_valid_nil.
      - exact VA.
      - exact VB.
      - lia.
      - exact Hdelayed.
      - apply cast_terms_terminate_below_nil. }
    eapply certificate_bundle_terminates_below_antired; [|exact Hbuild].
    now apply recursive_certificate_bundle_unfolds.
Qed.

Lemma bundle_terminates_below_all_implies_application_mut :
  and
  (forall H A B (d : CastEq H A B), forall radix self,
    (forall budget,
      certificate_bundle_terminates_below radix budget d self) ->
    certificate_bundle_application_terminates d self)
  (forall H A B (node : CastNode H A B), forall radix payload,
    (forall budget,
      node_bundle_terminates_below radix budget node payload) ->
    node_bundle_application_terminates node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH radix self Hall. cbn. split.
    + split; intros vi Hvi Hty.
      * specialize (Hall (S (cast_application_measure radix A B vi))).
        exact (proj1 (proj1 Hall) vi Hvi Hty ltac:(lia)).
      * specialize (Hall (S (cast_application_measure radix A B vi))).
        exact (proj2 (proj1 Hall) vi Hvi Hty ltac:(lia)).
    + eapply IH. intros budget. exact (proj2 (Hall budget)).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr radix payload Hall. cbn. split.
    + eapply IHl. intros budget. exact (proj1 (Hall budget)).
    + eapply IHr. intros budget. exact (proj2 (Hall budget)).
  - intros H A1 A2 B1 B2 l IHl r IHr radix payload Hall. cbn. split.
    + eapply IHl. intros budget. exact (proj1 (Hall budget)).
    + eapply IHr. intros budget. exact (proj2 (Hall budget)).
  - intros H A1 A2 B1 B2 l IHl r IHr radix payload Hall. cbn. split.
    + eapply IHl. intros budget. exact (proj1 (Hall budget)).
    + eapply IHr. intros budget. exact (proj2 (Hall budget)).
  - intros H body B child IH radix payload Hall. cbn.
    eapply IH. exact Hall.
  - intros H A body nm child IH radix payload Hall. cbn.
    eapply IH. exact Hall.
Qed.

Theorem recursive_certificate_bundle_application_terminates
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  certificate_bundle_application_terminates d
    (recursive_certificate_bundle d).
Proof.
  intros VA VB.
  eapply ((proj1 bundle_terminates_below_all_implies_application_mut)
    nil A B d (S (certificate_lmc_bound d))
    (recursive_certificate_bundle d)).
  now apply recursive_certificate_bundle_terminates_below_all.
Qed.

Theorem tied_certificate_bundle_action_unconditional
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall n,
    certificate_bundle_action n d frames_nil
      (tied_certificate_bundle d).
Proof.
  intros VA VB n. eapply tied_certificate_bundle_action_all_worlds;
    eauto using recursive_certificate_bundle_application_terminates.
Qed.

Corollary compile_global_pair_action_unconditional
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall n,
    cast_pair_full_action n (focus d frames_nil) (compile_global_pair d).
Proof.
  intros VA VB n. eapply compile_global_pair_action_all_worlds;
    eauto using recursive_certificate_bundle_application_terminates.
Qed.

Corollary compile_global_up_action_unconditional
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B -> forall n,
  forward_value_action n (focus d frames_nil) (compile_global_up d).
Proof.
  intros VA VB n. unfold compile_global_up, pair_up.
  exact (proj1 (proj1
    (compile_global_pair_action_unconditional d VA VB n))).
Qed.

Corollary compile_global_down_action_unconditional
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B -> forall n,
  reverse_value_action n (focus d frames_nil) (compile_global_down d).
Proof.
  intros VA VB n. unfold compile_global_down, pair_down.
  exact (proj2 (proj1
    (compile_global_pair_action_unconditional d VA VB n))).
Qed.

Corollary compile_global_up_recovery_unconditional
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B -> forall n,
  forward_recovery_action n (focus d frames_nil) (compile_global_up d).
Proof.
  intros VA VB n. unfold compile_global_up, pair_up.
  exact (proj1 (proj2
    (compile_global_pair_action_unconditional d VA VB n))).
Qed.

Corollary compile_global_down_recovery_unconditional
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B -> forall n,
  reverse_recovery_action n (focus d frames_nil) (compile_global_down d).
Proof.
  intros VA VB n. unfold compile_global_down, pair_down.
  exact (proj2 (proj2
    (compile_global_pair_action_unconditional d VA VB n))).
Qed.
