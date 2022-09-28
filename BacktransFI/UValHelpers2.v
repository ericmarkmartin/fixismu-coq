Require StlcFix.SpecSyntax.
Require StlcIso.SpecSyntax.
Require Import BacktransFI.UValHelpers.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.StlcOmega.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LRFI.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import LogRelFI.LemmasInversion.
Require Import Lia.
Require Import Db.Lemmas.
Require Import UValFI.UVal.
Require StlcIso.Fix.
Require Lia.

Definition uvalApp_pctx₁ n ts₂ τ τ' :=
  F.papp₁
    (F.papp₂
       (F.abs (UValFI n (I.tarr τ τ'))
              (F.abs (UValFI n τ)
                     (F.app (caseArrUp n (F.var 1) τ τ') (F.var 0))))
       F.phole)
    ts₂.
Definition uvalApp_pctxA₁ n ts₂ τ τ' :=
  F.a_papp₁ (UValFI n τ) (UValFI n τ')
            (F.a_papp₂ (UValFI n (I.tarr τ τ')) (F.tarr (UValFI n τ) (UValFI n τ'))
                       (F.a_abs (UValFI n (I.tarr τ τ')) (F.tarr (UValFI n τ) (UValFI n τ'))
                                (F.a_abs (UValFI n τ) (UValFI n τ')
                                         (F.a_app (UValFI n τ) (UValFI n τ')
                                                  (caseArrUpA n (F.a_var 1) τ τ')
                                                  (F.a_var 0))))
                       F.a_phole)
            ts₂.

Definition uvalApp_pctx₂ n ts₁ τ τ' :=
  F.papp₂
    (F.app
       (F.abs (UValFI n (I.tarr τ τ'))
              (F.abs (UValFI n τ)
                     (F.app
                        (caseArrUp n (F.var 1) τ τ')
                        (F.var 0))))
       ts₁)
    F.phole.
Definition uvalApp_pctxA₂ n ts₁ τ τ' :=
  F.a_papp₂ (UValFI n τ) (UValFI n τ')
    (F.a_app (UValFI n (I.tarr τ τ')) (F.tarr (UValFI n τ) (UValFI n τ'))
       (F.a_abs (UValFI n (I.tarr τ τ')) (F.tarr (UValFI n τ) (UValFI n τ'))
              (F.a_abs (UValFI n τ) (UValFI n τ')
                     (F.a_app (UValFI n τ) (UValFI n τ')
                        (caseArrUpA n (F.a_var 1) τ τ')
                        (F.a_var 0))))
       ts₁)
    F.a_phole.
Definition uvalApp n ts₁ ts₂ τ τ' :=
  F.app (F.app (F.abs (UValFI n (I.tarr τ τ')) (F.abs (UValFI n τ) (F.app (caseArrUp n (F.var 1) τ τ') (F.var 0)))) ts₁) ts₂.

Definition uvalAppA n ts₁ ts₂ τ τ' :=
  F.a_app (UValFI n τ) (UValFI n τ')
    (F.a_app (UValFI n (I.tarr τ τ')) (F.tarr (UValFI n τ) (UValFI n τ'))
       (F.a_abs (UValFI n (I.tarr τ τ')) (F.tarr (UValFI n τ) (UValFI n τ'))
              (F.a_abs (UValFI n τ) (UValFI n τ')
                     (F.a_app (UValFI n τ) (UValFI n τ')
                        (caseArrUpA n (F.a_var 1) τ τ')
                        (F.a_var 0))))
       ts₁)
    ts₂.

(* Arguments uvalApp_pctx₁ n ts₂ : simpl never. *)
(* Arguments uvalApp_pctx₂ n ts₁ : simpl never. *)
(* Arguments uvalApp n ts₁ ts₂ : simpl never. *)

Lemma uvalApp_T {n ts₁ ts₂ Γ τ τ'} :
  ⟪ Γ ⊢ ts₁ : UValFI n (I.tarr τ τ') ⟫ →
  ⟪ Γ ⊢ ts₂ : UValFI n τ ⟫ →
  ⟪ Γ ⊢ uvalApp n ts₁ ts₂ τ τ' : UValFI n τ' ⟫.
Proof.
  unfold uvalApp.
  eauto with typing uval_typing.
Qed.

Lemma uvalApp_pctx₁_T {n ts₂ Γ τ τ'} :
  ⟪ Γ ⊢ ts₂ : UValFI n τ ⟫ →
  ⟪ ⊢ uvalApp_pctx₁ n ts₂ τ τ' : Γ , UValFI n (I.tarr τ τ') → Γ , UValFI n τ' ⟫.
Proof.
  unfold uvalApp_pctx₁.
  eauto with typing uval_typing.
Qed.

Lemma uvalApp_pctx₂_T {n ts₁ Γ τ τ'} :
  ⟪ Γ ⊢ ts₁ : UValFI n (I.tarr τ τ') ⟫ →
  ⟪ ⊢ uvalApp_pctx₂ n ts₁ τ τ' : Γ , UValFI n τ → Γ , UValFI n τ' ⟫.
Proof.
  unfold uvalApp_pctx₂.
  eauto with typing uval_typing.
Qed.

Lemma uvalAppA_T {n ts₁ ts₂ Γ τ τ'} :
  ⟪ Γ a⊢ ts₁ : UValFI n (I.tarr τ τ') ⟫ →
  ⟪ Γ a⊢ ts₂ : UValFI n τ ⟫ →
  ⟪ Γ a⊢ uvalAppA n ts₁ ts₂ τ τ' : UValFI n τ' ⟫.
Proof.
  unfold uvalAppA.
  eauto with typing uval_typing.
Qed.

Lemma uvalApp_pctxA₁_T {n ts₂ Γ τ τ'} :
  ⟪ Γ a⊢ ts₂ : UValFI n τ ⟫ →
  ⟪ a⊢ uvalApp_pctxA₁ n ts₂ τ τ' : Γ , UValFI n (I.tarr τ τ') → Γ , UValFI n τ' ⟫.
Proof.
  unfold uvalApp_pctxA₁.
  eauto with typing uval_typing.
Qed.

Lemma uvalApp_pctxA₂_T {n ts₁ Γ τ τ'} :
  ⟪ Γ a⊢ ts₁ : UValFI n (I.tarr τ τ') ⟫ →
  ⟪ a⊢ uvalApp_pctxA₂ n ts₁ τ τ' : Γ , UValFI n τ → Γ , UValFI n τ' ⟫.
Proof.
  unfold uvalApp_pctxA₂.
  eauto with typing uval_typing.
Qed.


Lemma eraseAnnot_uvalAppA {n ts₁ ts₂ τ τ'} :
  eraseAnnot (uvalAppA n ts₁ ts₂ τ τ') = uvalApp n (eraseAnnot ts₁) (eraseAnnot ts₂) τ τ'.
Proof.
  unfold uvalAppA, uvalApp.
  cbn.
  now rewrite ?eraseAnnot_caseArrUpA.
Qed.

Lemma eraseAnnot_pctx_uvalApp_pctxA₁ {n ts₂ τ τ'} :
  eraseAnnot_pctx (uvalApp_pctxA₁ n ts₂ τ τ') = uvalApp_pctx₁ n (eraseAnnot ts₂) τ τ'.
Proof.
  unfold uvalApp_pctxA₁, uvalApp_pctx₁.
  cbn.
  now rewrite ?eraseAnnot_caseArrUpA.
Qed.

Lemma eraseAnnot_pctx_uvalApp_pctxA₂ {n ts₁ τ τ'} :
  eraseAnnot_pctx (uvalApp_pctxA₂ n ts₁ τ τ') = uvalApp_pctx₂ n (eraseAnnot ts₁) τ τ'.
Proof.
  unfold uvalApp_pctxA₂, uvalApp_pctx₂.
  cbn.
  now rewrite ?eraseAnnot_caseArrUpA.
Qed.

Hint Resolve uvalApp_T : uval_typing.
Hint Resolve uvalApp_pctx₁_T : uval_typing.
Hint Resolve uvalApp_pctx₂_T : uval_typing.
Hint Resolve uvalAppA_T : uval_typing.
Hint Resolve uvalApp_pctxA₁_T : uval_typing.
Hint Resolve uvalApp_pctxA₂_T : uval_typing.


Local Ltac crush :=
  repeat (repeat F.crushStlcSyntaxMatchH;
          repeat I.crushStlcSyntaxMatchH;
          repeat F.crushStlcEval;
          repeat I.crushStlcEval;
          (* repeat crushUtlcEvaluationMatchH;  *)
          (* repeat crushUtlcEvaluationMatchH2;  *)
          (* repeat crushUtlcEvaluationMatchH2;  *)
          (* repeat crushUtlcScopingMatchH; *)
          repeat crushDbSyntaxMatchH;
          repeat crushDbLemmasMatchH;
          repeat crushDbLemmasRewriteH;
          try assumption;
          crushOfType;
          trivial;
          eauto using caseUnit_pctx_ectx, caseSum_pctx_ectx, caseArr_pctx_ectx, upgrade_value, downgrade_value with typing
         ).

Lemma uvalApp_sub {n ts₁ ts₂ τ τ' γ} :
  (uvalApp n ts₁ ts₂ τ τ') [γ] = uvalApp n (ts₁[γ]) (ts₂[γ]) τ τ'.
Proof.
  unfold uvalApp; cbn.
  crush; rewrite caseArrUp_sub;
  crush.
Qed.

Lemma termrel_uvalApp {d w n p ts₁ tu₁ ts₂ tu₂ τ τ'} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (I.tarr τ τ')) ts₁ tu₁ →
  (∀ w' : World, w' ≤ w → termrel d w' (pEmulDV n p τ) ts₂ tu₂) →
  termrel d w (pEmulDV n p τ') (uvalApp n ts₁ ts₂ τ τ') (I.app tu₁ tu₂).
Proof.
  intros dwp tr₁ tr₂.
  unfold uvalApp, caseArrUp, caseArrUp_pctx.
  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); F.inferContext; I.inferContext.
  unfold pctx_cat, I.ECtx; crush.

  (* continuation boilerplate *)
  intros w' futw vs₁ vu₁ vr₁.
  destruct (valrel_implies_OfType vr₁) as [[vvs₁ ?] [? ?]].
  simpl in H, H1.
  cbn.
  rewrite F.pctx_cat_app; cbn.

  (* beta-reduce the outer let *)
  eapply termrel_antired_eval_left.
  eapply (F.eval_from_eval₀ (F.eval_beta vvs₁)); F.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (F.app (upgrade n 1 (I.tarr τ τ')) (F.var 1)) τ τ').
  rewrite caseArr_sub; cbn; crush; rewrite upgrade_sub.

  (* evaluate ts₂ and tu₂ *)
  specialize (tr₂ w' futw).
  eapply (termrel_ectx' tr₂); F.inferContext; I.inferContext;
  unfold pctx_cat, I.ECtx; crush.

  (* continuation boilerplate *)
  intros w'' futw' vs₂ vu₂ vr₂.
  destruct (valrel_implies_Value vr₂) as [vvs₂ ?].
  cbn.

  (* beta-reduce the remaining let *)
  eapply termrel_antired_eval_left.
  eapply (F.eval_from_eval₀ (F.eval_beta vvs₂)); F.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (F.app (upgrade n 1 (I.tarr τ τ')) (F.var 1)) τ τ').
  rewrite ?caseArr_sub; cbn; crush; rewrite ?upgrade_sub.
  rewrite <- ?ap_liftSub; rewrite -> ?liftSub_wkm; rewrite (apply_wkm_beta1_cancel vs₁ vs₂).

  (* execute the upgrade *)
  assert (w'' ≤ w) by lia.
  simpl in H, H1.
  assert (valrel d w'' (pEmulDV n p (I.tarr τ τ')) vs₁ vu₁) by eauto using valrel_mono.
  assert (trupg : termrel d w'' (pEmulDV (n + 1) p (I.tarr τ τ')) (F.app (upgrade n 1 (I.tarr τ τ')) vs₁) vu₁)
    by (eauto using upgrade_works', dwp_mono).
  unfold caseArr.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w''' futw'' vs₁' vu₁' vr₁'.
  replace (n + 1) with (S n) in vr₁' by lia.
  destruct (valrel_implies_OfType vr₁') as [[_ _] [_ ?]].
  simpl in H5.

  destruct (valrel_implies_Value vr₁').
  (* case analysis *)
  eapply invert_valrel_pEmulDV_for_caseUValArr in vr₁'.
  destruct vr₁' as [(vs₁'' & ? & es & vr₁')|(? & div)]; subst.
  - (* Correct case *)

    (* caseArr succeeds *)
    eapply termrel_antired_star_left.
    fold (caseArr n (F.inl vs₁'') τ τ').
    eapply (F.evalstar_ctx' es); F.inferContext; crush.
    cbn.
    crush.

    (* application works *)
    eapply valrel_in_termrel in vr₁'.
    eapply (termrel_app vr₁').

    (* application argument is also fine *)
    eauto using valrel_in_termrel, valrel_mono.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    fold (caseArr n vs₁' τ τ').
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; cbn; crush.
  - split; trivial.
  - simpl; trivial.
Qed.

Lemma uvalApp_pctx₁_app {n ts₁ ts₂ τ τ'} :
  F.pctx_app ts₁ (uvalApp_pctx₁ n ts₂ τ τ') = uvalApp n ts₁ ts₂ τ τ'.
Proof.
  crush.
Qed.

Lemma uvalApp_pctx₂_app {n ts₁ ts₂ τ τ'} :
  F.pctx_app ts₂ (uvalApp_pctx₂ n ts₁ τ τ') = uvalApp n ts₁ ts₂ τ τ'.
Proof.
  crush.
Qed.

Arguments uvalApp_pctx₁ n ts₂ : simpl never.
Arguments uvalApp_pctx₂ n ts₁ : simpl never.
Arguments uvalApp n ts₁ ts₂ : simpl never.
Arguments uvalApp_pctxA₁ n ts₂ : simpl never.
Arguments uvalApp_pctxA₂ n ts₁ : simpl never.
Arguments uvalAppA n ts₁ ts₂ : simpl never.
