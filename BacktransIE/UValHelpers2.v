Require StlcIsoValid.SpecSyntax.
Require StlcEqui.SpecSyntax.
Require Import BacktransIE.UValHelpers.
Require Import StlcIsoValid.SpecTyping.
Require Import StlcIsoValid.LemmasTyping.
Require Import StlcIsoValid.SpecEvaluation.
Require Import StlcIsoValid.LemmasEvaluation.
Require Import StlcIsoValid.SpecAnnot.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.LemmasTyping.
Require Import LogRelIE.PseudoTypeIE.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import LogRelIE.LemmasInversion.
Require Import Lia.
Require Import Db.Lemmas.
Require Import UValIE.UVal.
Require StlcEqui.Fix.
Require Lia.

Definition uvalApp_pctx₁ n ts₂ τ τ' :=
  I.papp₁
    (I.papp₂
       (I.abs (UValIE n (E.tarr τ τ'))
              (I.abs (UValIE n τ)
                     (I.app (caseArrUp n (I.var 1) τ τ') (I.var 0))))
       I.phole)
    ts₂.
Definition uvalApp_pctxA₁ n ts₂ τ τ' :=
  I.ia_papp₁ (UValIE n τ) (UValIE n τ')
            (I.ia_papp₂ (UValIE n (E.tarr τ τ')) (I.tarr (UValIE n τ) (UValIE n τ'))
                       (I.ia_abs (UValIE n (E.tarr τ τ')) (I.tarr (UValIE n τ) (UValIE n τ'))
                                (I.ia_abs (UValIE n τ) (UValIE n τ')
                                         (I.ia_app (UValIE n τ) (UValIE n τ')
                                                  (caseArrUpA n (I.ia_var 1) τ τ')
                                                  (I.ia_var 0))))
                       I.ia_phole)
            ts₂.

Definition uvalApp_pctx₂ n ts₁ τ τ' :=
  I.papp₂
    (I.app
       (I.abs (UValIE n (E.tarr τ τ'))
              (I.abs (UValIE n τ)
                     (I.app
                        (caseArrUp n (I.var 1) τ τ')
                        (I.var 0))))
       ts₁)
    I.phole.
Definition uvalApp_pctxA₂ n ts₁ τ τ' :=
  I.ia_papp₂ (UValIE n τ) (UValIE n τ')
    (I.ia_app (UValIE n (E.tarr τ τ')) (I.tarr (UValIE n τ) (UValIE n τ'))
       (I.ia_abs (UValIE n (E.tarr τ τ')) (I.tarr (UValIE n τ) (UValIE n τ'))
              (I.ia_abs (UValIE n τ) (UValIE n τ')
                     (I.ia_app (UValIE n τ) (UValIE n τ')
                        (caseArrUpA n (I.ia_var 1) τ τ')
                        (I.ia_var 0))))
       ts₁)
    I.ia_phole.
Definition uvalApp n ts₁ ts₂ τ τ' :=
  I.app (I.app (I.abs (UValIE n (E.tarr τ τ')) (I.abs (UValIE n τ) (I.app (caseArrUp n (I.var 1) τ τ') (I.var 0)))) ts₁) ts₂.

Definition uvalAppA n ts₁ ts₂ τ τ' :=
  I.ia_app (UValIE n τ) (UValIE n τ')
    (I.ia_app (UValIE n (E.tarr τ τ')) (I.tarr (UValIE n τ) (UValIE n τ'))
       (I.ia_abs (UValIE n (E.tarr τ τ')) (I.tarr (UValIE n τ) (UValIE n τ'))
              (I.ia_abs (UValIE n τ) (UValIE n τ')
                     (I.ia_app (UValIE n τ) (UValIE n τ')
                        (caseArrUpA n (I.ia_var 1) τ τ')
                        (I.ia_var 0))))
       ts₁)
    ts₂.

(* Arguments uvalApp_pctx₁ n ts₂ : simpl never. *)
(* Arguments uvalApp_pctx₂ n ts₁ : simpl never. *)
(* Arguments uvalApp n ts₁ ts₂ : simpl never. *)

Ltac crushTypingMatchH3 :=
  match goal with
    | [ |- ⟪ _ i⊢ caseArrUp _ _ _ _ : _ ⟫                  ] => eapply caseArrUp_T
    | [ |- ⟪ _ ia⊢ caseArrUpA _ _ _ _ : _ ⟫                  ] => eapply caseArrUpA_T
  end.

Local Ltac crush2 :=
  intros;
  repeat (I.crushTypingMatchH +
            I.crushTypingMatchH2 +
            crushTypingMatchH3 +
            I.crushValidTyMatch2 +
            crushValidTyMatchUval +
            I.crushValidTyMatch2 +
            I.crushTypingMatchIAH +
            I.crushTypingMatchIAH2 +
            assumption).

Lemma uvalApp_T {n ts₁ ts₂ Γ τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  ⟪ Γ i⊢ ts₁ : UValIE n (E.tarr τ τ') ⟫ →
  ⟪ Γ i⊢ ts₂ : UValIE n τ ⟫ →
  ⟪ Γ i⊢ uvalApp n ts₁ ts₂ τ τ' : UValIE n τ' ⟫.
Proof.
  unfold uvalApp.
  crush2.
Qed.


Lemma uvalApp_pctx₁_T {n ts₂ Γ τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  ⟪ Γ i⊢ ts₂ : UValIE n τ ⟫ →
  ⟪ i⊢ uvalApp_pctx₁ n ts₂ τ τ' : Γ , UValIE n (E.tarr τ τ') → Γ , UValIE n τ' ⟫.
Proof.
  unfold uvalApp_pctx₁.
  crush2.
Qed.

Lemma uvalApp_pctx₂_T {n ts₁ Γ τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  ⟪ Γ i⊢ ts₁ : UValIE n (E.tarr τ τ') ⟫ →
  ⟪ i⊢ uvalApp_pctx₂ n ts₁ τ τ' : Γ , UValIE n τ → Γ , UValIE n τ' ⟫.
Proof.
  unfold uvalApp_pctx₂.
  crush2.
Qed.

Lemma uvalAppA_T {n ts₁ ts₂ Γ τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  ⟪ Γ ia⊢ ts₁ : UValIE n (E.tarr τ τ') ⟫ →
  ⟪ Γ ia⊢ ts₂ : UValIE n τ ⟫ →
  ⟪ Γ ia⊢ uvalAppA n ts₁ ts₂ τ τ' : UValIE n τ' ⟫.
Proof.
  unfold uvalAppA.
  crush2.
Qed.

Lemma uvalApp_pctxA₁_T {n ts₂ Γ τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  ⟪ Γ ia⊢ ts₂ : UValIE n τ ⟫ →
  ⟪ ia⊢ uvalApp_pctxA₁ n ts₂ τ τ' : Γ , UValIE n (E.tarr τ τ') → Γ , UValIE n τ' ⟫.
Proof.
  unfold uvalApp_pctxA₁.
  crush2.
Qed.

Lemma uvalApp_pctxA₂_T {n ts₁ Γ τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  ⟪ Γ ia⊢ ts₁ : UValIE n (E.tarr τ τ') ⟫ →
  ⟪ ia⊢ uvalApp_pctxA₂ n ts₁ τ τ' : Γ , UValIE n τ → Γ , UValIE n τ' ⟫.
Proof.
  unfold uvalApp_pctxA₂.
  crush2.
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
  repeat (repeat I.crushStlcSyntaxMatchH;
          repeat E.crushStlcSyntaxMatchH;
          repeat I.crushStlcEval;
          repeat E.crushStlcEval;
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
  ValidTy τ -> ValidTy τ' ->
  (uvalApp n ts₁ ts₂ τ τ') [γ] = uvalApp n (ts₁[γ]) (ts₂[γ]) τ τ'.
Proof.
  intros vτ vτ'.
  unfold uvalApp; cbn.
  crush; rewrite caseArrUp_sub;
  crush.
Qed.

Lemma termrel_uvalApp {d w n p ts₁ tu₁ ts₂ tu₂ τ τ'} :
  E.ValidTy τ -> E.ValidTy τ' ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (E.tarr τ τ')) ts₁ tu₁ →
  (∀ w' : World, w' ≤ w → termrel d w' (pEmulDV n p τ) ts₂ tu₂) →
  termrel d w (pEmulDV n p τ') (uvalApp n ts₁ ts₂ τ τ') (E.app tu₁ tu₂).
Proof.
  intros vτ vτ' dwp tr₁ tr₂.
  unfold uvalApp, caseArrUp, caseArrUp_pctx.
  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); I.inferContext; E.inferContext; cbn; crushValidTy.
  unfold pctx_cat, E.ECtx; crush.

  (* continuation boilerplate *)
  intros w' futw vs₁ vu₁ vr₁.
  destruct (valrel_implies_OfType vr₁) as [[vvs₁ ?] [? ?]].
  simpl in H, H1.
  cbn.
  rewrite I.pctx_cat_app; cbn.

  (* beta-reduce the outer let *)
  eapply termrel_antired_eval_left.
  eapply (I.eval_from_eval₀ (I.eval_beta vvs₁)); I.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (I.app (upgrade n 1 (E.tarr τ τ')) (I.var 1)) τ τ').
  rewrite caseArr_sub; cbn; crush; rewrite upgrade_sub; crushValidTy.

  (* evaluate ts₂ and tu₂ *)
  specialize (tr₂ w' futw).
  eapply (termrel_ectx' tr₂); I.inferContext; E.inferContext;
  unfold pctx_cat, E.ECtx; crush.

  (* continuation boilerplate *)
  intros w'' futw' vs₂ vu₂ vr₂.
  destruct (valrel_implies_Value vr₂) as [vvs₂ ?].
  cbn.

  (* beta-reduce the remianing let *)
  eapply termrel_antired_eval_left.
  eapply (I.eval_from_eval₀ (I.eval_beta vvs₂)); I.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (I.app (upgrade n 1 (E.tarr τ τ')) (I.var 1)) τ τ').
  rewrite ?caseArr_sub; cbn; crush; rewrite ?upgrade_sub; crushValidTy.
  rewrite <- ?ap_liftSub; rewrite -> ?liftSub_wkm; rewrite (apply_wkm_beta1_cancel vs₁ vs₂).

  (* execute the upgrade *)
  assert (w'' ≤ w) by lia.
  simpl in H, H1.
  assert (valrel d w'' (pEmulDV n p (E.tarr τ τ')) vs₁ vu₁).
  { refine (valrel_mono _ _ vr₁); cbn; try crushValidPTyMatch; crushValidTy. }
  assert (trupg : termrel d w'' (pEmulDV (n + 1) p (E.tarr τ τ')) (I.app (upgrade n 1 (E.tarr τ τ')) vs₁) vu₁) by
    (eapply upgrade_works'; crushValidTy; now eapply (dwp_mono dwp)).
  unfold caseArr.
  eapply (termrel_ectx' trupg); I.inferContext; E.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w''' futw'' vs₁' vu₁' vr₁'.
  replace (n + 1) with (S n) in vr₁' by lia.
  destruct (valrel_implies_OfType vr₁') as [[_ _] [_ ?]].
  simpl in H5.

  destruct (valrel_implies_Value vr₁').
  (* case analysis *)
  eapply invert_valrel_pEmulDV_for_caseUValArr in vr₁'; crushValidTy.
  destruct vr₁' as [(vs₁'' & ? & es & vr₁')|(? & div)]; subst.
  - (* Correct case *)

    (* caseArr succeeds *)
    eapply termrel_antired_star_left.
    fold (caseArr n (I.inl vs₁'') τ τ').
    eapply (I.evalstar_ctx' es); I.inferContext; crush.
    cbn.
    crush.

    (* application works *)
    eapply valrel_in_termrel in vr₁'.
    assert (vpτ : ValidPTy (pEmulDV n p τ)) by (try crushValidPTyMatch; crushValidTy).
    assert (vpτ' : ValidPTy (pEmulDV n p τ')) by (try crushValidPTyMatch; crushValidTy).
    eapply (termrel_app vpτ vpτ' vr₁').

    (* application argument is also fine *)
    eauto using valrel_in_termrel, valrel_mono.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    fold (caseArr n vs₁' τ τ').
    eapply (I.divergence_closed_under_evalcontext' div); I.inferContext; cbn; crush.
Qed.

Lemma uvalApp_pctx₁_app {n ts₁ ts₂ τ τ'} :
  I.pctx_app ts₁ (uvalApp_pctx₁ n ts₂ τ τ') = uvalApp n ts₁ ts₂ τ τ'.
Proof.
  crush.
Qed.

Lemma uvalApp_pctx₂_app {n ts₁ ts₂ τ τ'} :
  I.pctx_app ts₂ (uvalApp_pctx₂ n ts₁ τ τ') = uvalApp n ts₁ ts₂ τ τ'.
Proof.
  crush.
Qed.

Arguments uvalApp_pctx₁ n ts₂ : simpl never.
Arguments uvalApp_pctx₂ n ts₁ : simpl never.
Arguments uvalApp n ts₁ ts₂ : simpl never.
Arguments uvalApp_pctxA₁ n ts₂ : simpl never.
Arguments uvalApp_pctxA₂ n ts₁ : simpl never.
Arguments uvalAppA n ts₁ ts₂ : simpl never.
