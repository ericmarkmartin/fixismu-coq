Require StlcFix.SpecSyntax.
Require StlcIso.SpecSyntax.
Require Import BacktransFI.UValHelpers.
Require Import BacktransFI.UValHelpers2.
Require Import StlcFix.SpecTyping.
Require Import StlcIso.SpecTyping.
Require Import StlcFix.StlcOmega.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.LemmasTyping.
Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LR.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import LogRelFI.LemmasInversion.
Require Import Lia.
Require Import Db.Lemmas.
Require Import UValFI.UVal.
Require StlcIso.Fix.
Require Lia.

Set Asymmetric Patterns.

Fixpoint emulate (n : nat) (t : TmA) : F.TmA :=
  match t with
    ia_var x => F.a_var x
  | ia_abs τ₁ τ₂ tb  => inArrDwnA τ₁ τ₂ n (F.a_abs (UValFI n τ₁) (UValFI n τ₂) (emulate n tb))
  | ia_app τ₁ τ₂ t₁ t₂ => uvalAppA n (emulate n t₁) (emulate n t₂) τ₁ τ₂
  | ia_unit => inUnitDwnA n F.a_unit
  | ia_true => inBoolDwnA n F.a_true
  | ia_false => inBoolDwnA n F.a_false
  | ia_ite τ t₁ t₂ t₃ => F.a_ite (UValFI n τ) (caseBoolUpA n (emulate n t₁)) (emulate n t₂) (emulate n t₃)
  | ia_pair τ₁ τ₂ t₁ t₂ => inProdDwnA τ₁ τ₂ n (F.a_pair (UValFI n τ₁) (UValFI n τ₂) (emulate n t₁) (emulate n t₂))
  | ia_proj₁ τ₁ τ₂ t => F.a_proj₁ (UValFI n τ₁) (UValFI n τ₂) (caseProdUpA n (emulate n t) τ₁ τ₂)
  | ia_proj₂ τ₁ τ₂ t => F.a_proj₂ (UValFI n τ₁) (UValFI n τ₂) (caseProdUpA n (emulate n t) τ₁ τ₂)
  | ia_inl τ₁ τ₂ t => inSumDwnA τ₁ τ₂ n (F.a_inl (UValFI n τ₁) (UValFI n τ₂) (emulate n t))
  | ia_inr τ₁ τ₂ t => inSumDwnA τ₁ τ₂ n (F.a_inr (UValFI n τ₁) (UValFI n τ₂) (emulate n t))
  | ia_caseof τ₁ τ₂ τ t₁ t₂ t₃ => F.a_caseof (UValFI n τ₁) (UValFI n τ₂) (UValFI n τ) (caseSumUpA n (emulate n t₁) τ₁ τ₂) (emulate n t₂) (emulate n t₃)
  | ia_seq τ t₁ t₂ => F.a_seq (UValFI n τ) (caseUnitUpA n (emulate n t₁)) (emulate n t₂)
  | ia_fold_ τ t => inRecDwnA τ n (emulate n t)
  | ia_unfold_ τ t => caseRecUpA n (emulate n t) τ
  end.

Fixpoint emulate_pctx (n : nat) (C : PCtxA) : F.PCtxA :=
  match C with
    | ia_phole => F.a_phole
    | ia_pabs τ₁ τ₂ C => F.pctxA_cat (F.a_pabs (UValFI n τ₁) (UValFI n τ₂) (emulate_pctx n C)) (inArrDwn_pctxA τ₁ τ₂ n)
    | ia_papp₁ τ₁ τ₂ C t₂ => F.pctxA_cat (emulate_pctx n C) (uvalApp_pctxA₁ n (emulate n t₂) τ₁ τ₂)
    | ia_papp₂ τ₁ τ₂ t₁ C => F.pctxA_cat (emulate_pctx n C) (uvalApp_pctxA₂ n (emulate n t₁) τ₁ τ₂)
    | ia_pite₁ τ C₁ t₂ t₃ => F.a_pite₁ (UValFI n τ) (F.pctxA_cat (emulate_pctx n C₁) (caseBoolUp_pctxA n)) (emulate n t₂) (emulate n t₃)
    | ia_pite₂ τ t₁ C₂ t₃ => F.a_pite₂ (UValFI n τ) (caseBoolUpA n (emulate n t₁)) (emulate_pctx n C₂) (emulate n t₃)
    | ia_pite₃ τ t₁ t₂ C₃ => F.a_pite₃ (UValFI n τ) (caseBoolUpA n (emulate n t₁)) (emulate n t₂) (emulate_pctx n C₃)
    | ia_ppair₁ τ₁ τ₂ C₁ t₂ => F.pctxA_cat (F.a_ppair₁ (UValFI n τ₁) (UValFI n τ₂) (emulate_pctx n C₁) (emulate n t₂)) (inProdDwn_pctxA τ₁ τ₂ n)
    | ia_ppair₂ τ₁ τ₂ t₁ C₂ => F.pctxA_cat (F.a_ppair₂ (UValFI n τ₁) (UValFI n τ₂) (emulate n t₁) (emulate_pctx n C₂)) (inProdDwn_pctxA τ₁ τ₂  n)
    | ia_pproj₁ τ₁ τ₂ C => F.a_pproj₁ (UValFI n τ₁) (UValFI n τ₂) (F.pctxA_cat (emulate_pctx n C) (caseProdUp_pctxA n τ₁ τ₂))
    | ia_pproj₂ τ₁ τ₂ C => F.a_pproj₂ (UValFI n τ₁) (UValFI n τ₂) (F.pctxA_cat (emulate_pctx n C) (caseProdUp_pctxA n τ₁ τ₂))
    | ia_pinl τ₁ τ₂ C => F.pctxA_cat (F.a_pinl (UValFI n τ₁) (UValFI n τ₂) (emulate_pctx n C)) (inSumDwn_pctxA τ₁ τ₂ n)
    | ia_pinr τ₁ τ₂ C => F.pctxA_cat (F.a_pinr (UValFI n τ₁) (UValFI n τ₂) (emulate_pctx n C)) (inSumDwn_pctxA τ₁ τ₂ n)
    | ia_pcaseof₁ τ₁ τ₂ τ C₁ t₂ t₃ => F.a_pcaseof₁ (UValFI n τ₁) (UValFI n τ₂) (UValFI n τ) (F.pctxA_cat (emulate_pctx n C₁) (caseSumUp_pctxA n τ₁ τ₂)) (emulate n t₂) (emulate n t₃)
    | ia_pcaseof₂ τ₁ τ₂ τ t₁ C₂ t₃ => F.a_pcaseof₂ (UValFI n τ₁) (UValFI n τ₂) (UValFI n τ) (caseSumUpA n (emulate n t₁) τ₁ τ₂) (emulate_pctx n C₂) (emulate n t₃)
    | ia_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C₃ => F.a_pcaseof₃ (UValFI n τ₁) (UValFI n τ₂) (UValFI n τ) (caseSumUpA n (emulate n t₁) τ₁ τ₂) (emulate n t₂) (emulate_pctx n C₃)
    | ia_pseq₁ τ C₁ t₂ => F.a_pseq₁ (UValFI n τ) (F.pctxA_cat (emulate_pctx n C₁) (caseUnitUp_pctxA n)) (emulate n t₂)
    | ia_pseq₂ τ t₁ C₂ => F.a_pseq₂ (UValFI n τ) (caseUnitUpA n (emulate n t₁)) (emulate_pctx n C₂)
    | ia_pfold τ C => F.pctxA_cat (emulate_pctx n C) (inRecDwn_pctxA τ n)
    | ia_punfold τ C => F.pctxA_cat (emulate_pctx n C) (caseRecUp_pctxA n τ)
  end.

Fixpoint toUVals n (Γ : I.Env) : F.Env :=
  match Γ with
    I.empty => F.empty
  | Γ r▻ τ => toUVals n Γ ▻ UValFI n τ
  end.

Lemma toUVals_entry {n Γ i τ} :
  ⟪  i : τ r∈ Γ  ⟫ → ⟪ i : UValFI n τ ∈ toUVals n Γ ⟫.
Proof.
  induction 1; simpl; crushTyping.
Qed.

(* Lemma emulate_T {n Γ t} : *)
(*   ⟨ Γ ⊢ t ⟩ → *)
(*   ⟪ toUVals n Γ ⊢ emulate n t : UVal n ⟫. *)
(* Proof. *)
(*   induction 1; unfold emulate; *)
(*   eauto using toUVals_entry with typing uval_typing. *)
(* Qed. *)

Lemma emulateT {n t Γ τ} :
  ⟪  Γ ia⊢ t : τ  ⟫ ->
  ⟪  toUVals n Γ a⊢ emulate n t : UValFI n τ  ⟫.
Proof.
  induction 1; cbn; eauto using toUVals_entry with typing uval_typing.
Qed.

Hint Resolve emulateT : uval_typing.

Lemma emulate_pctx_T {n C Γₒ τₒ Γ τ} :
  ⟪  ia⊢ C : Γₒ , τₒ → Γ , τ  ⟫ ->
  ⟪  a⊢ emulate_pctx n C : toUVals n Γₒ , UValFI n τₒ → toUVals n Γ , UValFI n τ  ⟫.
Proof.
  induction 1; cbn;
    crushTypingA;
    try change (toUVals n ?Γ ▻ UValFI n ?τ) with (toUVals n (Γ r▻ τ));
    eauto using emulateT, inArrDwn_pctx_T with typing uval_typing.
  (* crushTypingMatchAH. *)
Qed.

Local Ltac crush :=
  repeat (repeat I.crushStlcSyntaxMatchH;
          repeat F.crushStlcSyntaxMatchH;
          repeat F.crushStlcEval;
          repeat I.crushStlcEval;
          (* repeat crushUtlcEvaluationMatchH; *)
          (* repeat crushUtlcEvaluationMatchH2; *)
          (* repeat crushUtlcEvaluationMatchH2; *)
          repeat I.crushTypingMatchH;
          repeat I.crushTypingMatchH2;
          repeat crushDbSyntaxMatchH;
          repeat crushDbLemmasMatchH;
          repeat crushDbLemmasRewriteH;
          try assumption;
          crushOfType;
          trivial;
          eauto using (* caseUnit_pctx_ECtx, caseBool_pctx_ECtx, caseProd_pctx_ECtx, caseSum_pctx_ECtx, caseArr_pctx_ECtx,  *)
                upgrade_value, downgrade_value with typing uval_typing
         ).

(* Lemma termrel_omega_wrong { d w pτ} : *)
(*   termrel d w pτ (stlcOmega (repEmul pτ)) wrong. *)
(* Proof. *)
(*   eauto using termrel_div_wrong, stlcOmega_div with eval. *)
(* Qed. *)

(* Lemma compat_emul_wrong {Γ pτ d m} : *)
(*   ⟪ Γ ⊩ stlcOmega (repEmul pτ) ⟦ d , m ⟧ wrong : pτ ⟫. *)
(* Proof. *)
(*   split; [|split]; crush. *)
(*   intros w wn γs γu envrel. *)
(*   rewrite stlcOmega_sub. *)
(*   eauto using termrel_omega_wrong. *)
(* Qed. *)

(* Lemma compat_emul_wrong' {Γ n p d m} : *)
(*   ⟪ Γ ⊩ stlcOmega (UVal n) ⟦ d , m ⟧ wrong : pEmulDV n p ⟫. *)
(* Proof. *)
(*   change (UVal n) with (repEmul (pEmulDV n p)). *)
(*   eauto using compat_emul_wrong.  *)
(* Qed. *)

Lemma compat_emul_unit {Γ d n p m} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ inUnitDwn n F.unit ⟦ d , m ⟧ I.unit : pEmulDV n p tunit ⟫.
Proof.
  intros dwp.
  split; [|split].
  - eauto using inUnitDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.
    rewrite inUnitDwn_sub.
    simpl.
    eapply termrel₀_in_termrel.
    eauto using termrel₀_inUnitDwn, dwp_mono, valrel_in_termrel, valrel_unit with arith.
Qed.

Lemma compat_emul_true {Γ d n p m} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ inBoolDwn n F.true ⟦ d , m ⟧ I.true : pEmulDV n p tbool ⟫.
Proof.
  intros dwp.
  split; [|split].
  - eauto using inBoolDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.
    rewrite inBoolDwn_sub.
    simpl.
    eapply termrel₀_in_termrel.
    eauto using termrel₀_inBoolDwn, dwp_mono, valrel_in_termrel, valrel_true with arith.
Qed.

Lemma compat_emul_false {Γ d n p m} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ inBoolDwn n F.false ⟦ d , m ⟧ I.false : pEmulDV n p tbool ⟫.
Proof.
  intros dwp.
  split; [|split].
  - eauto using inBoolDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.
    rewrite inBoolDwn_sub.
    simpl.
    eapply termrel₀_in_termrel.
    eauto using termrel₀_inBoolDwn, dwp_mono, valrel_in_termrel, valrel_false with arith.
Qed.

Lemma compat_emul_abs {n m d p Γ τ₁ τ₂ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ p▻ pEmulDV n p τ₁ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p τ₂ ⟫ →
  ⟪ Γ ⊩ inArrDwn τ₁ τ₂ n (F.abs (UValFI n τ₁) ts) ⟦ d , m ⟧ I.abs τ₁ tu : pEmulDV n p (I.tarr τ₁ τ₂) ⟫.
Proof.
  intros dwp [ty [closed tr]].
  split; [|split].
  - eauto using inArrDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.

    assert (OfType (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂))
                   (F.abs (repEmul (pEmulDV n p τ₁))
                          (ts [γs↑])) (I.abs τ₁ (tu [γu↑])))
      by (pose proof (envrel_implies_WtSub envrel);
          pose proof (envrel_implies_WtSub_iso envrel);
          crush).

    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    rewrite inArrDwn_sub.
    eapply termrel₀_in_termrel.
    eapply termrel₀_inArrDwn; try assumption.

    change (UValFI n τ₁) with (repEmul (pEmulDV n p τ₁)).

    refine (valrel_lambda _ _); crush.

    intros w' vs vu futw sz valrel.
    fold F.apTm I.apTm.
    crush.
    rewrite ?ap_comp.

    assert (lev w' ≤ m) by (unfold lev in *; lia).
    eapply tr;
      eauto using extend_envrel, envrel_mono.
Qed.

(* Lemma compat_emul_pabs {n m d p Γ} : *)
(*   dir_world_prec n m d p → *)
(*   ⟪ ⊩ F.pctx_cat (F.pabs (UVal n) F.phole) (inArrDwn_pctx n) ⟦ d , m ⟧ I.pabs I.phole : Γ p▻ pEmulDV n p , pEmulDV n p → Γ , pEmulDV n p ⟫. *)
(* Proof. *)
(*   intros dwp. *)
(*   split. *)
(*   - eauto using inArrDwn_pctx_T with typing uval_typing. *)
(*   - intros ts tu lr. *)
(*     change (F.pctx_app ts (F.pctx_cat (F.pabs (UVal n) F.phole) (inArrDwn_pctx n))) *)
(*     with (inArrDwn n (F.abs (UVal n) ts)). *)
(*     eauto using compat_emul_abs. *)
(* Qed. *)

Lemma compat_emul_pair {n m d p Γ τ₁ τ₂ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p τ₁ ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ₂ ⟫ →
  ⟪ Γ ⊩ inProdDwn τ₁ τ₂ n (F.pair ts₁ ts₂) ⟦ d , m ⟧ I.pair tu₁ tu₂ : pEmulDV n p (I.tprod τ₁ τ₂)⟫.
Proof.
  intros dwp tr₁ tr₂.
  destruct tr₁ as (? & ? & tr₁).
  destruct tr₂ as (? & ? & tr₂).
  split; [|split].
  - eauto using inProdDwn_T with typing uval_typing.
  - I.crushTyping.
  - intros w wm γs γu envrel.
    rewrite inProdDwn_sub.
    enough (termrel d w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) (F.pair ts₁ ts₂)[γs] (I.pair tu₁ tu₂)[γu]) as trp.
    + eapply (termrel_ectx' trp); F.inferContext; I.inferContext; simpl; crush.
      intros w' futw vs vu vr.
      eapply termrel₀_in_termrel.
      eapply termrel₀_inProdDwn;
        eauto using dwp_mono with arith.
    + eapply termrel_pair;
        fold F.apTm I.apTm; crush.
      intros w' fw; eapply tr₂; eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_caseof {n w d p τ₁ τ₂ τ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (tsum τ₁ τ₂)) ts₁ tu₁ →
  (forall w' vs₂ vu₂, w' ≤ w →
                      valrel d w' (pEmulDV n p τ₁) vs₂ vu₂ →
                      termrel d w' (pEmulDV n p τ) (ts₂ [beta1 vs₂]) (tu₂ [beta1 vu₂])) →
  (forall w' vs₃ vu₃, w' ≤ w →
                      valrel d w' (pEmulDV n p τ₂) vs₃ vu₃ →
                      termrel d w' (pEmulDV n p τ) (ts₃ [beta1 vs₃]) (tu₃ [beta1 vu₃])) →
  termrel d w (pEmulDV n p τ) (F.caseof (caseSumUp n ts₁ τ₁ τ₂) ts₂ ts₃) (I.caseof tu₁ tu₂ tu₃).
Proof.
  intros dwp tr₁ tr₂ tr₃.
  unfold caseSumUp.
  (* evaluate ts₁ and ts₂ *)
  eapply (termrel_ectx' tr₁); F.inferContext; I.inferContext; crush;
  eauto using caseSumUp_pctx_ectx; try now cbn.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseSumUp_pctx; rewrite F.pctx_cat_app; crush; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (τ₁ r⊎ τ₂)) (F.app (upgrade n 1 (τ₁ r⊎ τ₂)) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext;
    crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  fold (caseSum n vs' τ₁ τ₂); cbn.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValSum in vr'.
  destruct vr' as [(vs₁' & ? & es & vr₁')|
                   (? & div)]; subst.

  - (* successful caseUValSum *)
    eapply termrel_antired_star_left.
    eapply (F.evalstar_ctx' es); F.inferContext; crush.

    cbn.
    eapply termrel_caseof; eauto using valrel_in_termrel.
    + intros w''' vs₂' vu₂' fw'' vr₂. eapply tr₂; eauto with arith.
    + intros w''' vs₃' vu₃' fw'' vr₃. eapply tr₃; eauto with arith.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; crush.
Qed.

Lemma compat_emul_caseof {n m d p τ₁ τ₂ τ Γ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p (τ₁ r⊎ τ₂) ⟫ →
  ⟪ Γ p▻ pEmulDV n p τ₁ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ ⟫ →
  ⟪ Γ p▻ pEmulDV n p τ₂ ⊩ ts₃ ⟦ d , m ⟧ tu₃ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ F.caseof (caseSumUp n ts₁ τ₁ τ₂) ts₂ ts₃ ⟦ d , m ⟧ I.caseof tu₁ tu₂ tu₃ : pEmulDV n p τ ⟫.
Proof.
  intros dwp lr₁ lr₂ lr₃.
  destruct lr₁ as (? & ? & tr₁).
  destruct lr₂ as (? & ? & tr₂).
  destruct lr₃ as (? & ? & tr₃).
  split; [|split].
  - eauto with typing uval_typing.
  - crush.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseSumUp_sub.
    eapply termrel_emul_caseof;
      eauto using envrel_mono, dwp_mono with arith;
      intros w' vs₂ vu₂ fw vr₂;
      rewrite ?ap_comp;
      assert (lev w' ≤ m) by (unfold lev in *; lia);
      [eapply tr₂|eapply tr₃];
      eauto using extend_envrel, envrel_mono.
Qed.

Lemma termrel_emul_ite {n w d p τ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p tbool) ts₁ tu₁ →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p τ) ts₂ tu₂) →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p τ) ts₃ tu₃) →
  termrel d w (pEmulDV n p τ) (F.ite (caseBoolUp n ts₁) ts₂ ts₃) (I.ite tu₁ tu₂ tu₃).
Proof.
  intros dwp tr₁ tr₂ tr₃.
  unfold caseBoolUp.
  (* evaluate ts₁ and ts₂ *)
  eapply (termrel_ectx' tr₁); F.inferContext; I.inferContext; crush;
  eauto using caseBoolUp_pctx_ectx; [|now cbn].

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseBoolUp_pctx; rewrite F.pctx_cat_app; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p tbool) (F.app (upgrade n 1 tbool) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext; crush; [|now cbn].

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  fold (caseBool vs'); cbn.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValBool in vr'.
  destruct vr' as [(vs₁' & ? & es & vr₁')|
                   (? & div)]; subst.

  - (* successful caseUValBool *)
    eapply termrel_antired_star_left.
    eapply (F.evalstar_ctx' es); F.inferContext; crush.

    cbn.
    eapply termrel_ite; eauto using valrel_in_termrel.
    + intros w''' fw''. eapply tr₂; lia.
    + intros w''' fw''. eapply tr₃; lia.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; crush.
Qed.

Lemma compat_emul_ite {n m d p Γ τ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p tbool ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ ts₃ ⟦ d , m ⟧ tu₃ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ F.ite (caseBoolUp n ts₁) ts₂ ts₃ ⟦ d , m ⟧ I.ite tu₁ tu₂ tu₃ : pEmulDV n p τ ⟫.
Proof.
  intros dwp lr₁ lr₂ lr₃.
  destruct lr₁ as (? & ? & tr₁).
  destruct lr₂ as (? & ? & tr₂).
  destruct lr₃ as (? & ? & tr₃).
  split; [|split].
  - simpl in *.
    eauto with typing uval_typing.
  - I.crushTyping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseBoolUp_sub.
    eapply termrel_emul_ite; eauto using envrel_mono, dwp_mono with arith.
Qed.

Lemma compat_emul_app {n m d p τ₁ τ₂ Γ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p (tarr τ₁ τ₂)⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ₁ ⟫ →
  ⟪ Γ ⊩ uvalApp n ts₁ ts₂ τ₁ τ₂ ⟦ d , m ⟧ I.app tu₁ tu₂ : pEmulDV n p τ₂ ⟫.
Proof.
  intros dwp (? & ? & tr₁) (? & ? & tr₂).
  split; [|split].
  - eauto using caseArrUp_T with typing uval_typing.
  - I.crushTyping.
  - intros w wn γs γu envrel.
    unfold lev in *.

    specialize (tr₁ w wn γs γu envrel).
    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    (* change (F.app (caseArrUp n ts₁ τ₁ τ₂) ts₂)[γs] *)
    (* with (F.app (caseArrUp n ts₁ τ₁ τ₂) [γs] ts₂[γs]). *)
    (* change (I.app tu₁ tu₂)[γu] with (I.app tu₁[γu] tu₂[γu]). *)
    cbn; crush.
    rewrite uvalApp_sub; cbn; crush.

    eapply termrel_uvalApp; eauto.
    intros w' futw.
    eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_seq {n w d p τ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p tunit) ts₁ tu₁ →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p τ) ts₂ tu₂) →
  termrel d w (pEmulDV n p τ) (F.seq (caseUnitUp n ts₁) ts₂) (I.seq tu₁ tu₂).
Proof.
  intros dwp tr₁ tr₂.
  unfold caseUnitUp.

  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); F.inferContext; I.inferContext; cbn; eauto using caseUnitUp_pctx_ectx.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.

  (* do the upgrade *)
  unfold caseUnitUp_pctx; rewrite F.pctx_cat_app; cbn.
  assert (trupg : termrel d w' (pEmulDV (n + 1) p tunit) (F.app (upgrade n 1 tunit) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValUnit in vr'.
  fold (caseUnit vs').
  destruct vr' as [(? & ? & es)| (? & div)]; subst.
  - (* successful caseUValUnit *)
    eapply termrel_antired_star_left.
    eapply (F.evalstar_ctx' es); F.inferContext; crush.

    subst; cbn.
    eapply termrel_seq.
    + eauto using valrel_in_termrel, valrel_unit.
    + intros; eapply tr₂; eauto with arith.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; crush.
    now cbn.
Qed.

Lemma compat_emul_seq {n m d p Γ τ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p tunit ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ F.seq (caseUnitUp n ts₁) ts₂ ⟦ d , m ⟧ I.seq tu₁ tu₂ : pEmulDV n p τ ⟫.
Proof.
  intros dwp (? & ? & tr₁) (? & ? & tr₂).
  split; [|split];
    eauto using caseUnitUp_T with typing uval_typing.

  intros w wn γs γu envrel.

  specialize (tr₁ w wn γs γu envrel).
  assert (dir_world_prec n w d p) by eauto using dwp_mono.

  cbn; crush.
  rewrite caseUnitUp_sub.

  eapply termrel_emul_seq; eauto.
  intros w' fw; eapply tr₂; eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_inl {n w d p τ₁ τ₂ ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p τ₁) ts tu →
  termrel d w (pEmulDV n p (τ₁ r⊎ τ₂)) (inSumDwn τ₁ τ₂ n (F.inl ts)) (I.inl tu).
Proof.
  intros dwp tr.
  unfold inSumDwn.
  eapply (termrel_ectx' tr); F.inferContext; I.inferContext; crush;
  eauto using inSumDwn_pctx_ectx.
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inSumDwn; simpl; eauto using valrel_inl, dwp_mono.
Qed.

Lemma compat_emul_inl {n m d p τ₁ τ₂ Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p τ₁ ⟫ →
  ⟪ Γ ⊩ inSumDwn τ₁ τ₂ n (F.inl ts) ⟦ d , m ⟧ I.inl tu : pEmulDV n p (τ₁ r⊎ τ₂) ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crush.
  - intros w wm γs γu envrel.
    rewrite inSumDwn_sub.
    eapply termrel_emul_inl; eauto using dwp_mono.
Qed.

Lemma termrel_emul_fold_ {n w d p τ ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (τ [beta1 (trec τ)])) ts tu →
  termrel d w (pEmulDV n p (trec τ)) (inRecDwn τ n ts) (I.fold_ tu).
Proof.
  intros dwp tr.
  unfold inRecDwn.
  eapply (termrel_ectx' tr); F.inferContext; I.inferContext; crush;
  eauto using inRecDwn_pctx_ectx.
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inRecDwn; cbn; eauto using valrel_inl, dwp_mono.
Qed.

Lemma compat_emul_fold_ {n m d p τ Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (τ [beta1 (trec τ)]) ⟫ →
  ⟪ Γ ⊩ (inRecDwn τ n ts) ⟦ d , m ⟧ I.fold_ tu : pEmulDV n p (trec τ) ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crush.
  - intros w wm γs γu envrel.
    rewrite inRecDwn_sub.
    eapply termrel_emul_fold_; eauto using dwp_mono.
Qed.

Lemma termrel_emul_unfold_ {n w d p τ ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (trec τ)) ts tu →
  termrel d w (pEmulDV n p (τ [beta1 (trec τ)])) (caseRecUp n ts τ) (I.unfold_ tu).
Proof.
  intros dwp tr.
  unfold caseRecUp.
  (* evaluate terms *)
  eapply (termrel_ectx' tr); F.inferContext; I.inferContext; crush;
  eauto using caseRecUp_pctx_ectx.
  intros w' fw vs vu vr.

  (* evaluate upgrade *)
  unfold caseRecUp_pctx; rewrite F.pctx_cat_app; cbn.
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (trec τ)) (F.app (upgrade n 1 (trec τ)) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext;
    crush.

  intros w2 fw2 vs2 vu2 vr2.
  destruct (valrel_implies_OfType vr2) as [[vvs2 tvs2] [vvu2 tvu2]].
  inversion tvu2; subst; cbn in vvu2; try contradiction.
  eapply invert_valrel_pEmulDV_for_caseUValRec in vr2.
  destruct vr2 as [(vs₁' & ? & es & vr₁')|
                   (? & div)]; subst.

  - (* successful caseUValRec *)
    cbn.
    eapply termrel_antired_step.
    + fold (caseRec n (F.inl vs₁') τ).
      exact es.
    + now eapply I.eval_eval₀, eval_fold_unfold.
    + intros w3 ->.
      eauto using valrel_in_termrel.
  - (* unk case *)
    cbn.
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    unfold caseRec in div.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; crush.
Qed.

Lemma compat_emul_unfold_ {n m d p τ Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (trec τ) ⟫ →
  ⟪ Γ ⊩ (caseRecUp n ts τ) ⟦ d , m ⟧ I.unfold_ tu : pEmulDV n p (τ [beta1 (trec τ)]) ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crush.
  - intros w wm γs γu envrel.
    rewrite caseRecUp_sub.
    cbn; crush.
    eapply termrel_emul_unfold_; eauto using dwp_mono.
Qed.


Lemma termrel_emul_inr {n w d p τ₁ τ₂ ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p τ₂) ts tu →
  termrel d w (pEmulDV n p (τ₁ r⊎ τ₂)) (inSumDwn τ₁ τ₂ n (F.inr ts)) (I.inr tu).
Proof.
  intros dwp tr. unfold inSumDwn.
  eapply (termrel_ectx' tr); F.inferContext; I.inferContext; crush;
  eauto using inSumDwn_pctx_ectx.
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inSumDwn; simpl; eauto using valrel_inr, dwp_mono.
Qed.

Lemma compat_emul_inr {n m d p τ₁ τ₂ Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p τ₂ ⟫ →
  ⟪ Γ ⊩ inSumDwn τ₁ τ₂ n (F.inr ts) ⟦ d , m ⟧ I.inr tu : pEmulDV n p (τ₁ r⊎ τ₂)⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crush.
  - intros w wm γs γu envrel.
    rewrite inSumDwn_sub.
    eapply termrel_emul_inr; eauto using dwp_mono.
Qed.

Lemma termrel_emul_proj₁ {n w d p τ₁ τ₂ ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (I.tprod τ₁ τ₂)) ts tu →
  termrel d w (pEmulDV n p τ₁) (F.proj₁ (caseProdUp n ts τ₁ τ₂)) (I.proj₁ tu).
Proof.
  intros dwp tr.
  unfold caseProdUp.

  (* evaluate ts and tu *)
  eapply (termrel_ectx' tr); F.inferContext; I.inferContext; crush;
  eauto using caseProdUp_pctx_ectx; [|now cbn].

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseProdUp_pctx; rewrite F.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (I.tprod τ₁ τ₂)) (F.app (upgrade n 1 (I.tprod τ₁ τ₂)) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext; crush; [|now cbn].

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'.
  fold (caseProd n vs' τ₁ τ₂).
  destruct vr' as [(vs'' & ? & es & vr'')|
                   (? & div)].
  - eapply termrel_antired_star_left.
    eapply (F.evalstar_ctx' es); F.inferContext; now cbn.
    simpl.
    eauto using termrel_proj₁, valrel_in_termrel.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; crush; now cbn.
Qed.

Lemma compat_emul_proj₁ {n m d p Γ τ₁ τ₂ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (I.tprod τ₁ τ₂) ⟫ →
  ⟪ Γ ⊩ F.proj₁ (caseProdUp n ts τ₁ τ₂) ⟦ d , m ⟧ I.proj₁ tu : pEmulDV n p τ₁ ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - I.crushTyping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseProdUp_sub.
    eapply termrel_emul_proj₁; eauto using dwp_mono.
Qed.

Lemma termrel_emul_proj₂ {n w d p τ₁ τ₂ ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (I.tprod τ₁ τ₂)) ts tu →
  termrel d w (pEmulDV n p τ₂) (F.proj₂ (caseProdUp n ts τ₁ τ₂)) (I.proj₂ tu).
Proof.
  intros dwp tr.
  unfold caseProdUp.

  (* evaluate ts and tu *)
  eapply (termrel_ectx' tr); F.inferContext; I.inferContext; crush;
  eauto using caseProdUp_pctx_ectx; [|now cbn].

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseProdUp_pctx; rewrite F.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (τ₁ r× τ₂)) (F.app (upgrade n 1 (τ₁ r× τ₂)) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); F.inferContext; I.inferContext; crush; [|now cbn].

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'.
  fold (caseProd n vs' τ₁ τ₂).
  destruct vr' as [(vs'' & ? & es & vr'')|
                   (? & div)].
  - eapply termrel_antired_star_left.
    eapply (F.evalstar_ctx' es); F.inferContext; crush.
    simpl.
    eauto using termrel_proj₂, valrel_in_termrel.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (F.divergence_closed_under_evalcontext' div); F.inferContext; crush.
Qed.

Lemma compat_emul_proj₂ {n m d p Γ τ₁ τ₂ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (τ₁ r× τ₂) ⟫ →
  ⟪ Γ ⊩ F.proj₂ (caseProdUp n ts τ₁ τ₂) ⟦ d , m ⟧ I.proj₂ tu : pEmulDV n p τ₂ ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - I.crushTyping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseProdUp_sub.
    eapply termrel_emul_proj₂; eauto using dwp_mono.
Qed.

Fixpoint toEmulDV n p (Γ : Env) : PEnv :=
  match Γ with
      I.empty => pempty
    | Γ r▻ τ => toEmulDV n p Γ p▻ pEmulDV n p τ
  end.

Lemma toEmulDV_entry {n p Γ i τ} :
  ⟪ i : τ r∈ Γ ⟫ → ⟪ i : pEmulDV n p τ p∈ toEmulDV n p Γ ⟫.
Proof.
  induction 1; simpl; eauto using GetEvarP.
Qed.

Lemma toEmulDV_repEmulCtx {n p Γ} :
  repEmulCtx (toEmulDV n p Γ) = toUVals n Γ.
Proof.
  induction Γ; cbn; f_equal; trivial.
Qed.

Lemma toEmulDV_fxToIsCtx {n p Γ} :
  fxToIsCtx (toEmulDV n p Γ) = Γ.
Proof.
  induction Γ; cbn; f_equal; trivial.
Qed.

Lemma emulate_works { Γ tu n p d m τ} :
  dir_world_prec n m d p →
  ⟪ Γ ia⊢ tu : τ ⟫ →
  ⟪ toEmulDV n p Γ ⊩ F.eraseAnnot (emulate n tu) ⟦ d , m ⟧ eraseAnnot tu : pEmulDV n p τ ⟫.
Proof.
  intros dwp; induction 1;
    cbn;
    rewrite ?eraseAnnot_inUnitDwnA, ?eraseAnnot_inBoolDwnA, ?eraseAnnot_inProdDwnA, ?eraseAnnot_inSumDwnA, ?eraseAnnot_inArrDwnA, ?eraseAnnot_inRecDwnA, ?eraseAnnot_caseUnitUpA, ?eraseAnnot_caseBoolUpA, ?eraseAnnot_caseProdUpA, ?eraseAnnot_caseSumUpA, ?eraseAnnot_caseRecUpA, ?eraseAnnot_uvalAppA;
    eauto using compat_emul_app, compat_emul_abs, compat_var, toEmulDV_entry
    (* , compat_emul_wrong' *)
    , compat_emul_unit
    , compat_emul_true, compat_emul_false, compat_emul_pair, compat_emul_ite
    , compat_emul_inl, compat_emul_inr
    , compat_emul_fold_, compat_emul_unfold_
    , compat_emul_proj₁, compat_emul_proj₂
    , compat_emul_seq
    , compat_emul_caseof.
Qed.


Lemma emulate_pctx_works { Γ τ Γₒ τₒ Cu n p d m} :
  dir_world_prec n m d p →
  ⟪ ia⊢ Cu : Γₒ , τₒ → Γ , τ ⟫ →
  ⟪ ⊩ F.eraseAnnot_pctx (emulate_pctx n Cu) ⟦ d , m ⟧ eraseAnnot_pctx Cu : toEmulDV n p Γₒ , pEmulDV n p τₒ → toEmulDV n p Γ , pEmulDV n p τ ⟫.
Proof.
  intros dwp scp; unfold OpenLRCtxN; split; [|split].
  - simpl.
    rewrite ?toEmulDV_repEmulCtx.
    eauto using F.eraseAnnot_pctxT, emulate_pctx_T.
  - simpl.
    rewrite ?toEmulDV_fxToIsCtx.
    eauto using eraseAnnot_pctxT.
  - induction scp; cbn;
    intros ts tu lr;
    rewrite ?F.eraseAnnot_pctx_cat, ?F.pctx_cat_app;
    rewrite ?eraseAnnot_inUnitDwnA, ?eraseAnnot_inSumDwnA, ?eraseAnnot_inArrDwnA, ?eraseAnnot_inRecDwnA, ?eraseAnnot_caseUnitUpA, ?eraseAnnot_caseBoolUpA, ?eraseAnnot_caseProdUpA, ?eraseAnnot_caseSumUpA, ?eraseAnnot_caseRecUpA, ?eraseAnnot_uvalAppA;
    rewrite ?eraseAnnot_pctx_inUnitDwn_pctxA, ?eraseAnnot_pctx_inBoolDwn_pctxA, ?eraseAnnot_pctx_inProdDwn_pctxA, ?eraseAnnot_pctx_inSumDwn_pctxA, ?eraseAnnot_pctx_inArrDwn_pctxA, ?eraseAnnot_pctx_inRecDwn_pctxA, ?eraseAnnot_pctx_caseUnitUp_pctxA, ?eraseAnnot_pctx_caseBoolUp_pctxA, ?eraseAnnot_pctx_caseProdUp_pctxA, ?eraseAnnot_pctx_caseSumUp_pctxA, ?eraseAnnot_pctx_caseRecUp_pctxA, ?eraseAnnot_pctx_uvalApp_pctxA₂, ?eraseAnnot_pctx_uvalApp_pctxA₁, ?upgrade_upgradeA, ?downgrade_downgradeA;
    rewrite ?uvalApp_pctx₁_app, ?uvalApp_pctx₂_app;
    cbn;
    eauto using emulate_works
    , compat_emul_app
    , compat_emul_abs
    , compat_var
    , toEmulDV_entry
    (* , compat_emul_wrong' *)
    , compat_emul_unit
    , compat_emul_true
    , compat_emul_false
    , compat_emul_pair
    , compat_emul_ite
    , compat_emul_inl
    , compat_emul_inr
    , compat_emul_proj₁
    , compat_emul_proj₂
    , compat_emul_seq
    , compat_emul_caseof
    , compat_emul_fold_
    , compat_emul_unfold_.
    + eapply compat_emul_pair; eauto using emulate_works.
    + eapply compat_emul_pair; eauto using emulate_works.
    + eapply compat_emul_caseof; crush;
        repeat change (toEmulDV n p Γ p▻ pEmulDV n p ?τ) with (toEmulDV n p (Γ r▻ τ));
        eauto using emulate_works.
    + eapply (emulate_works dwp) in H, H0.
      eauto using emulate_works, compat_emul_caseof.
    + eapply (emulate_works dwp) in H, H0.
      eauto using emulate_works, compat_emul_caseof.
Qed.
