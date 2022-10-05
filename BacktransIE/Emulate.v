Require StlcIso.SpecSyntax.
Require StlcEqui.SpecSyntax.
Require Import BacktransIE.UValHelpers.
Require Import BacktransIE.UValHelpers2.
Require Import StlcIso.SpecTyping.
Require Import StlcEqui.SpecTyping.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecAnnot.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.LemmasTyping.
Require Import LogRelIE.PseudoType.
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

Set Asymmetric Patterns.

Fixpoint emulate (n : nat) (t : TmA) : I.TmA :=
  match t with
    ea_var x => I.ia_var x
  | ea_abs τ₁ τ₂ tb  => inArrDwnA τ₁ τ₂ n (I.ia_abs (UValIE n τ₁) (UValIE n τ₂) (emulate n tb))
  | ea_app τ₁ τ₂ t₁ t₂ => uvalAppA n (emulate n t₁) (emulate n t₂) τ₁ τ₂
  | ea_unit => inUnitDwnA n I.ia_unit
  | ea_true => inBoolDwnA n I.ia_true
  | ea_false => inBoolDwnA n I.ia_false
  | ea_ite τ t₁ t₂ t₃ => I.ia_ite (UValIE n τ) (caseBoolUpA n (emulate n t₁)) (emulate n t₂) (emulate n t₃)
  | ea_pair τ₁ τ₂ t₁ t₂ => inProdDwnA τ₁ τ₂ n (I.ia_pair (UValIE n τ₁) (UValIE n τ₂) (emulate n t₁) (emulate n t₂))
  | ea_proj₁ τ₁ τ₂ t => I.ia_proj₁ (UValIE n τ₁) (UValIE n τ₂) (caseProdUpA n (emulate n t) τ₁ τ₂)
  | ea_proj₂ τ₁ τ₂ t => I.ia_proj₂ (UValIE n τ₁) (UValIE n τ₂) (caseProdUpA n (emulate n t) τ₁ τ₂)
  | ea_inl τ₁ τ₂ t => inSumDwnA τ₁ τ₂ n (I.ia_inl (UValIE n τ₁) (UValIE n τ₂) (emulate n t))
  | ea_inr τ₁ τ₂ t => inSumDwnA τ₁ τ₂ n (I.ia_inr (UValIE n τ₁) (UValIE n τ₂) (emulate n t))
  | ea_caseof τ₁ τ₂ τ t₁ t₂ t₃ => I.ia_caseof (UValIE n τ₁) (UValIE n τ₂) (UValIE n τ) (caseSumUpA n (emulate n t₁) τ₁ τ₂) (emulate n t₂) (emulate n t₃)
  | ea_seq τ t₁ t₂ => I.ia_seq (UValIE n τ) (caseUnitUpA n (emulate n t₁)) (emulate n t₂)
  | ea_coerce τ t => emulate n t
  end.

Fixpoint emulate_pctx (n : nat) (C : PCtxA) : I.PCtxA :=
  match C with
    | ea_phole => I.ia_phole
    | ea_pabs τ₁ τ₂ C => I.pctxA_cat (I.ia_pabs (UValIE n τ₁) (UValIE n τ₂) (emulate_pctx n C)) (inArrDwn_pctxA τ₁ τ₂ n)
    | ea_papp₁ τ₁ τ₂ C t₂ => I.pctxA_cat (emulate_pctx n C) (uvalApp_pctxA₁ n (emulate n t₂) τ₁ τ₂)
    | ea_papp₂ τ₁ τ₂ t₁ C => I.pctxA_cat (emulate_pctx n C) (uvalApp_pctxA₂ n (emulate n t₁) τ₁ τ₂)
    | ea_pite₁ τ C₁ t₂ t₃ => I.ia_pite₁ (UValIE n τ) (I.pctxA_cat (emulate_pctx n C₁) (caseBoolUp_pctxA n)) (emulate n t₂) (emulate n t₃)
    | ea_pite₂ τ t₁ C₂ t₃ => I.ia_pite₂ (UValIE n τ) (caseBoolUpA n (emulate n t₁)) (emulate_pctx n C₂) (emulate n t₃)
    | ea_pite₃ τ t₁ t₂ C₃ => I.ia_pite₃ (UValIE n τ) (caseBoolUpA n (emulate n t₁)) (emulate n t₂) (emulate_pctx n C₃)
    | ea_ppair₁ τ₁ τ₂ C₁ t₂ => I.pctxA_cat (I.ia_ppair₁ (UValIE n τ₁) (UValIE n τ₂) (emulate_pctx n C₁) (emulate n t₂)) (inProdDwn_pctxA τ₁ τ₂ n)
    | ea_ppair₂ τ₁ τ₂ t₁ C₂ => I.pctxA_cat (I.ia_ppair₂ (UValIE n τ₁) (UValIE n τ₂) (emulate n t₁) (emulate_pctx n C₂)) (inProdDwn_pctxA τ₁ τ₂  n)
    | ea_pproj₁ τ₁ τ₂ C => I.ia_pproj₁ (UValIE n τ₁) (UValIE n τ₂) (I.pctxA_cat (emulate_pctx n C) (caseProdUp_pctxA n τ₁ τ₂))
    | ea_pproj₂ τ₁ τ₂ C => I.ia_pproj₂ (UValIE n τ₁) (UValIE n τ₂) (I.pctxA_cat (emulate_pctx n C) (caseProdUp_pctxA n τ₁ τ₂))
    | ea_pinl τ₁ τ₂ C => I.pctxA_cat (I.ia_pinl (UValIE n τ₁) (UValIE n τ₂) (emulate_pctx n C)) (inSumDwn_pctxA τ₁ τ₂ n)
    | ea_pinr τ₁ τ₂ C => I.pctxA_cat (I.ia_pinr (UValIE n τ₁) (UValIE n τ₂) (emulate_pctx n C)) (inSumDwn_pctxA τ₁ τ₂ n)
    | ea_pcaseof₁ τ₁ τ₂ τ C₁ t₂ t₃ => I.ia_pcaseof₁ (UValIE n τ₁) (UValIE n τ₂) (UValIE n τ) (I.pctxA_cat (emulate_pctx n C₁) (caseSumUp_pctxA n τ₁ τ₂)) (emulate n t₂) (emulate n t₃)
    | ea_pcaseof₂ τ₁ τ₂ τ t₁ C₂ t₃ => I.ia_pcaseof₂ (UValIE n τ₁) (UValIE n τ₂) (UValIE n τ) (caseSumUpA n (emulate n t₁) τ₁ τ₂) (emulate_pctx n C₂) (emulate n t₃)
    | ea_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C₃ => I.ia_pcaseof₃ (UValIE n τ₁) (UValIE n τ₂) (UValIE n τ) (caseSumUpA n (emulate n t₁) τ₁ τ₂) (emulate n t₂) (emulate_pctx n C₃)
    | ea_pseq₁ τ C₁ t₂ => I.ia_pseq₁ (UValIE n τ) (I.pctxA_cat (emulate_pctx n C₁) (caseUnitUp_pctxA n)) (emulate n t₂)
    | ea_pseq₂ τ t₁ C₂ => I.ia_pseq₂ (UValIE n τ) (caseUnitUpA n (emulate n t₁)) (emulate_pctx n C₂)
    | ea_pcoerce τ C => emulate_pctx n C
  end.

Fixpoint toUVals n (Γ : E.Env) : I.Env :=
  match Γ with
    E.empty => I.empty
  | Γ r▻ τ => toUVals n Γ r▻ UValIE n τ
  end.

Lemma toUVals_entry {n Γ i τ} :
  ⟪  i : τ r∈ Γ  ⟫ → ⟪ i : UValIE n τ r∈ toUVals n Γ ⟫.
Proof.
  induction 1; simpl; crushTyping.
Qed.

Lemma emulateT {n t Γ τ} :
  ValidEnv Γ -> ValidTy τ ->
  ⟪  Γ ea⊢ t : τ  ⟫ ->
  ⟪  toUVals n Γ ia⊢ emulate n t : UValIE n τ  ⟫.
Proof.
  intros vΓ vτ tyτ.
  revert vΓ vτ.
  induction tyτ;
  cbn; intros vΓ vτ;
    repeat match goal with
    | H : ValidTy (_ r⇒ _) |- _ => eapply ValidTy_invert_arr in H
    | H : ValidTy (_ r× _) |- _ => eapply ValidTy_invert_prod in H
    | H : ValidTy (_ r⊎ _) |- _ => eapply ValidTy_invert_sum in H
    | H1 : ?P, H2 : ?P -> _ |- _ => specialize (H2 H1)
    end; destruct_conjs;
    eauto using toUVals_entry with typing uval_typing tyvalid.
  - eapply inArrDwnA_T; crushValidTy_with_UVal.
    I.crushTypingIA; crushValidTy_with_UVal.
    eapply IHtyτ; crushValidTy_with_UVal.
  - eapply uvalAppA_T; crushValidTy_with_UVal.
    refine (typed_terms_are_valid _ _ _ (eraseAnnotT tyτ2));
      eauto with tyvalid.
    assert (vτ₁₂ := typed_terms_are_valid _ _ vΓ (eraseAnnotT tyτ1)).
    eapply IHtyτ1; crushValidTy_with_UVal.
    eapply IHtyτ2; crushValidTy_with_UVal.
    now refine (typed_terms_are_valid _ _ _ (eraseAnnotT tyτ2)).
  - constructor; eauto.
    eapply caseBoolUpA_T; eauto with tyvalid tyvalid2.
  - constructor.
    assert (vτ₁₂ := typed_terms_are_valid _ _ vΓ (eraseAnnotT tyτ)).
    eapply caseProdUpA_T; crushValidTy_with_UVal.
    eapply IHtyτ; crushValidTy_with_UVal.
  - constructor.
    assert (vτ' := typed_terms_are_valid _ _ vΓ (eraseAnnotT tyτ)).
    eapply caseProdUpA_T; crushValidTy_with_UVal.
    eapply IHtyτ; crushValidTy_with_UVal.
  - eapply inSumDwnA_T; crushValidTy_with_UVal.
    I.crushTypingIA; crushValidTy_with_UVal.
  - eapply inSumDwnA_T; crushValidTy_with_UVal.
    I.crushTypingIA; crushValidTy_with_UVal.
  - constructor; crushValidTy_with_UVal.
    eapply caseSumUpA_T; crushValidTy_with_UVal.
    eapply IHtyτ1; crushValidTy_with_UVal.
    eapply IHtyτ2; crushValidTy_with_UVal.
    eapply IHtyτ3; crushValidTy_with_UVal.
  - constructor.
    eapply caseUnitUpA_T; crushValidTy_with_UVal.
    eapply IHtyτ1; crushValidTy_with_UVal.
    eapply IHtyτ2; crushValidTy_with_UVal.
  - rewrite <-(UVal_eq H0 H1 H).
    now eapply IHtyτ.
Qed.

#[export]
Hint Resolve emulateT : uval_typing.

Lemma emulate_pctx_T {n C Γₒ τₒ Γ τ} :
  ValidEnv Γ -> ValidTy τ ->
  ⟪  ea⊢ C : Γₒ , τₒ → Γ , τ  ⟫ ->
  ⟪  ia⊢ emulate_pctx n C : toUVals n Γₒ , UValIE n τₒ → toUVals n Γ , UValIE n τ  ⟫.
Proof.
  intros vΓ vτ.
  induction 1; cbn;
    I.crushTypingIA;
    repeat match goal with
    | H : ValidTy (_ r⇒ _) |- _ => eapply ValidTy_invert_arr in H; destruct H
    | H : ValidTy (_ r× _) |- _ => eapply ValidTy_invert_prod in H; destruct H
    | H : ValidTy (_ r⊎ _) |- _ => eapply ValidTy_invert_sum in H; destruct H
    | H1 : ?P, H2 : ?P -> _ |- _ => specialize (H2 H1)
    end; destruct_conjs;
    crushValidTy_with_UVal;
    try change (toUVals n ?Γ r▻ UValIE n ?τ) with (toUVals n (Γ r▻ τ));
    eauto using emulateT, inArrDwn_pctx_T with typing uval_typing tyvalid tyvalid2.
  - assert (vτ₁ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H1)).
    eauto using emulateT, inArrDwn_pctx_T with typing uval_typing tyvalid tyvalid2.
  - assert (vτ₁ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H1)).
    eauto using emulateT, inArrDwn_pctx_T with typing uval_typing tyvalid tyvalid2.
  - rewrite <-(UVal_eq H1 H2 H).
    eauto using emulateT, inArrDwn_pctx_T with typing uval_typing tyvalid tyvalid2.
Qed.

Local Ltac crush :=
  repeat (repeat E.crushStlcSyntaxMatchH;
          repeat I.crushStlcSyntaxMatchH;
          repeat I.crushStlcEval;
          repeat E.crushStlcEval;
          (* repeat crushUtlcEvaluationMatchH; *)
          (* repeat crushUtlcEvaluationMatchH2; *)
          (* repeat crushUtlcEvaluationMatchH2; *)
          repeat E.crushTypingMatchH;
          repeat E.crushTypingMatchH2;
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
  ⟪ Γ ⊩ inUnitDwn n I.unit ⟦ d , m ⟧ E.unit : pEmulDV n p tunit ⟫.
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
  ⟪ Γ ⊩ inBoolDwn n I.true ⟦ d , m ⟧ E.true : pEmulDV n p tbool ⟫.
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
  ⟪ Γ ⊩ inBoolDwn n I.false ⟦ d , m ⟧ E.false : pEmulDV n p tbool ⟫.
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
  ValidPEnv Γ -> ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ p▻ pEmulDV n p τ₁ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p τ₂ ⟫ →
  ⟪ Γ ⊩ inArrDwn τ₁ τ₂ n (I.abs (UValIE n τ₁) ts) ⟦ d , m ⟧ E.abs τ₁ tu : pEmulDV n p (E.tarr τ₁ τ₂) ⟫.
Proof.
  intros vΓ vτ₁ vτ₂ dwp [ty [closed tr]].
  split; [|split].
  - eauto using UValIE_valid, inArrDwn_T with typing uval_typing tyvalid.
  - crush.
  - intros w wn γs γu envrel.

    assert (OfType (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂))
                   (I.abs (repEmul (pEmulDV n p τ₁))
                          (ts [γs↑])) (E.abs τ₁ (tu [γu↑]))).
    { pose proof (envrel_implies_WtSub_iso envrel).
      pose proof (envrel_implies_WtSub_equi envrel).
      crush.
      eapply tyeq_refl.
      I.crushTyping; crushValidTy_with_UVal.
    }

    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    rewrite inArrDwn_sub; try assumption.
    eapply termrel₀_in_termrel.
    eapply termrel₀_inArrDwn; try assumption.

    change (UValIE n τ₁) with (repEmul (pEmulDV n p τ₁)).

    refine (valrel_lambda _ _ _ _ _ _); crush; try crushValidPTyMatch; crushValidTy_with_UVal; [eapply tyeq_refl|].

    intros w' vs vu futw sz valrel.
    fold I.apTm E.apTm.
    crush.
    rewrite ?ap_comp.

    assert (lev w' ≤ m) by (unfold lev in *; lia).
    eapply tr;
      eauto using extend_envrel, envrel_mono.
Qed.

(* Lemma compat_emul_pabs {n m d p Γ} : *)
(*   dir_world_prec n m d p → *)
(*   ⟪ ⊩ I.pctx_cat (I.pabs (UVal n) I.phole) (inArrDwn_pctx n) ⟦ d , m ⟧ E.pabs E.phole : Γ p▻ pEmulDV n p , pEmulDV n p → Γ , pEmulDV n p ⟫. *)
(* Proof. *)
(*   intros dwp. *)
(*   split. *)
(*   - eauto using inArrDwn_pctx_T with typing uval_typing. *)
(*   - intros ts tu lr. *)
(*     change (I.pctx_app ts (I.pctx_cat (I.pabs (UVal n) I.phole) (inArrDwn_pctx n))) *)
(*     with (inArrDwn n (I.abs (UVal n) ts)). *)
(*     eauto using compat_emul_abs. *)
(* Qed. *)

Lemma compat_emul_pair {n m d p Γ τ₁ τ₂ ts₁ tu₁ ts₂ tu₂} :
  ValidPEnv Γ -> ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p τ₁ ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ₂ ⟫ →
  ⟪ Γ ⊩ inProdDwn τ₁ τ₂ n (I.pair ts₁ ts₂) ⟦ d , m ⟧ E.pair tu₁ tu₂ : pEmulDV n p (E.tprod τ₁ τ₂)⟫.
Proof.
  intros vΓ vτ₁ vτ₂ dwp tr₁ tr₂.
  destruct tr₁ as (? & ? & tr₁).
  destruct tr₂ as (? & ? & tr₂).
  split; [|split].
  - eauto using inProdDwn_T with typing uval_typing.
  - E.crushTyping.
  - intros w wm γs γu envrel.
    rewrite inProdDwn_sub; try assumption.
    enough (termrel d w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) (I.pair ts₁ ts₂)[γs] (E.pair tu₁ tu₂)[γu]) as trp.
    + eapply (termrel_ectx' trp); I.inferContext; E.inferContext; simpl; crush.
      intros w' futw vs vu vr.
      eapply termrel₀_in_termrel.
      eapply termrel₀_inProdDwn;
        eauto using dwp_mono with arith.
    + eapply termrel_pair;
        fold I.apTm E.apTm; crush; try crushValidPTyMatch; crushValidTy.
      intros w' fw; eapply tr₂; eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_caseof {n w d p τ₁ τ₂ τ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  ValidTy τ₁ -> ValidTy τ₂ -> ValidTy τ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (tsum τ₁ τ₂)) ts₁ tu₁ →
  (forall w' vs₂ vu₂, w' ≤ w →
                      valrel d w' (pEmulDV n p τ₁) vs₂ vu₂ →
                      termrel d w' (pEmulDV n p τ) (ts₂ [beta1 vs₂]) (tu₂ [beta1 vu₂])) →
  (forall w' vs₃ vu₃, w' ≤ w →
                      valrel d w' (pEmulDV n p τ₂) vs₃ vu₃ →
                      termrel d w' (pEmulDV n p τ) (ts₃ [beta1 vs₃]) (tu₃ [beta1 vu₃])) →
  termrel d w (pEmulDV n p τ) (I.caseof (caseSumUp n ts₁ τ₁ τ₂) ts₂ ts₃) (E.caseof tu₁ tu₂ tu₃).
Proof.
  intros vτ₁ vτ₂ vτ dwp tr₁ tr₂ tr₃.
  unfold caseSumUp.
  (* evaluate ts₁ and ts₂ *)
  eapply (termrel_ectx' tr₁); I.inferContext; E.inferContext; crush;
  eauto using caseSumUp_pctx_ectx; try now cbn.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseSumUp_pctx; rewrite I.pctx_cat_app; crush; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (τ₁ r⊎ τ₂)) (I.app (upgrade n 1 (τ₁ r⊎ τ₂)) vs) vu) by
    (eauto using upgrade_works', dwp_mono with tyvalid).
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); I.inferContext; E.inferContext;
    crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  fold (caseSum n vs' τ₁ τ₂); cbn.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValSum in vr'; try assumption.
  destruct vr' as [(vs₁' & ? & es & vr₁')|
                   (? & div)]; subst.

  - (* successful caseUValSum *)
    eapply termrel_antired_star_left.
    eapply (I.evalstar_ctx' es); I.inferContext; crush.

    cbn.
    eapply termrel_caseof;
      eauto using valrel_in_termrel with tyvalid; try crushValidPTyMatch; crushValidTy_with_UVal.
    + intros w''' vs₂' vu₂' fw'' vr₂. eapply tr₂; eauto with arith.
    + intros w''' vs₃' vu₃' fw'' vr₃. eapply tr₃; eauto with arith.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (I.divergence_closed_under_evalcontext' div); I.inferContext; crush.
Qed.

Lemma compat_emul_caseof {n m d p τ₁ τ₂ τ Γ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  ValidPEnv Γ -> ValidTy τ₁ -> ValidTy τ₂ -> ValidTy τ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p (τ₁ r⊎ τ₂) ⟫ →
  ⟪ Γ p▻ pEmulDV n p τ₁ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ ⟫ →
  ⟪ Γ p▻ pEmulDV n p τ₂ ⊩ ts₃ ⟦ d , m ⟧ tu₃ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ I.caseof (caseSumUp n ts₁ τ₁ τ₂) ts₂ ts₃ ⟦ d , m ⟧ E.caseof tu₁ tu₂ tu₃ : pEmulDV n p τ ⟫.
Proof.
  intros vΓ vτ₁ vτ₂ vτ dwp lr₁ lr₂ lr₃.
  destruct lr₁ as (? & ? & tr₁).
  destruct lr₂ as (? & ? & tr₂).
  destruct lr₃ as (? & ? & tr₃).
  split; [|split].
  - I.crushTyping; eauto using UValIE_valid with typing uval_typing tyvalid.
  - crush.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseSumUp_sub; try assumption.
    eapply termrel_emul_caseof;
      eauto using envrel_mono, dwp_mono with arith;
      intros w' vs₂ vu₂ fw vr₂;
      rewrite ?ap_comp;
      assert (lev w' ≤ m) by (unfold lev in *; lia);
      [eapply tr₂|eapply tr₃];
      eauto using extend_envrel, envrel_mono.
Qed.

Lemma termrel_emul_ite {n w d p τ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  ValidTy τ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p tbool) ts₁ tu₁ →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p τ) ts₂ tu₂) →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p τ) ts₃ tu₃) →
  termrel d w (pEmulDV n p τ) (I.ite (caseBoolUp n ts₁) ts₂ ts₃) (E.ite tu₁ tu₂ tu₃).
Proof.
  intros vτ dwp tr₁ tr₂ tr₃.
  unfold caseBoolUp.
  (* evaluate ts₁ and ts₂ *)
  eapply (termrel_ectx' tr₁); I.inferContext; E.inferContext; crush;
  eauto using caseBoolUp_pctx_ectx; [|now cbn].

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseBoolUp_pctx; rewrite I.pctx_cat_app; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p tbool) (I.app (upgrade n 1 tbool) vs) vu)
    by eauto using upgrade_works', dwp_mono with tyvalid.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); I.inferContext; E.inferContext; crush; [|now cbn].

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
    eapply (I.evalstar_ctx' es); I.inferContext; crush.

    now cbn.
    eapply termrel_ite; eauto using valrel_in_termrel.
    + intros w''' fw''. eapply tr₂; lia.
    + intros w''' fw''. eapply tr₃; lia.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (I.divergence_closed_under_evalcontext' div); I.inferContext; crush.
    now cbn.
Qed.

Lemma compat_emul_ite {n m d p Γ τ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  ValidPEnv Γ -> ValidTy τ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p tbool ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ ts₃ ⟦ d , m ⟧ tu₃ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ I.ite (caseBoolUp n ts₁) ts₂ ts₃ ⟦ d , m ⟧ E.ite tu₁ tu₂ tu₃ : pEmulDV n p τ ⟫.
Proof.
  intros vΓ vτ dwp lr₁ lr₂ lr₃.
  destruct lr₁ as (? & ? & tr₁).
  destruct lr₂ as (? & ? & tr₂).
  destruct lr₃ as (? & ? & tr₃).
  split; [|split].
  - simpl in *.
    eauto with typing uval_typing.
  - E.crushTyping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseBoolUp_sub.
    eapply termrel_emul_ite; eauto using envrel_mono, dwp_mono with tyvalid arith.
Qed.

Lemma compat_emul_app {n m d p τ₁ τ₂ Γ ts₁ tu₁ ts₂ tu₂} :
  ValidPEnv Γ -> ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p (tarr τ₁ τ₂)⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ₁ ⟫ →
  ⟪ Γ ⊩ uvalApp n ts₁ ts₂ τ₁ τ₂ ⟦ d , m ⟧ E.app tu₁ tu₂ : pEmulDV n p τ₂ ⟫.
Proof.
  intros vΓ vτ₁ vτ₂ dwp (? & ? & tr₁) (? & ? & tr₂).
  split; [|split].
  - eauto using caseArrUp_T with typing uval_typing.
  - E.crushTyping.
  - intros w wn γs γu envrel.
    unfold lev in *.

    specialize (tr₁ w wn γs γu envrel).
    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    (* change (I.app (caseArrUp n ts₁ τ₁ τ₂) ts₂)[γs] *)
    (* with (I.app (caseArrUp n ts₁ τ₁ τ₂) [γs] ts₂[γs]). *)
    (* change (E.app tu₁ tu₂)[γu] with (E.app tu₁[γu] tu₂[γu]). *)
    cbn; crush.
    rewrite uvalApp_sub; cbn; crush.

    eapply termrel_uvalApp; eauto.
    intros w' futw.
    eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_seq {n w d p τ ts₁ tu₁ ts₂ tu₂} :
  ValidTy τ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p tunit) ts₁ tu₁ →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p τ) ts₂ tu₂) →
  termrel d w (pEmulDV n p τ) (I.seq (caseUnitUp n ts₁) ts₂) (E.seq tu₁ tu₂).
Proof.
  intros vτ dwp tr₁ tr₂.
  unfold caseUnitUp.

  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); I.inferContext; E.inferContext; cbn; eauto using caseUnitUp_pctx_ectx.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.

  (* do the upgrade *)
  unfold caseUnitUp_pctx; rewrite I.pctx_cat_app; cbn.
  assert (trupg : termrel d w' (pEmulDV (n + 1) p tunit) (I.app (upgrade n 1 tunit) vs) vu)
    by eauto using upgrade_works', dwp_mono with tyvalid.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); I.inferContext; E.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValUnit in vr'.
  fold (caseUnit vs').
  destruct vr' as [(? & ? & es)| (? & div)]; subst.
  - (* successful caseUValUnit *)
    eapply termrel_antired_star_left.
    eapply (I.evalstar_ctx' es); I.inferContext; crush.

    subst; cbn.
    eapply termrel_seq; try crushValidPTyMatch; crushValidTy_with_UVal; try try_typed_terms_are_valid.
    + eauto using valrel_in_termrel, valrel_unit.
    + intros; eapply tr₂; eauto with arith.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (I.divergence_closed_under_evalcontext' div); I.inferContext; crush.
    now cbn.
Qed.

Lemma compat_emul_seq {n m d p Γ τ ts₁ tu₁ ts₂ tu₂} :
  ValidPEnv Γ -> ValidTy τ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p tunit ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p τ ⟫ →
  ⟪ Γ ⊩ I.seq (caseUnitUp n ts₁) ts₂ ⟦ d , m ⟧ E.seq tu₁ tu₂ : pEmulDV n p τ ⟫.
Proof.
  intros vΓ vτ dwp (? & ? & tr₁) (? & ? & tr₂).
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
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p τ₁) ts tu →
  termrel d w (pEmulDV n p (τ₁ r⊎ τ₂)) (inSumDwn τ₁ τ₂ n (I.inl ts)) (E.inl tu).
Proof.
  intros vτ₁ vτ₂ dwp tr.
  unfold inSumDwn.
  eapply (termrel_ectx' tr); I.inferContext; E.inferContext; crush;
  eauto using inSumDwn_pctx_ectx.
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inSumDwn; eauto using valrel_inl, dwp_mono with tyvalid.
  eapply valrel_inl; try crushValidPTyMatch; crushValidTy.
Qed.

Lemma compat_emul_inl {n m d p τ₁ τ₂ Γ ts tu} :
  ValidPEnv Γ -> ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p τ₁ ⟫ →
  ⟪ Γ ⊩ inSumDwn τ₁ τ₂ n (I.inl ts) ⟦ d , m ⟧ E.inl tu : pEmulDV n p (τ₁ r⊎ τ₂) ⟫.
Proof.
  intros vΓ vτ₁ vτ₂ dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing tyvalid ptyvalid.
    eapply inSumDwn_T; I.crushTyping; crushValidTy_with_UVal.
  - crush.
  - intros w wm γs γu envrel.
    rewrite inSumDwn_sub; try assumption.
    eapply termrel_emul_inl; eauto using dwp_mono with tyvalid.
Qed.

Lemma termrel_emul_fold_ {n w d p τ ts tu} :
  ValidTy (trec τ) ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (τ [beta1 (trec τ)])) ts tu →
  termrel d w (pEmulDV n p (trec τ)) (inRecDwn τ n ts) tu.
Proof.
  intros vτ dwp tr.
  unfold inRecDwn.
  eapply (termrel_ectx' tr); I.inferContext; E.inferContext; crush;
  eauto using inRecDwn_pctx_ectx.
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inRecDwn; cbn; eauto using valrel_inl, dwp_mono.
Qed.

Lemma compat_emul_fold_ {n m d p τ Γ ts tu} :
  ValidTy (trec τ) ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (τ [beta1 (trec τ)]) ⟫ →
  ⟪ Γ ⊩ (inRecDwn τ n ts) ⟦ d , m ⟧ tu : pEmulDV n p (trec τ) ⟫.
Proof.
  intros vτ dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crush.
    cbn.
    refine (WtEq _ _ _ _ H0); cbn; eauto with tyvalid.
    + eapply EqMuR, tyeq_refl.
    + refine (ValidTy_unfoldOnce vτ).
  - intros w wm γs γu envrel.
    rewrite inRecDwn_sub.
    eapply termrel_emul_fold_; eauto using dwp_mono.
Qed.

Lemma termrel_emul_unfold_ {n w d p τ ts tu} :
  ValidTy (trec τ) ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (trec τ)) ts tu →
  termrel d w (pEmulDV n p (τ [beta1 (trec τ)])) (caseRecUp n ts τ) tu.
Proof.
  intros vτ dwp tr.
  unfold caseRecUp.

  assert (vτ' := ValidTy_unfoldOnce vτ); cbn in vτ'.
  (* evaluate terms *)
  eapply (termrel_ectx' tr); I.inferContext; E.inferContext; crush;
  eauto using caseRecUp_pctx_ectx.
  intros w' fw vs vu vr.

  unfold caseRecUp_pctx.
  cbn.
  eapply valrel_in_termrel.
  rewrite valrel_pEmulDV_unfoldn; try assumption.
  rewrite valrel_pEmulDV_unfoldn in vr; try assumption.
  cbn in vr.
  change (LMC τ[beta1 (trec τ)]) with (LMC (unfoldOnce (trec τ))).
  rewrite LMC_unfoldOnce; crushValidTy.
  cbn; lia.
Qed.

(* Lemma compat_emul_unfold_ {n m d p τ Γ ts tu} : *)
(*   ValidTy (trec τ) -> *)
(*   dir_world_prec n m d p → *)
(*   ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (trec τ) ⟫ → *)
(*   ⟪ Γ ⊩ (caseRecUp n ts τ) ⟦ d , m ⟧ tu : pEmulDV n p (τ [beta1 (trec τ)]) ⟫. *)
(* Proof. *)
(*   intros vτ dwp lr. *)
(*   destruct lr as (? & ? & tr). *)
(*   split; [|split]. *)
(*   - simpl in *. *)
(*     eauto using inSumDwn_T with typing uval_typing. *)
(*   - cbn in *. *)
(*     refine (WtEq _ _ _ _ H0); cbn; eauto with tyvalid. *)
(*     + eapply EqMuL, tyeq_refl. *)
(*     + refine (ValidTy_unfoldOnce vτ). *)
(*   - intros w wm γs γu envrel. *)
(*     rewrite caseRecUp_sub. *)
(*     cbn; crush. *)
(*     eapply termrel_emul_unfold_; eauto using dwp_mono. *)
(* Qed. *)

Lemma compat_emul_unfold_ {n m d p τ Γ ts tu} :
  ValidTy (trec τ) ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (trec τ) ⟫ →
  ⟪ Γ ⊩ (caseRecUp n ts τ) ⟦ d , m ⟧ tu : pEmulDV n p (τ [beta1 (trec τ)]) ⟫.
Proof.
  intros vτ dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - cbn in *.
    refine (WtEq _ _ _ _ H0); cbn; eauto with tyvalid.
    + eapply EqMuL, tyeq_refl.
    + refine (ValidTy_unfoldOnce vτ).
  - intros w wm γs γu envrel.
    rewrite caseRecUp_sub.
    cbn; crush.
    eapply termrel_emul_unfold_; eauto using dwp_mono.
Qed.


Lemma termrel_emul_inr {n w d p τ₁ τ₂ ts tu} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p τ₂) ts tu →
  termrel d w (pEmulDV n p (τ₁ r⊎ τ₂)) (inSumDwn τ₁ τ₂ n (I.inr ts)) (E.inr tu).
Proof.
  intros vτ₁ vτ₂ dwp tr. unfold inSumDwn.
  eapply (termrel_ectx' tr); I.inferContext; E.inferContext; crush;
  eauto using inSumDwn_pctx_ectx.
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inSumDwn;
  eauto using dwp_mono.
  eapply valrel_inr; try crushValidPTyMatch; crush.
Qed.

Lemma compat_emul_inr {n m d p τ₁ τ₂ Γ ts tu} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p τ₂ ⟫ →
  ⟪ Γ ⊩ inSumDwn τ₁ τ₂ n (I.inr ts) ⟦ d , m ⟧ E.inr tu : pEmulDV n p (τ₁ r⊎ τ₂)⟫.
Proof.
  intros vτ₁ vτ₂ dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T, UValIE_valid with typing uval_typing tyvalid ptyvalid.
  - crush.
  - intros w wm γs γu envrel.
    rewrite inSumDwn_sub; try assumption.
    eapply termrel_emul_inr; eauto using dwp_mono.
Qed.

Lemma termrel_emul_proj₁ {n w d p τ₁ τ₂ ts tu} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (E.tprod τ₁ τ₂)) ts tu →
  termrel d w (pEmulDV n p τ₁) (I.proj₁ (caseProdUp n ts τ₁ τ₂)) (E.proj₁ tu).
Proof.
  intros vτ₁ vτ₂ dwp tr.
  unfold caseProdUp.

  (* evaluate ts and tu *)
  eapply (termrel_ectx' tr); I.inferContext; E.inferContext; crush;
  eauto using caseProdUp_pctx_ectx; [|now cbn].

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseProdUp_pctx; rewrite I.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (E.tprod τ₁ τ₂)) (I.app (upgrade n 1 (E.tprod τ₁ τ₂)) vs) vu)
    by eauto using upgrade_works', dwp_mono with tyvalid.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); I.inferContext; E.inferContext; crush; [|now cbn].

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'; try assumption.
  fold (caseProd n vs' τ₁ τ₂).
  destruct vr' as [(vs'' & ? & es & vr'')|
                   (? & div)].
  - eapply termrel_antired_star_left.
    eapply (I.evalstar_ctx' es); I.inferContext; now cbn.
    simpl.
    eapply valrel_in_termrel in vr''.
    refine (termrel_proj₁ _ _ vr''); cbn; try crushValidPTyMatch; eauto with tyvalid ptyvalid.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (I.divergence_closed_under_evalcontext' div); I.inferContext; crush; now cbn.
Qed.

Lemma compat_emul_proj₁ {n m d p Γ τ₁ τ₂ ts tu} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (E.tprod τ₁ τ₂) ⟫ →
  ⟪ Γ ⊩ I.proj₁ (caseProdUp n ts τ₁ τ₂) ⟦ d , m ⟧ E.proj₁ tu : pEmulDV n p τ₁ ⟫.
Proof.
  intros vτ₁ vτ₂ dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - E.crushTyping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseProdUp_sub; try assumption.
    eapply termrel_emul_proj₁; eauto using dwp_mono with tyvalid.
Qed.

Lemma termrel_emul_proj₂ {n w d p τ₁ τ₂ ts tu} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p (E.tprod τ₁ τ₂)) ts tu →
  termrel d w (pEmulDV n p τ₂) (I.proj₂ (caseProdUp n ts τ₁ τ₂)) (E.proj₂ tu).
Proof.
  intros vτ₁ vτ₂ dwp tr.
  unfold caseProdUp.

  (* evaluate ts and tu *)
  eapply (termrel_ectx' tr); I.inferContext; E.inferContext; crush;
  eauto using caseProdUp_pctx_ectx; [|now cbn].

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseProdUp_pctx; rewrite I.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p (τ₁ r× τ₂)) (I.app (upgrade n 1 (τ₁ r× τ₂)) vs) vu)
    by eauto using upgrade_works', dwp_mono with tyvalid.
  replace (n + 1) with (S n) in trupg by lia.
  eapply (termrel_ectx' trupg); I.inferContext; E.inferContext; crush; [|now cbn].

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'; try assumption.
  fold (caseProd n vs' τ₁ τ₂).
  destruct vr' as [(vs'' & ? & es & vr'')|
                   (? & div)].
  - eapply termrel_antired_star_left.
    eapply (I.evalstar_ctx' es); I.inferContext; crush.
    now cbn.
    eapply valrel_in_termrel in vr''.
    refine (termrel_proj₂ _ _ vr''); try crushValidPTyMatch; eauto with tyvalid ptyvalid.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (I.divergence_closed_under_evalcontext' div); I.inferContext; crush.
    now cbn.
Qed.

Lemma compat_emul_proj₂ {n m d p Γ τ₁ τ₂ ts tu} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p (τ₁ r× τ₂) ⟫ →
  ⟪ Γ ⊩ I.proj₂ (caseProdUp n ts τ₁ τ₂) ⟦ d , m ⟧ E.proj₂ tu : pEmulDV n p τ₂ ⟫.
Proof.
  intros vτ₁ vτ₂ dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - E.crushTyping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseProdUp_sub; try assumption.
    eapply termrel_emul_proj₂; eauto using dwp_mono with tyvalid.
Qed.

Fixpoint toEmulDV n p (Γ : Env) : PEnv :=
  match Γ with
      E.empty => pempty
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

Lemma toEmulDV_isToEqCtx {n p Γ} :
  isToEqCtx (toEmulDV n p Γ) = Γ.
Proof.
  induction Γ; cbn; f_equal; trivial.
Qed.

Lemma ValidPEnv_toEmulDV {n p Γ} :
  ValidEnv Γ ->
  ValidPEnv (toEmulDV n p Γ).
Proof.
  induction Γ; cbn; eauto using ValidPEnv_nil.
  intros (vΓ & vτ)%ValidEnv_invert_cons.
  eapply ValidPEnv_cons; try crushValidPTyMatch; eauto.
Qed.

Lemma emulate_works { Γ tu n p d m τ} :
  ValidEnv Γ -> ValidTy τ ->
  dir_world_prec n m d p →
  ⟪ Γ ea⊢ tu : τ ⟫ →
  ⟪ toEmulDV n p Γ ⊩ I.eraseAnnot (emulate n tu) ⟦ d , m ⟧ eraseAnnot tu : pEmulDV n p τ ⟫.
Proof.
  intros vΓ vτ dwp; induction 1;
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
    , compat_emul_caseof
    , ValidPEnv_toEmulDV
    with tyvalid2.
  - destruct (ValidTy_invert_arr vτ) as [vτ₁ vτ₂].
    eapply compat_emul_abs; eauto using ValidPEnv_toEmulDV with tyvalid.
  - assert (vτ₁ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H0)).
    assert (vτ₁₂ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H)).
    eapply compat_emul_app; eauto using ValidPEnv_toEmulDV with tyvalid.
  - eapply compat_emul_ite; eauto using ValidPEnv_toEmulDV with tyvalid.
  - assert (vτ₁₂ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H)).
    eapply compat_emul_proj₁; eauto using ValidPEnv_toEmulDV with tyvalid2.
  - assert (vτ₁₂ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H)).
    eapply compat_emul_proj₂; eauto using ValidPEnv_toEmulDV with tyvalid2.
  - eapply compat_emul_caseof; eauto using ValidPEnv_toEmulDV with tyvalid2.
    eapply IHAnnotTyping2; eauto using ValidPEnv_toEmulDV, ValidPEnv_cons, ValidEnv_cons with tyvalid2.
    eapply IHAnnotTyping3; eauto using ValidPEnv_toEmulDV, ValidPEnv_cons, ValidEnv_cons with tyvalid2.
  - eapply (compat_type_eq H0 H1 H); intuition.
Qed.


Lemma emulate_pctx_works { Γ τ Γₒ τₒ Cu n p d m} :
  dir_world_prec n m d p →
  ValidEnv Γ -> ValidTy τ ->
  ⟪ ea⊢ Cu : Γₒ , τₒ → Γ , τ ⟫ →
  ⟪ ⊩ I.eraseAnnot_pctx (emulate_pctx n Cu) ⟦ d , m ⟧ eraseAnnot_pctx Cu : toEmulDV n p Γₒ , pEmulDV n p τₒ → toEmulDV n p Γ , pEmulDV n p τ ⟫.
Proof.
  intros dwp vΓ vτ scp; unfold OpenLRCtxN; split; [|split].
  - simpl.
    rewrite ?toEmulDV_repEmulCtx.
    eauto using I.eraseAnnot_pctxT, emulate_pctx_T.
  - simpl.
    rewrite ?toEmulDV_isToEqCtx.
    eauto using eraseAnnot_pctxT.
  - induction scp; cbn;
    intros ts tu lr;
    rewrite ?I.eraseAnnot_pctx_cat, ?I.pctx_cat_app;
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
    , compat_emul_unfold_
    , ValidPEnv_toEmulDV
      , ValidEnv_cons
      with tyvalid2.
    + assert (vτ₁ := typed_terms_are_valid _ _ vΓ (eraseAnnotT H0)).
      eapply compat_emul_app; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons.
      eapply IHscp; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply compat_emul_ite; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply compat_emul_ite; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply compat_emul_ite; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply compat_emul_pair; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply compat_emul_pair; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply emulate_works in H, H0; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
      eapply compat_emul_caseof; crush;
        repeat change (toEmulDV n p Γ p▻ pEmulDV n p ?τ) with (toEmulDV n p (Γ r▻ τ))
      ; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply emulate_works in H, H0; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
      eauto using emulate_works, compat_emul_caseof, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply emulate_works in H, H0; eauto using emulate_works, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
      eauto using emulate_works, compat_emul_caseof, ValidPEnv_toEmulDV, ValidEnv_cons with tyvalid2.
    + eapply (compat_type_eq H0 H1 H); intuition.
Qed.

Print Assumptions emulate_pctx_works.
