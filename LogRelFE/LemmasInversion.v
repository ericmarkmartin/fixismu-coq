Require Import Common.Common.
Require Import LogRelFE.PseudoTypeFE.
Require Import LogRelFE.LemmasPseudoType.
Require Import LogRelFE.LR.
Require Import LogRelFE.LemmasLR.
Require Import LogRelFE.LemmasIntro.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.CanForm.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.Size.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.Inst.
Require Import UValFE.UVal.

Require Import Lia.
Require Import Min.

Section ValrelInversion.

  Local Ltac crush :=
    repeat
      (cbn in * |-; cbn;
       try assumption;
       crushOfType;
       repeat E.crushTyping;
       repeat F.crushTyping;
       repeat E.crushStlcSyntaxMatchH;
       repeat F.crushStlcSyntaxMatchH;
       (* repeat crushUtlcScopingMatchH; *)
       repeat crushDbSyntaxMatchH;
       try subst;
       destruct_conjs;
       repeat match goal with
                  [ |- _ ∧ _ ] => split
              end;
       eauto
      );
    try discriminate;
    eauto with eval;
    try lia.

  Lemma valrel_ptunit_inversion {d w vs vu} :
    valrel d w ptunit vs vu →
    vs = F.unit ∧ vu = E.unit.
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    tauto.
  Qed.

  (* Lemma valrel_ptbool_inversion {d w vs vu} : *)
  (*   valrel d w ptbool vs vu → *)
  (*   (vs = S.true ∧ vu = U.true) ∨ (vs = S.false ∧ vu = U.false). *)
  (* Proof. *)
  (*   rewrite valrel_fixp; unfold valrel'. *)
  (*   crush. *)
  (* Qed. *)

  Lemma valrel_ptprod_inversion {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w (ptprod τ₁ τ₂) vs vu →
    exists vs₁ vs₂ vu₁ vu₂,
      (vs = F.pair vs₁ vs₂ ∧ vu = E.pair vu₁ vu₂ ∧
       OfType τ₁ vs₁ vu₁ ∧
       OfType τ₂ vs₂ vu₂ ∧
       ∀ w', w' < w → valrel d w' τ₁ vs₁ vu₁ ∧ valrel d w' τ₂ vs₂ vu₂).
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (OfType_inversion_ptprod vτ₁ vτ₂ (valrel_implies_OfType vr))
      as (ts1' & tu1' & ts2' & tu2' & Hvs & Hvu & oft1 & oft2).
    exists ts1', ts2', tu1', tu2';
    rewrite -> valrel_fixp in vr;
    unfold valrel' in vr; crush.
  Qed.

  Lemma valrel_ptsum_inversion {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w (ptsum τ₁ τ₂) vs vu →
    exists vs' vu',
      (vs = F.inl vs' ∧ vu = E.inl vu' ∧
       OfType τ₁ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₁ vs' vu') ∨
      (vs = F.inr vs' ∧ vu = E.inr vu' ∧
       OfType τ₂ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₂ vs' vu').
  Proof.
    intros vτ₁ vτ₂ vr.
    rewrite -> valrel_fixp in vr; destruct vr as [oft sumrel];
    apply OfType_inversion_ptsum in oft;
    destruct oft as (tsb & tub & Hvs); intuition; crush;
    exists tsb, tub; crush.
  Qed.

  Lemma valrel_ptarr_inversion {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w (ptarr τ₁ τ₂) vs vu →
    ∃ tsb tub τ,
      vs = F.abs (repEmul τ₁) tsb ∧ vu = E.abs τ tub ∧
      ValidTy τ /\
      ⟪ τ ≗ fxToIs τ₁ ⟫ /\
      ⟪ F.empty ▻ repEmul τ₁ ⊢ tsb : repEmul τ₂ ⟫ ∧
      ⟪ E.empty r▻ fxToIs τ₁ e⊢ tub : fxToIs τ₂ ⟫ ∧
      ∀ w' vs' vu',
        w' < w →
        (d = dir_gt -> E.size vu' <= w') ->
        valrel d w' τ₁ vs' vu' →
        termrel d w' τ₂ (tsb[beta1 vs']) (tub[beta1 vu']).
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_Value vr) as [? ?].
    destruct (OfType_inversion_ptarr vτ₁ vτ₂ (valrel_implies_OfType vr))
      as (tsb & tub & τ & ? & ? & ?).
    exists tsb, tub, τ; crush.
    rewrite -> valrel_fixp in vr.
    unfold valrel' in vr; unfold termrel; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_zero {dir w p vs vu τ} :
    valrel dir w (pEmulDV 0 p τ) vs vu →
    OfType (pEmulDV 0 p τ) vs vu ∧ vs = F.unit ∧ p = imprecise.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    tauto.
  Qed.

  Lemma invert_valrel_pEmulDV_unk {dir w n p vu τ} :
    valrel dir w (pEmulDV (S n) p τ) (F.inr F.unit) vu →
    p = imprecise.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as (ot & [(? & ?) | ?]).
    - assumption.
    - destruct (unfoldn (LMC τ) τ); destruct_conjs; unfold is_inl in H0; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p E.tunit) (F.inl vs) vu →
    vs = F.unit ∧ vu = E.unit.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    unfold valrel' in vr.
    destruct vr as (ot & [(? & ?) | ?]);
      try (destruct H as [? H']; unfold is_inl in H');
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p E.tunit) (F.inl vs) vu →
    valrel dir w ptunit vs vu.
  Proof.
    intros vr.
    destruct (invert_valrel_pEmulDV_inUnit' vr); subst.
    apply valrel_unit.
  Qed.

  Lemma invert_valrel_pEmulDV_unit {dir w n p vs vu} :
   valrel dir w (pEmulDV (S n) p E.tunit) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    ∃ vs', (vs = F.inl vs' ∧ valrel dir w ptunit vs' vu).
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbn in *; unfold UValFE in H0; cbn in *.
    E.stlcCanForm.
    F.stlcCanForm.
    - right. eexists; eauto using invert_valrel_pEmulDV_inUnit.
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.

  (* TODO: ^^ one of these per type **)

  Lemma invert_valrel_pEmulDV_inVar {dir w n p vs vu i} :
    not (valrel dir w (pEmulDV (S n) p (E.tvar i)) (F.inl vs) vu).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [[? ?] | ?]];
    crush.
  Qed.

  Lemma invert_valrel_pEmulDV_var {dir w n p vs vu i} :
    valrel dir w (pEmulDV (S n) p (E.tvar i)) vs vu →
    vs = unkUVal (S n) ∧ p = imprecise.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv in H0, H2.
    E.stlcCanForm.
    F.stlcCanForm.
    - exfalso. exact (invert_valrel_pEmulDV_inVar vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.


  Lemma invert_valrel_pEmulDV_inBool' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p tbool) (inBool n vs) vu →
    (vs = F.true ∧ vu = E.true) ∨ (vs = F.false ∧ vu = E.false).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [_ [(? & ?)|(? & ? & [(? & ?)|(? & ?)])]];
      unfold is_inl in *;
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inBool {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p tbool) (inBool n vs) vu →
    valrel dir w ptbool vs vu.
  Proof.
    intros vr.
    destruct (invert_valrel_pEmulDV_inBool' vr) as [[? ?]|[? ?]]; subst;
    auto using valrel_true, valrel_false.
  Qed.

  Lemma invert_valrel_pEmulDV_bool {dir w n p vs vu} :
   valrel dir w (pEmulDV (S n) p E.tbool) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    ∃ vs', (vs = F.inl vs' ∧ valrel dir w ptbool vs' vu).
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbn in *; unfold UValFE in H0; cbn in *.
    rewrite valrel_fixp in vr; unfold valrel' in vr; cbn in vr.
    destruct vr as (ot & [(-> & ->)|(ts' & eq & vr)]).
    - left. eauto using invert_valrel_pEmulDV_unk.
    - right.
      exists ts'.
      split; [exact eq|].
      destruct vr as [[? ?]|[? ?]]; subst; eauto using valrel_true, valrel_false.
  Qed.


  Lemma invert_valrel_pEmulDV_inProd' {dir w n p τ₁ τ₂ vs vu} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) (inProd n vs) vu →
    ∃ vs₁ vs₂ vu₁ vu₂, vs = F.pair vs₁ vs₂ ∧ vu = E.pair vu₁ vu₂ ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs₁ vu₁) ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs₂ vu₂).
  Proof.
    intros vτ₁ vτ₂ vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [[[vvs tvs] [vvu tvu]] [(? & ?) |(x & ? & vr)]];
      unfold is_inl in *; simpl in *; crush.
    F.stlcCanForm.
    E.stlcCanForm.
    exists x0, x1, x, x2; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inProd {dir w n p τ₁ τ₂ vs vu} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) (inProd n vs) vu →
    valrel dir w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    assert (ValidEnv E.empty) by eauto with tyvalid.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inProd' vτ₁ vτ₂ vr) as (? & ? & ? & ? & ? & ? & ? & ?); subst.
    apply valrel_pair''; crush.
    - unshelve eapply (E.typed_terms_are_valid _ _ _ H9);
        eauto with tyvalid.
    - unshelve eapply (E.typed_terms_are_valid _ _ _ H3);
        eauto with tyvalid.
  Qed.

  Lemma invert_valrel_pEmulDV_prod {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise)
    ∨ exists vs', vs = F.inl vs' ∧ valrel dir w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFE UValFE' fxToIs repEmul] in *.
    F.stlcCanForm; [right | eauto using invert_valrel_pEmulDV_unk].
    exists (F.pair x0 x1).
    crush; exact (invert_valrel_pEmulDV_inProd vτ₁ vτ₂ vr).
  Qed.

  Lemma invert_valrel_pEmulDV_inSum' {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) (F.inl vs) vu →
    ∃ vs' vu', ((vs = F.inl vs' ∧ vu = E.inl vu') ∨ (vs = F.inr vs' ∧ vu = E.inr vu')) ∧
               ((∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs' vu')
                ∨ (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs' vu')).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [? | [? ?]]]; crush.
    unfold OfType, OfTypeStlcFix, OfTypeStlcEqui in H; destruct_conjs.
    unfold is_inl in H0.
    assert (F.Value (F.inl x)) by crush.
    unfold sum_rel in H1; simpl in H1.
    destruct x; destruct vu;
    try exists x, vu; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum'' {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) (F.inl vs) vu →
    ∃ vs' vu',
        ((vs = F.inl vs' ∧ vu = E.inl vu' ∧ (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs' vu'))
        ∨ (vs = F.inr vs' ∧ vu = E.inr vu' ∧
               (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs' vu'))).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [? | [? ?]]]; crush.
    unfold OfType, OfTypeStlcFix, OfTypeStlcEqui in H; destruct_conjs.
    unfold is_inl in H0.
    assert (F.Value (F.inl x)) by crush.
    unfold sum_rel in H1; simpl in H1.
    destruct x; destruct vu;
    try exists x, vu; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) (F.inl vs) vu →
    valrel dir w (ptsum (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    assert (ValidEnv E.empty) by eauto with tyvalid.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inSum'' vr) as (? & ? & [(? & ? & ?) | (? & ? & ?)]);
      subst;
      [apply valrel_inl''| apply valrel_inr''];
      crush.
    - unshelve eapply (E.typed_terms_are_valid _ _ _ H7);
        eauto with tyvalid.
    - unshelve eapply (E.typed_terms_are_valid _ _ _ H7);
        eauto with tyvalid.
  Qed.

  Lemma invert_valrel_pEmulDV_sum {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise)
    ∨ exists vs', vs = F.inl vs' ∧ valrel dir w (ptsum (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFE UValFE' fxToIs repEmul] in *.
    F.stlcCanForm; [right | right | eauto using invert_valrel_pEmulDV_unk];
    [exists (F.inl x0) | exists (F.inr x0)];
    crush; exact (invert_valrel_pEmulDV_inSum vτ₁ vτ₂ vr).
  Qed.

  Lemma invert_valrel_pEmulDV_inArr {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (E.tarr τ₁ τ₂)) (F.inl vs) vu →
    valrel dir w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    intro vr.
    split.
    destruct vr as [? [? | [? ?]]];
    unfold OfType, OfTypeStlcFix, OfTypeStlcEqui in *; destruct_conjs;
    crush.
    destruct vr as [? [? | [? ?]]].
      - crush.
      - destruct H0. inversion H0. assumption.
  Qed.

  Lemma invert_valrel_pEmulDV_arr {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (E.tarr τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    exists vs', vs = F.inl vs' ∧ valrel dir w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFE UValFE' fxToIs repEmul] in *.
    F.stlcCanForm.
    - right. exists x. crush. exact (invert_valrel_pEmulDV_inArr vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.

  (* Lemma invert_valrel_pEmulDV_inRec {dir w n p vs vu τ} : *)
  (*   valrel dir (S w) (pEmulDV (S n) p (E.trec τ)) (F.inl vs) vu → *)
  (*   valrel dir w (pEmulDV n p τ[beta1 (E.trec τ)]) vs vu. *)
  (* Proof. *)
  (*   intros vr. *)
  (*   rewrite valrel_fixp in vr; unfold valrel' in vr. *)
  (*   destruct vr as [? [? | [? ?]]]; crush. *)
  (*   unfold OfType, OfTypeStlcFix, OfTypeStlcEqui in H; destruct_conjs. *)
  (*   unfold is_inl in H0. *)
  (*   inversion H0. *)
  (*   subst. *)
  (*   assert (F.Value (F.inl x)) by crush. *)
  (*   apply H1. *)
  (*   lia. *)
  (* Qed. *)

  Lemma invert_valrel_pEmulDV_inRec {d w n p vs vu τ} :
    ValidTy (trec τ) ->
    valrel d w (pEmulDV n p (E.trec τ)) vs vu ->
    valrel d w (pEmulDV n p τ[beta1 (E.trec τ)]) vs vu.
  Proof.
    intros [clτ crτ] vr.
    rewrite valrel_fixp; unfold valrel'; cbn.
    change (τ[beta1 (E.trec τ)]) with (unfoldOnce (trec τ)).
    rewrite (LMC_unfoldOnce (trec τ)); try assumption; [|cbn;eauto with arith].
    cbn.
    rewrite valrel_fixp in vr; unfold valrel' in vr; cbn in vr.
    destruct vr as [ot vr].
    split; [|assumption].
    destruct ot as ((vvs & tys) & (vvu & tyu));
    crush;
    cbn in tys, tyu.
    rewrite <-UValFE_trec; try assumption.
    now inversion crτ.
    refine (WtEq _ _ _ _ tyu); try assumption.
    eapply EqMuL, tyeq_refl.
    now split.
    now eapply E.ValidTy_unfold_trec.
  Qed.

  (* Lemma invert_valrel_pEmulDV_rec {dir w n p vs vu τ} : *)
  (*   valrel dir (S w) (pEmulDV (S n) p (E.trec τ)) vs vu → *)
  (*   (vs = unkUVal (S n) ∧ p = imprecise) ∨ *)
  (*   exists vs', vs = F.inl vs' ∧ valrel dir w (pEmulDV n p τ[beta1 (E.trec τ)]) vs' vu. *)
  (* Proof. *)
  (*   intro vr. *)
  (*   destruct (valrel_implies_OfType vr) as [[? ?] [? ?]]. *)
  (*   cbn in H0, H2. *)
  (*   cbv [UValFE UValFE'] in H0. *)
  (*   F.stlcCanForm. *)
  (*   - right. exists x. crush. exact (invert_valrel_pEmulDV_inRec vr). *)
  (*   - eauto using invert_valrel_pEmulDV_unk. *)
  (* Qed. *)
  (*   rewrite valrel_fixp; unfold valrel'. *)
  (*   intro vr. *)
  (*   split. *)
  (*   destruct vr as [? [? | [? ?]]]; *)
  (*   destruct H as [[? ?] [? ?]]; *)
  (*   crush. *)

  (*   destruct vr as [? [? | [? ?]]]. *)
  (*   exfalso. *)
  (*   crush. *)
  (*   destruct_conjs. *)
  (*   inversion H2. *)
  (*   subst. *)
  (*   dependent induction n. *)
  (*   unfold is_inl in H0. *)
  (*   inversion H0. *)
  (*   subst. *)
  (*   destruct H as [[? ?] [? ?]]. *)
  (*   simpl in H4, H6. *)
  (*   unfold UValFE in H4. *)
  (*   inversion H4. *)
  (*   subst. *)
  (*   split. *)
  (*   eapply F.can_form_tunit; *)
  (*     crush. *)
  (*   crush. *)
  (*   assert (vu = H1). *)
  (*   - destruct H as [[? ?] [? ?]]. *)
  (*     crush. *)
  (*   - dependent induction n. *)
  (*     destruct H as [[? ?] [? ?]]. *)
  (*     simpl in H1. *)
  (*     dependent induction n. *)
  (*     constructor *)
  (*   intro vr. *)
  (*   split. *)
  (*   destruct vr as [? [? | [? ?]]]; crush; *)
  (*   assert (vs = x) by (unfold is_inl in H0; crush); *)
  (*     subst; *)
  (*   destruct (OfType_implies_Value H); *)
  (*   crush. *)
  (*   destruct H as [[_ ?] _]. *)
  (*   simpl in H. *)
  (*   unfold UValFE in H. *)
  (*   destruct n. *)
  (*   unfold UValFE. *)
  (*   inversion H. *)
  (*   assumption. *)
  (*   destruct τ. *)
  (*   crush. *)
  (* Admitted. *)


  (* Lemma invert_valrel_pEmulDV {dir w n p vs vu} : *)
  (*   valrel dir w (pEmulDV (S n) p) vs vu → *)
  (*   (vs = unkUVal (S n) ∧ p = imprecise) ∨ *)
  (*   ∃ vs', vs = F.inl vs' *)
  (*     (vs = inUnit n vs' ∧ valrel dir w ptunit vs' vu) ∨ *)
  (*     (vs = inBool n vs' ∧ valrel dir w ptbool vs' vu) ∨ *)
  (*     (vs = inProd n vs' ∧ valrel dir w (ptprod (pEmulDV n p) (pEmulDV n p)) vs' vu) ∨ *)
  (*     (vs = inSum n vs' ∧ valrel dir w (ptsum (pEmulDV n p) (pEmulDV n p)) vs' vu) ∨ *)
  (*     (vs = inArr n vs' ∧ valrel dir w (ptarr (pEmulDV n p) (pEmulDV n p)) vs' vu). *)
  (* Proof. *)
  (*   intros vr. *)
  (*   destruct (valrel_implies_OfType vr) as [[? ?] _]. *)
  (*   simpl in H0. *)
  (*   canonUVal. *)
  (*   - left; crush. *)
  (*     exact (invert_valrel_pEmulDV_unk vr). *)
  (*   - right. exists x. left. crush. *)
  (*     exact (invert_valrel_pEmulDV_inUnit vr). *)
  (*   - right. exists x. right. left. crush. *)
  (*     exact (invert_valrel_pEmulDV_inBool vr). *)
  (*   - right. exists x. right. right. left. crush. *)
  (*     exact (invert_valrel_pEmulDV_inProd vr). *)
  (*   - right. exists x. right. right. right. left. crush. *)
  (*     exact (invert_valrel_pEmulDV_inSum vr). *)
  (*   - right. exists x. right. right. right. right. crush. *)
  (*     exact (invert_valrel_pEmulDV_inArr vr). *)
  (* Qed. *)
End ValrelInversion.

Ltac invert_valrel_pEmulDV :=
  match goal with
      | [ H : valrel _ _ (pEmulDV (S _) _ E.tunit) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inUnit H)
      | [ H : valrel _ _ (pEmulDV (S _) _ (E.tsum _ _)) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inSum H)
      | [ H : valrel _ _ (pEmulDV (S _) _ (E.tarr _ _)) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inArr H)
      | [ H : valrel _ _ (pEmulDV (S _) _ (E.trec _)) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inRec H)
      | [ H : valrel _ _ (pEmulDV 0 _ _) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_zero H) as (? & ? & ?)
  end.

(* Lemma valrel_precise_size {w τ vs vu n} : *)
(*   valrel dir_gt w (pEmulDV n precise τ) vs vu -> *)
(*   size vs <= S (S w). *)
(* Proof. *)
(*   revert vs vu n. *)
(*   induction τ; *)
(*     intros vs vu n; *)
(*     rewrite valrel_fixp; *)
(*     unfold valrel'; *)
(*            intros [ot vr]; *)
(*     destruct n. *)
(*   - destruct vr as [-> [=]]. *)
(*   - destruct vr as [[_ eq] _|(ts' & -> & vr)]; try inversion eq. *)
(*     cbn. *)
(*     destruct vr as (tsb & tub & τ₁' & τ₂' & -> & -> & vr). *)
(*     cbn. *)
(*     lia. *)
(*   - destruct vr as (-> & [= ]). *)
(*   - destruct vr as [(_ & [= ])| (? & -> & -> & ->)]. *)
(*     cbn. lia. *)
(*   - destruct vr as (-> & [=]). *)
(*   - destruct vr as [(_ & [= ])| (ts & -> & hyp)]. *)
(*     destruct ts, vu; try contradiction. *)
(*     destruct w. *)
(*     unfold sum_rel in hyp. *)
(*     cbn. *)
(*     eapply IHτ1. *)
(*     rewrite valrel_fixp; unfold valrel'; cbn. *)
(*     split; eauto. *)
(*     cbn; lia. *)
(*   -  *)

Lemma OfType_pEmulDV_unfoldn {n p τ ts tu} :
  ValidTy τ ->
  OfType (pEmulDV n p τ) ts tu <->
  OfType (pEmulDV n p (unfoldn (LMC τ) τ)) ts tu.
Proof.
  intros vτ; split;
    intros ((vvs & tvs) & (vvu & tvu));
  cbn in *;
  repeat split; cbn; try assumption;
  try rewrite <-UValFE_unfoldn in *;
    try assumption; E.crushValidTy.
  - refine (WtEq _ _ _ _ tvu);
      eauto using E.ValidTy_unfoldn with tyvalid.
    eapply ty_eq_peel_recs; E.crushValidTy.
    eapply tyeq_refl.
  - rewrite <-UValFE_unfoldn in tvs; E.crushValidTy.
  - refine (WtEq _ _ _ _ tvu);
      eauto using E.ValidTy_unfoldn with tyvalid.
    eapply ty_eq_unf_ty; E.crushValidTy.
    eapply tyeq_refl.
Qed.

Lemma valrel_pEmulDV_unfoldn {d n p w τ ts tu} :
  ValidTy τ ->
  valrel d w (pEmulDV n p τ) ts tu <->
  valrel d w (pEmulDV n p (unfoldn (LMC τ) τ)) ts tu.
Proof.
  intros vτ.
  rewrite valrel_fixp.
  unfold valrel'.
  rewrite unfoldn_LMC; E.crushValidTy.
  now rewrite <-OfType_pEmulDV_unfoldn.
Qed.

Lemma OfType_tyeq {T U n p ts tu} :
  ValidTy T ->
  ValidTy U ->
  ⟪ T ≗ U ⟫ ->
  OfType (pEmulDV n p T) ts tu <->
  OfType (pEmulDV n p U) ts tu.
Proof.
  intros vT vU tyeq; split;
  intros [[vts tts] [vtu ttu]];
  repeat split;
  cbn in *; try assumption.
  - now rewrite <-?(UVal_eq vT vU tyeq).
  - refine (WtEq _ tyeq vT vU ttu).
  - now rewrite ?(UVal_eq vT vU tyeq).
  - refine (WtEq _ (tyeq_symm tyeq) vU vT ttu).
Qed.

Lemma valrel_tyeq {T U d w n p ts tu} :
  ValidTy T ->
  ValidTy U ->
  ⟪ T ≗ U ⟫ ->
  valrel d w (pEmulDV n p T) ts tu ->
  valrel d w (pEmulDV n p U) ts tu.
Proof.
  revert T U d w p ts tu.
  induction n;
  intros T U d w p ts tu vT vU tyeq;
  rewrite valrel_fixp;
    unfold valrel';
    rewrite (OfType_tyeq vT vU tyeq);
    destruct 1 as [ot vr];
    cbn in *; [eauto|].
  split; [assumption|].
  destruct vr as [[-> ->]|[ts' vr']]; [now left|right].
  exists ts'.
  assert (⟪ unfoldn (LMC T) T ≗ unfoldn (LMC U) U ⟫).
  refine (eq_trans_contr _ _ (eq_trans_contr _ tyeq _));
    E.crushValidTy.
  eapply ty_eq_peel_recs_left; E.crushValidTy; eapply tyeq_refl.
  eapply ty_eq_peel_recs; E.crushValidTy; eapply tyeq_refl.

  assert (ValidTy (unfoldn (LMC T) T)) by eauto using E.ValidTy_unfoldn.
  assert (ValidTy (unfoldn (LMC U) U)) by eauto using E.ValidTy_unfoldn.
  assert (luz : LMC (unfoldn (LMC U) U) = 0) by (eapply unfoldn_LMC; E.crushValidTy).
  destruct H; eauto.
  - split;[now trivial|].
    eapply E.ValidTy_invert_arr in H0, H1.
    destruct vr' as (-> & ts'' & tu' & τ₁' & τ₂' & -> & -> & trb).
    exists ts'', tu', τ₁', τ₂'.
    intuition.
    specialize (trb w' fw vs vu H1 (IHn _ _ _ _ _ _ _ H0 H3 (tyeq_symm H) H6)).
    unfold termrel', contrel' in *.
    intros Cs Cu eCs eCu contrel.
    eapply (trb Cs Cu eCs eCu).
    intros w'' fw' ts' tu'' vr'.
    eapply (contrel w'' fw' ts' tu'').
    eapply (IHn _ _ _ _ _ _ _ H4 H5 H2 vr').
  - intuition.
    eapply E.ValidTy_invert_sum in H0, H1.
    unfold sum_rel in *.
    destruct ts', tu; intuition;
    specialize (H4 w' fw); refine (IHn _ _ _ _ _ _ _  _ _ _ H4);
      assumption.
  - intuition.
    eapply E.ValidTy_invert_prod in H0, H1.
    unfold prod_rel in *.
    destruct ts', tu; intuition;
    specialize (H1 w' fw);
      specialize (H8 w' fw).
    refine (IHn _ _ _ _ _ _ _  _ _ _ H1); assumption.
    refine (IHn _ _ _ _ _ _ _  _ _ _ H8); assumption.
  - contradiction vr'.
  - cbn in luz. exfalso. lia.
Qed.

Lemma valrel_tyeq' {T U d w n p ts tu} :
  ValidTy T ->
  ValidTy U ->
  ⟪ T ≗ U ⟫ ->
  valrel d w (pEmulDV n p T) ts tu <->
  valrel d w (pEmulDV n p U) ts tu.
Proof.
  intros vT vU tyeq.
  assert (tyeq' := tyeq_symm tyeq).
  split; intros vr;
  now refine (valrel_tyeq _ _ _ vr).
Qed.

Lemma compat_type_eq {T U Γ n p d m ts tu} :
  ValidTy T ->
  ValidTy U ->
  ⟪ T ≗ U ⟫ ->
  ⟪ Γ ⊩ ts ⟦d,m⟧ tu : pEmulDV n p T ⟫ ->
  ⟪ Γ ⊩ ts ⟦d,m⟧ tu : pEmulDV n p U ⟫.
Proof.
  intros vT vU tyeq [tts [ttu trel]].
  split; [|split]; cbn in *.
  - now rewrite <-(UVal_eq vT vU tyeq).
  - now refine (WtEq _ _ _ _ ttu).
  - revert trel.
    unfold termrel, termrel', contrel, contrel'.
    now setoid_rewrite <-(valrel_tyeq' vT vU tyeq).
Qed.

