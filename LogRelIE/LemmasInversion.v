Require Import Common.Common.
Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.CanForm.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.Size.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.Inst.
Require Import UValIE.UVal.

Require Import Lia.
Require Import Min.

Section ValrelInversion.

  Local Ltac crush :=
    repeat
      (cbn in * |-; cbn;
       try assumption;
       crushOfType;
       repeat E.crushTyping;
       repeat I.crushTyping;
       repeat E.crushStlcSyntaxMatchH;
       repeat I.crushStlcSyntaxMatchH;
       (* repeat crushUtlcScopingMatchH; *)
       repeat crushDbSyntaxMatchH;
       repeat crushValidPTyMatch;
       try subst;
       destruct_conjs;
       repeat match goal with
                  [ |- _ ∧ _ ] => split
              end;
       repeat match goal with
           [ H : is_inl (I.inl _) _ |- _] => inversion H; clear H
         end;
       eauto
      );
    try discriminate;
    eauto with eval;
    try lia.

  Lemma valrel_ptunit_inversion {d w vs vu} :
    valrel d w ptunit vs vu →
    vs = I.unit ∧ vu = E.unit.
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    now intros (? & (? & -> & ?)).
  Qed.

  Lemma valrel_ptbool_inversion {d w vs vu} :
    valrel d w ptbool vs vu →
    (vs = I.true ∧ vu = E.true) ∨ (vs = I.false ∧ vu = E.false).
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    now intros (? & ? & -> & ?).
  Qed.

  Lemma valrel_ptprod_inversion {d w τ₁ τ₂ vs vu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    valrel d w (ptprod τ₁ τ₂) vs vu →
    exists vs₁ vs₂ vu₁ vu₂,
      (vs = I.pair vs₁ vs₂ ∧ vu = E.pair vu₁ vu₂ ∧
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
      (vs = I.inl vs' ∧ vu = E.inl vu' ∧
       OfType τ₁ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₁ vs' vu') ∨
      (vs = I.inr vs' ∧ vu = E.inr vu' ∧
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
    ∃ tsb tub τ₁',
      vs = I.abs (repEmul τ₁) tsb ∧ vu = E.abs τ₁' tub ∧
        ValidTy τ₁' /\
        ⟪ τ₁' ≗ isToEq τ₁ ⟫ /\
      ⟪ empty r▻ repEmul τ₁ i⊢ tsb : repEmul τ₂ ⟫ ∧
      ⟪ empty r▻ isToEq τ₁ e⊢ tub : isToEq τ₂ ⟫ ∧
      ∀ w' vs' vu',
        w' < w →
        (d = dir_gt -> E.size vu' <= w') ->
        valrel d w' τ₁ vs' vu' →
        termrel d w' τ₂ (tsb[beta1 vs']) (tub[beta1 vu']).
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_Value vr) as [? ?].
    destruct (OfType_inversion_ptarr vτ₁ vτ₂ (valrel_implies_OfType vr))
      as (tsb & tub & ? & ? & ?).
    exists tsb, tub, x. crush.
    rewrite -> valrel_fixp in vr.
    unfold valrel' in vr; unfold termrel; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_zero {dir w p vs vu τ} :
    ValidTy τ ->
    valrel dir w (pEmulDV 0 p τ) vs vu →
    OfType (pEmulDV 0 p τ) vs vu ∧ vs = I.unit ∧ p = imprecise.
  Proof.
    rewrite valrel_fixp.
    intros vτ (? & ? & <- & ? & vr).
    now cbn in vr.
  Qed.

  Lemma invert_valrel_pEmulDV_unk {dir w n p vu τ} :
    valrel dir w (pEmulDV (S n) p τ) (I.inr I.unit) vu →
    p = imprecise.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as (ot & (? & <- & ? & [(? & ?) | ?])).
    - assumption.
    - destruct (unfoldn (LMC τ) τ); destruct_conjs; unfold is_inl in H0; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p E.tunit) (I.inl vs) vu →
    vs = I.unit ∧ vu = E.unit.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    unfold valrel' in vr.
    destruct vr as (ot & (? & <- & ? & [(? & ?) | ?]));
      try (destruct H as [? H']; unfold is_inl in H');
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p E.tunit) (I.inl vs) vu →
    valrel dir w ptunit vs vu.
  Proof.
    intros vr.
    destruct (invert_valrel_pEmulDV_inUnit' vr); subst.
    apply valrel_unit.
  Qed.

  Lemma invert_valrel_pEmulDV_unit {dir w n p vs vu} :
   valrel dir w (pEmulDV (S n) p E.tunit) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    ∃ vs', (vs = I.inl vs' ∧ valrel dir w ptunit vs' vu).
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbn in *; unfold UValIE in H0; cbn in *.
    E.stlcCanForm.
    I.stlcCanForm.
    - right. eexists; eauto using invert_valrel_pEmulDV_inUnit.
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.

  (* TODO: ^^ one of these per type **)

  Lemma invert_valrel_pEmulDV_inVar {dir w n p vs vu i} :
    not (valrel dir w (pEmulDV (S n) p (E.tvar i)) (I.inl vs) vu).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as (? & ? & <- & ? & [[? ?] | ?]);
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
    I.stlcCanForm.
    - exfalso. exact (invert_valrel_pEmulDV_inVar vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.


  Lemma invert_valrel_pEmulDV_inBool' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p tbool) (inBool n vs) vu →
    (vs = I.true ∧ vu = E.true) ∨ (vs = I.false ∧ vu = E.false).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as (_ & ? & <- & ? & [(? & ?)|(? & ? & [(? & ?)|(? & ?)])]);
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
    ∃ vs', (vs = I.inl vs' ∧ valrel dir w ptbool vs' vu).
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbn in *; unfold UValIE in H0; cbn in *.
    rewrite valrel_fixp in vr; unfold valrel' in vr; cbn in vr.
    destruct vr as (ot & ? & <- & ? & [(-> & ->)|(ts' & eq & vr)]).
    - left. eauto using invert_valrel_pEmulDV_unk.
    - right.
      exists ts'.
      split; [exact eq|].
      destruct vr as [[? ?]|[? ?]]; subst; eauto using valrel_true, valrel_false.
  Qed.


  Lemma invert_valrel_pEmulDV_inProd' {dir w n p τ₁ τ₂ vs vu} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) (inProd n vs) vu →
    ∃ vs₁ vs₂ vu₁ vu₂, vs = I.pair vs₁ vs₂ ∧ vu = E.pair vu₁ vu₂ ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs₁ vu₁) ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs₂ vu₂).
  Proof.
    intros vτ₁ vτ₂ vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    assert (ValidEnv empty) by crush.
    destruct vr as ([[vvs tvs] [vvu tvu]] & ? & <- & ? & [(? & ?) |(x & ? & vr)]);
      unfold is_inl in *; simpl in *; crush.
    I.stlcCanForm.
    E.stlcCanForm.
    exists x0, x1, x, x2; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inProd {dir w n p τ₁ τ₂ vs vu} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) (inProd n vs) vu →
    valrel dir w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inProd' vτ₁ vτ₂ vr) as (? & ? & ? & ? & ? & ? & ? & ?); subst.
    assert (ValidEnv empty) by crush.
    apply valrel_pair''; crush;
      now E.try_typed_terms_are_valid.
  Qed.

  Lemma invert_valrel_pEmulDV_prod {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tprod τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise)
    ∨ exists vs', vs = I.inl vs' ∧ valrel dir w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValIE UValIE' isToEq repEmul] in *.
    I.stlcCanForm; [right | eauto using invert_valrel_pEmulDV_unk].
    exists (I.pair x0 x1).
    crush; exact (invert_valrel_pEmulDV_inProd vτ₁ vτ₂ vr).
  Qed.

  Lemma invert_valrel_pEmulDV_inSum' {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) (I.inl vs) vu →
    ∃ vs' vu', ((vs = I.inl vs' ∧ vu = E.inl vu') ∨ (vs = I.inr vs' ∧ vu = E.inr vu')) ∧
               ((∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs' vu')
                ∨ (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs' vu')).
  Proof.
    intros vτ₁ vτ₂ vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as (? & ? & <- & ? & [? | [? ?]]); crush.
    unfold OfType, OfTypeStlcIso, OfTypeStlcEqui in H; destruct_conjs.
    unfold is_inl in H0.
    assert (I.Value (I.inl x)) by crush.
    unfold sum_rel in H1; simpl in H1.
    destruct x; destruct vu;
    try exists x, vu; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum'' {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) (I.inl vs) vu →
    ∃ vs' vu',
        ((vs = I.inl vs' ∧ vu = E.inl vu' ∧ (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs' vu'))
        ∨ (vs = I.inr vs' ∧ vu = E.inr vu' ∧
               (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs' vu'))).
  Proof.
    intros vτ₁ vτ₂ vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as (? & ? & <- & ? & [? | [? ?]]); crush.
    unfold OfType, OfTypeStlcIso, OfTypeStlcEqui in H; destruct_conjs.
    unfold is_inl in H0.
    assert (I.Value (I.inl x)) by crush.
    unfold sum_rel in H1; simpl in H1.
    destruct x; destruct vu;
    try exists x, vu; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) (I.inl vs) vu →
    valrel dir w (ptsum (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    assert (ValidEnv empty) by crush.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inSum'' vτ₁ vτ₂ vr) as (? & ? & [(? & ? & ?) | (? & ? & ?)]);
      subst;
      [apply valrel_inl''| apply valrel_inr''];
      crush; now E.try_typed_terms_are_valid.
  Qed.

  Lemma invert_valrel_pEmulDV_sum {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tsum τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise)
    ∨ exists vs', vs = I.inl vs' ∧ valrel dir w (ptsum (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValIE UValIE' isToEq repEmul] in *.
    I.stlcCanForm; [right | right | eauto using invert_valrel_pEmulDV_unk];
    [exists (I.inl x0) | exists (I.inr x0)];
    crush; exact (invert_valrel_pEmulDV_inSum vτ₁ vτ₂ vr).
  Qed.

  Lemma invert_valrel_pEmulDV_inArr {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tarr τ₁ τ₂)) (I.inl vs) vu →
    valrel dir w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    assert (ValidEnv empty) by crush.
    rewrite valrel_fixp; unfold valrel'.
    intros vτ₁ vτ₂ vr.
    split.
    destruct vr as (? & ? & <- & ? & [? | [? ?]]);
    unfold OfType, OfTypeStlcIso, OfTypeStlcEqui in *; destruct_conjs;
    crush.
    destruct vr as (? & ? & <- & ? & [? | [? [? ?]]]).
      - crush.
      - inversion H2; subst.
        crush.
  Qed.

  Lemma invert_valrel_pEmulDV_arr {dir w n p vs vu τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
    valrel dir w (pEmulDV (S n) p (E.tarr τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    exists vs', vs = I.inl vs' ∧ valrel dir w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intros vτ₁ vτ₂ vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValIE UValIE' isToEq repEmul] in *.
    I.stlcCanForm.
    - right. exists x. crush. exact (invert_valrel_pEmulDV_inArr vτ₁ vτ₂ vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.

  (* Lemma invert_valrel_pEmulDV_inRec {dir w n p vs vu τ} : *)
  (*   ValidTy τ -> *)
  (*   valrel dir (S w) (pEmulDV (S n) p (E.trec τ)) (I.inl vs) (E.fold_ vu) → *)
  (*   valrel dir w (pEmulDV n p τ[beta1 (E.trec τ)]) vs vu. *)
  (* Proof. *)
  (*   intros vτ vr. *)
  (*   rewrite valrel_fixp in vr; unfold valrel' in vr. *)
  (*   destruct vr as [? [? | [? ?]]]; crush. *)
  (*   unfold OfType, OfTypeStlcFix, OfTypeStlcIso in H; destruct_conjs. *)
  (*   unfold is_inl in H0. *)
  (*   inversion H0. *)
  (*   subst. *)
  (*   assert (I.Value (I.inl x)) by crush. *)
  (*   apply H3. *)
  (*   lia. *)
  (* Qed. *)

  (* Lemma invert_valrel_pEmulDV_rec {dir w n p vs vu τ} : *)
  (*   ValidTy τ -> *)
  (*   valrel dir (S w) (pEmulDV (S n) p (E.trec τ)) vs vu → *)
  (*   (vs = unkUVal (S n) ∧ p = imprecise) ∨ *)
  (*   exists vs' vu', vs = I.inl vs' ∧ vu = E.fold_ vu' ∧ valrel dir w (pEmulDV n p τ[beta1 (E.trec τ)]) vs' vu'. *)
  (* Proof. *)
  (*   intro vr. *)
  (*   destruct (valrel_implies_OfType vr) as [[? ?] [? ?]]. *)
  (*   cbv [UValIE UValIE' fxToIs repEmul] in *. *)
  (*   destruct (E.can_form_trec H1 H2) as (? & ? & ?). *)
  (*   I.stlcCanForm. *)
  (*   - right. exists x0, x. crush. exact (invert_valrel_pEmulDV_inRec vr). *)
  (*   - eauto using invert_valrel_pEmulDV_unk. *)
  (* Qed. *)

  (* Lemma invert_valrel_pEmulDV {dir w n p vs vu} : *)
  (*   valrel dir w (pEmulDV (S n) p) vs vu → *)
  (*   (vs = unkUVal (S n) ∧ p = imprecise) ∨ *)
  (*   ∃ vs', vs = I.inl vs' *)
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
      (* | [ H : valrel _ _ (pEmulDV (S _) _ (E.trec _)) _ _ |- _ ] => *)
      (* destruct (invert_valrel_pEmulDV_inRec H) *)
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
  rewrite <-?UValIE_unfoldn in tvs;
  rewrite <-?UValIE_unfoldn;
    try assumption; crushValidTy.
  - refine (WtEq _ _ _ _ tvu);
      eauto using E.ValidTy_unfoldn with tyvalid.
    eapply ty_eq_peel_recs; E.crushValidTy.
    eapply tyeq_refl.
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
  cbn.
  rewrite unfoldn_LMC; E.crushValidTy.
  cbn.
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
  destruct vr as (? & <- & vts & [[-> ->]|[ts' vr']]); eexists; repeat split; try easy; [now left|right].
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
  - cbn in luz.  lia.
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
