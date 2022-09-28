Require Import Common.Common.
Require Import LogRelFI.PseudoTypeFI.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LRFI.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.CanForm.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.Size.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.Inst.
Require Import UValFI.UVal.

Require Import Lia.
Require Import Min.

Section ValrelInversion.

  Local Ltac crush :=
    repeat
      (cbn in * |-; cbn;
       try assumption;
       crushOfType;
       repeat I.crushTyping;
       repeat F.crushTyping;
       repeat I.crushStlcSyntaxMatchH;
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
    vs = F.unit ∧ vu = I.unit.
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
    valrel d w (ptprod τ₁ τ₂) vs vu →
    exists vs₁ vs₂ vu₁ vu₂,
      (vs = F.pair vs₁ vs₂ ∧ vu = I.pair vu₁ vu₂ ∧
       OfType τ₁ vs₁ vu₁ ∧
       OfType τ₂ vs₂ vu₂ ∧
       ∀ w', w' < w → valrel d w' τ₁ vs₁ vu₁ ∧ valrel d w' τ₂ vs₂ vu₂).
  Proof.
    intros vr.
    destruct (OfType_inversion_ptprod (valrel_implies_OfType vr))
      as (ts1' & tu1' & ts2' & tu2' & Hvs & Hvu & oft1 & oft2).
    exists ts1', ts2', tu1', tu2';
    rewrite -> valrel_fixp in vr;
    unfold valrel' in vr; crush.
  Qed.

  Lemma valrel_ptsum_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptsum τ₁ τ₂) vs vu →
    exists vs' vu',
      (vs = F.inl vs' ∧ vu = I.inl vu' ∧
       OfType τ₁ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₁ vs' vu') ∨
      (vs = F.inr vs' ∧ vu = I.inr vu' ∧
       OfType τ₂ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₂ vs' vu').
  Proof.
    intros vr.
    rewrite -> valrel_fixp in vr; destruct vr as [oft sumrel];
    apply OfType_inversion_ptsum in oft;
    destruct oft as (tsb & tub & Hvs); intuition; crush;
    exists tsb, tub; crush.
  Qed.

  Lemma valrel_ptarr_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptarr τ₁ τ₂) vs vu →
    ∃ tsb tub,
      vs = F.abs (repEmul τ₁) tsb ∧ vu = I.abs (fxToIs τ₁) tub ∧
      ⟪ F.empty ▻ repEmul τ₁ ⊢ tsb : repEmul τ₂ ⟫ ∧
      ⟪ I.empty r▻ fxToIs τ₁ i⊢ tub : fxToIs τ₂ ⟫ ∧
      ∀ w' vs' vu',
        w' < w →
        (d = dir_gt -> I.size vu' <= w') ->
        valrel d w' τ₁ vs' vu' →
        termrel d w' τ₂ (tsb[beta1 vs']) (tub[beta1 vu']).
  Proof.
    intros vr.
    destruct (valrel_implies_Value vr) as [? ?].
    destruct (OfType_inversion_ptarr (valrel_implies_OfType vr))
      as (tsb & tub & ? & ? & ?).
    exists tsb, tub; crush.
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
    - destruct τ; destruct_conjs; unfold is_inl in H0; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p I.tunit) (F.inl vs) vu →
    vs = F.unit ∧ vu = I.unit.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    unfold valrel' in vr.
    destruct vr as (ot & [(? & ?) | ?]);
      try (destruct H as [? H']; unfold is_inl in H');
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p I.tunit) (F.inl vs) vu →
    valrel dir w ptunit vs vu.
  Proof.
    intros vr.
    destruct (invert_valrel_pEmulDV_inUnit' vr); subst.
    apply valrel_unit.
  Qed.

  Lemma invert_valrel_pEmulDV_unit {dir w n p vs vu} :
   valrel dir w (pEmulDV (S n) p I.tunit) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    ∃ vs', (vs = F.inl vs' ∧ valrel dir w ptunit vs' vu).
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbn in *; unfold UValFI in H0; cbn in *.
    I.stlcCanForm.
    F.stlcCanForm.
    - right. eexists; eauto using invert_valrel_pEmulDV_inUnit.
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.

  (* TODO: ^^ one of these per type **)

  Lemma invert_valrel_pEmulDV_inVar {dir w n p vs vu i} :
    not (valrel dir w (pEmulDV (S n) p (I.tvar i)) (F.inl vs) vu).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [[? ?] | ?]];
    crush.
  Qed.

  Lemma invert_valrel_pEmulDV_var {dir w n p vs vu i} :
    valrel dir w (pEmulDV (S n) p (I.tvar i)) vs vu →
    vs = unkUVal (S n) ∧ p = imprecise.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv in H0, H2.
    I.stlcCanForm.
    F.stlcCanForm.
    - exfalso. exact (invert_valrel_pEmulDV_inVar vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.


  Lemma invert_valrel_pEmulDV_inBool' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p tbool) (inBool n vs) vu →
    (vs = F.true ∧ vu = I.true) ∨ (vs = F.false ∧ vu = I.false).
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
   valrel dir w (pEmulDV (S n) p I.tbool) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    ∃ vs', (vs = F.inl vs' ∧ valrel dir w ptbool vs' vu).
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbn in *; unfold UValFI in H0; cbn in *.
    rewrite valrel_fixp in vr; unfold valrel' in vr; cbn in vr.
    destruct vr as (ot & [(-> & ->)|(ts' & eq & vr)]).
    - left. eauto using invert_valrel_pEmulDV_unk.
    - right.
      exists ts'.
      split; [exact eq|].
      destruct vr as [[? ?]|[? ?]]; subst; eauto using valrel_true, valrel_false.
  Qed.


  Lemma invert_valrel_pEmulDV_inProd' {dir w n p τ₁ τ₂ vs vu} :
    valrel dir w (pEmulDV (S n) p (I.tprod τ₁ τ₂)) (inProd n vs) vu →
    ∃ vs₁ vs₂ vu₁ vu₂, vs = F.pair vs₁ vs₂ ∧ vu = I.pair vu₁ vu₂ ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs₁ vu₁) ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs₂ vu₂).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [[[vvs tvs] [vvu tvu]] [(? & ?) |(x & ? & vr)]];
      unfold is_inl in *; simpl in *; crush.
    F.stlcCanForm.
    I.stlcCanForm.
    exists x0, x1, x, x2; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inProd {dir w n p τ₁ τ₂ vs vu} :
    valrel dir w (pEmulDV (S n) p (I.tprod τ₁ τ₂)) (inProd n vs) vu →
    valrel dir w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inProd' vr) as (? & ? & ? & ? & ? & ? & ? & ?); subst.
    apply valrel_pair''; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_prod {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tprod τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise)
    ∨ exists vs', vs = F.inl vs' ∧ valrel dir w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFI UValFI' fxToIs repEmul] in *.
    F.stlcCanForm; [right | eauto using invert_valrel_pEmulDV_unk].
    exists (F.pair x0 x1).
    crush; exact (invert_valrel_pEmulDV_inProd vr).
  Qed.

  Lemma invert_valrel_pEmulDV_inSum' {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tsum τ₁ τ₂)) (F.inl vs) vu →
    ∃ vs' vu', ((vs = F.inl vs' ∧ vu = I.inl vu') ∨ (vs = F.inr vs' ∧ vu = I.inr vu')) ∧
               ((∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs' vu')
                ∨ (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs' vu')).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [? | [? ?]]]; crush.
    unfold OfType, OfTypeStlcFix, OfTypeStlcIso in H; destruct_conjs.
    unfold is_inl in H0.
    assert (F.Value (F.inl x)) by crush.
    unfold sum_rel in H1; simpl in H1.
    destruct x; destruct vu;
    try exists x, vu; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum'' {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tsum τ₁ τ₂)) (F.inl vs) vu →
    ∃ vs' vu',
        ((vs = F.inl vs' ∧ vu = I.inl vu' ∧ (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₁) vs' vu'))
        ∨ (vs = F.inr vs' ∧ vu = I.inr vu' ∧
               (∀ w', w' < w → valrel dir w' (pEmulDV n p τ₂) vs' vu'))).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [? | [? ?]]]; crush.
    unfold OfType, OfTypeStlcFix, OfTypeStlcIso in H; destruct_conjs.
    unfold is_inl in H0.
    assert (F.Value (F.inl x)) by crush.
    unfold sum_rel in H1; simpl in H1.
    destruct x; destruct vu;
    try exists x, vu; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tsum τ₁ τ₂)) (F.inl vs) vu →
    valrel dir w (ptsum (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inSum'' vr) as (? & ? & [(? & ? & ?) | (? & ? & ?)]);
      subst;
      [apply valrel_inl''| apply valrel_inr''];
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_sum {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tsum τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise)
    ∨ exists vs', vs = F.inl vs' ∧ valrel dir w (ptsum (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFI UValFI' fxToIs repEmul] in *.
    F.stlcCanForm; [right | right | eauto using invert_valrel_pEmulDV_unk];
    [exists (F.inl x0) | exists (F.inr x0)];
    crush; exact (invert_valrel_pEmulDV_inSum vr).
  Qed.

  Lemma invert_valrel_pEmulDV_inArr {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tarr τ₁ τ₂)) (F.inl vs) vu →
    valrel dir w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs vu.
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    intro vr.
    split.
    destruct vr as [? [? | [? ?]]];
    unfold OfType, OfTypeStlcFix, OfTypeStlcIso in *; destruct_conjs;
    crush.
    destruct vr as [? [? | [? ?]]].
      - crush.
      - destruct H0. inversion H0. assumption.
  Qed.

  Lemma invert_valrel_pEmulDV_arr {dir w n p vs vu τ₁ τ₂} :
    valrel dir w (pEmulDV (S n) p (I.tarr τ₁ τ₂)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    exists vs', vs = F.inl vs' ∧ valrel dir w (ptarr (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFI UValFI' fxToIs repEmul] in *.
    F.stlcCanForm.
    - right. exists x. crush. exact (invert_valrel_pEmulDV_inArr vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.

  Lemma invert_valrel_pEmulDV_inRec {dir w n p vs vu τ} :
    valrel dir (S w) (pEmulDV (S n) p (I.trec τ)) (F.inl vs) (I.fold_ vu) →
    valrel dir w (pEmulDV n p τ[beta1 (I.trec τ)]) vs vu.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [? [? | [? ?]]]; crush.
    unfold OfType, OfTypeStlcFix, OfTypeStlcIso in H; destruct_conjs.
    unfold is_inl in H0.
    inversion H0.
    subst.
    assert (F.Value (F.inl x)) by crush.
    apply H3.
    lia.
  Qed.

  Lemma invert_valrel_pEmulDV_rec {dir w n p vs vu τ} :
    valrel dir (S w) (pEmulDV (S n) p (I.trec τ)) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    exists vs' vu', vs = F.inl vs' ∧ vu = I.fold_ vu' ∧ valrel dir w (pEmulDV n p τ[beta1 (I.trec τ)]) vs' vu'.
  Proof.
    intro vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    cbv [UValFI UValFI' fxToIs repEmul] in *.
    destruct (I.can_form_trec H1 H2) as (? & ? & ?).
    F.stlcCanForm.
    - right. exists x0, x. crush. exact (invert_valrel_pEmulDV_inRec vr).
    - eauto using invert_valrel_pEmulDV_unk.
  Qed.
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
  (*   unfold UValFI in H4. *)
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
  (*   unfold UValFI in H. *)
  (*   destruct n. *)
  (*   unfold UValFI. *)
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
      | [ H : valrel _ _ (pEmulDV (S _) _ I.tunit) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inUnit H)
      | [ H : valrel _ _ (pEmulDV (S _) _ (I.tsum _ _)) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inSum H)
      | [ H : valrel _ _ (pEmulDV (S _) _ (I.tarr _ _)) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV_inArr H)
      | [ H : valrel _ _ (pEmulDV (S _) _ (I.trec _)) _ _ |- _ ] =>
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
