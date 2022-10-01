Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.LemmasTyping.
Require Import StlcIsoValid.SpecSyntax.
Require Import StlcIsoValid.Inst.
Require Import StlcIsoValid.SpecTyping.
Require Import StlcIsoValid.SpecAnnot.
Require Import StlcIsoValid.SpecEvaluation.
Require Import StlcIsoValid.LemmasTyping.
Require Import StlcIsoValid.LemmasEvaluation.
Require Import StlcIsoValid.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import LogRelIE.LemmasInversion.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.PseudoTypeIE.
Require Import UValIE.UVal.

Require Import Lia.

Require Import Program.Wf.

Local Ltac matchValidTyUValIE :=
  match goal with
  | [ |- ValidTy (UValIE _ _) ] => eapply UValIE_valid
  end.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushRecTypesMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushRepEmulEmbed;
     repeat E.crushStlcSyntaxMatchH;
     repeat I.crushStlcSyntaxMatchH;
     crushTyping;
     crushTypingIA;
     E.crushTyping;
     try matchValidTyUValIE;
     try crushValidTyMatch2;
     try crushOfType;
     trivial;
     subst*);
  try discriminate; try lia;
  eauto using unkUValT with eval;
  repeat crushStlcSyntaxMatchH (* remove apTm's again *).

Fixpoint downgrade (n : nat) (d : nat) (τ : E.Ty) {struct n} : I.Tm :=
  let abs_creator := I.abs (UValIE (n + d) τ) in
  match n with
    | 0 => abs_creator (unkUVal 0)
    | S n =>
      match unfoldn (LMC τ) τ with
        | E.tunit => abs_creator (I.var 0)
        | E.tbool => abs_creator (I.var 0)
        | E.tprod τ τ' => abs_creator (I.caseof (I.var 0)
                                               (I.inl (I.pair (I.app (downgrade n d τ) (I.proj₁ (I.var 0)))
                                                              (I.app (downgrade n d τ') (I.proj₂ (I.var 0)))))
                                              (I.inr (I.var 0)))
        | E.tsum τ τ' => abs_creator (I.caseof (I.var 0)
                                              (I.inl (I.caseof (I.var 0)
                                                               (I.inl (I.app (downgrade n d τ)
                                                                             (I.var 0)))
                                                               (I.inr (I.app (downgrade n d τ')
                                                                             (I.var 0)))))
                                              (I.inr (I.var 0)))
        | E.tarr τ τ' => abs_creator (I.caseof (I.var 0)
                                              (I.inl (I.abs (UValIE n τ)
                                                            (I.app (downgrade n d τ')
                                                                   (I.app (I.var 1)
                                                                          (I.app (upgrade n d τ)
                                                                                 (I.var 0))))))
                                              (I.inr (I.var 0)))
        | E.trec τ => abs_creator (unkUVal (S n))
        | E.tvar _ => abs_creator (I.caseof (I.var 0) (I.inl (I.var 0)) (I.inr (I.var 0)))
      end
  end
with
upgrade (n : nat) (d : nat) (τ : E.Ty) {struct n} :=
  let abs_creator := I.abs (UValIE n τ) in
  match n with
    | 0 => abs_creator (unkUVal d)
    | S n =>
      match unfoldn (LMC τ) τ with
        | E.tunit => abs_creator (I.var 0)
        | E.tbool => abs_creator (I.var 0)
        | E.tprod τ τ' => abs_creator (I.caseof (I.var 0)
                                               (I.inl (I.pair (I.app (upgrade n d τ) (I.proj₁ (I.var 0)))
                                                              (I.app (upgrade n d τ') (I.proj₂ (I.var 0)))))
                                              (I.inr (I.var 0)))
        | E.tsum τ τ' => abs_creator (I.caseof (I.var 0)
                                        (I.inl (I.caseof (I.var 0)
                                                          (I.inl (I.app (upgrade n d τ)
                                                                        (I.var 0)))
                                                          (I.inr (I.app (upgrade n d τ')
                                                                        (I.var 0)))))
                                        (I.inr (I.var 0)))
        | E.tarr τ τ' => abs_creator (I.caseof (I.var 0)
                                              (I.inl (I.abs (UValIE (n + d) τ)
                                                            (I.app (upgrade n d τ')
                                                                  (I.app (I.var 1)
                                                                          (I.app (downgrade n d τ)
                                                                                (I.var 0))))))
                                              (I.inr (I.var 0)))
        (* | E.trec τ' => upgrade n d (fu' (E.trec τ')) *)
        | E.trec τ => abs_creator (unkUVal (S n + d))
        | E.tvar _ => abs_creator (I.caseof (I.var 0) (I.inl (I.var 0)) (I.inr (I.var 0)))
        end
  end.

Fixpoint downgradeA (n : nat) (d : nat) (τ : E.Ty) {struct n} : I.TmA
  :=
  let abs_creator := I.ia_abs (UValIE (n + d) τ) (UValIE n τ) in
  match n with
    | 0 => abs_creator (unkUValA 0 τ)
    | S n =>
      match unfoldn (LMC τ) τ with
        | E.tunit => abs_creator (I.ia_var 0)
        | E.tbool => abs_creator (I.ia_var 0)
        | E.tprod τ τ' =>
          abs_creator
            (I.ia_caseof (I.tprod (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit (UValIE (S n) (E.tprod τ τ'))
                        (I.ia_var 0)
                        (I.ia_inl (I.tprod (UValIE n τ) (UValIE n τ')) I.tunit
                           (I.ia_pair (UValIE n τ) (UValIE n τ')
                                     (I.ia_app (UValIE (n + d) τ) (UValIE n τ)
                                              (downgradeA n d τ) (I.ia_proj₁ (UValIE (n +d) τ) (UValIE (n +d) τ') (I.ia_var 0)))
                                     (I.ia_app (UValIE (n + d) τ') (UValIE n τ')
                                              (downgradeA n d τ') (I.ia_proj₂ (UValIE (n +d) τ) (UValIE (n+d) τ') (I.ia_var 0)))))
                        (I.ia_inr (I.tprod (UValIE n τ) (UValIE n τ')) I.tunit (I.ia_var 0)))
        | E.tsum τ τ' =>
          abs_creator
            (I.ia_caseof (I.tsum (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit (UValIE (S n) (E.tsum τ τ'))
                        (I.ia_var 0)
                        (I.ia_inl (I.tsum (UValIE n τ) (UValIE n τ')) I.tunit
                                 (I.ia_caseof (UValIE (n + d) τ) (UValIE (n + d) τ') (I.tsum (UValIE n τ) (UValIE n τ')) (I.ia_var 0)
                                             (I.ia_inl (UValIE n τ) (UValIE n τ') (I.ia_app (UValIE (n + d) τ) (UValIE n τ) (downgradeA n d τ)
                                                                                          (I.ia_var 0)))
                                             (I.ia_inr (UValIE n τ) (UValIE n τ') (I.ia_app (UValIE (n + d) τ') (UValIE n τ') (downgradeA n d τ')
                                                                       (I.ia_var 0)))))
                        (I.ia_inr (I.tsum (UValIE n τ) (UValIE n τ')) I.tunit (I.ia_var 0)))
        | E.tarr τ τ' =>
          abs_creator
            (I.ia_caseof (I.tarr (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit (UValIE (S n) (E.tarr τ τ'))
                        (I.ia_var 0)
                        (I.ia_inl (I.tarr (UValIE n τ) (UValIE n τ')) I.tunit
                                 (I.ia_abs (UValIE n τ) (UValIE n τ')
                                          (I.ia_app (UValIE (n + d) τ') (UValIE n τ') (downgradeA n d τ')
                                                   (I.ia_app (UValIE (n + d) τ) (UValIE (n + d) τ') (I.ia_var 1)
                                                            (I.ia_app (UValIE n τ) (UValIE (n + d) τ) (upgradeA n d τ)
                                                                     (I.ia_var 0))))))
                        (I.ia_inr (I.tarr (UValIE n τ) (UValIE n τ')) I.tunit (I.ia_var 0)))
        | E.trec τ =>
          abs_creator (unkUValA (S n) (trec τ))
        | E.tvar _ => abs_creator (I.ia_caseof I.tunit I.tunit (I.tsum I.tunit I.tunit) (I.ia_var 0) (I.ia_inl I.tunit I.tunit (I.ia_var 0)) (I.ia_inr I.tunit I.tunit (I.ia_var 0)))
      end
  end
with
upgradeA (n : nat) (d : nat) (τ : E.Ty) {struct n} :=
  let abs_creator := I.ia_abs (UValIE n τ) (UValIE (n + d) τ) in
  match n with
    | 0 => abs_creator (unkUValA d τ)
    | S n =>
      match unfoldn (LMC τ) τ with
        | E.tunit => abs_creator (I.ia_var 0)
        | E.tbool => abs_creator (I.ia_var 0)
        | E.tprod τ τ' =>
          abs_creator
            (I.ia_caseof (I.tprod (UValIE n τ) (UValIE n τ')) I.tunit (UValIE (S (n + d)) (E.tprod τ τ'))
                        (I.ia_var 0)
                        (I.ia_inl (I.tprod (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit
                           (I.ia_pair (UValIE (n + d) τ) (UValIE (n + d) τ')
                                     (I.ia_app (UValIE n τ) (UValIE (n + d) τ)
                                              (upgradeA n d τ) (I.ia_proj₁ (UValIE n τ) (UValIE n τ') (I.ia_var 0)))
                                     (I.ia_app (UValIE n τ') (UValIE (n + d) τ')
                                              (upgradeA n d τ') (I.ia_proj₂ (UValIE n τ) (UValIE n τ') (I.ia_var 0)))))
                        (I.ia_inr (I.tprod (UValIE (n+d) τ) (UValIE (n+d) τ')) I.tunit (I.ia_var 0)))
        | E.tsum τ τ' =>
          abs_creator
            (I.ia_caseof (I.tsum (UValIE n τ) (UValIE n τ')) I.tunit (UValIE (S n + d) (E.tsum τ τ'))
                        (I.ia_var 0)
                        (I.ia_inl (I.tsum (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit
                                 (I.ia_caseof (UValIE n τ) (UValIE n τ') (I.tsum (UValIE (n + d) τ) (UValIE (n + d) τ'))
                                             (I.ia_var 0)
                                             (I.ia_inl (UValIE (n + d) τ) (UValIE (n + d) τ')
                                                      (I.ia_app (UValIE n τ) (UValIE (n + d) τ) (upgradeA n d τ)
                                                                   (I.ia_var 0)))
                                             (I.ia_inr (UValIE (n + d) τ) (UValIE (n + d) τ')
                                                      (I.ia_app (UValIE n τ') (UValIE (n + d) τ') (upgradeA n d τ')
                                                               (I.ia_var 0)))))
                        (I.ia_inr (I.tsum (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit (I.ia_var 0)))
        | E.tarr τ τ' =>
          abs_creator
            (I.ia_caseof (I.tarr (UValIE n τ) (UValIE n τ')) I.tunit (UValIE (S n + d) (E.tarr τ τ'))
                        (I.ia_var 0)
                        (I.ia_inl (I.tarr (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit
                                 (I.ia_abs (UValIE (n + d) τ) (UValIE (n + d) τ')
                                          (I.ia_app (UValIE n τ') (UValIE (n + d) τ') (upgradeA n d τ')
                                                   (I.ia_app (UValIE n τ) (UValIE n τ') (I.ia_var 1)
                                                            (I.ia_app (UValIE (n + d) τ) (UValIE n τ) (downgradeA n d τ)
                                                                     (I.ia_var 0))))))
                        (I.ia_inr (I.tarr (UValIE (n + d) τ) (UValIE (n + d) τ')) I.tunit (I.ia_var 0)))
        (* | E.trec τ' => upgradeA n d (fu' (E.trec τ')) *)
        | E.trec τ =>
          abs_creator (unkUValA (S n + d) (trec τ))
        | E.tvar _ =>
          abs_creator
            (I.ia_caseof I.tunit I.tunit (I.tsum I.tunit I.tunit)
                        (I.ia_var 0)
                        (I.ia_inl I.tunit I.tunit (I.ia_var 0))
                        (I.ia_inr I.tunit I.tunit (I.ia_var 0)))
        end
  end.

Lemma upgrade_annot_T {n : nat} {Γ d τ} :
  ValidTy τ ->
  ⟪ Γ ia⊢ upgradeA n d τ : UValIE n τ r⇒ UValIE (n + d) τ ⟫
with
downgrade_annot_T {n : nat} {Γ d τ} :
  ValidTy τ ->
  ⟪ Γ ia⊢ downgradeA n d τ : UValIE (n + d) τ r⇒ UValIE n τ ⟫.
Proof.
  - induction n;
      intros vτ;
      simpl.
      + repeat constructor;
        try eapply unkUValAT;
        crushValidTy.
      + assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
        assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
        rewrite ?(UVal_eq_unfoldn vτ).
        remember (unfoldn (LMC τ) τ) as τ'.
        destruct τ'; crush.
  - induction n;
      intros vτ; simpl.
      + crush.
      + assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
        assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
        rewrite ?(UVal_eq_unfoldn vτ).
        remember (unfoldn (LMC τ) τ) as τ'.
        destruct τ'; crush.
Qed.

Lemma upgrade_annot_T1 {Γ n τ} :
  ValidTy τ ->
  ⟪ Γ ia⊢ upgradeA n 1 τ : UValIE n τ r⇒ UValIE (S n) τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using upgrade_annot_T.
Qed.

Lemma downgrade_annot_T1 {Γ n τ} :
  ValidTy τ ->
  ⟪ Γ ia⊢ downgradeA n 1 τ : UValIE (S n) τ r⇒ UValIE n τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using downgrade_annot_T.
Qed.

Lemma upgrade_annot_T1' {Γ n τ τ'} :
  ValidTy τ ->
  τ' = UValIE' (UValIE n) (unfoldn (LMC τ) τ) ->
  ⟪ Γ ia⊢ upgradeA n 1 τ : UValIE n τ r⇒ τ' ⟫.
Proof.
  intros. subst.
  now eapply upgrade_annot_T1.
Qed.

Lemma downgrade_annot_T1' {Γ n τ τ'} :
  ValidTy τ ->
  τ' = UValIE' (UValIE n) (unfoldn (LMC τ) τ) ->
  ⟪ Γ ia⊢ downgradeA n 1 τ : τ' r⇒ UValIE n τ ⟫.
Proof.
  intros. subst.
  now eapply downgrade_annot_T1.
Qed.

Ltac crushUpgradeTypingMatch :=
  repeat match goal with
    | |- ⟪ _ ia⊢ upgradeA _ _ _ : _ ⟫ => apply upgrade_annot_T1'
    | |- ⟪ _ ia⊢ downgradeA _ _ _ : _ ⟫ => apply downgrade_annot_T1'
  end.

Hint Extern 20 (⟪ _ ia⊢ upgradeA _ _ _ : _ ⟫) => crushUpgradeTypingMatch : typing.

Hint Extern 20 (⟪ _ ia⊢ downgradeA _ _ _ : _ ⟫) => crushUpgradeTypingMatch : typing.


Fixpoint upgrade_upgradeA {n d τ} {struct n} :
  eraseAnnot (upgradeA n d τ) = upgrade n d τ
  with
    downgrade_downgradeA {n d τ} {struct n} :
  eraseAnnot (downgradeA n d τ) = downgrade n d τ.
Proof.
  - destruct n.
    + cbn; rewrite <-?unkUVal_unkUValA;
      repeat f_equal.
    + cbn;
        destruct (unfoldn (LMC τ) τ);
        cbn;
        rewrite <-?unkUVal_unkUValA;
        repeat f_equal;
        eauto using downgrade_annot_T1.
  - destruct n.
    + cbn;
      rewrite <-?unkUVal_unkUValA;
      repeat f_equal.
    + cbn;
        destruct (unfoldn (LMC τ) τ);
        cbn;
        rewrite <-?unkUVal_unkUValA;
        repeat f_equal;
        eauto.
Qed.

Lemma upgrade_T {n : nat} {Γ d τ} :
  ValidTy τ ->
  ⟪ Γ i⊢ upgrade n d τ : UValIE n τ r⇒ UValIE (n + d) τ ⟫
with
downgrade_T {n : nat} {Γ d τ} :
  ValidTy τ ->
  ⟪ Γ i⊢ downgrade n d τ : UValIE (n + d) τ r⇒ UValIE n τ ⟫.
Proof.
  - revert τ;
      induction n;
      intros τ vτ;
      crush.
      assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
      assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
      rewrite ?(UVal_eq_unfoldn vτ).
      destruct (unfoldn (LMC τ) τ); crush.
  - revert τ;
      induction n;
      intros τ vτ;
      crush.
      assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
      assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
      rewrite ?(UVal_eq_unfoldn vτ).
      destruct (unfoldn (LMC τ) τ);
      crush.
Qed.

Lemma upgrade_T1 {Γ n τ} :
  ValidTy τ ->
  ⟪ Γ i⊢ upgrade n 1 τ : UValIE n τ r⇒ UValIE (S n) τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using upgrade_T.
Qed.

Lemma downgrade_T1 {Γ n τ} :
  ValidTy τ ->
  ⟪ Γ i⊢ downgrade n 1 τ : UValIE (S n) τ r⇒ UValIE n τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using downgrade_T.
Qed.

Hint Resolve upgrade_T1 : uval_typing.
Hint Resolve downgrade_T1 : uval_typing.
Hint Resolve upgrade_annot_T1 : uval_typing.
Hint Resolve downgrade_annot_T1 : uval_typing.

Lemma upgrade_closed {n d τ} :
  ValidTy τ ->
  ⟨ 0 ⊢ upgrade n d τ ⟩.
Proof.
  intros vτ.
  enough (⟪ I.empty i⊢ upgrade n d τ : UValIE n τ r⇒ UValIE (n + d) τ ⟫) as ty by eapply (wt_implies_ws ty).
  now eapply upgrade_T.
Qed.

Lemma downgrade_closed {n d τ} :
  ValidTy τ ->
  ⟨ 0 ⊢ downgrade n d τ ⟩.
Proof.
  intros vτ.
  enough (⟪ I.empty i⊢ downgrade n d τ : UValIE (n + d) τ r⇒ UValIE n τ ⟫) as ty by eapply (wt_implies_ws ty).
  now eapply downgrade_T.
Qed.

Lemma upgrade_sub {n d τ γ} :
  ValidTy τ ->
  (upgrade n d τ)[γ] = upgrade n d τ.
Proof.
  intros vτ.
  apply wsClosed_invariant.
  now eapply upgrade_closed.
Qed.

Lemma downgrade_sub {n d τ γ} :
  ValidTy τ ->
  (downgrade n d τ)[γ] = downgrade n d τ.
Proof.
  intros vτ.
  apply wsClosed_invariant.
  now eapply downgrade_closed.
Qed.

Lemma downgrade_value {n d τ} : Value (downgrade n d τ).
Proof.
  revert d τ;
    induction n; intros; simpl;
    destruct (unfoldn (LMC τ) τ); simpl; trivial.
Qed.

Lemma upgrade_value {n d τ} : Value (upgrade n d τ).
Proof.
  revert d τ;
    induction n; intros; simpl;
    destruct (unfoldn (LMC τ) τ); simpl; trivial.
Qed.

Lemma downgrade_unfoldn {n d τ} :
  ValidTy τ ->
  downgrade n d τ = downgrade n d (unfoldn (LMC τ) τ).
Proof.
  induction n; intros vτ; cbn.
  - erewrite UValIE_unfoldn; try reflexivity.
    crushValidTy.
  - erewrite unfoldn_LMC; cbn; crushValidTy.
    rewrite <-(UValIE_unfoldn (m := LMC τ)); crushValidTy.
Qed.

Lemma upgrade_unfoldn {n d τ} :
  ValidTy τ ->
  upgrade n d τ = upgrade n d (unfoldn (LMC τ) τ).
Proof.
  induction n; intros vτ; cbn.
  - erewrite UValIE_unfoldn; try reflexivity.
    crushValidTy.
  - erewrite unfoldn_LMC; cbn; crushValidTy.
    rewrite <-(UValIE_unfoldn (m := LMC τ)); crushValidTy.
Qed.

Lemma downgrade_zero_eval {d τ v} : Value v → app (downgrade 0 d τ) v -->* unkUVal 0.
Proof.
  intros vv.
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  simpl; eauto with eval.
Qed.

Lemma upgrade_zero_eval {d τ v} : Value v → app (upgrade 0 d τ) v -->* unkUVal d.
Proof.
  intros vv.
  unfold upgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  destruct d; simpl; eauto with eval.
Qed.

Lemma downgrade_eval_unk {n d τ} :
  ValidTy τ ->
  app (downgrade n d τ) (unkUVal (n + d)) -->* unkUVal n.
Proof.
  intros vτ.
  assert (vv : Value (unkUVal (n + d))) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    simpl; eauto with eval.
  - change _ with (Value (inr unit)) in vv.
    assert (ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
    destruct (unfoldn (LMC τ) τ);
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
    subst; cbn; crush; rewrite ?downgrade_sub, ?upgrade_sub;
      crushValidTy;
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_case_inr _) I); eauto;
    crush.
Qed.

Lemma upgrade_eval_unk {n d τ} :
  ValidTy τ ->
  app (upgrade n d τ) (unkUVal n) -->* unkUVal (n + d).
Proof.
  intros vτ.
  assert (vv : Value (unkUVal n)) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval.
    repeat constructor.
    destruct d;
    simpl; eauto with eval.
  - assert (ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
    destruct (unfoldn (LMC τ) τ);
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_beta _) I);
    crush;
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_case_inr _) I);
    crush.
Qed.

Lemma downgrade_eval_inUnit {n d} :
  app (downgrade (S n) d E.tunit) (I.inl I.unit) -->* I.inl I.unit.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply I.eval_beta.
  all: eauto with eval.
  crush.
Qed.

Lemma upgrade_eval_inUnit {n d} :
  app (upgrade (S n) d E.tunit) (I.inl I.unit) -->* I.inl I.unit.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply I.eval_beta.
  all: eauto with eval.
  crush.
Qed.

Lemma downgrade_eval_inBool {n d v} (vv : Value v) :
  app (downgrade (S n) d E.tbool) (I.inl v) -->* I.inl v.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply I.eval_beta; now cbn.
  crush.
Qed.

Lemma upgrade_eval_inBool {n d v} (vv : Value v):
  app (upgrade (S n) d E.tbool) (I.inl v) -->* I.inl v.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply I.eval_beta; now cbn.
  crush.
Qed.

Lemma downgrade_eval_inSum {n d v v' va va' τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  Value v → Value v' →
  (va = inl v ∧ va' = inl v' ∧ app (downgrade n d τ) v -->* v')
  ∨ (va = inr v ∧ va' = inr v' ∧ app (downgrade n d τ') v -->* v') →
  app (downgrade (S n) d (E.tsum τ τ')) (I.inl va) -->* I.inl va'.
Proof.
  intros vτ vτ' vv vv' eqs.
  cbn.
  destruct eqs as [(? & ? & ?)|(? & ? & ?)]; subst;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
    eauto;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
    eauto;
    eapply evalStepStar;
  [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); crush|
  |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); crush|];
  cbn; crush; rewrite ?upgrade_sub, ?downgrade_sub;
    crushValidTy;
  [change (I.inl (I.inl ?t)) with (pctx_app t (pinl (pinl phole)))
  |change (I.inl (I.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
  apply evalstar_ctx;
  cbn;
  trivial.
Qed.

Lemma downgrade_eval_inProd {n d v1 v2 v1' v2' τ1 τ2} :
  ValidTy τ1 -> ValidTy τ2 ->
  Value v1 -> Value v2 → Value v1' → Value v2' →
  app (downgrade n d τ1) v1 -->* v1' ->
  app (downgrade n d τ2) v2 -->* v2' ->
  app (downgrade (S n) d (E.tprod τ1 τ2)) (I.inl (pair v1 v2)) -->* I.inl (pair v1' v2').
Proof.
  intros vτ1 vτ2 vv1 vv2 vv1' vv2' es1 es2.
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_beta; now cbn. }
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_case_inl; now cbn. }
  crushTyping.
  rewrite ?downgrade_sub;
    eauto.
  eapply evalStepStar.
  { refine (eval_from_eval₀ (eval_proj₁ vv1 vv2) _ _ _); I.inferContext.
    cbn; eauto using downgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es1); I.inferContext; now cbn. }
  eapply evalStepStar.
  { eapply (eval_from_eval₀ (eval_proj₂ vv1 vv2)); I.inferContext.
      cbn; eauto using downgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es2); I.inferContext; now cbn. }
  crush.
Qed.

Lemma upgrade_eval_inProd {n d v1 v2 v1' v2' τ1 τ2} :
  ValidTy τ1 -> ValidTy τ2 ->
  Value v1 -> Value v2 → Value v1' → Value v2' →
  app (upgrade n d τ1) v1 -->* v1' ->
  app (upgrade n d τ2) v2 -->* v2' ->
  app (upgrade (S n) d (E.tprod τ1 τ2)) (I.inl (pair v1 v2)) -->* I.inl (pair v1' v2').
Proof.
  intros vτ1 vτ2 vv1 vv2 vv1' vv2' es1 es2.
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_beta; now cbn. }
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_case_inl; now cbn. }
  crushTyping.
  rewrite ?upgrade_sub; crushValidTy.
  eapply evalStepStar.
  { refine (eval_from_eval₀ (eval_proj₁ vv1 vv2) _ _ _); I.inferContext.
    cbn; eauto using upgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es1); I.inferContext; now cbn. }
  eapply evalStepStar.
  { eapply (eval_from_eval₀ (eval_proj₂ vv1 vv2)); I.inferContext; cbn; eauto using upgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es2); I.inferContext; now cbn. }
  crush.
Qed.

Lemma upgrade_eval_inSum {n d v v' va va' τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  Value v → Value v' →
  (va = inl v ∧ va' = inl v' ∧ app (upgrade n d τ) v -->* v')
  ∨ (va = inr v ∧ va' = inr v' ∧ app (upgrade n d τ') v -->* v') →
  app (upgrade (S n) d (E.tsum τ τ')) (I.inl va) -->* I.inl va'.
Proof.
  intros vτ vτ' vv vv' eqs.
  cbn.
  destruct eqs as [(? & ? & ?)|(? & ? & ?)]; subst;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
    crushValidTy;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
    crushValidTy;
    eapply evalStepStar;
  [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); crush|
  |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); crush|];
  cbn; crush; rewrite ?upgrade_sub, ?downgrade_sub;
    crushValidTy;
  [change (I.inl (I.inl ?t)) with (pctx_app t (pinl (pinl phole)))
  |change (I.inl (I.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
  apply evalstar_ctx;
  cbn;
  trivial.
Qed.


Lemma downgrade_eval_inArr {n d v τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  Value v →
  app (downgrade (S n) d (E.tarr τ τ')) (I.inl v) -->*
     I.inl (abs (UValIE n τ) (app (downgrade n d τ') (app (v[wk]) (app (upgrade n d τ) (var 0))))).
Proof.
  intros vτ vτ' vv.
  cbn.

  (* beta-reduce *)
  ((eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
      rewrite -> ?upgrade_sub, ?downgrade_sub);
  crushValidTy;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  crushValidTy;
  change (wk 0) with 1; simpl;
  eauto with eval.
Qed.

Lemma upgrade_eval_inArr {n d v τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  Value v →
  app (upgrade (S n) d (E.tarr τ τ')) (I.inl v) -->*
     I.inl (abs (UValIE (n + d) τ) (app (upgrade n d τ') (app (v[wk]) (app (downgrade n d τ) (var 0))))).
Proof.
  intros vτ vτ' vv.
  cbn.

  (* beta-reduce *)
  ((eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
      rewrite -> ?upgrade_sub, ?downgrade_sub);
  crushValidTy;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  crushValidTy;
  change (wk 0) with 1; simpl;
  eauto with eval.
Qed.

Lemma downgrade_eval_inRec {n d τ} :
  ValidTy τ ->
  downgrade n d τ[beta1 (E.trec τ)] = downgrade n d (E.trec τ).
      (* I.inl (app (downgrade n d τ[beta1 (E.trec τ)]) v). *)
Proof.
  intros vτ.
  induction n; simpl.
  - rewrite UValIE_trec;
    now crushValidTy.
  - unfold UValIE.
    change (τ[beta1 (E.trec τ)]) with (unfoldOnce (trec τ)).
    rewrite (LMC_unfoldOnce (trec τ)); crushValidTy.
    cbn; lia.
Qed.

Lemma upgrade_eval_inRec {n d τ} :
  ValidTy τ ->
  upgrade n d τ[beta1 (E.trec τ)] = upgrade n d (E.trec τ).
Proof.
  intros vτ.
  induction n; cbn.
  - rewrite ?UValIE_trec;
    now crushValidTy.
  - unfold UValIE.
    change (τ[beta1 (E.trec τ)]) with (unfoldOnce (trec τ)).
    rewrite (LMC_unfoldOnce (trec τ)); crushValidTy; cbn.
    cbn; lia.
Qed.

Lemma downgrade_reduces {n d v τ} :
  ValidTy τ ->
  ⟪ I.empty i⊢ v : UValIE (n + d) τ ⟫ → Value v →
  exists v', Value v' ∧ ⟪ I.empty i⊢ v' : UValIE n τ ⟫ ∧
             app (downgrade n d τ) v -->* v'.
Proof.
  revert τ;
  revert v; induction n;
  intros v τ vτ ty vv.
  - exists (unkUVal 0).
    eauto using unkUVal_Value, unkUValT, downgrade_zero_eval.
  - change (S n + d) with (S (n + d)) in ty.
    unfold downgrade, UValIE.
    cbn.
    unfold UValIE in ty.
    cbn in ty.
    assert (ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
    assert (LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
    destruct (unfoldn (LMC τ) τ).
    + destruct (canonUValS_Arr vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (I.can_form_tarr H1 H3).
        exists (I.inl (I.abs (UValIE n t1) (I.app (downgrade n d t2)
                                             (I.app x
                                                    (I.app (upgrade n d t1)
                                                           (* x))))). *)
                                                           (I.var 0)))))).
        eapply ValidTy_invert_arr in H.
        destruct H as (? & ?).
        repeat split.
        replace x with x [wk] by (eapply wsClosed_invariant;
                                  refine (I.wt_implies_ws H3)).
        crush;
        eauto using downgrade_T, upgrade_T with typing ws tyvalid tyvalid2.
        now eapply UValIE_valid.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub;
          try assumption.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub;
          try assumption.
        change ((beta1 x)↑ (wk 0)) with x [wk].
        replace x[wkm] with x; [econstructor|].
        eapply eq_sym, wsClosed_invariant.
        refine (I.wt_implies_ws H3).
        (* eauto using inArr_Value, downgrade_eval_inArr, inArr_T,  *)
        (* downgrade_T, upgrade_T with typing. *)
      * exists (unkUVal (S n)).
        eapply ValidTy_invert_arr in H.
        destruct H as (? & ?).
        repeat split.
        refine (unkUValT (τ := t1 r⇒ t2) _); crush.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub;
        try assumption.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
        cbn; eauto with eval.
    + destruct (canonUValS_Unit (n := n + d) vv ty) as [? | ?].
      * exists v.
        repeat split.
        assumption.
        subst.
        eauto with typing ws.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        crush.
      * exists (unkUVal (S n)).
        repeat split.
        refine (unkUValT (τ := E.tunit) _); crush.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; crush.
    + destruct (canonUValS_Bool (n := n + d) vv ty) as [? | [?|?]]; destruct_conjs; subst.
      * exists (I.inl I.true); crush.
        split; crush.
        split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (I.inl I.false); crush.
        split; crush.
        split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (I.inr I.unit); crush.
        split; crush.
        split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
    + destruct (canonUValS_Prod vv ty) as [?| ?]; destruct_conjs; subst.
      eapply ValidTy_invert_prod in H.
      destruct H as (? & ?).
      stlcCanForm.
      destruct vv as (vx & vx0).
      destruct (IHn x t1 H H6 vx) as (v1 & vv1 & tv1 & es1).
      destruct (IHn x0 t2 H3 H7 vx0) as (v2 & vv2 & tv2 & es2).
      * exists (inl (pair v1 v2)); crush.
        split; crush.
        split; crush.
        eapply downgrade_eval_inProd; eauto.
      * exists (I.inr I.unit); crush.
      * exists (I.inr I.unit); crush.
        split; crush.
        split; crush.
        now eapply UValIE_valid.
        now eapply UValIE_valid.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); now cbn.
        crush.
    + eapply ValidTy_invert_sum in H.
      destruct H as (? & ?).
      destruct (canonUValS_Sum vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (I.can_form_tsum H2 H4) as [(? & ? & ?) | (? & ? & ?)];
        assert (I.Value x0) by (subst; trivial);
        [destruct (IHn _ _ H H6) as (vf & vvf & tyf & ex)
        |destruct (IHn _ _ H1 H6) as (vf & vvf & tyf & ex)];
        try assumption;
        [exists (I.inl (I.inl vf)) | exists (I.inl (I.inr vf))];
        repeat split;
        crush; try (now eapply UValIE_valid);
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_beta _) I); crush;
          rewrite ?downgrade_sub; crushValidTy;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_case_inl _) I); crush;
        rewrite ?downgrade_sub; crushValidTy;
        eapply evalStepStar;
        [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); eauto | idtac
        |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); eauto | idtac];
          rewrite ?downgrade_sub; crushValidTy;
          cbn;
        [change (I.inl (I.inl ?t)) with (pctx_app t (pinl (pinl phole)))
        |change (I.inl (I.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
        apply evalstar_ctx;
        cbn;
        crush;
        now rewrite downgrade_sub.
      * exists (unkUVal (S n)).
        repeat split.
        refine (unkUValT (τ := t1 r⊎ t2) _); crush.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub; crushValidTy.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); crush.
        crush.
    + exfalso. cbn in *. lia.
    + exfalso. destruct H.
      inversion H.
      inversion H3.
Qed.

Lemma upgrade_reduces {n v τ } d :
  ValidTy τ ->
  ⟪ I.empty i⊢ v : UValIE n τ ⟫ → Value v →
  exists v', Value v' ∧ ⟪ I.empty i⊢ v' : UValIE (n + d) τ ⟫ ∧
             app (upgrade n d τ) v -->* v'.
Proof.
  revert τ;
  revert v; induction n;
  intros v τ vτ ty vv.
  - exists (unkUVal d).
    eauto using unkUVal_Value, unkUValT, upgrade_zero_eval.
  - change (S n + d) with (S (n + d)).
    unfold downgrade, UValIE.
    cbn.
    unfold UValIE in ty.
    cbn in ty.
    assert (vτ' : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
    assert (lτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
    destruct (unfoldn (LMC τ) τ).
    + eapply ValidTy_invert_arr in vτ'.
      destruct vτ' as (vt1 & vt2).
      destruct (canonUValS_Arr vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (I.can_form_tarr H H1).
        exists (I.inl (I.abs (UValIE (n + d) t1) (I.app (upgrade n d t2)
                                             (I.app x
                                                    (I.app (downgrade n d t1)
                                                           (* x))))). *)
                                                           (I.var 0)))))).
        repeat split.
        replace x with x [wk] by (eapply wsClosed_invariant;
                                  refine (I.wt_implies_ws H1)).

        I.crushTyping;
        eauto using downgrade_T, upgrade_T, UValIE_valid with typing ws.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub; eauto.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        cbn; crush; rewrite downgrade_sub, upgrade_sub; eauto.
        replace x[wkm] with x; [econstructor|].
        eapply eq_sym, wsClosed_invariant.
        refine (I.wt_implies_ws H1).
        (* eauto using inArr_Value, downgrade_eval_inArr, inArr_T,  *)
        (* downgrade_T, upgrade_T with typing. *)
      * exists (unkUVal (S (n + d))).
        repeat split.
        refine (unkUValT (τ := t1 r⇒ t2) _); crushValidTy.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub; eauto.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); crush.
        crush.
    + destruct (canonUValS_Unit (n := n) vv ty) as [? | ?].
      * exists v.
        repeat split.
        assumption.
        rewrite H.
        eauto with typing ws.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        crush.
      * exists (unkUVal (S (n + d))).
        repeat split.
        refine (unkUValT (τ := E.tunit) _); crushValidTy.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; crush.
    + destruct (canonUValS_Bool (n := n) vv ty) as [? | [?|?]]; destruct_conjs; subst.
      * exists (I.inl I.true); crush.
        repeat split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (I.inl I.false); repeat split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (I.inr I.unit); repeat split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
    + eapply ValidTy_invert_prod in vτ'.
      destruct vτ' as (vt1 & vt2).
      destruct (canonUValS_Prod vv ty) as [?| ?]; destruct_conjs; subst.
      stlcCanForm.
      destruct vv as (vx & vx0).
      destruct (IHn x t1 vt1 H3 vx) as (v1 & vv1 & tv1 & es1).
      destruct (IHn x0 t2 vt2 H4 vx0) as (v2 & vv2 & tv2 & es2).
      * exists (inl (pair v1 v2)); repeat split; crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); now cbn.
        cbn.
        crush.
        rewrite ?upgrade_sub; eauto.
        eapply evalStepStar.
        refine (eval_ctx₀ (pinl (ppair₁ (papp₂ _ phole) _)) (eval_proj₁ _ _) _); cbn; eauto using upgrade_value.
        cbn.
        eapply evalStepTrans.
        eapply (evalstar_ctx' es1); I.inferContext; now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ (pinl (ppair₂ _ (papp₂ _ phole))) (eval_proj₂ _ _) _); cbn; eauto using upgrade_value.
        cbn.
        eapply (evalstar_ctx' es2); I.inferContext; now cbn.
      * exists (I.inr I.unit); crush.
      * exists (I.inr I.unit); repeat split; crush.
        refine (UValIE_valid _); crushValidTy.
        refine (UValIE_valid _); crushValidTy.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); now cbn.
        crush.
    + eapply ValidTy_invert_sum in vτ'.
      destruct vτ' as (vt1 & vt2).
      destruct (canonUValS_Sum vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (I.can_form_tsum H H1) as [(? & ? & ?) | (? & ? & ?)];
        assert (I.Value x0) by (rewrite H2 in H; trivial);
          [destruct (IHn _ _ vt1 H3 H4) as (vf & vvf & tyf & ex)
          |destruct (IHn _ _ vt2 H3 H4) as (vf & vvf & tyf & ex)];
        [exists (I.inl (I.inl vf)) | exists (I.inl (I.inr vf))];
        repeat split;
        try (simpl; trivial; fail);
          try crushTyping;
        try (eauto using tyf, UValIE_valid with typing ws);
        subst;
        cbn;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
        subst; cbn; crush; rewrite ?upgrade_sub; eauto;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_case_inl _) I); eauto;
        subst; cbn; crush; rewrite ?upgrade_sub; eauto;
        eapply evalStepStar;
        [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); eauto | idtac
        |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); eauto | idtac];
        subst; cbn; crush; rewrite ?upgrade_sub; eauto;
        [change (I.inl (I.inl ?t)) with (pctx_app t (pinl (pinl phole)))
        |change (I.inl (I.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
        apply evalstar_ctx;
        cbn;
        trivial.
      * exists (unkUVal (S (n + d))).
        repeat split.
        refine (unkUValT (τ := t1 r⊎ t2) _); crushValidTy.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite upgrade_sub; eauto.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); crush.
        crush.
    + cbn in lτz.
      exfalso; lia.
    + inversion vτ'.
      inversion H.
      inversion H2.
Qed.

Definition dir_world_prec (n : nat) (w : World) (d : Direction) (p : Prec) : Prop :=
  (lev w < n ∧ p = precise) ∨ (d = dir_lt ∧ p = imprecise).

Arguments dir_world_prec n w d p : simpl never.

Lemma dwp_zero {w d p} : dir_world_prec 0 w d p → p = imprecise ∧ d = dir_lt.
Proof.
  destruct 1 as [[? ?]|[? ?]].
  - depind H.
  - auto.
Qed.

Lemma dwp_precise {n d w} : lev w < n → dir_world_prec n w d precise.
Proof.
  left; auto.
Qed.

Lemma dwp_imprecise {n w} : dir_world_prec n w dir_lt imprecise.
Proof.
  right; auto.
Qed.

Lemma dwp_invert_imprecise {n w d} : dir_world_prec n w d imprecise → d = dir_lt.
Proof.
  destruct 1 as [[? ?]|[? ?]].
  - inversion H0.
  - auto.
Qed.

Lemma dwp_invert_gt {n w p} : dir_world_prec n w dir_gt p → p = precise /\ lev w < n.
Proof.
  destruct 1 as [[? ?]|[eq ?]]; [auto|inversion eq].
Qed.

Lemma dwp_invert_S {w d p n} : dir_world_prec (S n) (S w) d p → dir_world_prec n w d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.

Lemma dwp_invert_S' {w d p n} : 
  dir_world_prec (S n) w d p → 
  forall w', w' < w → dir_world_prec n w' d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.

Lemma dwp_mono {w d p n} :
  dir_world_prec n w d p →
  forall w', w' ≤ w → dir_world_prec n w' d p.
Proof.
  destruct 1 as [[? ?]|[? ?]]; [left|right];
  eauto with arith.
Qed.

Lemma downgrade_inProd_works {n d w dir p vs vu τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  valrel dir w (pEmulDV (S (n + d)) p (E.tprod τ τ')) (I.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  exists v',
    app (downgrade (S n) d (E.tprod τ τ')) (I.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (E.tprod τ τ')) v' vu.
Proof.
  intros vτ vτ' vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].
  destruct (invert_valrel_pEmulDV_inProd' vτ vτ' vr) as (vs1 & vs2 & vu1 & vu2 & -> & -> & vr1 & vr2).
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Prod vvs tvs) as [(? & ? & ? & ?) | ?]; [| inversion H].
    I.stlcCanForm. inversion H0; subst.
    destruct H as (vx2 & vx3).
    destruct (downgrade_reduces vτ H3 vx2) as (x4 & vx4 & tyx4 & esx4).
    destruct (downgrade_reduces vτ' H4 vx3) as (x5 & vx5 & tyx5 & esx5).
    exists (inl (pair x4 x5)); split; E.crushTyping.
    * eapply downgrade_eval_inProd; eauto.
    * subst.
      assert (ValidEnv E.empty) by eauto with tyvalid.
      apply valrel_inProd''; eauto;
        apply valrel_0_pair; repeat crushValidPTyMatch; crush.
      eauto using typed_terms_are_valid.
      eapply E.typed_terms_are_valid; eauto.
      eapply E.typed_terms_are_valid; eauto.
  + (* w = S w *)
    (* destruct vr as (? & [([=] & _)|(? & -> & vr')]). *)
    (* unfold prod_rel in vr'; cbn in vr'. *)
    (* destruct x; cbn in vr'; try contradiction. *)
    assert (wlt : w < S w) by eauto with arith.
    specialize (vr1 w wlt).
    specialize (vr2 w wlt).
    cbn in *.
    destruct (ih w _ _ _ wlt vτ vr1) as (vs1' & es1 & vr1').
    destruct (ih w _ _ _ wlt vτ' vr2) as (vs2' & es2 & vr2').
    destruct vvs as (vvs1 & vvs2).
    destruct (valrel_implies_Value vr1').
    destruct (valrel_implies_Value vr2').
    exists (I.inl (I.pair vs1' vs2'));
    split.
    * apply (downgrade_eval_inProd vτ vτ' vvs1 vvs2); eauto.
    * eapply (valrel_inProd'); assumption.
Qed.

Lemma upgrade_inProd_works {n d w dir p vs vu τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  valrel dir w (pEmulDV (S n) p (E.tprod τ τ')) (I.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              (* valrel dir w' (pEmulDV (n + d) p τ') vs₁ vu₁) → *)
              (* ∃ vs₁', app (downgrade n d (E.tprod τ τ')) vs₁ -->* vs₁' ∧ *)
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
                      (* valrel dir w' (pEmulDV n p (E.tprod τ τ')) vs₁' vu₁) → *)
  exists v',
    app (upgrade (S n) d (E.tprod τ τ')) (I.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (E.tprod τ τ')) v' vu.
Proof.
  intros vτ vτ' vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].
  destruct (invert_valrel_pEmulDV_inProd' vτ vτ' vr) as (vs1 & vs2 & vu1 & vu2 & -> & -> & vr1 & vr2).
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Prod vvs tvs) as [(? & ? & ? & ?) | ?]; [| inversion H].
    I.stlcCanForm. inversion H0; subst.
    destruct H as (vx2 & vx3).
    destruct (upgrade_reduces d vτ H3 vx2) as (x4 & vx4 & tyx4 & esx4).
    destruct (upgrade_reduces d vτ' H4 vx3) as (x5 & vx5 & tyx5 & esx5).
    exists (inl (pair x4 x5)); split; E.crushTyping.
    * eapply upgrade_eval_inProd; eauto.
    * subst.
      assert (ValidEnv E.empty) by eauto with tyvalid.
      apply valrel_inProd''; eauto;
        apply valrel_0_pair; repeat crushValidPTyMatch; eauto.
      crushOfType; repeat crushValidPTyMatch; E.crushTyping; eapply E.typed_terms_are_valid; eauto.
      crushOfType; repeat crushValidPTyMatch; E.crushTyping; eapply E.typed_terms_are_valid; eauto.
  + assert (wlt : w < S w) by eauto with arith.
    specialize (vr1 w wlt).
    specialize (vr2 w wlt).
    cbn in *.
    destruct (ih w _ _ _ wlt vτ vr1) as (vs1' & es1 & vr1').
    destruct (ih w _ _ _ wlt vτ' vr2) as (vs2' & es2 & vr2').
    destruct vvs as (vvs1 & vvs2).
    destruct (valrel_implies_Value vr1').
    destruct (valrel_implies_Value vr2').
    exists (I.inl (I.pair vs1' vs2'));
    split.
    * apply (upgrade_eval_inProd vτ vτ' vvs1 vvs2); eauto.
    * eapply (valrel_inProd'); assumption.
Qed.

Lemma downgrade_inSum_works {n d w dir p vs vu τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  valrel dir w (pEmulDV (S (n + d)) p (E.tsum τ τ')) (I.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              (* valrel dir w' (pEmulDV (n + d) p τ') vs₁ vu₁) → *)
              (* ∃ vs₁', app (downgrade n d (E.tsum τ τ')) vs₁ -->* vs₁' ∧ *)
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
                      (* valrel dir w' (pEmulDV n p (E.tsum τ τ')) vs₁' vu₁) → *)
  exists v',
    app (downgrade (S n) d (E.tsum τ τ')) (I.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (E.tsum τ τ')) v' vu.
Proof.
  intros vτ vτ' vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  destruct (invert_valrel_pEmulDV_inSum'' vτ vτ' vr) as (vs' & vu' & ?); subst.
  simpl in H0, H2.
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Sum H H0) as [(? & ? & ? & ?) | ?]; [| inversion H4].
    inversion H5; subst.
    I.stlcCanForm1;
    [destruct (downgrade_reduces vτ H8 H4) as (vs'' & vvs'' & ty' & es')
    |destruct (downgrade_reduces vτ' H8 H4) as (vs'' & vvs'' & ty' & es')];
    destruct H3 as [(? & ? & ?) | (? & ? & ?)]; try (inversion H3; fail); inversion H3; subst;
    assert (ValidEnv E.empty) by (eauto with tyvalid).
    * exists ((I.inl (I.inl vs''))).
      assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu') by lia.
      split; [apply (downgrade_eval_inSum vτ vτ' H4 vvs''); crush|].
      crush.
      eapply valrel_inSum_l; crush.
      eauto using E.typed_terms_are_valid.
    * exists ((I.inl (I.inr vs''))).
      split; [apply (downgrade_eval_inSum vτ vτ' H4 vvs''); crush|].
      eapply valrel_inSum_r; crush.
      eauto using E.typed_terms_are_valid.
  + (* w = S w *)
    assert (wlt : w < S w) by lia.
    destruct H3 as [(? & ? & vr') | (? & ? & vr')]; try (inversion H3; fail); subst;
    specialize (vr' w wlt);
    assert (ValidEnv E.empty) by eauto with tyvalid.
    * destruct (ih w _ _ _ wlt vτ vr') as (vs'' & es' & vr'').
      destruct (valrel_implies_Value vr'').
      exists (I.inl (I.inl vs'')).
      split.
      apply (downgrade_eval_inSum (v := vs') vτ vτ' H H4); eauto.
      eapply valrel_inSum'; crush.
    * destruct (ih w _ _ _ wlt vτ' vr') as (vs'' & es' & vr'').
      destruct (valrel_implies_Value vr'').
      exists (I.inl (I.inr vs'')).
      split.
      apply (downgrade_eval_inSum (v := vs') vτ vτ' H H4); eauto.
      eapply valrel_inSum'; crush.
Qed.

Lemma upgrade_inSum_works {n d w dir p vs vu τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  valrel dir w (pEmulDV (S n) p (E.tsum τ τ')) (I.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              (* valrel dir w' (pEmulDV (n + d) p τ') vs₁ vu₁) → *)
              (* ∃ vs₁', app (downgrade n d (E.tsum τ τ')) vs₁ -->* vs₁' ∧ *)
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
                      (* valrel dir w' (pEmulDV n p (E.tsum τ τ')) vs₁' vu₁) → *)
  exists v',
    app (upgrade (S n) d (E.tsum τ τ')) (I.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (E.tsum τ τ')) v' vu.
Proof.
  intros vτ vτ' vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  destruct (invert_valrel_pEmulDV_inSum'' vτ vτ' vr) as (vs' & vu' & ?); subst.
  simpl in H0, H2.
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Sum H H0) as [(? & ? & ? & ?) | ?]; [| inversion H4].
    I.stlcCanForm1; inversion H5; subst;
    [destruct (upgrade_reduces d vτ H8 H4) as (vs'' & vvs'' & ty' & es')
    | destruct (upgrade_reduces d vτ' H8 H4) as (vs'' & vvs'' & ty' & es')
    ];
    destruct H3 as [(? & ? & ?) | (? & ? & ?)]; try (inversion H3; fail); inversion H3; subst;
    [exists ((I.inl (I.inl vs''))) | exists ((I.inl (I.inr vs'')))];
    (split; [apply (upgrade_eval_inSum vτ vτ' H4 vvs''); crush|]);
    assert (ValidEnv E.empty) by eauto with tyvalid;
    assert (vτs := E.typed_terms_are_valid _ _ H6 H2);
    destruct (ValidTy_invert_sum vτs);
    apply valrel_inSum''; crush.
    * apply valrel_0_inl; try crushValidPTyMatch; crush;
      eauto using E.typed_terms_are_valid.
    * apply valrel_0_inr; try crushValidPTyMatch; crush;
      eauto using E.typed_terms_are_valid.
  + (* w = S w *)
    assert (wlt : w < S w) by eauto with arith;
    destruct H3 as [(? & ? & vr') | (? & ? & vr')]; try (inversion H3; fail); subst;
    specialize (vr' w wlt);
    cbn in H.
    assert (ValidEnv E.empty) by eauto with tyvalid;
    assert (vτs := E.typed_terms_are_valid _ _ H3 H2);
    destruct (ValidTy_invert_sum vτs).
    * destruct (ih w _ _ _ wlt vτ vr') as (vs'' & es' & vr'').
      destruct (valrel_implies_Value vr'').
      exists (I.inl (I.inl vs'')).
      split.
      apply (upgrade_eval_inSum vτ vτ' H H6); eauto.
      eapply valrel_inSum'; crush.
    * destruct (ih w _ _ _ wlt vτ' vr') as (vs'' & es' & vr'').
      destruct (valrel_implies_Value vr'').
      exists (I.inl (I.inr vs'')).
      split.
      apply (upgrade_eval_inSum vτ vτ' H H3); eauto.
      eapply valrel_inSum'; crush.
Qed.


(* Lemma downgrade_inRec_works {n d w dir p vs vu τ} : *)
(*   ValidTy (E.trec τ) -> *)
(*   valrel dir w (pEmulDV (S (n + d)) p (E.trec τ)) (I.inl vs) vu → *)
(*   (forall w' vs₁ vu₁ τ, w' < w → *)
(*                    ValidTy τ -> *)
(*               valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ → *)
(*               ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧ *)
(*                       valrel dir w' (pEmulDV n p τ) vs₁' vu₁) → *)
(*   exists v', *)
(*     app (downgrade (S n) d (E.trec τ)) (I.inl vs) -->* v' ∧ *)
(*     valrel dir w (pEmulDV (S n) p (E.trec τ)) v' vu. *)
(* Proof. *)
(*   intros vτ vr ih. *)
(*   destruct (valrel_implies_OfType vr) as [[? ?] [? ?]]. *)
(*   simpl in H0, H2. *)
(*   destruct w. *)
(*   + (* w = 0 *) *)
(*     destruct (canonUValS_Rec H H0) as [(? & ? & ? & ?) | ?]; [| inversion H3]. *)
(*     inversion H4; subst. *)
(*     destruct (downgrade_reduces H5 H3) as (vs'' & vvs'' & ty' & es'). *)
(*     assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu) by lia. *)
(*     exists (I.inl vs''). *)
(*     split. *)
(*     exact (downgrade_eval_inRec H3 vvs'' es'). *)
(*     apply valrel_0_inRec. *)
(*     crush. *)
(*   + (* w = S w *) *)
(*     pose proof (invert_valrel_pEmulDV_inRec vr). *)
(*     assert (wlt : w < S w) by eauto with arith. *)
(*     assert (vτ' : ValidTy (τ[beta1 (E.trec τ)])) by now eapply ValidTy_unfold_trec. *)
(*     destruct (ih _ _ _ _ wlt vτ' H3) as (? & ? & ?). *)
(*     exists (I.inl x). *)
(*     split. *)
(*     destruct (valrel_implies_OfType H5) as [[? _] _]. *)
(*     apply downgrade_eval_inRec; crush. *)
(*     now apply valrel_inRec. *)
(* Qed. *)

(* Lemma upgrade_inRec_works {n d w dir p vs vu τ} : *)
(*   ValidTy (E.trec τ) -> *)
(*   valrel dir w (pEmulDV (S n) p (E.trec τ)) (I.inl vs) vu → *)
(*   (forall w' vs₁ vu₁ τ, w' < w → *)
(*                    ValidTy τ -> *)
(*               valrel dir w' (pEmulDV n p τ) vs₁ vu₁ → *)
(*               ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧ *)
(*                       valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) → *)
(*   exists v', *)
(*     app (upgrade (S n) d (E.trec τ)) (I.inl vs) -->* v' ∧ *)
(*     valrel dir w (pEmulDV (S (n + d)) p (E.trec τ)) v' vu. *)
(* Proof. *)
(*   intros vτ vr ih. *)
(*   destruct (valrel_implies_OfType vr) as [[? ?] [? ?]]. *)
(*   simpl in H0, H2. *)
(*   destruct w. *)
(*   + (* w = 0 *) *)
(*     destruct (canonUValS_Rec H H0) as [(? & ? & ? & ?) | ?]; [| inversion H3]. *)
(*     inversion H4; subst. *)
(*     destruct (upgrade_reduces d H5 H3) as (vs'' & vvs'' & ty' & es'). *)
(*     assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu) by lia. *)
(*     exists (I.inl vs''). *)
(*     split. *)
(*     exact (upgrade_eval_inRec H3 vvs'' es'). *)
(*     apply valrel_0_inRec. *)
(*     crush. *)
(*   + (* w = S w *) *)
(*     pose proof (invert_valrel_pEmulDV_inRec vr). *)
(*     assert (wlt : w < S w) by eauto with arith. *)
(*     assert (vτ' : ValidTy (τ[beta1 (E.trec τ)])) by now eapply ValidTy_unfold_trec. *)
(*     destruct (ih _ _ _ _ wlt vτ' H3) as (? & ? & ?). *)
(*     exists (I.inl x). *)
(*     split. *)
(*     destruct (valrel_implies_OfType H5) as [[? _] _]. *)
(*     apply upgrade_eval_inRec; crush. *)
(*     now apply valrel_inRec. *)
(* Qed. *)

Lemma downgrade_inArr_works {n d w dir p vs vu τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  valrel dir w (pEmulDV (S (n + d)) p (E.tarr τ τ')) (I.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
  exists v',
    app (downgrade (S n) d (E.tarr τ τ')) (I.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (E.tarr τ τ')) v' vu.
Proof.
  intros vτ vτ' vr ihd ihu.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  exists (I.inl (abs (UValIE n τ) (app (downgrade n d τ') (app (vs[wk]) (app (upgrade n d τ) (var 0)))))).
  split.
  - eapply downgrade_eval_inArr; crush; crushValidTy.
  - eapply valrel_inArr; try assumption.
    apply invert_valrel_pEmulDV_inArr in vr; try assumption.
    simpl in vvs.
    apply valrel_ptarr_inversion in vr; try crushValidPTyMatch; crush.
    destruct vr as (tsb & tub & τ₁' & -> & -> & eqτ₁ & tytsb & tytub & vr).

    (* unfold the valrel-ptarr *)
    change (abs (UValIE n τ)) with (abs (repEmul (pEmulDV n p τ))).
    change (E.abs τ₁') with (E.abs (isToEq (pEmulDV n p τ₁'))).
    apply valrel_lambda; try crushValidPTyMatch; crush;
    crushOfType; crushTyping; E.crushTyping;
    eauto using downgrade_T, upgrade_T; try crushValidPTyMatch; crushValidTy.
    rewrite -> ?upgrade_sub, ?downgrade_sub; crushValidTy.

    rewrite <- ap_liftSub, <- up_liftSub, -> liftSub_wkm.
    rewrite (apply_wkm_beta1_up_cancel tsb vs).

    (* first execute the upgrade *)
    specialize (ihu w' _ _ _ H vτ H1).
    destruct ihu as (vs' & eups & vr').
    enough (termrel dir w' (pEmulDV n p τ')
                    (app (downgrade n d τ') (app (abs (UValIE (n + d) τ) tsb) vs')) (tub [beta1 vu])) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' eups _ _ _) tr');
            inferContext; crush; eauto using downgrade_value).

    (* now beta-reduce *)
    enough (termrel dir w' (pEmulDV n p τ')
                    (app (downgrade n d τ') (tsb[beta1 vs']))
                    tub[beta1 vu]) as tr'
    by (refine (termrel_antired_star_left _ tr'); simpl; eauto with eval;
        apply evalToStar;
        destruct (valrel_implies_Value vr') as [? _];
        assert (e₀ : app (abs (UValIE (n + d) τ) tsb) vs' -->₀ tsb[beta1 vs']) by (eauto with eval);
        eapply (eval_from_eval₀ e₀); inferContext; crush; eauto using downgrade_value).

    (* now execute the application *)
    specialize (H3 w' _ _ H H0 vr').
    eapply (termrel_ectx' H3); I.inferContext; E.inferContext; crush;
    eauto using downgrade_value.

    (* now execute the downgrade *)
    assert (wlt0 : w'0 < w) by lia.
    specialize (ihd w'0 _ _ _ wlt0 vτ' H4).
    destruct ihd as (vs'' & edowns & vr'').
    enough (termrel dir w'0 (pEmulDV n p τ')
                    vs'' vu0) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' edowns _ _ _) tr');
            inferContext; crush; eauto using downgrade_value).

    (* conclude *)
    now apply valrel_in_termrel.
Qed.

Lemma upgrade_inArr_works {n d w dir p vs vu τ τ'} :
  ValidTy τ -> ValidTy τ' ->
  valrel dir w (pEmulDV (S n) p (E.tarr τ τ')) (I.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  (forall w' vs₁ vu₁ τ, w' < w →
                   ValidTy τ ->
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
  exists v',
    app (upgrade (S n) d (E.tarr τ τ')) (I.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (E.tarr τ τ')) v' vu.
Proof.
  intros vτ vτ' vr ihd ihu.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  exists (I.inl (abs (UValIE (n + d) τ) (app (upgrade n d τ') (app (vs[wk]) (app (downgrade n d τ) (var 0)))))).
  split.
  - eapply upgrade_eval_inArr; crush; crushValidTy.
  - eapply valrel_inArr; try assumption.
    apply invert_valrel_pEmulDV_inArr in vr; crush.
    simpl in vvs.
    apply valrel_ptarr_inversion in vr; try crushValidPTyMatch; crush.
    destruct vr as (tsb & tub & τ₁' & -> & -> & eqτ₁ & tytsb & tytub & vr).

    (* unfold the valrel-ptarr *)
    change (abs (UValIE (n + d) τ)) with (abs (repEmul (pEmulDV (n + d) p τ))).
    change (E.abs τ₁') with (E.abs (isToEq (pEmulDV n p τ₁'))).
    apply valrel_lambda; crush; try crushValidPTyMatch;
    eauto using downgrade_T, upgrade_T.
    rewrite -> ?upgrade_sub, ?downgrade_sub; crushValidTy.

    rewrite <- ap_liftSub; rewrite <- up_liftSub;
    rewrite -> liftSub_wkm; rewrite (apply_wkm_beta1_up_cancel tsb vs).

    (* first execute the upgrade *)
    specialize (ihd w' _ _ _ H vτ H1).
    destruct ihd as (vs' & edowns & vr').
    enough (termrel dir w' (pEmulDV (n + d) p τ')
                    (app (upgrade n d τ') (app (abs (UValIE n τ) tsb) vs')) (tub [beta1 vu])) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' edowns _ _ _) tr');
            inferContext; crush; eauto using upgrade_value).

    (* now beta-reduce *)
    enough (termrel dir w' (pEmulDV (n + d) p τ')
                    (app (upgrade n d τ') (tsb[beta1 vs']))
                    tub[beta1 vu]) as tr'
    by (refine (termrel_antired_star_left _ tr'); simpl; eauto with eval;
        apply evalToStar;
        destruct (valrel_implies_Value vr') as [? _];
        assert (e₀ : app (abs (UValIE n τ) tsb) vs' -->₀ tsb[beta1 vs']) by (eauto with eval);
        eapply (eval_from_eval₀ e₀); inferContext; crush; eauto using upgrade_value).

    (* now execute the application *)
    specialize (H3 w' _ _ H H0 vr').
    eapply (termrel_ectx' H3); I.inferContext; E.inferContext; crush;
    eauto using upgrade_value.

    (* now execute the downgrade *)
    assert (wlt0 : w'0 < w) by lia.
    specialize (ihu w'0 _ _ _ wlt0 vτ' H4).
    destruct ihu as (vs'' & eups & vr'').
    enough (termrel dir w'0 (pEmulDV (n + d) p τ')
                    vs'' vu0) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' eups _ _ _) tr');
            inferContext; crush; eauto using upgrade_value).

    (* conclude *)
    now apply valrel_in_termrel.
Qed.

Lemma downgrade_zero_works {d v vu dir w p τ} :
  dir_world_prec 0 w dir p →
  valrel dir w (pEmulDV d p τ) v vu →
  exists v',
    app (downgrade 0 d τ) v -->* v' ∧
    valrel dir w (pEmulDV 0 p τ) v' vu.
Proof.
  intros dwp vr;
  destruct (valrel_implies_OfType vr) as [[vv tyv] [vvu tyvu]];
  exists (unkUVal 0).
  destruct (dwp_zero dwp).
  repeat split; crush;
  eauto using downgrade_zero_eval.
Qed.

Lemma downgrade_inr_works {n d v vu dir w p τ} :
  valrel dir w (pEmulDV (S (n + d)) p τ) (I.inr v) vu →
  exists v',
    app (downgrade (S n) d τ) (I.inr v) -->* v' ∧
    valrel dir w (pEmulDV (S n) p τ) v' vu.
Proof.
  intros vr.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  simpl in H0, H2.
  assert (v = unit) by (
  dependent destruction H0;
  cbn in H;
  apply (I.can_form_tunit H H0)).
  subst.
  assert (E.ValidEnv E.empty) as ve by eauto with tyvalid.
  exists (I.inr unit).
  unfold downgrade.
  destruct (unfoldn (LMC τ) τ);
  (split; [
  eapply evalStepStar;
  try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
  crush;
  eapply evalStepStar;
  try refine (eval_ctx₀ phole (eval_case_inr _) I); eauto;
  crush|
  assert (p = imprecise) by exact (invert_valrel_pEmulDV_unk vr);
  refine (valrel_unk _ H3);
  crush;
  split; [trivial|];
  split; [trivial|];
  eapply (unkUValT (n := S n));
  E.try_typed_terms_are_valid;
  crush]).
Qed.

Lemma downgrade_S_works {n d v vu dir w p τ} :
  ValidTy τ ->
  dir_world_prec (S n) w dir p →
  valrel dir w (pEmulDV (S (n + d)) p τ) v vu →
  (forall v vu w' τ, dir_world_prec n w' dir p →
                ValidTy τ ->
                valrel dir w' (pEmulDV (n + d) p τ) v vu →
                   exists v',
                     app (downgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV n p τ) v' vu) →
  (forall v vu w' τ, dir_world_prec n w' dir p →
                ValidTy τ ->
                valrel dir w' (pEmulDV n p τ) v vu →
                   exists v',
                     app (upgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV (n + d) p τ) v' vu) →
  exists v',
    app (downgrade (S n) d τ) v -->* v' ∧
    valrel dir w (pEmulDV (S n) p τ) v' vu.
Proof.
  intros vτ dwp vr IHdown IHup.
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] [vvu tyvu]].
  simpl in ty, tyvu.
  destruct (I.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)]; subst; [
    | exact (downgrade_inr_works vr)
  ].
  assert (vτ' : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
  assert (lτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
  rewrite downgrade_unfoldn; try assumption.
  rewrite valrel_pEmulDV_unfoldn in vr; try assumption.

(*   (* not sure why generalized rewriting is not working here *) *)
  enough (∃ v' : Tm,
    (clos_refl_trans_1n Tm eval
          (app (downgrade (S n) d (unfoldn (LMC τ) τ)) (inl x)) v')
    ∧ valrel dir w (pEmulDV (S n) p (unfoldn (LMC τ) τ)) v' vu).
  { destruct H1 as (v' & es & vr').
    exists v'. split; try assumption.
    now rewrite valrel_pEmulDV_unfoldn.
  }
  destruct (unfoldn (LMC τ) τ).
  - (* inArr *)
    destruct (ValidTy_invert_arr vτ') as (vτ1 & vτ2).
    eapply (downgrade_inArr_works vτ1 vτ2 vr); crush.
    + eapply IHdown; try assumption.
      eapply dwp_invert_S'; crush.
    + eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inUnit *)
    assert (x = unit) by (crushTyping; stlcCanForm; reflexivity);
      subst.
    exists (I.inl unit).
    eauto using downgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inBool *)
    exists (inl x); split; crush.
    now eapply (downgrade_eval_inBool (n := n) (d := d)).
  - (* inProd *)
    destruct (ValidTy_invert_prod vτ') as (vτ1 & vτ2).
    eapply (downgrade_inProd_works vτ1 vτ2 vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
  - (* inSum *)
    destruct (ValidTy_invert_sum vτ') as (vτ1 & vτ2).
    eapply (downgrade_inSum_works vτ1 vτ2 vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
  - (* inRec *)
    exfalso; cbn in lτz; lia.
  - (* tvar *)
    contradiction (invert_valrel_pEmulDV_inVar vr).
Qed.

Lemma upgrade_zero_works {d v vu dir w p τ} :
  dir_world_prec 0 w dir p →
  valrel dir w (pEmulDV 0 p τ) v vu →
  exists v',
    app (upgrade 0 d τ) v -->* v' ∧
    valrel dir w (pEmulDV d p τ) v' vu.
Proof.
  intros dwp vr;
  destruct (valrel_implies_OfType vr) as [[vv ty] [vvu tyvu]].
  assert (OfType (pEmulDV d p τ) (unkUVal d) vu).
  cbn in tyvu.
  crushOfType. eauto using unkUVal_Value, unkUValT, E.typed_terms_are_valid, ValidEnv_nil.
  exists (unkUVal d).
  destruct (dwp_zero dwp).
  eauto using upgrade_zero_eval, valrel_unk, dwp_zero.
Qed.


Lemma upgrade_inr_works {n d v vu dir w p τ} :
  ValidTy τ ->
  valrel dir w (pEmulDV (S n) p τ) (I.inr v) vu →
  exists v',
    app (upgrade (S n) d τ) (I.inr v) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p τ) v' vu.
Proof.
  intros vτ vr.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  simpl in H0, H2.
  assert (v = unit) by (
  dependent destruction H0;
  cbn in H;
  apply (I.can_form_tunit H H0)).
  subst.
  exists (I.inr unit).
  split.
  - refine (upgrade_eval_unk vτ).
  - assert (p = imprecise) by exact (invert_valrel_pEmulDV_unk vr);
      refine (valrel_unk _ H3);
      crush; eauto using (unkUValT (n := S n + d)).
Qed.


Lemma upgrade_S_works {n d v vu dir w p τ} :
  ValidTy τ ->
  dir_world_prec (S n) w dir p →
  valrel dir w (pEmulDV (S n) p τ) v vu →
  (forall v vu w' τ, dir_world_prec n w' dir p →
                ValidTy τ ->
                valrel dir w' (pEmulDV (n + d) p τ) v vu →
                   exists v',
                     app (downgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV n p τ) v' vu) →
  (forall v vu w' τ, dir_world_prec n w' dir p →
                ValidTy τ ->
                valrel dir w' (pEmulDV n p τ) v vu →
                   exists v',
                     app (upgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV (n + d) p τ) v' vu) →
  exists v',
    app (upgrade (S n) d τ) v -->* v' ∧
    valrel dir w (pEmulDV (S n + d) p τ) v' vu.
Proof.
  intros vτ dwp vr IHdown IHup.
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] [vvu tyvu]].
  simpl in ty, tyvu.
  destruct (I.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)]; subst; [
    | exact (upgrade_inr_works vτ vr)
  ].
  assert (vτ' : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
  assert (lτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
  rewrite upgrade_unfoldn; try assumption.
  rewrite valrel_pEmulDV_unfoldn in vr; try assumption.

(*   (* not sure why generalized rewriting is not working here *) *)
  enough (∃ v' : Tm,
    (clos_refl_trans_1n Tm eval
          (app (upgrade (S n) d (unfoldn (LMC τ) τ)) (inl x)) v')
    ∧ valrel dir w (pEmulDV (S n + d) p (unfoldn (LMC τ) τ)) v' vu).
  { destruct H1 as (v' & es & vr').
    exists v'. split; try assumption.
    now rewrite valrel_pEmulDV_unfoldn.
  }

  destruct (unfoldn (LMC τ) τ).
  - (* inArr *)
    destruct (ValidTy_invert_arr vτ') as (vτ1 & vτ2).
    eapply (upgrade_inArr_works vτ1 vτ2 vr); crush.
    + eapply IHdown; try assumption.
      eapply dwp_invert_S'; crush.
    + eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inUnit *)
    assert (x = unit) by (crushTyping; stlcCanForm; reflexivity);
      subst.
    exists (I.inl unit).
    eauto using upgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inBool *)
    exists (inl x); split; crush.
    now eapply (upgrade_eval_inBool (n := n) (d := d)).
  - (* inProd *)
    destruct (ValidTy_invert_prod vτ') as (vτ1 & vτ2).
    eapply (upgrade_inProd_works vτ1 vτ2 vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inSum *)
    destruct (ValidTy_invert_sum vτ') as (vτ1 & vτ2).
    eapply (upgrade_inSum_works vτ1 vτ2 vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inRec *)
    exfalso; cbn in lτz; lia.
  - (* tvar *)
    contradiction (invert_valrel_pEmulDV_inVar vr).
Qed.

Lemma downgrade_works {n d v vu dir w p τ} :
  ValidTy τ ->
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p τ) v vu →
  exists v',
    app (downgrade n d τ) v -->* v' ∧
    valrel dir w (pEmulDV n p τ) v' vu
with upgrade_works {n v vu dir w p τ} d :
       ValidTy τ ->
       dir_world_prec n w dir p →
       valrel dir w (pEmulDV n p τ) v vu →
       exists v',
         app (upgrade n d τ) v -->* v' ∧
         valrel dir w (pEmulDV (n + d) p τ) v' vu.
Proof.
  (* the following is easier, but cheats by using the inductive hypotheses
  immediately *)
  (* auto using downgrade_zero_works, downgrade_S_works, upgrade_zero_works, upgrade_S_works. *)

  - destruct n.
    + intros; apply downgrade_zero_works; trivial.
    + specialize (downgrade_works n).
      specialize (upgrade_works n).
      eauto using downgrade_S_works.
  - destruct n.
    + intros; apply upgrade_zero_works; trivial.
    + specialize (downgrade_works n).
      specialize (upgrade_works n).
      auto using upgrade_S_works.
Qed.

Lemma downgrade_works' {n d v vu dir w p τ} :
  ValidTy τ ->
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p τ) v vu →
  termrel dir w (pEmulDV n p τ) (app (downgrade n d τ) v) vu.
Proof.
  intros vτ dwp vr.
  destruct (downgrade_works vτ dwp vr) as (v' & es & vr').
  apply valrel_in_termrel in vr'.
  refine (termrel_antired_star_left es vr').
Qed.

Lemma downgrade_works'' {n d v vu dir w p τ} :
  ValidTy τ ->
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p τ) v vu →
  termrel₀ dir w (pEmulDV n p τ) (app (downgrade n d τ) v) vu.
Proof.
  intros vτ dwp vr.
  destruct (downgrade_works vτ dwp vr) as (v' & es & vr').
  apply valrel_in_termrel₀ in vr'.
  refine (termrel₀_antired_star_left es vr').
Qed.

Lemma upgrade_works' {n v vu dir w p τ} d :
  ValidTy τ ->
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV n p τ) v vu →
  termrel dir w (pEmulDV (n + d) p τ) (app (upgrade n d τ) v) vu.
Proof.
  intros vτ dwp vr.
  destruct (upgrade_works d vτ dwp vr) as (v' & es & vr').
  apply valrel_in_termrel in vr'.
  refine (termrel_antired_star_left es vr').
Qed.

Lemma upgrade_works'' {n v vu dir w p τ} d :
  ValidTy τ ->
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV n p τ) v vu →
  termrel₀ dir w (pEmulDV (n + d) p τ) (app (upgrade n d τ) v) vu.
Proof.
  intros vτ dwp vr.
  destruct (upgrade_works d vτ dwp vr) as (v' & es & vr').
  apply valrel_in_termrel₀ in vr'.
  refine (termrel₀_antired_star_left es vr').
Qed.

Lemma compat_upgrade {Γ ts dir m tu n p τ} d :
  ValidTy τ ->
  dir_world_prec n m dir p →
  ⟪ Γ ⊩ ts ⟦ dir , m ⟧ tu : pEmulDV n p τ⟫ →
  ⟪ Γ ⊩ app (upgrade n d τ) ts ⟦ dir , m ⟧ tu : pEmulDV (n + d) p τ ⟫.
Proof.
  intros.
  repeat crushLRMatch.
  - eauto using upgrade_T with typing.
  - E.crushTyping.
  - intros.
    specialize (H3 w H4 _ _ H5).
    simpl; repeat crushStlcSyntaxMatchH.
    rewrite upgrade_sub; try assumption.
    eapply (termrel_ectx' H3); I.inferContext; E.inferContext; crush;
    eauto using upgrade_value.
    simpl.
    eauto using upgrade_works', dwp_mono.
Qed.

Lemma compat_downgrade {Γ ts dir m tu n p d τ} :
  ValidTy τ ->
  dir_world_prec n m dir p →
  ⟪ Γ ⊩ ts ⟦ dir , m ⟧ tu : pEmulDV (n + d) p τ ⟫ →
  ⟪ Γ ⊩ app (downgrade n d τ) ts ⟦ dir , m ⟧ tu : pEmulDV n p τ ⟫.
Proof.
  intros.
  repeat crushLRMatch.
  - eauto using downgrade_T with typing.
  - E.crushTyping.
  - intros.
    specialize (H3 w H4 _ _ H5).
    simpl; repeat crushStlcSyntaxMatchH.
    rewrite downgrade_sub; try assumption.
    eapply (termrel_ectx' H3); I.inferContext; E.inferContext; crush;
    eauto using downgrade_value.
    simpl.
    eauto using downgrade_works', dwp_mono.
Qed.
