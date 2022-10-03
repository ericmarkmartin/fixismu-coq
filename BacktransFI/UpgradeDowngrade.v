Require Import StlcIso.SpecSyntax.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.Inst.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRelFI.LR.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import LogRelFI.LemmasInversion.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.PseudoType.
Require Import UValFI.UVal.

Require Import Lia.

Require Import Program.Wf.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushRepEmulEmbed;
     repeat I.crushStlcSyntaxMatchH;
     repeat F.crushStlcSyntaxMatchH;
     split;
     trivial;
     crushTyping;
     I.crushTyping;
     try crushOfType;
     subst*);
  try discriminate; try lia;
  eauto with eval;
  repeat crushStlcSyntaxMatchH (* remove apTm's again *).

Fixpoint downgrade (n : nat) (d : nat) (τ : I.Ty) {struct n} : F.Tm :=
  let abs_creator := F.abs (UValFI (n + d) τ) in
  match n with
    | 0 => abs_creator (unkUVal 0)
    | S n =>
      match τ with
        | I.tunit => abs_creator (F.var 0)
        | I.tbool => abs_creator (F.var 0)
        | I.tprod τ τ' => abs_creator (F.caseof (F.var 0)
                                               (F.inl (F.pair (F.app (downgrade n d τ) (F.proj₁ (F.var 0)))
                                                              (F.app (downgrade n d τ') (F.proj₂ (F.var 0)))))
                                              (F.inr (F.var 0)))
        | I.tsum τ τ' => abs_creator (F.caseof (F.var 0)
                                              (F.inl (F.caseof (F.var 0)
                                                               (F.inl (F.app (downgrade n d τ)
                                                                             (F.var 0)))
                                                               (F.inr (F.app (downgrade n d τ')
                                                                             (F.var 0)))))
                                              (F.inr (F.var 0)))
        | I.tarr τ τ' => abs_creator (F.caseof (F.var 0)
                                              (F.inl (F.abs (UValFI n τ)
                                                            (F.app (downgrade n d τ')
                                                                   (F.app (F.var 1)
                                                                          (F.app (upgrade n d τ)
                                                                                 (F.var 0))))))
                                              (F.inr (F.var 0)))
        | I.trec τ => abs_creator (F.caseof (F.var 0)
                                           (F.inl (F.app (downgrade n d τ[beta1 (I.trec τ)]) (F.var 0)))
                                           (F.inr (F.var 0)))
        | I.tvar _ => abs_creator (F.caseof (F.var 0) (F.inl (F.var 0)) (F.inr (F.var 0)))
      end
  end
with
upgrade (n : nat) (d : nat) (τ : I.Ty) {struct n} :=
  let abs_creator := F.abs (UValFI n τ) in
  match n with
    | 0 => abs_creator (unkUVal d)
    | S n =>
      match τ with
        | I.tunit => abs_creator (F.var 0)
        | I.tbool => abs_creator (F.var 0)
        | I.tprod τ τ' => abs_creator (F.caseof (F.var 0)
                                               (F.inl (F.pair (F.app (upgrade n d τ) (F.proj₁ (F.var 0)))
                                                              (F.app (upgrade n d τ') (F.proj₂ (F.var 0)))))
                                              (F.inr (F.var 0)))
        | I.tsum τ τ' => abs_creator (F.caseof (F.var 0)
                                        (F.inl (F.caseof (F.var 0)
                                                          (F.inl (F.app (upgrade n d τ)
                                                                        (F.var 0)))
                                                          (F.inr (F.app (upgrade n d τ')
                                                                        (F.var 0)))))
                                        (F.inr (F.var 0)))
        | I.tarr τ τ' => abs_creator (F.caseof (F.var 0)
                                              (F.inl (F.abs (UValFI (n + d) τ)
                                                            (F.app (upgrade n d τ')
                                                                  (F.app (F.var 1)
                                                                          (F.app (downgrade n d τ)
                                                                                (F.var 0))))))
                                              (F.inr (F.var 0)))
        (* | I.trec τ' => upgrade n d (fu' (I.trec τ')) *)
        | I.trec τ => abs_creator (F.caseof (F.var 0)
                                           (F.inl (F.app (upgrade n d τ[beta1 (I.trec τ)]) (F.var 0)))
                                           (F.inr (F.var 0)))
        | I.tvar _ => abs_creator (F.caseof (F.var 0) (F.inl (F.var 0)) (F.inr (F.var 0)))
        end
  end.

Fixpoint downgradeA (n : nat) (d : nat) (τ : I.Ty) {struct n} : F.TmA
  :=
  let abs_creator := F.a_abs (UValFI (n + d) τ) (UValFI n τ) in
  match n with
    | 0 => abs_creator (unkUValA 0 τ)
    | S n =>
      match τ with
        | I.tunit => abs_creator (F.a_var 0)
        | I.tbool => abs_creator (F.a_var 0)
        | I.tprod τ τ' =>
          abs_creator
            (F.a_caseof (F.tprod (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit (UValFI (S n) (I.tprod τ τ'))
                        (F.a_var 0)
                        (F.a_inl (F.tprod (UValFI n τ) (UValFI n τ')) F.tunit
                           (F.a_pair (UValFI n τ) (UValFI n τ')
                                     (F.a_app (UValFI (n + d) τ) (UValFI n τ)
                                              (downgradeA n d τ) (F.a_proj₁ (UValFI (n +d) τ) (UValFI (n +d) τ') (F.a_var 0)))
                                     (F.a_app (UValFI (n + d) τ') (UValFI n τ')
                                              (downgradeA n d τ') (F.a_proj₂ (UValFI (n +d) τ) (UValFI (n+d) τ') (F.a_var 0)))))
                        (F.a_inr (F.tprod (UValFI n τ) (UValFI n τ')) F.tunit (F.a_var 0)))
        | I.tsum τ τ' =>
          abs_creator
            (F.a_caseof (F.tsum (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit (UValFI (S n) (I.tsum τ τ'))
                        (F.a_var 0)
                        (F.a_inl (F.tsum (UValFI n τ) (UValFI n τ')) F.tunit
                                 (F.a_caseof (UValFI (n + d) τ) (UValFI (n + d) τ') (F.tsum (UValFI n τ) (UValFI n τ')) (F.a_var 0)
                                             (F.a_inl (UValFI n τ) (UValFI n τ') (F.a_app (UValFI (n + d) τ) (UValFI n τ) (downgradeA n d τ)
                                                                                          (F.a_var 0)))
                                             (F.a_inr (UValFI n τ) (UValFI n τ') (F.a_app (UValFI (n + d) τ') (UValFI n τ') (downgradeA n d τ')
                                                                       (F.a_var 0)))))
                        (F.a_inr (F.tsum (UValFI n τ) (UValFI n τ')) F.tunit (F.a_var 0)))
        | I.tarr τ τ' =>
          abs_creator
            (F.a_caseof (F.tarr (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit (UValFI (S n) (I.tarr τ τ'))
                        (F.a_var 0)
                        (F.a_inl (F.tarr (UValFI n τ) (UValFI n τ')) F.tunit
                                 (F.a_abs (UValFI n τ) (UValFI n τ')
                                          (F.a_app (UValFI (n + d) τ') (UValFI n τ') (downgradeA n d τ')
                                                   (F.a_app (UValFI (n + d) τ) (UValFI (n + d) τ') (F.a_var 1)
                                                            (F.a_app (UValFI n τ) (UValFI (n + d) τ) (upgradeA n d τ)
                                                                     (F.a_var 0))))))
                        (F.a_inr (F.tarr (UValFI n τ) (UValFI n τ')) F.tunit (F.a_var 0)))
        | I.trec τ =>
          abs_creator
            (F.a_caseof (UValFI (n + d) (τ [beta1 (trec τ)])) F.tunit (UValFI (S n) (trec τ))
                        (F.a_var 0)
                        (F.a_inl (UValFI n (τ [beta1 (trec τ)])) F.tunit (F.a_app (UValFI (n + d) (τ [beta1 (trec τ)])) (UValFI n (τ [beta1 (trec τ)])) (downgradeA n d τ[beta1 (I.trec τ)]) (F.a_var 0)))
                        (F.a_inr (UValFI n (τ [beta1 (trec τ)])) F.tunit (F.a_var 0)))
        | I.tvar _ => abs_creator (F.a_caseof F.tunit F.tunit (F.tsum F.tunit F.tunit) (F.a_var 0) (F.a_inl F.tunit F.tunit (F.a_var 0)) (F.a_inr F.tunit F.tunit (F.a_var 0)))
      end
  end
with
upgradeA (n : nat) (d : nat) (τ : I.Ty) {struct n} :=
  let abs_creator := F.a_abs (UValFI n τ) (UValFI (n + d) τ) in
  match n with
    | 0 => abs_creator (unkUValA d τ)
    | S n =>
      match τ with
        | I.tunit => abs_creator (F.a_var 0)
        | I.tbool => abs_creator (F.a_var 0)
        | I.tprod τ τ' =>
          abs_creator
            (F.a_caseof (F.tprod (UValFI n τ) (UValFI n τ')) F.tunit (UValFI (S (n + d)) (I.tprod τ τ'))
                        (F.a_var 0)
                        (F.a_inl (F.tprod (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit
                           (F.a_pair (UValFI (n + d) τ) (UValFI (n + d) τ')
                                     (F.a_app (UValFI n τ) (UValFI (n + d) τ)
                                              (upgradeA n d τ) (F.a_proj₁ (UValFI n τ) (UValFI n τ') (F.a_var 0)))
                                     (F.a_app (UValFI n τ') (UValFI (n + d) τ')
                                              (upgradeA n d τ') (F.a_proj₂ (UValFI n τ) (UValFI n τ') (F.a_var 0)))))
                        (F.a_inr (F.tprod (UValFI (n+d) τ) (UValFI (n+d) τ')) F.tunit (F.a_var 0)))
        | I.tsum τ τ' =>
          abs_creator
            (F.a_caseof (F.tsum (UValFI n τ) (UValFI n τ')) F.tunit (UValFI (S n + d) (I.tsum τ τ'))
                        (F.a_var 0)
                        (F.a_inl (F.tsum (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit
                                 (F.a_caseof (UValFI n τ) (UValFI n τ') (F.tsum (UValFI (n + d) τ) (UValFI (n + d) τ'))
                                             (F.a_var 0)
                                             (F.a_inl (UValFI (n + d) τ) (UValFI (n + d) τ')
                                                      (F.a_app (UValFI n τ) (UValFI (n + d) τ) (upgradeA n d τ)
                                                                   (F.a_var 0)))
                                             (F.a_inr (UValFI (n + d) τ) (UValFI (n + d) τ')
                                                      (F.a_app (UValFI n τ') (UValFI (n + d) τ') (upgradeA n d τ')
                                                               (F.a_var 0)))))
                        (F.a_inr (F.tsum (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit (F.a_var 0)))
        | I.tarr τ τ' =>
          abs_creator
            (F.a_caseof (F.tarr (UValFI n τ) (UValFI n τ')) F.tunit (UValFI (S n + d) (I.tarr τ τ'))
                        (F.a_var 0)
                        (F.a_inl (F.tarr (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit
                                 (F.a_abs (UValFI (n + d) τ) (UValFI (n + d) τ')
                                          (F.a_app (UValFI n τ') (UValFI (n + d) τ') (upgradeA n d τ')
                                                   (F.a_app (UValFI n τ) (UValFI n τ') (F.a_var 1)
                                                            (F.a_app (UValFI (n + d) τ) (UValFI n τ) (downgradeA n d τ)
                                                                     (F.a_var 0))))))
                        (F.a_inr (F.tarr (UValFI (n + d) τ) (UValFI (n + d) τ')) F.tunit (F.a_var 0)))
        (* | I.trec τ' => upgradeA n d (fu' (I.trec τ')) *)
        | I.trec τ =>
          abs_creator
            (F.a_caseof (UValFI n (τ [beta1 (trec τ)])) F.tunit (UValFI (S n + d) (trec τ)) (F.a_var 0)
                        (F.a_inl (UValFI (n + d) (τ [beta1 (trec τ)])) F.tunit
                                 (F.a_app (UValFI n (τ [beta1 (trec τ)])) (UValFI (n + d) (τ [beta1 (trec τ)]))
                                          (upgradeA n d τ[beta1 (I.trec τ)]) (F.a_var 0)))
                        (F.a_inr (UValFI (n + d) (τ [beta1 (trec τ)])) F.tunit (F.a_var 0)))
        | I.tvar _ =>
          abs_creator
            (F.a_caseof F.tunit F.tunit (F.tsum F.tunit F.tunit)
                        (F.a_var 0)
                        (F.a_inl F.tunit F.tunit (F.a_var 0))
                        (F.a_inr F.tunit F.tunit (F.a_var 0)))
        end
  end.

Lemma upgrade_annot_T {n : nat} {Γ d τ} :
  ⟪ Γ a⊢ upgradeA n d τ : UValFI n τ ⇒ UValFI (n + d) τ ⟫
with
downgrade_annot_T {n : nat} {Γ d τ} :
  ⟪ Γ a⊢ downgradeA n d τ : UValFI (n + d) τ ⇒ UValFI n τ ⟫.
Proof.
  - induction n;
      induction τ;
      unfold upgradeA, downgradeA;
      eauto with typing uval_typing.
  - induction n;
      induction τ;
      unfold upgradeA, downgradeA;
      eauto with typing uval_typing.
Qed.

Lemma upgrade_annot_T1 {Γ n τ} :
  ⟪ Γ a⊢ upgradeA n 1 τ : UValFI n τ ⇒ UValFI (S n) τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using upgrade_annot_T.
Qed.

Lemma downgrade_annot_T1 {Γ n τ} :
  ⟪ Γ a⊢ downgradeA n 1 τ : UValFI (S n) τ ⇒ UValFI n τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using downgrade_annot_T.
Qed.

Lemma upgrade_annot_T1' {Γ n τ τ'} :
  τ' = UValFI' (UValFI n) τ ->
  ⟪ Γ a⊢ upgradeA n 1 τ : UValFI n τ ⇒ τ' ⟫.
Proof.
  intros. subst.
  eapply upgrade_annot_T1.
Qed.

Lemma downgrade_annot_T1' {Γ n τ τ'} :
  τ' = UValFI' (UValFI n) τ ->
  ⟪ Γ a⊢ downgradeA n 1 τ : τ' ⇒ UValFI n τ ⟫.
Proof.
  intros. subst.
  eapply downgrade_annot_T1.
Qed.

Ltac crushUpgradeTypingMatch :=
  repeat match goal with
    | |- ⟪ _ a⊢ upgradeA _ _ _ : _ ⟫ => apply upgrade_annot_T1'
    | |- ⟪ _ a⊢ downgradeA _ _ _ : _ ⟫ => apply downgrade_annot_T1'
  end.

#[export]
Hint Extern 20 (⟪ _ a⊢ upgradeA _ _ _ : _ ⟫) => crushUpgradeTypingMatch : typing.

#[export]
Hint Extern 20 (⟪ _ a⊢ downgradeA _ _ _ : _ ⟫) => crushUpgradeTypingMatch : typing.


Fixpoint upgrade_upgradeA {n d τ} {struct n} :
  eraseAnnot (upgradeA n d τ) = upgrade n d τ
  with
    downgrade_downgradeA {n d τ} {struct n} :
  eraseAnnot (downgradeA n d τ) = downgrade n d τ.
Proof.
  - destruct n.
    + clear upgrade_upgradeA.
      cbn; rewrite <-?unkUVal_unkUValA;
      repeat f_equal.
    + destruct τ;
        cbn;
        rewrite <-?unkUVal_unkUValA;
        repeat f_equal;
        eauto.
  - destruct n.
    + clear downgrade_downgradeA.
      cbn;
      rewrite <-?unkUVal_unkUValA;
      repeat f_equal.
    + destruct τ;
        cbn;
        rewrite <-?unkUVal_unkUValA;
        repeat f_equal;
        eauto.
Qed.

Lemma upgrade_T {n : nat} {Γ d τ} :
  ⟪ Γ ⊢ upgrade n d τ : UValFI n τ ⇒ UValFI (n + d) τ ⟫
with
downgrade_T {n : nat} {Γ d τ} :
  ⟪ Γ ⊢ downgrade n d τ : UValFI (n + d) τ ⇒ UValFI n τ ⟫.
Proof.
  - induction n;
      induction τ;
      unfold upgrade, downgrade;
      eauto with typing uval_typing.
  - induction n;
      induction τ;
      unfold upgrade, downgrade;
      eauto with typing uval_typing.
Qed.

Lemma upgrade_T1 {Γ n τ} :
  ⟪ Γ ⊢ upgrade n 1 τ : UValFI n τ ⇒ UValFI (S n) τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using upgrade_T.
Qed.

Lemma downgrade_T1 {Γ n τ} :
  ⟪ Γ ⊢ downgrade n 1 τ : UValFI (S n) τ ⇒ UValFI n τ ⟫.
Proof.
  replace (S n) with (n + 1) by lia.
  eauto using downgrade_T.
Qed.

#[export]
Hint Resolve upgrade_T1 : uval_typing.
#[export]
Hint Resolve downgrade_T1 : uval_typing.
#[export]
Hint Resolve upgrade_annot_T1 : uval_typing.
#[export]
Hint Resolve downgrade_annot_T1 : uval_typing.

Lemma upgrade_closed {n d τ} :
  ⟨ 0 ⊢ upgrade n d τ ⟩.
Proof.
  enough (⟪ F.empty ⊢ upgrade n d τ : UValFI n τ ⇒ UValFI (n + d) τ ⟫) as ty by eapply (wt_implies_ws ty).
  eapply upgrade_T.
Qed.

Lemma downgrade_closed {n d τ} :
  ⟨ 0 ⊢ downgrade n d τ ⟩.
Proof.
  enough (⟪ F.empty ⊢ downgrade n d τ : UValFI (n + d) τ ⇒ UValFI n τ ⟫) as ty by eapply (wt_implies_ws ty).
  eapply downgrade_T.
Qed.

Lemma upgrade_sub {n d τ γ} : (upgrade n d τ)[γ] = upgrade n d τ.
Proof.
  apply wsClosed_invariant.
  eapply upgrade_closed.
Qed.

Lemma downgrade_sub {n d τ γ} : (downgrade n d τ)[γ] = downgrade n d τ.
Proof.
  apply wsClosed_invariant.
  eapply downgrade_closed.
Qed.

Lemma downgrade_value {n d τ} : Value (downgrade n d τ).
Proof.
  revert d τ;
  induction n; destruct τ; simpl; trivial.
Qed.

Lemma upgrade_value {n d τ} : Value (upgrade n d τ).
Proof.
  revert d τ;
  induction n; destruct τ; simpl; trivial.
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

Lemma downgrade_eval_unk {n d τ} : app (downgrade n d τ) (unkUVal (n + d)) -->* unkUVal n.
Proof.
  assert (vv : Value (unkUVal (n + d))) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    simpl; eauto with eval.
  - change _ with (Value (inr unit)) in vv.
    destruct τ;
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
    subst; cbn; crush; rewrite ?downgrade_sub, ?upgrade_sub;
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_case_inr _) I); eauto;
    crush.
Qed.

Lemma upgrade_eval_unk {n d τ} : app (upgrade n d τ) (unkUVal n) -->* unkUVal (n + d).
Proof.
  assert (vv : Value (unkUVal n)) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    destruct d;
    simpl; eauto with eval.
  - change _ with (Value (inl unit)) in vv.
    destruct τ;
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
    subst; cbn; crush; rewrite ?downgrade_sub, ?upgrade_sub;
    eapply evalStepStar;
    try refine (eval_ctx₀ phole (eval_case_inr _) I); eauto;
    crush.
Qed.

Lemma downgrade_eval_inUnit {n d} :
  app (downgrade (S n) d I.tunit) (F.inl F.unit) -->* F.inl F.unit.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply F.eval_beta.
  all: eauto with eval.
  crush.
Qed.

Lemma upgrade_eval_inUnit {n d} :
  app (upgrade (S n) d I.tunit) (F.inl F.unit) -->* F.inl F.unit.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply F.eval_beta.
  all: eauto with eval.
  crush.
Qed.

Lemma downgrade_eval_inBool {n d v} (vv : Value v) :
  app (downgrade (S n) d I.tbool) (F.inl v) -->* F.inl v.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply F.eval_beta; now cbn.
  crush.
Qed.

Lemma upgrade_eval_inBool {n d v} (vv : Value v):
  app (upgrade (S n) d I.tbool) (F.inl v) -->* F.inl v.
Proof.
  eapply evalStepStar.
  eapply eval₀_to_eval.
  simpl.
  apply F.eval_beta; now cbn.
  crush.
Qed.

Lemma downgrade_eval_inSum {n d v v' va va' τ τ'} :
  Value v → Value v' →
  (va = inl v ∧ va' = inl v' ∧ app (downgrade n d τ) v -->* v')
  ∨ (va = inr v ∧ va' = inr v' ∧ app (downgrade n d τ') v -->* v') →
  app (downgrade (S n) d (I.tsum τ τ')) (F.inl va) -->* F.inl va'.
Proof.
  intros vv vv' eqs.
  cbn.
  destruct eqs as [(? & ? & ?)|(? & ? & ?)]; subst;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
    eapply evalStepStar;
  [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); crush|
  |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); crush|];
  cbn; crush; rewrite ?upgrade_sub, ?downgrade_sub;
  [change (F.inl (F.inl ?t)) with (pctx_app t (pinl (pinl phole)))
  |change (F.inl (F.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
  apply evalstar_ctx;
  cbn;
  trivial.
Qed.

Lemma downgrade_eval_inProd {n d v1 v2 v1' v2' τ1 τ2} :
  Value v1 -> Value v2 → Value v1' → Value v2' →
  app (downgrade n d τ1) v1 -->* v1' ->
  app (downgrade n d τ2) v2 -->* v2' ->
  app (downgrade (S n) d (I.tprod τ1 τ2)) (F.inl (pair v1 v2)) -->* F.inl (pair v1' v2').
Proof.
  intros vv1 vv2 vv1' vv2' es1 es2.
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_beta; now cbn. }
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_case_inl; now cbn. }
  crushTyping.
  rewrite ?downgrade_sub.
  eapply evalStepStar.
  { refine (eval_ctx₀' (eval_proj₁ vv1 vv2) _ _ _); F.inferContext.
    cbn; eauto using downgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es1); F.inferContext; now cbn. }
  eapply evalStepStar.
  { eapply (eval_ctx₀' (eval_proj₂ vv1 vv2)); F.inferContext; cbn; eauto using downgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es2); F.inferContext; now cbn. }
  crush.
Qed.

Lemma upgrade_eval_inProd {n d v1 v2 v1' v2' τ1 τ2} :
  Value v1 -> Value v2 → Value v1' → Value v2' →
  app (upgrade n d τ1) v1 -->* v1' ->
  app (upgrade n d τ2) v2 -->* v2' ->
  app (upgrade (S n) d (I.tprod τ1 τ2)) (F.inl (pair v1 v2)) -->* F.inl (pair v1' v2').
Proof.
  intros vv1 vv2 vv1' vv2' es1 es2.
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_beta; now cbn. }
  eapply evalStepStar.
  { eapply eval_eval₀; eapply eval_case_inl; now cbn. }
  crushTyping.
  rewrite ?upgrade_sub.
  eapply evalStepStar.
  { refine (eval_ctx₀' (eval_proj₁ vv1 vv2) _ _ _); F.inferContext.
    cbn; eauto using upgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es1); F.inferContext; now cbn. }
  eapply evalStepStar.
  { eapply (eval_ctx₀' (eval_proj₂ vv1 vv2)); F.inferContext; cbn; eauto using upgrade_value. }
  eapply evalStepTrans.
  { eapply (evalstar_ctx' es2); F.inferContext; now cbn. }
  crush.
Qed.

Lemma upgrade_eval_inSum {n d v v' va va' τ τ'} :
  Value v → Value v' →
  (va = inl v ∧ va' = inl v' ∧ app (upgrade n d τ) v -->* v')
  ∨ (va = inr v ∧ va' = inr v' ∧ app (upgrade n d τ') v -->* v') →
  app (upgrade (S n) d (I.tsum τ τ')) (F.inl va) -->* F.inl va'.
Proof.
  intros vv vv' eqs.
  cbn.
  destruct eqs as [(? & ? & ?)|(? & ? & ?)]; subst;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
    eapply evalStepStar;
  [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); crush|
  |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); crush|];
  cbn; crush; rewrite ?upgrade_sub, ?downgrade_sub;
  [change (F.inl (F.inl ?t)) with (pctx_app t (pinl (pinl phole)))
  |change (F.inl (F.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
  apply evalstar_ctx;
  cbn;
  trivial.
Qed.


Lemma downgrade_eval_inArr {n d v τ τ'} :
  Value v →
  app (downgrade (S n) d (I.tarr τ τ')) (F.inl v) -->*
     F.inl (abs (UValFI n τ) (app (downgrade n d τ') (app (v[wk]) (app (upgrade n d τ) (var 0))))).
Proof.
  intros vv.
  cbn.

  (* beta-reduce *)
  ((eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
      rewrite -> ?upgrade_sub, ?downgrade_sub);
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  change (wk 0) with 1; simpl;
  eauto with eval.
Qed.

Lemma upgrade_eval_inArr {n d v τ τ'} :
  Value v →
  app (upgrade (S n) d (I.tarr τ τ')) (F.inl v) -->*
     F.inl (abs (UValFI (n + d) τ) (app (upgrade n d τ') (app (v[wk]) (app (downgrade n d τ) (var 0))))).
Proof.
  intros vv.
  cbn.

  (* beta-reduce *)
  ((eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
      rewrite -> ?upgrade_sub, ?downgrade_sub);
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  change (wk 0) with 1; simpl;
  eauto with eval.
Qed.

Lemma downgrade_eval_inRec {n d v v' τ} :
  Value v → Value v' →
  app (downgrade n d τ[beta1 (I.trec τ)]) v -->* v' →
  app (downgrade (S n) d (I.trec τ)) (F.inl v) -->* (F.inl v').
      (* F.inl (app (downgrade n d τ[beta1 (I.trec τ)]) v). *)
Proof.
  intros vv vv' es.
  cbn.
  (* beta-reduce *)
  ((eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
      rewrite -> ?upgrade_sub, ?downgrade_sub);
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  eauto with eval.
  change (F.inl ?t) with (pctx_app t (pinl phole)).
  eapply evalstar_ctx;
    cbn;
    eauto.
Qed.

Lemma upgrade_eval_inRec {n d v v' τ} :
  Value v → Value v' →
  app (upgrade n d τ[beta1 (I.trec τ)]) v -->* v' →
  app (upgrade (S n) d (I.trec τ)) (F.inl v) -->* (F.inl v').
      (* F.inl (app (downgrade n d τ[beta1 (I.trec τ)]) v). *)
Proof.
  intros vv vv' es.
  cbn.
  (* beta-reduce *)
  ((eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
      rewrite -> ?upgrade_sub, ?downgrade_sub);
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;
  eauto with eval.
  change (F.inl ?t) with (pctx_app t (pinl phole)).
  eapply evalstar_ctx;
    cbn;
    eauto.
Qed.


Lemma downgrade_reduces {n d v τ} :
  ⟪ F.empty ⊢ v : UValFI (n + d) τ ⟫ → Value v →
  exists v', Value v' ∧ ⟪ F.empty ⊢ v' : UValFI n τ ⟫ ∧
             app (downgrade n d τ) v -->* v'.
Proof.
  revert τ;
  revert v; induction n;
  intros v τ ty vv.
  - exists (unkUVal 0).
    eauto using unkUVal_Value, unkUValT, downgrade_zero_eval.
  - change (S n + d) with (S (n + d)) in ty.
    destruct τ.
    + destruct (canonUValS_Arr vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (F.can_form_tarr H H1).
        exists (F.inl (F.abs (UValFI n τ1) (F.app (downgrade n d τ2)
                                             (F.app x
                                                    (F.app (upgrade n d τ1)
                                                           (* x))))). *)
                                                           (F.var 0)))))).
        repeat split.
        replace x with x [wk] by (eapply wsClosed_invariant;
                                  refine (F.wt_implies_ws H1)).
        eauto using downgrade_T, upgrade_T with typing ws.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub.
        change ((beta1 x)↑ (wk 0)) with x [wk].
        replace x[wk] with x; [econstructor|].
        eapply eq_sym, wsClosed_invariant.
        refine (F.wt_implies_ws H1).
        (* eauto using inArr_Value, downgrade_eval_inArr, inArr_T,  *)
        (* downgrade_T, upgrade_T with typing. *)
      * exists (unkUVal (S n)).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
    + destruct (canonUValS_Unit vv ty) as [? | ?].
      * exists v.
        repeat split.
        assumption.
        rewrite H.
        eauto with typing ws.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        crush.
      * exists (unkUVal (S n)).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; crush.
    + destruct (canonUValS_Bool vv ty) as [? | [?|?]]; destruct_conjs; subst.
      * exists (F.inl F.true); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (F.inl F.false); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (F.inr F.unit); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
    + destruct (canonUValS_Prod vv ty) as [?| ?]; destruct_conjs; subst.
      stlcCanForm.
      destruct vv as (vx & vx0).
      destruct (IHn x τ1 H3 vx) as (v1 & vv1 & tv1 & es1).
      destruct (IHn x0 τ2 H4 vx0) as (v2 & vv2 & tv2 & es2).
      * exists (inl (pair v1 v2)); crush.
        eapply downgrade_eval_inProd; eauto.
      * exists (F.inr F.unit); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); now cbn.
        crush.
    + destruct (canonUValS_Sum vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (F.can_form_tsum H H1) as [(? & ? & ?) | (? & ? & ?)];
        assert (F.Value x0) by (rewrite H2 in H; trivial);
        destruct (IHn _ _ H3 H4) as (vf & vvf & tyf & ex);
        [exists (F.inl (F.inl vf)) | exists (F.inl (F.inr vf))];
        repeat split;
        try (simpl; trivial; fail);
        try (eauto using tyf with typing ws);
        subst;
        cbn;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
        subst; cbn; crush; rewrite ?downgrade_sub;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_case_inl _) I); eauto;
        subst; cbn; crush; rewrite ?downgrade_sub;
        eapply evalStepStar;
        [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); eauto | idtac
        |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); eauto | idtac];
        subst; cbn; crush; rewrite ?downgrade_sub;
        [change (F.inl (F.inl ?t)) with (pctx_app t (pinl (pinl phole)))
        |change (F.inl (F.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
        apply evalstar_ctx;
        cbn;
        trivial.
      * exists (unkUVal (S n)).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
    + destruct (canonUValS_Rec vv ty) as [(? & ? & ? & ?) | ?].
      * destruct (IHn _ _ H1 H) as (vf & vvf & tyf & ex).
        exists (F.inl vf).
        repeat split.
        cbn; assumption.
        eauto using tyf with typing.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub.
        change (F.inl ?t) with (pctx_app t (pinl phole)).
        apply evalstar_ctx;
        cbn; trivial.
      * exists (unkUVal (S n)).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
    + unfold UValFI in ty.
      destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
      (* [exists (F.inl unit) | exists (F.inr unit)]; *)
      exists v;
      repeat split;
      eauto with typing;
      cbn;
      eapply evalStepStar;
      try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
      subst; cbn; crush;
      eapply evalStepStar;
      [refine (eval_ctx₀ phole (eval_case_inl _) I) | idtac |
       refine (eval_ctx₀ phole (eval_case_inr _) I) | idtac];
      subst; cbn; crush.
Qed.

Lemma upgrade_reduces {n v τ } d :
  ⟪ F.empty ⊢ v : UValFI n τ ⟫ → Value v →
  exists v', Value v' ∧ ⟪ F.empty ⊢ v' : UValFI (n + d) τ ⟫ ∧
             app (upgrade n d τ) v -->* v'.
Proof.
  revert τ;
  revert v; induction n;
  intros v τ ty vv.
  - exists (unkUVal d).
    eauto using unkUVal_Value, unkUValT, upgrade_zero_eval.
  - change (S n + d) with (S (n + d)).
    destruct τ.
    + destruct (canonUValS_Arr vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (F.can_form_tarr H H1).
        exists (F.inl (F.abs (UValFI (n + d) τ1) (F.app (upgrade n d τ2)
                                             (F.app x
                                                    (F.app (downgrade n d τ1)
                                                           (* x))))). *)
                                                           (F.var 0)))))).
        repeat split.
        replace x with x [wk] by (eapply wsClosed_invariant;
                                  refine (F.wt_implies_ws H1)).

        eauto using downgrade_T, upgrade_T with typing ws.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        cbn; crush; rewrite downgrade_sub, upgrade_sub.
        change ((beta1 x)↑ (wk 0)) with x [wk].
        replace x[wk] with x; [econstructor|].
        eapply eq_sym, wsClosed_invariant.
        refine (F.wt_implies_ws H1).
        (* eauto using inArr_Value, downgrade_eval_inArr, inArr_T,  *)
        (* downgrade_T, upgrade_T with typing. *)
      * exists (unkUVal (S (n + d))).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite downgrade_sub, upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
    + destruct (canonUValS_Unit vv ty) as [? | ?].
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
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; crush.
    + destruct (canonUValS_Bool vv ty) as [? | [?|?]]; destruct_conjs; subst.
      * exists (F.inl F.true); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (F.inl F.false); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
      * exists (F.inr F.unit); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        crush.
    + destruct (canonUValS_Prod vv ty) as [?| ?]; destruct_conjs; subst.
      stlcCanForm.
      destruct vv as (vx & vx0).
      destruct (IHn x τ1 H3 vx) as (v1 & vv1 & tv1 & es1).
      destruct (IHn x0 τ2 H4 vx0) as (v2 & vv2 & tv2 & es2).
      * exists (inl (pair v1 v2)); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); now cbn.
        cbn.
        crush.
        rewrite ?upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ (pinl (ppair₁ (papp₂ _ phole) _)) (eval_proj₁ _ _) _); cbn; eauto using upgrade_value.
        cbn.
        eapply evalStepTrans.
        eapply (evalstar_ctx' es1); F.inferContext; now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ (pinl (ppair₂ _ (papp₂ _ phole))) (eval_proj₂ _ _) _); cbn; eauto using upgrade_value.
        cbn.
        eapply (evalstar_ctx' es2); F.inferContext; now cbn.
      * exists (F.inr F.unit); crush.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); now cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); now cbn.
        crush.
    + destruct (canonUValS_Sum vv ty) as [(? & ? & ? & ?) | ?].
      * pose proof (F.can_form_tsum H H1) as [(? & ? & ?) | (? & ? & ?)];
        assert (F.Value x0) by (rewrite H2 in H; trivial);
        destruct (IHn _ _ H3 H4) as (vf & vvf & tyf & ex);
        [exists (F.inl (F.inl vf)) | exists (F.inl (F.inr vf))];
        repeat split;
        try (simpl; trivial; fail);
        try (eauto using tyf with typing ws);
        subst;
        cbn;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
        subst; cbn; crush; rewrite ?upgrade_sub;
        eapply evalStepStar;
        try refine (eval_ctx₀ phole (eval_case_inl _) I); eauto;
        subst; cbn; crush; rewrite ?upgrade_sub;
        eapply evalStepStar;
        [refine (eval_ctx₀ (pinl phole) (eval_case_inl _) I); eauto | idtac
        |refine (eval_ctx₀ (pinl phole) (eval_case_inr _) I); eauto | idtac];
        subst; cbn; crush; rewrite ?upgrade_sub;
        [change (F.inl (F.inl ?t)) with (pctx_app t (pinl (pinl phole)))
        |change (F.inl (F.inr ?t)) with (pctx_app t (pinl (pinr phole)))];
        apply evalstar_ctx;
        cbn;
        trivial.
      * exists (unkUVal (S (n + d))).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
    + destruct (canonUValS_Rec vv ty) as [(? & ? & ? & ?) | ?].
      * destruct (IHn _ _ H1 H) as (vf & vvf & tyf & ex).
        exists (F.inl vf).
        repeat split.
        cbn; assumption.
        eauto using tyf with typing.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inl _) I); eauto.
        subst; cbn; crush; rewrite upgrade_sub.
        change (F.inl ?t) with (pctx_app t (pinl phole)).
        apply evalstar_ctx;
        cbn; trivial.
      * exists (unkUVal (S (n + d))).
        repeat split.
        exact unkUValT.
        cbn.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_beta _) I); eauto.
        subst; cbn; crush; rewrite upgrade_sub.
        eapply evalStepStar.
        refine (eval_ctx₀ phole (eval_case_inr _) I); eauto.
        crush.
    + unfold UValFI in ty.
      destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
      (* [exists (F.inl unit) | exists (F.inr unit)]; *)
      exists v;
      repeat split;
      eauto with typing;
      cbn;
      eapply evalStepStar;
      try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
      subst; cbn; crush;
      eapply evalStepStar;
      [refine (eval_ctx₀ phole (eval_case_inl _) I) | idtac |
       refine (eval_ctx₀ phole (eval_case_inr _) I) | idtac];
      subst; cbn; crush.
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
  valrel dir w (pEmulDV (S (n + d)) p (I.tprod τ τ')) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  exists v',
    app (downgrade (S n) d (I.tprod τ τ')) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (I.tprod τ τ')) v' vu.
Proof.
  intros vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].
  destruct (invert_valrel_pEmulDV_inProd' vr) as (vs1 & vs2 & vu1 & vu2 & -> & -> & vr1 & vr2).
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Prod vvs tvs) as [(? & ? & ? & ?) | ?]; [| inversion H].
    F.stlcCanForm. inversion H0; subst.
    destruct H as (vx2 & vx3).
    destruct (downgrade_reduces H3 vx2) as (x4 & vx4 & tyx4 & esx4).
    destruct (downgrade_reduces H4 vx3) as (x5 & vx5 & tyx5 & esx5).
    exists (inl (pair x4 x5)); split; I.crushTyping.
    * eapply downgrade_eval_inProd; eauto.
    * subst.
      apply valrel_inProd'';
        apply valrel_0_pair;
        crush.
  + (* w = S w *)
    (* destruct vr as (? & [([=] & _)|(? & -> & vr')]). *)
    (* unfold prod_rel in vr'; cbn in vr'. *)
    (* destruct x; cbn in vr'; try contradiction. *)
    assert (wlt : w < S w) by eauto with arith.
    specialize (vr1 w wlt).
    specialize (vr2 w wlt).
    cbn in *.
    destruct (ih w _ _ _ wlt vr1) as (vs1' & es1 & vr1').
    destruct (ih w _ _ _ wlt vr2) as (vs2' & es2 & vr2').
    destruct vvs as (vvs1 & vvs2).
    destruct (valrel_implies_Value vr1').
    destruct (valrel_implies_Value vr2').
    exists (F.inl (F.pair vs1' vs2'));
    split.
    * apply (downgrade_eval_inProd vvs1 vvs2); eauto.
    * eapply (valrel_inProd'); assumption.
Qed.

Lemma upgrade_inProd_works {n d w dir p vs vu τ τ'} :
  valrel dir w (pEmulDV (S n) p (I.tprod τ τ')) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              (* valrel dir w' (pEmulDV (n + d) p τ') vs₁ vu₁) → *)
              (* ∃ vs₁', app (downgrade n d (I.tprod τ τ')) vs₁ -->* vs₁' ∧ *)
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
                      (* valrel dir w' (pEmulDV n p (I.tprod τ τ')) vs₁' vu₁) → *)
  exists v',
    app (upgrade (S n) d (I.tprod τ τ')) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (I.tprod τ τ')) v' vu.
Proof.
  intros vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].
  destruct (invert_valrel_pEmulDV_inProd' vr) as (vs1 & vs2 & vu1 & vu2 & -> & -> & vr1 & vr2).
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Prod vvs tvs) as [(? & ? & ? & ?) | ?]; [| inversion H].
    F.stlcCanForm. inversion H0; subst.
    destruct H as (vx2 & vx3).
    destruct (upgrade_reduces d H3 vx2) as (x4 & vx4 & tyx4 & esx4).
    destruct (upgrade_reduces d H4 vx3) as (x5 & vx5 & tyx5 & esx5).
    exists (inl (pair x4 x5)); split; I.crushTyping.
    * eapply upgrade_eval_inProd; eauto.
    * subst.
      apply valrel_inProd'';
        apply valrel_0_pair;
        crush.
  + assert (wlt : w < S w) by eauto with arith.
    specialize (vr1 w wlt).
    specialize (vr2 w wlt).
    cbn in *.
    destruct (ih w _ _ _ wlt vr1) as (vs1' & es1 & vr1').
    destruct (ih w _ _ _ wlt vr2) as (vs2' & es2 & vr2').
    destruct vvs as (vvs1 & vvs2).
    destruct (valrel_implies_Value vr1').
    destruct (valrel_implies_Value vr2').
    exists (F.inl (F.pair vs1' vs2'));
    split.
    * apply (upgrade_eval_inProd vvs1 vvs2); eauto.
    * eapply (valrel_inProd'); assumption.
Qed.

Lemma downgrade_inSum_works {n d w dir p vs vu τ τ'} :
  valrel dir w (pEmulDV (S (n + d)) p (I.tsum τ τ')) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              (* valrel dir w' (pEmulDV (n + d) p τ') vs₁ vu₁) → *)
              (* ∃ vs₁', app (downgrade n d (I.tsum τ τ')) vs₁ -->* vs₁' ∧ *)
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
                      (* valrel dir w' (pEmulDV n p (I.tsum τ τ')) vs₁' vu₁) → *)
  exists v',
    app (downgrade (S n) d (I.tsum τ τ')) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (I.tsum τ τ')) v' vu.
Proof.
  intros vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  destruct (invert_valrel_pEmulDV_inSum'' vr) as (vs' & vu' & ?); subst.
  simpl in H0, H2.
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Sum H H0) as [(? & ? & ? & ?) | ?]; [| inversion H4].
    F.stlcCanForm; inversion H5; subst;
    destruct (downgrade_reduces H8 H4) as (vs'' & vvs'' & ty' & es');
    destruct H3 as [(? & ? & ?) | (? & ? & ?)]; try (inversion H3; fail); inversion H3; subst;
    [exists ((F.inl (F.inl vs''))) | exists ((F.inl (F.inr vs'')))];
    [assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu') by lia
    |assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ') vs'' vu') by lia];
    (split; [apply (downgrade_eval_inSum H4 vvs''); crush|]);
    [assert (OfType (pEmulDV n p τ) vs'' vu') by crush
    |assert (OfType (pEmulDV n p τ') vs'' vu') by crush];
    apply valrel_inSum'';
    [apply valrel_0_inl | apply valrel_0_inr];
    crush.
  + (* w = S w *)
    assert (wlt : w < S w) by eauto with arith;
    destruct H3 as [(? & ? & vr') | (? & ? & vr')]; try (inversion H3; fail); subst;
    specialize (vr' w wlt);
    cbn in H;
    destruct (ih w _ _ _ wlt vr') as (vs'' & es' & vr'');
    destruct (valrel_implies_Value vr'');
    [exists (F.inl (F.inl vs'')) | exists (F.inl (F.inr vs''))];
    (split; [
       apply (downgrade_eval_inSum H H3); eauto
       | eapply (valrel_inSum'); (left; eauto; fail) || (right; eauto; fail)]).
Qed.

Lemma upgrade_inSum_works {n d w dir p vs vu τ τ'} :
  valrel dir w (pEmulDV (S n) p (I.tsum τ τ')) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              (* valrel dir w' (pEmulDV (n + d) p τ') vs₁ vu₁) → *)
              (* ∃ vs₁', app (downgrade n d (I.tsum τ τ')) vs₁ -->* vs₁' ∧ *)
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
                      (* valrel dir w' (pEmulDV n p (I.tsum τ τ')) vs₁' vu₁) → *)
  exists v',
    app (upgrade (S n) d (I.tsum τ τ')) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (I.tsum τ τ')) v' vu.
Proof.
  intros vr ih.
  pose proof (valrel_implies_OfType vr) as ot''.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  destruct (invert_valrel_pEmulDV_inSum'' vr) as (vs' & vu' & ?); subst.
  simpl in H0, H2.
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Sum H H0) as [(? & ? & ? & ?) | ?]; [| inversion H4].
    F.stlcCanForm; inversion H5; subst;
    destruct (upgrade_reduces d H8 H4) as (vs'' & vvs'' & ty' & es');
    destruct H3 as [(? & ? & ?) | (? & ? & ?)]; try (inversion H3; fail); inversion H3; subst;
    [exists ((F.inl (F.inl vs''))) | exists ((F.inl (F.inr vs'')))];
    [assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu') by lia
    |assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ') vs'' vu') by lia];
    (split; [apply (upgrade_eval_inSum H4 vvs''); crush|]);
    [assert (OfType (pEmulDV (n + d) p τ) vs'' vu') by crush
    |assert (OfType (pEmulDV (n + d) p τ') vs'' vu') by crush];
    apply valrel_inSum'';
    [apply valrel_0_inl | apply valrel_0_inr];
    crush.
  + (* w = S w *)
    assert (wlt : w < S w) by eauto with arith;
    destruct H3 as [(? & ? & vr') | (? & ? & vr')]; try (inversion H3; fail); subst;
    specialize (vr' w wlt);
    cbn in H;
    destruct (ih w _ _ _ wlt vr') as (vs'' & es' & vr'');
    destruct (valrel_implies_Value vr'');
    [exists (F.inl (F.inl vs'')) | exists (F.inl (F.inr vs''))];
    (split; [
       apply (upgrade_eval_inSum H H3); eauto
       | eapply (valrel_inSum'); (left; eauto; fail) || (right; eauto; fail)]).
Qed.


Lemma downgrade_inRec_works {n d w dir p vs vu τ} :
  valrel dir w (pEmulDV (S (n + d)) p (I.trec τ)) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  exists v',
    app (downgrade (S n) d (I.trec τ)) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (I.trec τ)) v' vu.
Proof.
  intros vr ih.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  simpl in H0, H2.
  assert (exists vu', vu = fold_ vu') by (dependent destruction H2; crush).
  destruct H3 as (vu' & ?);
  subst.
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Rec H H0) as [(? & ? & ? & ?) | ?]; [| inversion H3].
    inversion H4; subst.
    destruct (downgrade_reduces H5 H3) as (vs'' & vvs'' & ty' & es').
    assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu') by lia.
    exists (F.inl vs'').
    split.
    exact (downgrade_eval_inRec H3 vvs'' es').
    apply valrel_0_inRec.
    crush.
  + (* w = S w *)
    pose proof (invert_valrel_pEmulDV_inRec vr).
    assert (wlt : w < S w) by eauto with arith.
    destruct (ih _ _ _ _ wlt H3) as (? & ? & ?).
    exists (F.inl x).
    split.
    destruct (valrel_implies_OfType H5) as [[? _] _].
    apply downgrade_eval_inRec; crush.
    apply valrel_inRec.
    assumption.
Qed.

Lemma upgrade_inRec_works {n d w dir p vs vu τ} :
  valrel dir w (pEmulDV (S n) p (I.trec τ)) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
  exists v',
    app (upgrade (S n) d (I.trec τ)) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (I.trec τ)) v' vu.
Proof.
  intros vr ih.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  simpl in H0, H2.
  assert (exists vu', vu = fold_ vu') by (dependent destruction H2; crush).
  destruct H3 as (vu' & ?);
  subst.
  destruct w.
  + (* w = 0 *)
    destruct (canonUValS_Rec H H0) as [(? & ? & ? & ?) | ?]; [| inversion H3].
    inversion H4; subst.
    destruct (upgrade_reduces d H5 H3) as (vs'' & vvs'' & ty' & es').
    assert (forall w', w' < 0 → valrel dir w' (pEmulDV n p τ) vs'' vu') by lia.
    exists (F.inl vs'').
    split.
    exact (upgrade_eval_inRec H3 vvs'' es').
    apply valrel_0_inRec.
    crush.
  + (* w = S w *)
    pose proof (invert_valrel_pEmulDV_inRec vr).
    assert (wlt : w < S w) by eauto with arith.
    destruct (ih _ _ _ _ wlt H3) as (? & ? & ?).
    exists (F.inl x).
    split.
    destruct (valrel_implies_OfType H5) as [[? _] _].
    apply upgrade_eval_inRec; crush.
    apply valrel_inRec.
    assumption.
Qed.

Lemma downgrade_inArr_works {n d w dir p vs vu τ τ'} :
  valrel dir w (pEmulDV (S (n + d)) p (I.tarr τ τ')) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
  exists v',
    app (downgrade (S n) d (I.tarr τ τ')) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S n) p (I.tarr τ τ')) v' vu.
Proof.
  intros vr ihd ihu.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  exists (F.inl (abs (UValFI n τ) (app (downgrade n d τ') (app (vs[wk]) (app (upgrade n d τ) (var 0)))))).
  split.
  - eapply downgrade_eval_inArr; crush.
  - eapply valrel_inArr.
    apply invert_valrel_pEmulDV_inArr in vr.
    simpl in vvs.
    apply valrel_ptarr_inversion in vr; destruct_conjs; subst.
    simpl in *.

    (* unfold the valrel-ptarr *)
    change (abs (UValFI n τ)) with (abs (repEmul (pEmulDV n p τ))).
    change (I.abs τ) with (I.abs (fxToIs (pEmulDV n p τ))).
    apply valrel_lambda; crushOfType; crushTyping;
    eauto using downgrade_T, upgrade_T.
    rewrite -> ?upgrade_sub, ?downgrade_sub.

    rewrite <- ap_liftSub; rewrite <- up_liftSub;
    rewrite -> liftSub_wkm; rewrite (apply_wkm_beta1_up_cancel vr vs).

    (* first execute the upgrade *)
    specialize (ihu w' _ _ _ H0 H5).
    destruct ihu as (vs' & eups & vr').
    enough (termrel dir w' (pEmulDV n p τ')
                    (app (downgrade n d τ') (app (abs (UValFI (n + d) τ) vr) vs')) (H [beta1 vu])) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' eups _ _ _) tr'); 
            inferContext; crush; eauto using downgrade_value).

    (* now beta-reduce *)
    enough (termrel dir w' (pEmulDV n p τ')
                    (app (downgrade n d τ') (vr[beta1 vs']))
                    H[beta1 vu]) as tr'
    by (refine (termrel_antired_star_left _ tr'); simpl; eauto with eval;
        apply evalToStar;
        destruct (valrel_implies_Value vr') as [? _];
        assert (e₀ : app (abs (UValFI (n + d) τ) vr) vs' -->₀ vr[beta1 vs']) by (eauto with eval);
        eapply (eval_from_eval₀ e₀); inferContext; crush; eauto using downgrade_value).

    (* now execute the application *)
    specialize (H4 w' _ _ H0 H1 vr').
    eapply (termrel_ectx' H4); F.inferContext; I.inferContext; crush;
    eauto using downgrade_value.

    (* now execute the downgrade *)
    assert (wlt0 : w'0 < w) by lia.
    specialize (ihd w'0 _ _ _ wlt0 H8).
    destruct ihd as (vs'' & edowns & vr'').
    enough (termrel dir w'0 (pEmulDV n p τ')
                    vs'' vu0) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' edowns _ _ _) tr');
            inferContext; crush; eauto using downgrade_value).

    (* conclude *)
    apply valrel_in_termrel.
    assumption.
Qed.

Lemma upgrade_inArr_works {n d w dir p vs vu τ τ'} :
  valrel dir w (pEmulDV (S n) p (I.tarr τ τ')) (F.inl vs) vu →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV (n + d) p τ) vs₁ vu₁ →
              ∃ vs₁', app (downgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV n p τ) vs₁' vu₁) →
  (forall w' vs₁ vu₁ τ, w' < w →
              valrel dir w' (pEmulDV n p τ) vs₁ vu₁ →
              ∃ vs₁', app (upgrade n d τ) vs₁ -->* vs₁' ∧
                      valrel dir w' (pEmulDV (n + d) p τ) vs₁' vu₁) →
  exists v',
    app (upgrade (S n) d (I.tarr τ τ')) (F.inl vs) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p (I.tarr τ τ')) v' vu.
Proof.
  intros vr ihd ihu.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  exists (F.inl (abs (UValFI (n + d) τ) (app (upgrade n d τ') (app (vs[wk]) (app (downgrade n d τ) (var 0)))))).
  split.
  - eapply upgrade_eval_inArr; crush.
  - eapply valrel_inArr.
    apply invert_valrel_pEmulDV_inArr in vr.
    simpl in vvs.
    apply valrel_ptarr_inversion in vr; destruct_conjs; subst.
    simpl in *.

    (* unfold the valrel-ptarr *)
    change (abs (UValFI (n + d) τ)) with (abs (repEmul (pEmulDV (n + d) p τ))).
    change (I.abs τ) with (I.abs (fxToIs (pEmulDV (n + d) p τ))).
    apply valrel_lambda; crushOfType; crushTyping;
    eauto using downgrade_T, upgrade_T.
    rewrite -> ?upgrade_sub, ?downgrade_sub.

    rewrite <- ap_liftSub; rewrite <- up_liftSub;
    rewrite -> liftSub_wkm; rewrite (apply_wkm_beta1_up_cancel vr vs).

    (* first execute the upgrade *)
    specialize (ihd w' _ _ _ H0 H5).
    destruct ihd as (vs' & edowns & vr').
    enough (termrel dir w' (pEmulDV (n + d) p τ')
                    (app (upgrade n d τ') (app (abs (UValFI n τ) vr) vs')) (H [beta1 vu])) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' edowns _ _ _) tr');
            inferContext; crush; eauto using upgrade_value).

    (* now beta-reduce *)
    enough (termrel dir w' (pEmulDV (n + d) p τ')
                    (app (upgrade n d τ') (vr[beta1 vs']))
                    H[beta1 vu]) as tr'
    by (refine (termrel_antired_star_left _ tr'); simpl; eauto with eval;
        apply evalToStar;
        destruct (valrel_implies_Value vr') as [? _];
        assert (e₀ : app (abs (UValFI n τ) vr) vs' -->₀ vr[beta1 vs']) by (eauto with eval);
        eapply (eval_from_eval₀ e₀); inferContext; crush; eauto using upgrade_value).

    (* now execute the application *)
    specialize (H4 w' _ _ H0 H1 vr').
    eapply (termrel_ectx' H4); F.inferContext; I.inferContext; crush;
    eauto using upgrade_value.

    (* now execute the downgrade *)
    assert (wlt0 : w'0 < w) by lia.
    specialize (ihu w'0 _ _ _ wlt0 H8).
    destruct ihu as (vs'' & eups & vr'').
    enough (termrel dir w'0 (pEmulDV (n + d) p τ')
                    vs'' vu0) as tr'
        by (refine (termrel_antired_star_left (evalstar_ctx' eups _ _ _) tr');
            inferContext; crush; eauto using upgrade_value).

    (* conclude *)
    apply valrel_in_termrel.
    assumption.
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
  crush.
  eauto using downgrade_zero_eval.
Qed.

Lemma downgrade_inr_works {n d v vu dir w p τ} :
  valrel dir w (pEmulDV (S (n + d)) p τ) (F.inr v) vu →
  exists v',
    app (downgrade (S n) d τ) (F.inr v) -->* v' ∧
    valrel dir w (pEmulDV (S n) p τ) v' vu.
Proof.
  intros vr.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  simpl in H0, H2.
  assert (v = unit) by (
  dependent destruction H0;
  cbn in H;
  apply (F.can_form_tunit H H0)).
  subst.
  exists (F.inr unit).
  dependent destruction τ;
  (split; [
  eapply evalStepStar;
  try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
  subst; cbn; crush;
  eapply evalStepStar;
  try refine (eval_ctx₀ phole (eval_case_inr _) I); eauto;
  crush|
  assert (p = imprecise) by exact (invert_valrel_pEmulDV_unk vr);
  refine (valrel_unk _ H3);
  crush

  ]).
Qed.


Lemma downgrade_S_works {n d v vu dir w p τ} :
  dir_world_prec (S n) w dir p →
  valrel dir w (pEmulDV (S (n + d)) p τ) v vu →
  (forall v vu w' τ, dir_world_prec n w' dir p → valrel dir w' (pEmulDV (n + d) p τ) v vu →
                   exists v',
                     app (downgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV n p τ) v' vu) →
  (forall v vu w' τ, dir_world_prec n w' dir p → valrel dir w' (pEmulDV n p τ) v vu →
                   exists v',
                     app (upgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV (n + d) p τ) v' vu) →
  exists v', 
    app (downgrade (S n) d τ) v -->* v' ∧
    valrel dir w (pEmulDV (S n) p τ) v' vu.
Proof.
  intros dwp vr IHdown IHup.
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] [vvu tyvu]].
  simpl in ty, tyvu.
  destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)]; subst; [
    | exact (downgrade_inr_works vr)
  ].
  dependent destruction τ.
  - (* inArr *)
    eapply (downgrade_inArr_works vr); crush.
    + eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
    + eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inUnit *)
    assert (x = unit) by (crushTyping; stlcCanForm; reflexivity);
      subst.
    exists (F.inl unit).
    eauto using downgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inBool *)
    exists (inl x); crush.
    eauto using downgrade_eval_inBool, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inProd *)
    eapply (downgrade_inProd_works vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
  - (* inSum *)
    eapply (downgrade_inSum_works vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
  - (* inRec *)
    eapply (downgrade_inRec_works vr); crush;
    eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
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
  destruct (valrel_implies_OfType vr) as [[vv ty] [vvu tyvu]];
  assert (OfType (pEmulDV d p τ) (unkUVal d) vu) by (crush; eauto using unkUVal_Value, unkUValT);
  exists (unkUVal d).
  destruct (dwp_zero dwp).
  eauto using upgrade_zero_eval, valrel_unk, dwp_zero.
Qed.


Lemma upgrade_inr_works {n d v vu dir w p τ} :
  valrel dir w (pEmulDV (S n) p τ) (F.inr v) vu →
  exists v',
    app (upgrade (S n) d τ) (F.inr v) -->* v' ∧
    valrel dir w (pEmulDV (S (n + d)) p τ) v' vu.
Proof.
  intros vr.
  destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
  simpl in H0, H2.
  assert (v = unit) by (
  dependent destruction H0;
  cbn in H;
  apply (F.can_form_tunit H H0)).
  subst.
  exists (F.inr unit).
  dependent destruction τ;
  (split; [
  eapply evalStepStar;
  try refine (eval_ctx₀ phole (eval_beta _) I); eauto;
  subst; cbn; crush;
  eapply evalStepStar;
  try refine (eval_ctx₀ phole (eval_case_inr _) I); eauto;
  crush|
  assert (p = imprecise) by exact (invert_valrel_pEmulDV_unk vr);
  refine (valrel_unk _ H3);
  crush

  ]).
Qed.


Lemma upgrade_S_works {n d v vu dir w p τ} :
  dir_world_prec (S n) w dir p →
  valrel dir w (pEmulDV (S n) p τ) v vu →
  (forall v vu w' τ, dir_world_prec n w' dir p → valrel dir w' (pEmulDV (n + d) p τ) v vu →
                   exists v', 
                     app (downgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV n p τ) v' vu) →
  (forall v vu w' τ, dir_world_prec n w' dir p → valrel dir w' (pEmulDV n p τ) v vu →
                   exists v', 
                     app (upgrade n d τ) v -->* v' ∧ valrel dir w' (pEmulDV (n + d) p τ) v' vu) →
  exists v', 
    app (upgrade (S n) d τ) v -->* v' ∧
    valrel dir w (pEmulDV (S n + d) p τ) v' vu.
Proof.
  change (S n + d) with (S (n + d)).
  intros dwp vr IHdown IHup.
  destruct (valrel_implies_Value vr);
  destruct (valrel_implies_OfType vr) as [[vv ty] [vvu tyvu]].
  simpl in ty, tyvu.
  destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)]; subst; [
    | exact (upgrade_inr_works vr)
  ].
  dependent destruction τ.
  - (* inArr *)
    eapply (upgrade_inArr_works vr); crush.
    + eapply IHdown; try assumption; eapply dwp_invert_S'; crush.
    + eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inUnit *)
    assert (x = unit) by (crushTyping; stlcCanForm; reflexivity);
      subst.
    exists (F.inl unit).
    eauto using upgrade_eval_inUnit, invert_valrel_pEmulDV_inUnit', valrel_inUnit.
  - (* inBool *)
    exists (F.inl x).
    split; [|assumption].
    eapply evalStepStar.
    cbn.
    eapply (F.eval_ctx₀' (F.eval_beta H)); F.inferContext; now cbn.
    crush.
  - (* inProd *)
    eapply (upgrade_inProd_works vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inSum *)
    eapply (upgrade_inSum_works vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* inRec *)
    eapply (upgrade_inRec_works vr); crush;
    eapply IHup; try assumption; eapply dwp_invert_S'; crush.
  - (* tvar *)
    contradiction (invert_valrel_pEmulDV_inVar vr).
Qed.

Lemma downgrade_works {n d v vu dir w p τ} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p τ) v vu →
  exists v', 
    app (downgrade n d τ) v -->* v' ∧
    valrel dir w (pEmulDV n p τ) v' vu
with upgrade_works {n v vu dir w p τ} d :
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
      auto using downgrade_S_works.
  - destruct n.
    + intros; apply upgrade_zero_works; trivial.
    + specialize (downgrade_works n).
      specialize (upgrade_works n).
      auto using upgrade_S_works.
Qed.

Lemma downgrade_works' {n d v vu dir w p τ} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p τ) v vu →
  termrel dir w (pEmulDV n p τ) (app (downgrade n d τ) v) vu.
Proof.
  intros dwp vr.
  destruct (downgrade_works dwp vr) as (v' & es & vr').
  apply valrel_in_termrel in vr'.
  refine (termrel_antired_star_left es vr').
Qed.

Lemma downgrade_works'' {n d v vu dir w p τ} :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV (n + d) p τ) v vu →
  termrel₀ dir w (pEmulDV n p τ) (app (downgrade n d τ) v) vu.
Proof.
  intros dwp vr.
  destruct (downgrade_works dwp vr) as (v' & es & vr').
  apply valrel_in_termrel₀ in vr'.
  refine (termrel₀_antired_star_left es vr').
Qed.

Lemma upgrade_works' {n v vu dir w p τ} d :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV n p τ) v vu →
  termrel dir w (pEmulDV (n + d) p τ) (app (upgrade n d τ) v) vu.
Proof.
  intros dwp vr.
  destruct (upgrade_works d dwp vr) as (v' & es & vr').
  apply valrel_in_termrel in vr'.
  refine (termrel_antired_star_left es vr').
Qed.

Lemma upgrade_works'' {n v vu dir w p τ} d :
  dir_world_prec n w dir p →
  valrel dir w (pEmulDV n p τ) v vu →
  termrel₀ dir w (pEmulDV (n + d) p τ) (app (upgrade n d τ) v) vu.
Proof.
  intros dwp vr.
  destruct (upgrade_works d dwp vr) as (v' & es & vr').
  apply valrel_in_termrel₀ in vr'.
  refine (termrel₀_antired_star_left es vr').
Qed.

Lemma compat_upgrade {Γ ts dir m tu n p τ} d :
  dir_world_prec n m dir p →
  ⟪ Γ ⊩ ts ⟦ dir , m ⟧ tu : pEmulDV n p τ⟫ →
  ⟪ Γ ⊩ app (upgrade n d τ) ts ⟦ dir , m ⟧ tu : pEmulDV (n + d) p τ ⟫.
Proof.
  intros.
  repeat crushLRMatch.
  - eauto using upgrade_T with typing.
  - I.crushTyping.
  - intros.
    specialize (H2 w H3 _ _ H4).
    simpl; repeat crushStlcSyntaxMatchH.
    rewrite upgrade_sub.
    eapply (termrel_ectx' H2); F.inferContext; I.inferContext; crush;
    eauto using upgrade_value.
    simpl.
    eauto using upgrade_works', dwp_mono.
Qed.

Lemma compat_downgrade {Γ ts dir m tu n p d τ} :
  dir_world_prec n m dir p →
  ⟪ Γ ⊩ ts ⟦ dir , m ⟧ tu : pEmulDV (n + d) p τ ⟫ →
  ⟪ Γ ⊩ app (downgrade n d τ) ts ⟦ dir , m ⟧ tu : pEmulDV n p τ ⟫.
Proof.
  intros.
  repeat crushLRMatch.
  - eauto using downgrade_T with typing.
  - I.crushTyping.
  - intros.
    specialize (H2 w H3 _ _ H4).
    simpl; repeat crushStlcSyntaxMatchH.
    rewrite downgrade_sub.
    eapply (termrel_ectx' H2); F.inferContext; I.inferContext; crush;
    eauto using downgrade_value.
    simpl.
    eauto using downgrade_works', dwp_mono.
Qed.
