Require StlcIsoValid.SpecSyntax.
Require StlcEqui.SpecSyntax.
Require Import StlcIsoValid.SpecTyping.
Require Import StlcIsoValid.LemmasTyping.
Require Import StlcIsoValid.Size.
Require Import StlcIsoValid.SpecAnnot.
Require Import StlcIsoValid.Fix.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcIsoValid.SpecEvaluation.
Require Import StlcIsoValid.CanForm.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.TypeSafety.
Require Import StlcEqui.SpecTyping.
Require Import StlcIsoValid.LemmasEvaluation.
Require Import UValIE.UVal.
Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import LogRelIE.LemmasInversion.
Require Import Lia.
Require Import Db.Lemmas.

Require Import LogRelIE.LR.
(* Require Import CompilerIE.ProtectConfine. *)
Require Import CompilerIE.CompilerIE.

Require Import BacktransIE.UValHelpers.
Require Import BacktransIE.UValHelpers2.

Require Import UValIE.UVal.

Local Ltac crush :=
  cbn in * |-;
  repeat
    (repeat I.crushStlcSyntaxMatchH;
     repeat E.crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushRepEmulEmbed;
     repeat I.crushStlcEval;
     repeat E.crushStlcEval;
     I.crushTyping;
     E.crushTyping;
     crushOfType;
     try split;
     trivial;
     subst*);
  try discriminate; try lia;
  eauto with eval;
  repeat I.crushStlcSyntaxMatchH; (* remove apTm's again *)
  repeat E.crushStlcSyntaxMatchH. (* remove apTm's again *)

Lemma Terminating_inl {t} : t ⇓ -> (inl t) ⇓.
Proof.
  intros (v & vv & vreds).
  exists (inl v).
  split; eauto with eval.
  now eapply (evalstar_ctx (pinl phole)).
Qed.

Fixpoint removeTRec (τ : Ty) : Ty :=
  match τ with
  | trec τ' => τ'
  | _ => tunit
  end.

Fixpoint ia_unfolds (n : nat) (τ : Ty) (t : TmA) : TmA :=
  match n with
  | 0 => t
  | S n => ia_unfolds n (unfoldOnce τ) (ia_unfold_ (removeTRec τ) t)
  end.

Lemma ia_unfolds_T {n τ t Γ} :
  n <= LMC τ -> ValidTy τ ->
  ⟪ Γ ia⊢ t : τ ⟫ ->
  ⟪ Γ ia⊢ ia_unfolds n τ t : unfoldn n τ ⟫.
Proof.
  revert t τ.
  induction n; intros t τ ineq vτ tyt; [easy|].
  cbn.
  destruct τ; cbn in ineq;
    try match goal with
    | [ _ : S n <= 0 |- _ ] => exfalso; lia
    end.
  eapply IHn.
  rewrite (LMC_unfoldOnce (trec τ)); cbn; crushValidTy.
  eauto with tyvalid.
  constructor; crushValidTy; cbn.
Qed.

Fixpoint unfolds (n : nat) (t : Tm) : Tm :=
  match n with
  | 0 => t
  | S n => unfolds n (unfold_ t)
  end.

Lemma unfolds_T {n τ t Γ} :
  n <= LMC τ -> ValidTy τ ->
  ⟪ Γ i⊢ t : τ ⟫ ->
  ⟪ Γ i⊢ unfolds n t : unfoldn n τ ⟫.
Proof.
  revert t τ.
  induction n; intros t τ ineq vτ tyt; [easy|].
  cbn.
  destruct τ; cbn in ineq;
    try match goal with
    | [ _ : S n <= 0 |- _ ] => exfalso; lia
    end.
  eapply IHn.
  rewrite (LMC_unfoldOnce (trec τ)); cbn; crushValidTy.
  eauto with tyvalid.
  constructor; crushValidTy; cbn.
Qed.

Lemma unfolds_sub {n γ} : forall t, (unfolds n t) [ γ ] = unfolds n (t [ γ ]).
Proof.
  induction n; intros; cbn; [easy|].
  now rewrite IHn.
Qed.

Fixpoint unfolds_ctx (n : nat) : PCtx :=
  match n with
  | 0 => phole
  | S n => pctx_cat (punfold phole) (unfolds_ctx n)
  end.

Lemma unfolds_unfolds_ctx {n} : forall t, unfolds n t = pctx_app t (unfolds_ctx n).
Proof.
  induction n; [easy|].
  intros t; simpl.
  now rewrite IHn, pctx_cat_app.
Qed.

Lemma unfolds_ectx {n} : ECtx (unfolds_ctx n).
Proof.
  induction n; cbn; [easy|].
  now eapply ectx_cat.
Qed.

Lemma unfolds_terminate {τ} : forall vs,
  ValidTy τ ->
  ⟪ empty i⊢ vs : τ ⟫ ->
  Value vs ->
  (unfolds (LMC τ) vs) ⇓.
Proof.
  remember (LMC τ) as n.
  revert τ Heqn.
  induction n; intros.
  destruct τ; cbn; intros;
   now eapply values_terminate.
  destruct τ; inversion Heqn.
  stlcCanForm1.
  destruct_conjs; subst.
  cbn in *.
  eapply I.termination_closed_under_antireduction.
  eapply eval_from_eval₀.
  eapply (eval_fold_unfold _ H1).
  rewrite unfolds_unfolds_ctx; reflexivity.
  reflexivity.
  now eapply unfolds_ectx.
  rewrite <- unfolds_unfolds_ctx.
  eapply (IHn (unfoldOnce (trec τ)));
  crushValidTy.
  rewrite LMC_unfoldOnce; crushValidTy.
  cbn; lia.
Qed.

Lemma ia_unfolds_eraseAnnot {n τ t} :
  eraseAnnot (ia_unfolds n τ t) = unfolds n (eraseAnnot t).
Proof.
  revert τ t.
  induction n; [easy|].
  intros τ t.
  cbn. now rewrite IHn.
Qed.

Fixpoint ia_folds (n : nat) (τ : Ty) (t : TmA) : TmA :=
  match n with
  | 0 => t
  | S n => ia_fold_ (removeTRec τ) (ia_folds n (unfoldOnce τ) t)
  end.

Lemma ia_folds_T {n τ t Γ} :
  n <= LMC τ -> ValidTy τ ->
  ⟪ Γ ia⊢ t : unfoldn n τ ⟫ ->
  ⟪ Γ ia⊢ ia_folds n τ t : τ ⟫.
Proof.
  revert t τ.
  induction n; intros t τ ineq vτ tyt; [easy|].
  cbn.
  destruct τ; cbn in ineq;
    try match goal with
    | [ _ : S n <= 0 |- _ ] => exfalso; lia
    end.
  I.crushTypingIA.
  eapply IHn; try easy.
  change (LMC _) with (LMC (unfoldOnce (trec τ))).
  rewrite (LMC_unfoldOnce (trec τ)); cbn; crushValidTy.
  crushValidTy.
Qed.

Fixpoint folds (n : nat) (t : Tm) : Tm :=
  match n with
  | 0 => t
  | S n => fold_ (folds n t)
  end.

Lemma folds_T {n τ t Γ} :
  n <= LMC τ -> ValidTy τ ->
  ⟪ Γ i⊢ t : unfoldn n τ ⟫ ->
  ⟪ Γ i⊢ folds n t : τ ⟫.
Proof.
  revert t τ.
  induction n; intros t τ ineq vτ tyt; [easy|].
  cbn.
  destruct τ; cbn in ineq;
    try match goal with
    | [ _ : S n <= 0 |- _ ] => exfalso; lia
    end.
  constructor; try assumption.
  eapply IHn.
  change (n <= LMC (unfoldOnce (trec τ))).
  rewrite (LMC_unfoldOnce (trec τ)); cbn; crushValidTy.
  crushValidTy.
  exact tyt.
Qed.

Lemma ia_folds_eraseAnnot {n τ t} :
  eraseAnnot (ia_folds n τ t) = folds n (eraseAnnot t).
Proof.
  revert τ t.
  induction n; [easy|].
  intros τ t.
  cbn. now rewrite IHn.
Qed.

Lemma folds_Value {n vs} :
  Value (folds n vs) <-> Value vs.
Proof.
  induction n; intuition.
Qed.

Lemma folds_sub {n γ} : forall t, (folds n t) [ γ ] = folds n (t [ γ ]).
Proof.
  induction n; intros; simpl; [easy|].
  now rewrite <-IHn.
Qed.

Fixpoint folds_ctx (n : nat) : PCtx :=
  match n with
  | 0 => phole
  | S n => pctx_cat (folds_ctx n) (pfold phole)
  end.

Lemma folds_folds_ctx {n} : forall t, folds n t = pctx_app t (folds_ctx n).
Proof.
  induction n; [easy|].
  intros t; simpl.
  now rewrite <-IHn.
Qed.

Lemma folds_ectx {n} : ECtx (folds_ctx n).
Proof.
  induction n; now cbn.
Qed.

Lemma unfolds_folds_evalStar {n vs} :
  Value vs ->
  unfolds n (folds n vs) -->* vs.
Proof.
  revert vs.
  induction n; [eauto with eval|].
  intros vs vvs.
  cbn.
  eapply evalStepStar.
  rewrite unfolds_unfolds_ctx.
  eapply eval_ctx₀.
  now eapply eval_fold_unfold, folds_Value.
  now eapply unfolds_ectx.
  rewrite <-unfolds_unfolds_ctx.
  now eapply IHn.
Qed.

Fixpoint injectA (n : nat) (τ : I.Ty) {struct n} : I.TmA :=
       I.ia_abs τ (UValIE n τ)
         (* TODO: argument of type τ needs to be unfolded (LMC τ) times before use! *)
             (match n with
              | O => I.ia_unit
              | S n => (match (unfoldn (LMC τ) τ) with
                       | I.tarr τ₁ τ₂ => I.ia_inl (I.tarr (UValIE n τ₁) (UValIE n τ₂)) I.tunit
                                          (I.ia_abs (UValIE n τ₁) (UValIE n τ₂)
                                              (I.ia_app τ₂ (UValIE n τ₂)
                                                       (injectA n τ₂)
                                                       (I.ia_app τ₁ τ₂ (ia_unfolds (LMC τ) τ (I.ia_var 1))
                                                                (I.ia_app (UValIE n τ₁) τ₁
                                                                         (extractA n τ₁)
                                                                         (I.ia_var 0)))))
                       | I.tunit => I.ia_inl I.tunit I.tunit (ia_unfolds (LMC τ) τ (I.ia_var 0))
                       | I.tbool => I.ia_inl I.tbool I.tunit (ia_unfolds (LMC τ) τ (I.ia_var 0))
                       | I.tprod τ₁ τ₂ => I.ia_inl (I.tprod (UValIE n τ₁) (UValIE n τ₂)) I.tunit
                                                 (I.ia_pair (UValIE n τ₁) (UValIE n τ₂)
                                                           (I.ia_app τ₁ (UValIE n τ₁) (injectA n τ₁)
                                                                    (I.ia_proj₁ τ₁ τ₂ (ia_unfolds (LMC τ) τ (I.ia_var 0))))
                                                           (I.ia_app τ₂ (UValIE n τ₂) (injectA n τ₂)
                                                                    (I.ia_proj₂ τ₁ τ₂ (ia_unfolds (LMC τ) τ (I.ia_var 0)))))
                       | I.tsum τ₁ τ₂ => I.ia_inl (I.tsum (UValIE n τ₁) (UValIE n τ₂)) I.tunit (I.ia_caseof τ₁ τ₂ (I.tsum (UValIE n τ₁) (UValIE n τ₂)) (ia_unfolds (LMC τ) τ (I.ia_var 0))
                                                 (I.ia_inl (UValIE n τ₁) (UValIE n τ₂)
                                                          (I.ia_app τ₁ (UValIE n τ₁) (injectA n τ₁)
                                                                 (I.ia_var 0)))
                                                 (I.ia_inr (UValIE n τ₁) (UValIE n τ₂)
                                                          (I.ia_app τ₂ (UValIE n τ₂) (injectA n τ₂)
                                                               (I.ia_var 0))))
                       | I.trec _ => I.ia_unit
                       | I.tvar _ => I.ia_unit
                       end)
                end)
  with extractA (n : nat) (τ : I.Ty) {struct n} : I.TmA :=
         let caseτ : I.Tm → I.Tm := caseUVal (UValIE n τ) in
         I.ia_abs (UValIE n τ) τ
               (match n with
                   | O => OmA τ
                   | S n => match (unfoldn (LMC τ) τ) with
                           | I.tarr τ₁ τ₂ => ia_folds (LMC τ) τ (I.ia_abs τ₁ τ₂ (I.ia_app (UValIE n τ₂) τ₂
                                                                (extractA n τ₂)
                                                                (I.ia_app (UValIE n τ₁) (UValIE n τ₂)
                                                                         (caseArrA n (I.ia_var 1)
                                                                                   τ₁
                                                                                   τ₂)
                                                                         (I.ia_app τ₁ (UValIE n τ₁) (injectA n τ₁)
                                                                                  (I.ia_var 0)))))
                           | I.tunit => ia_folds (LMC τ) τ (caseUnitA n (I.ia_var 0))
                           | I.tbool => ia_folds (LMC τ) τ (caseBoolA n (I.ia_var 0))
                           | I.tprod τ₁ τ₂ => ia_folds (LMC τ) τ (I.ia_pair τ₁ τ₂
                                                      (I.ia_app (UValIE n τ₁) τ₁ (extractA n τ₁)
                                                               (I.ia_proj₁ (UValIE n τ₁) (UValIE n τ₂) (caseProdA n (I.ia_var 0) τ₁ τ₂)))
                                                      (I.ia_app (UValIE n τ₂) τ₂ (extractA n τ₂)
                                                               (I.ia_proj₂ (UValIE n τ₁) (UValIE n τ₂) (caseProdA n (I.ia_var 0) τ₁ τ₂))))
                           | I.tsum τ₁ τ₂ => ia_folds (LMC τ) τ (I.ia_caseof (UValIE n τ₁) (UValIE n τ₂) (I.tsum τ₁ τ₂)
                                                       (caseSumA n (I.ia_var 0) τ₁ τ₂)
                                                       (I.ia_inl τ₁ τ₂ (I.ia_app (UValIE n τ₁) τ₁ (extractA n τ₁) (I.ia_var 0)))
                                                       (I.ia_inr τ₁ τ₂ (I.ia_app (UValIE n τ₂) τ₂ (extractA n τ₂) (I.ia_var 0))))
                           | I.trec _ => I.ia_unit
                           | I.tvar _ => I.ia_unit
                           end
               end).
Definition inject n τ := eraseAnnot (injectA n τ).
Definition extract n τ := eraseAnnot (extractA n τ).

Arguments injectA !n τ.
Arguments extractA !n τ.
Arguments inject !n τ.
Arguments extract !n τ.

Lemma inject_value {n τ} : I.Value (inject n τ).
Proof.
  (* exact E. *)
  (* Should be doable without the induction, but I don't see how *)
  destruct n; destruct τ; simpl; eauto with eval.
Qed.

Arguments UValIE !n τ.
Lemma injectAT {n τ Γ} : ValidTy τ -> ⟪ Γ ia⊢ injectA n τ : I.tarr τ (UValIE n τ) ⟫
with extractAT {n τ Γ} : ValidTy τ -> ⟪ Γ ia⊢ extractA n τ : I.tarr (UValIE n τ) τ ⟫.
Proof.
  - intros vτ. destruct n.
    + simpl.
      eauto with typing uval_typing.
    + simpl [UValIE UValIE'].
      assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
      assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
      remember (unfoldn (LMC τ) τ) as τ'.
      destruct τ'; try inversion luτz; I.crushTypingIA; crushValidTy_with_UVal;
      rewrite Heqτ';
      eapply ia_unfolds_T; I.crushTypingIA.
  - intros vτ. destruct n.
    + simpl.
      eauto with typing uval_typing tyvalid.
    + simpl [UValIE UValIE'].
      assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
      assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
      remember (unfoldn (LMC τ) τ) as τ'.
      destruct τ'; try inversion luτz; I.crushTypingIA; crushValidTy_with_UVal;
      eapply ia_folds_T; I.crushTypingIA;
      rewrite <-Heqτ'; I.crushTypingIA;
      eauto using wtOmA_tau with typing uval_typing; crushValidTy_with_UVal;
      eapply wtOmA_tau; crushValidTy_with_UVal.
Qed.

Lemma injectT {n τ Γ} : ValidTy τ -> ⟪ Γ i⊢ inject n τ : I.tarr τ (UValIE n τ) ⟫.
Proof.
  eauto using eraseAnnotT, injectAT.
Qed.
Lemma extractT {n τ Γ} : ValidTy τ -> ⟪ Γ i⊢ extract n τ : I.tarr (UValIE n τ) τ ⟫.
Proof.
  eauto using eraseAnnotT, extractAT.
Qed.

Hint Resolve injectT : uval_typing.
Hint Resolve extractT : uval_typing.
Hint Resolve injectAT : uval_typing.
Hint Resolve extractAT : uval_typing.

Lemma inject_closed {n τ} :
  ValidTy τ ->
  ⟨ 0 ⊢ inject n τ ⟩.
Proof.
  intros vτ.
  eapply (wt_implies_ws (Γ := I.empty)).
  now eapply injectT.
Qed.

Lemma extract_value {n τ} : I.Value (extract n τ).
Proof.
  (* exact E. *)
  (* Should be doable without the induction, but I don't see how *)
  destruct n; destruct τ; simpl; eauto with eval.
Qed.

Lemma extract_closed {n τ} :
  ValidTy τ ->
  ⟨ 0 ⊢ extract n τ ⟩.
Proof.
  intros vτ.
  eapply (wt_implies_ws (Γ := I.empty)).
  now eapply extractT.
Qed.

Lemma inject_sub {n τ γ} : ValidTy τ -> (inject n τ)[γ] = inject n τ.
Proof.
  intros vτ.
  apply wsClosed_invariant.
  now eapply inject_closed.
Qed.

Lemma extract_sub {n τ γ} : ValidTy τ -> (extract n τ)[γ] = extract n τ.
Proof.
  intros vτ.
  apply wsClosed_invariant.
  now eapply extract_closed.
Qed.

Fixpoint inject_terminates n {τ vs}:
  ValidTy τ ->
  OfTypeStlcIso (embed τ) vs ->
  Terminating (I.app (inject n τ) vs).
Proof.
  intros vτ [vvs vty].
  assert (vuτ : ValidTy (unfoldn (LMC τ) τ)) by eauto using ValidTy_unfoldn.
  assert (luτz : LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
  destruct n.
  - eapply I.termination_closed_under_antireduction.
    now eapply eval_eval₀, eval_beta.
    now eapply values_terminate.
  - unfold inject.
    cbn [injectA eraseAnnot].
    remember (unfoldn (LMC τ) τ) as τ'.
    rewrite repEmul_embed_leftinv in vty.
    destruct τ';
     (eapply I.termination_closed_under_antireduction;
      [now eapply eval_eval₀, eval_beta|]);
      simpl;
      I.crushTyping;
      rewrite ?ia_unfolds_eraseAnnot;
      rewrite ?unfolds_sub;
      simpl.
    + eapply values_terminate.
      now cbn.
    + crushTyping.
      eapply Terminating_inl.
      now eapply unfolds_terminate.
    + assert ((unfolds (LMC τ) vs) ⇓) as (v & vv & vreds).
      { eapply unfolds_terminate; crush; I.crushTyping. }
      eapply I.termination_closed_under_antireductionStar.
      { eapply (evalstar_ctx' vreds); inferContext.
        cbn; eauto using inject_value.
      }
      cbn.
      eapply values_terminate; now cbn.
    + change (app _) with (app (inject n τ'1)[beta1 vs]) at 1.
      change (app _) with (app (inject n τ'2)[beta1 vs]) at 2.
      rewrite ?inject_sub; crushValidTy.
      rewrite ?unfolds_sub; cbn.
      assert ((unfolds (LMC τ) vs) ⇓) as (v & vv & vreds).
      { eapply unfolds_terminate; crush; I.crushTyping. }
      eapply I.termination_closed_under_antireductionStar.
      { eapply (evalstar_ctx' vreds); inferContext.
        cbn; eauto using inject_value.
      }
      cbn.
      assert ⟪ empty i⊢ v : τ'1 r× τ'2 ⟫.
      { eapply (I.preservation_star vreds); I.crushTyping.
        rewrite Heqτ'.
        eapply unfolds_T; crush.
      }
      I.stlcCanForm1.
      destruct vv as (vx & vx0).
      eapply I.termination_closed_under_antireduction.
      { eapply (eval_from_eval₀ (eval_proj₁ vx vx0)); I.inferContext; cbn; eauto using inject_value with eval. }
      cbn.
      assert (OfTypeStlcIso (embed τ'1) x) as otx.
      { split; crush. }
      destruct (inject_terminates n τ'1 x H otx) as (vs' & vvs' & es).
      eapply I.termination_closed_under_antireductionStar.
      { eapply (evalstar_ctx' es); I.inferContext; now cbn. }
      cbn.
      eapply I.termination_closed_under_antireductionStar.
      { eapply (evalstar_ctx' vreds); inferContext.
        cbn; eauto using inject_value.
      }
      cbn.
      eapply I.termination_closed_under_antireduction.
      { eapply (eval_from_eval₀ (eval_proj₂ vx vx0)); I.inferContext; cbn; eauto using inject_value with eval. }
      cbn.
      assert (OfTypeStlcIso (embed τ'2) x0) as otx0.
      { split; crush. }
      destruct (inject_terminates n τ'2 x0 H0 otx0) as (vs2' & vvs2' & es2).
      eapply I.termination_closed_under_antireductionStar.
      { eapply (evalstar_ctx' es2); I.inferContext; now cbn. }
      cbn.
      eapply values_terminate; now cbn.
    + change (app _) with (app (inject n τ'1) [(beta1 vs)↑]) at 1.
      change (app _) with (app (inject n τ'2) [(beta1 vs)↑]) at 2.
      rewrite ?inject_sub; crushValidTy.
      assert ((unfolds (LMC τ) vs) ⇓) as (v & vv & vreds).
      { eapply unfolds_terminate; crush; I.crushTyping. }
      eapply I.termination_closed_under_antireductionStar.
      { eapply (evalstar_ctx' vreds); I.inferContext; now cbn. }
      cbn.
      assert ⟪ empty i⊢ v : τ'1 r⊎ τ'2 ⟫.
      { eapply (I.preservation_star vreds); I.crushTyping.
        rewrite Heqτ'.
        eapply unfolds_T; crush.
      }
      I.stlcCanForm1.
      * eapply I.termination_closed_under_antireduction.
        { eapply (eval_from_eval₀ (eval_case_inl vv)); I.inferContext; now cbn. }
        crushTyping.
        rewrite inject_sub; crushValidTy.
        assert (OfTypeStlcIso (embed τ'1) x) as otx.
        { split; crush. }
        destruct (inject_terminates n τ'1 x H otx) as (v' & vv' & es).
        eapply I.termination_closed_under_antireductionStar.
        { eapply (evalstar_ctx' es); I.inferContext; now cbn. }
        cbn.
        eapply values_terminate; now cbn.
      * eapply I.termination_closed_under_antireduction.
        { eapply (eval_from_eval₀ (eval_case_inr vv)); I.inferContext; now cbn. }
        crushTyping.
        rewrite inject_sub; crushValidTy.
        assert (OfTypeStlcIso (embed τ'2) x) as otx.
        { split; crush. }
        destruct (inject_terminates n τ'2 x H0 otx) as (v' & vv' & es).
        eapply I.termination_closed_under_antireductionStar.
        { eapply (evalstar_ctx' es); I.inferContext; now cbn. }
        cbn.
        eapply values_terminate; now cbn.
    + eapply values_terminate; now cbn.
    + eapply values_terminate; now cbn.
Qed.

Definition inject_works_prop (n : nat) (w : World) (d : Direction) (p : Prec) (vs : I.Tm) (vu : E.Tm) (τ : I.Ty) : Prop :=
  dir_world_prec n w d p →
  valrel d w (embed τ) vs vu →
  termrelnd₀ d w (pEmulDV n p τ) (I.app (inject n τ) vs) vu.
  (* ECtx Cs → E.ECtx Cu → *)
  (* contrel d w (embed τ) Cs Cu → *)
  (* (exists vs', I.pctx_app (I.app (inject n τ) vs) Cs -->* I.pctx_app vs' Cs *)
  (*        ∧ valrel d w (pEmulDV n p τ) vs' vu) *)
  (* ∨ Obs d w (I.pctx_app (I.app (inject n τ) vs) Cs) (E.pctx_app vu Cu). *)

Definition extract_works_prop (n : nat) (w : World) (d : Direction) (p : Prec) (vs : I.Tm) (vu : E.Tm) (τ : I.Ty) : Prop :=
  dir_world_prec n w d p →
  (d = dir_gt -> E.size vu <= w) ->
  valrel d w (pEmulDV n p τ) vs vu →
  termrelnd₀ d w (embed τ) (I.app (extract n τ) vs) vu.
  (* ECtx Cs → E.ECtx Cu → *)
  (* contrel d w (embed τ) Cs Cu → *)
  (* (exists vs', I.pctx_app (I.app (extract n τ) vs) Cs -->* I.pctx_app vs' Cs *)
  (*        ∧ valrel d w (embed τ) vs' vu) *)
  (* ∨ Obs d w (I.pctx_app (I.app (extract n τ) vs) Cs) (E.pctx_app vu Cu). *)

Lemma inject_zero_works {w d p vs vu τ} :
  inject_works_prop 0 w d p vs vu τ.
Proof.
  intros dwp vr.
  destruct (dwp_zero dwp); subst.
  destruct (valrel_implies_OfType vr) as [[vvs ovs] [vvu ovu]].
  eapply termrelnd₀_antired.
  - eapply evalToStar, eval₀_to_eval, eval_beta.
    assumption.
  - eapply rt1n_refl.
  - eapply valrel_termrelnd₀.
    crush.
    now rewrite isToEq_embed_leftinv in ovu.
Qed.

Lemma extract_zero_works {w d p vs vu τ} :
  extract_works_prop 0 w d p vs vu τ.
Proof.
  intros dwp _ vr.
  destruct (dwp_zero dwp); subst.
  intros vs0 vvs0 es.
  exfalso.
  cbn in es.
  eapply Om_div.
  exists vs0; split; [assumption|].
  refine (I.determinacyStar1 _ es _).
  - eapply eval_eval₀.
    destruct (valrel_implies_Value vr).
    eenough (Om _ = ?[t']) as ->.
    eapply eval_beta; crush.
    now cbn.
  - eauto using values_are_normal.
Qed.

Lemma has_n_folds_eq {n ts1 ts2}:
  has_n_folds n ts1 ts2 <->
  ts1 = folds n ts2.
Proof.
  revert ts1 ts2.
  induction n; cbn; [easy|].
  split.
  - intros (ts1' & -> & eq).
    specialize (proj1 (IHn _ _) eq).
    intros; now f_equal.
  - intros ->.
    exists (folds n ts2).
    split; [reflexivity|].
    now eapply (proj2 (IHn _ _)).
Qed.

Lemma invert_folds_Value {n vs} :
  Value (folds n vs) -> Value vs.
Proof.
  induction n; eauto.
Qed.

Lemma LMC_pty_embed {τ} :
  LMC_pty (embed τ) = LMC τ.
Proof.
  induction τ; crush.
Qed.

Lemma pUnfoldOnce_embed {τ} :
  pUnfoldOnce (embed τ) = embed (unfoldOnce τ).
Proof.
  destruct τ; cbn; intuition.
  rewrite embed_sub.
  f_equal.
  extensionality i.
  destruct i; now cbn.
Qed.

Lemma pUnfoldn_embed {n τ} :
  pUnfoldn n (embed τ) = embed (unfoldn n τ).
Proof.
  revert τ.
  induction n; cbn; intuition.
  rewrite pUnfoldOnce_embed.
  now rewrite IHn.
Qed.

Lemma folds_T_inversion {n τ t Γ} :
  ⟪ Γ i⊢ folds n t : τ ⟫ ->
  ⟪ Γ i⊢ t : unfoldn n τ ⟫.
Proof.
  revert τ t Γ.
  induction n; cbn; [easy|].
  intros τ t Γ tyτ.
  inversion tyτ; subst.
  eapply IHn in H0; crushValidTy.
Qed.

Lemma unfolds_works {d w τ vs vu}:
  ValidTy τ ->
  valrel d w (embed τ) vs vu ->
  exists vs',
    Value vs' /\
    unfolds (LMC τ) vs -->* vs' /\
    valrel d w (embed (unfoldn (LMC τ) τ)) vs' vu.
Proof.
  intros vτ vr.
  rewrite valrel_fixp in vr.
  unfold valrel' in vr.
  destruct vr as (ot & vs' & hnf & vvs & vr).
  rewrite has_n_folds_eq in hnf.
  rewrite hnf in *.
  exists vs'.
  split.
  - eauto using invert_folds_Value.
  - rewrite LMC_pty_embed in *.
    split.
    + eapply unfolds_folds_evalStar.
      now rewrite folds_Value in vvs.
    + rewrite pUnfoldn_embed in vr.
      rewrite valrel_fixp.
      destruct ot as ((? & ?) & (? & ?)).
      split.
      split; split; crushOfType;
      eauto using folds_Value.
      now rewrite folds_Value in vvs.
      rewrite repEmul_embed_leftinv in *.
      eapply folds_T_inversion; crush.
      rewrite isToEq_embed_leftinv in *.
      eapply WtEq.
      eapply tyeq_symm.
      eapply E.ty_eq_unfoldn; crush.
      now destruct vτ as (? & ?).
      crushValidTy.
      eapply E.ValidTy_unfoldn; crushValidTy.
      crush.
      exists vs'.
      rewrite ?LMC_pty_embed.
      rewrite ?unfoldn_LMC; cbn.
      crush.
      now rewrite folds_Value in vvs.
      now destruct vτ as (? & ?).
Qed.

Lemma folds_works {d w τ vs vu}:
  ValidTy τ ->
  valrel d w (embed (unfoldn (LMC τ) τ)) vs vu ->
  valrel d w (embed τ) (folds (LMC τ) vs) vu.
Proof.
  intros vτ.
  rewrite ?valrel_fixp.
  unfold valrel'.
  rewrite ?LMC_pty_embed.
  rewrite ?pUnfoldn_embed.
  rewrite unfoldn_LMC.
  intros (ot & ts2 & hnf & vvs' & vr).
  cbn in vr.
  split.
  - destruct ot as ((? & ?) & ? & ?).
    split; split; crush.
    now eapply folds_Value.
    eapply folds_T; crush.
    now rewrite repEmul_embed_leftinv in *.
    rewrite isToEq_embed_leftinv in *.
    refine (WtEq _ _ _ _ H2).
    eapply ty_eq_unfoldn; crushValidTy.
    eapply ValidTy_unfoldn; crushValidTy.
    crushValidTy.
  - exists vs.
    rewrite has_n_folds_eq.
    split; [reflexivity|].
    split; [now eapply folds_Value|].
    destruct hnf.
    exact vr.
  - crushValidTy.
Qed.

Lemma inject_unit_works {n w d p vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tunit ->
  inject_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  eapply unfolds_works in vr; crushValidTy.
  destruct vr as (vs' & vvs' & vpreds & vr).
  eapply termrelnd₀_antired.
  - eapply evalStepStar.
    refine (eval_ctx₀ phole (eval_beta _) I); eauto.
    rewrite eq, ia_unfolds_eraseAnnot.
    cbn.
    I.crushStlcSyntaxMatchH.
    rewrite unfolds_sub.
    now eapply (evalstar_ctx' vpreds); I.inferContext.
  - eapply rt1n_refl.
  - cbn.
    eapply valrel_termrelnd₀.
    eapply valrel_pEmulDV_unfoldn; crushValidTy.
    rewrite eq in *.
    eapply valrel_ptunit_inversion in vr.
    apply valrel_inUnit; intuition.
Qed.

Lemma extract_unit_works {n w d p vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tunit ->
  extract_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  cbn -[UValIE] in tyvs, tyvu.

  eapply valrel_pEmulDV_unfoldn in vr; crushValidTy.
  rewrite eq in vr.

  destruct (invert_valrel_pEmulDV_unit vr) as [(? & ?) | (vs' & ? & ?)];
    unfold unkUVal in H;
    subst.

  - apply dwp_invert_imprecise in dwp; subst.
    intros vs vvs' es.
    exfalso.
    refine (divergence_closed_under_evalstar _ _ (ex_intro _ vs (conj vvs' es))).
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      rewrite folds_sub.

      eapply evalStepStar.
      rewrite folds_folds_ctx.
      eapply (eval_from_eval₀ (eval_case_inr (t := I.unit) I)); I.inferContext; eauto using folds_ectx.
      eapply rt1n_refl.
    + eapply divergence_closed_under_evalcontext; eauto using folds_ectx.
      exact (Om_div (τ := tunit)).
  - eapply termrelnd₀_antired.
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      rewrite folds_sub.
      unfold caseUnitA, caseUnit_pctxA, caseUVal_pctxA.
      eapply evalStepStar.
      * rewrite folds_folds_ctx.
        cbn in vvs.
        eapply (eval_from_eval₀ (eval_case_inl vvs)); I.inferContext;
         eauto using folds_ectx.
      * eapply rt1n_refl.
    + eapply rt1n_refl.
    + eapply valrel_termrelnd₀.
      cbn.
      rewrite <-folds_folds_ctx.
      eapply folds_works; crushValidTy.
      now rewrite eq.
Qed.

Lemma inject_bool_works {n w d p vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tbool ->
  inject_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  eapply unfolds_works in vr; crushValidTy.
  destruct vr as (vs' & vvs' & vpreds & vr).
  eapply termrelnd₀_antired.
  - eapply evalStepStar.
    refine (eval_ctx₀ phole (eval_beta _) I); eauto.
    rewrite eq, ia_unfolds_eraseAnnot.
    cbn.
    I.crushStlcSyntaxMatchH.
    rewrite unfolds_sub.
    now eapply (evalstar_ctx' vpreds); I.inferContext.
  - eapply rt1n_refl.
  - cbn.
    eapply valrel_termrelnd₀.
    eapply valrel_pEmulDV_unfoldn; crushValidTy.
    rewrite eq in *.
    eapply valrel_ptbool_inversion in vr.
    apply valrel_inBool; intuition.
Qed.

Lemma extract_bool_works {n w d p vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tbool ->
  extract_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  cbn -[UValIE] in tyvs, tyvu.

  eapply valrel_pEmulDV_unfoldn in vr; crushValidTy.
  rewrite eq in vr.

  destruct (invert_valrel_pEmulDV_bool vr) as [(? & ?) | (vs' & ? & ?)];
    unfold unkUVal in H;
    subst.

  - apply dwp_invert_imprecise in dwp; subst.
    intros vs vvs' es.
    exfalso.
    refine (divergence_closed_under_evalstar _ _ (ex_intro _ vs (conj vvs' es))).
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      rewrite folds_sub.

      eapply evalStepStar.
      rewrite folds_folds_ctx.
      eapply (eval_from_eval₀ (eval_case_inr (t := I.unit) I)); I.inferContext; eauto using folds_ectx.
      eapply rt1n_refl.
    + eapply divergence_closed_under_evalcontext; eauto using folds_ectx.
      exact (Om_div (τ := tbool)).
  - eapply termrelnd₀_antired.
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      rewrite folds_sub.
      unfold caseUnitA, caseUnit_pctxA, caseUVal_pctxA.
      eapply evalStepStar.
      * rewrite folds_folds_ctx.
        cbn in vvs.
        eapply (eval_from_eval₀ (eval_case_inl vvs)); I.inferContext;
         eauto using folds_ectx.
      * eapply rt1n_refl.
    + eapply rt1n_refl.
    + eapply valrel_termrelnd₀.
      cbn.
      rewrite <-folds_folds_ctx.
      eapply folds_works; crushValidTy.
      now rewrite eq.
Qed.

Lemma fizzbuzz {n p τ} : isToEq (pEmulDV n p τ) = isToEq (embed τ).
Proof.
  now rewrite isToEq_embed_leftinv.
Qed.

Lemma value_sub t (v: I.Value t) :
  ∀ (ζ: Sub I.Tm), Value t[ζ].
Proof.
  induction t; crush; cbn; apply IHt;
  assumption.
Qed.
Hint Resolve value_sub.

Lemma inject_tarr_works {n w d p vs vu τ1 τ2 τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tarr τ1 τ2 ->
  ValidTy τ1 -> ValidTy τ2 ->
  (forall w' vs1 vu1, inject_works_prop n w' d p vs1 vu1 τ2) →
  (forall w' vs1 vu1, extract_works_prop n w' d p vs1 vu1 τ1) →
  inject_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq vτ1 vτ2 IHinj IHext dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  destruct (unfolds_works vτ' vr) as (vs' & vvs' & vspreds & vr').
  eapply termrelnd₀_antired.
  - eapply evalToStar.
    unfold inject, injectA; cbn.
    eapply (I.eval_ctx₀ I.phole); simpl;
      eauto using I.eval_beta.
  - apply rt1n_refl.
  - rewrite eq.
    crushTyping.
    change (eraseAnnot _) with (inject n τ2) at 1.
    rewrite ia_unfolds_eraseAnnot.
    change (eraseAnnot _) with (extract n τ1) at 2.
    rewrite inject_sub, extract_sub, unfolds_sub; crushValidTy.
    cbn.
    assert (veτ1 : ValidPTy (embed τ1)) by eauto using ValidTy_implies_ValidPTy_embed.
    assert (veτ2 : ValidPTy (embed τ2)) by eauto using ValidTy_implies_ValidPTy_embed.

    rewrite eq in vr'.
    destruct (valrel_ptarr_inversion veτ1 veτ2 vr') as (tsb & tub & τ₁' & -> & -> & vτ₁' & tyeq & tytsb & tytub & trtsub).
    eapply valrel_termrelnd₀.

    eapply valrel_pEmulDV_unfoldn; crushValidTy.
    rewrite eq.
    eapply valrel_inArr.
    change (UValIE n τ1) with (repEmul (pEmulDV n p τ1)).
    rewrite isToEq_embed_leftinv in tyeq.
    refine (valrel_lambda _ _ _ _ _ _); cbn;
      eauto using ValidTy_implies_ValidPTy_embed, ValidTy_implies_ValidPTy_pEmulDV with tyvalid;
      crushOfType.
    now eapply tyeq_refl.
    cbn.
    erewrite <-?(fizzbuzz (n := n) (p := p)) in tytub; cbn in tytub.
    I.crushTyping;
    rewrite ?repEmul_embed_leftinv.
    eapply injectT; crushValidTy.
    erewrite <- eq.
    eapply unfolds_T; crush.
    now rewrite repEmul_embed_leftinv in tyvs.
    eapply extractT; crushValidTy.
    now eapply UValIE_valid.
    cbn.
    E.crushTyping.
    now rewrite ?isToEq_embed_leftinv in tytub.

    intros w' vs' vu' fw' szvu vr''.
    destruct (valrel_implies_Value vr'') as (vvs'' & vvu').
    cbn.
    crush.
    rewrite inject_sub, extract_sub; crushValidTy.

    rewrite unfolds_sub.
    rewrite <-ap_liftSub, liftSub_wkm, apply_wkm_beta1_cancel.
    assert (dir_world_prec n w' d p) as dwp' by apply (dwp_invert_S' dwp _ fw').
    destruct d.
    + (* eapply termrel_size_left. *)
      (* intros sz. *)
      (* cbn in sz. *)
      (* assert (szvs' : (size vs') <= w') by lia. *)
      assert (nsz : forall A, dir_lt = dir_gt -> A) by (intros _ [=]).
      pose proof (IHext _ _ _ dwp' (nsz _) vr'') as extr_tr.
      refine (termrel_antired_star_left _ _).
      eapply (evalstar_ctx' vspreds);
        I.inferContext; cbn; eauto using inject_value.
      cbn.
      (* clear sz szvs'. *)
      refine (termrelnd₀_ectx_sub (I.papp₂ (inject n τ2) (I.papp₂ _ I.phole)) _ extr_tr _);
        cbn; eauto using inject_value.
      intros vs2 vr2.
      destruct (valrel_implies_Value vr2) as (vvs2 & _).
      clear extr_tr IHext.
      cbn.
      refine (termrel_antired_star_left _ _).
      {eapply evalToStar.
       refine (eval_ctx₀ (I.papp₂ (inject n τ2) I.phole) (I.eval_beta _) _); cbn; eauto using inject_value.
      }
      rewrite valrel_fixp in vr'.
      destruct vr' as [_ vr'].
      destruct vr' as (tsb' & eq1 & _ & tsb2 & tub' & ? & ? & -> & eq2 & vr').
      inversion eq1; inversion eq2; subst.
      specialize (vr' w' fw' vs2 vu' (nsz _) vr2).
      cbn.
      eapply (termrel_ectx' vr'); I.inferContext; E.inferContext;
        cbn; eauto using inject_value.
      intros w3 fw3 vs3 vu3 vr3.
      eapply termrelnd₀_termrel.
      refine (IHinj w3 vs3 vu3 _ vr3); eauto using dwp_mono.
    + destruct (dwp_invert_gt dwp) as (-> & ineq).
      pose proof (IHext _ _ _ dwp' (fun _ => szvu eq_refl) vr'') as extr_tr.
      refine (termrel_antired_star_left _ _).
      eapply (evalstar_ctx' vspreds);
        I.inferContext; cbn; eauto using inject_value.
      cbn.
      refine (termrelnd₀_ectx_sub (I.papp₂ (inject n τ2) (I.papp₂ _ I.phole)) _ extr_tr _);
        cbn; eauto using inject_value.
      intros vs2 vr2.
      destruct (valrel_implies_Value vr2) as (vvs2 & _).
      clear extr_tr IHext.
      cbn.
      refine (termrel_antired_star_left _ _).
      eapply evalToStar.
      refine (eval_ctx₀ (I.papp₂ (inject n τ2) I.phole) (I.eval_beta _) _); cbn; eauto using inject_value.

      rewrite valrel_fixp in vr'.
      destruct vr' as [_ vr'].
      destruct vr' as (tsb' & eq1 & _ & tsb2 & tub' & ? & ? & -> & eq2 & vr').
      inversion eq1; inversion eq2; subst.
      specialize (vr' w' fw' vs2 vu' (fun _ => szvu eq_refl) vr2).
      eapply (termrel_ectx' vr'); I.inferContext; E.inferContext;
        cbn; eauto using inject_value.
      intros w3 fw3 vs3 vu3 vr3.
      eapply termrelnd₀_termrel.
      refine (IHinj w3 vs3 vu3 _ vr3); eauto using dwp_mono.
Qed.

Lemma inject_tprod_works {n w d p τ₁ τ₂ vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tprod τ₁ τ₂ ->
  ValidTy τ₁ -> ValidTy τ₂ ->
  (forall w' vs1 vu1, inject_works_prop n w' d p vs1 vu1 τ₁) →
  (forall w' vs1 vu1, inject_works_prop n w' d p vs1 vu1 τ₂) →
  inject_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq vτ₁ vτ₂ inj₁ inj₂ dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].
  destruct (unfolds_works vτ' vr) as (vs' & vvs' & vspreds & vr').
  rewrite eq in vr'.

  assert (veτ₁ : ValidPTy (embed τ₁)) by eauto using ValidTy_implies_ValidPTy_embed.
  assert (veτ₂ : ValidPTy (embed τ₂)) by eauto using ValidTy_implies_ValidPTy_embed.
  destruct (valrel_ptprod_inversion veτ₁ veτ₂ vr') as (vs1 & vs2 & vu1 & vu2 & -> & -> & ot1 & ot2 & vr2).
  destruct ot1 as [[vvs1 tvs1] tvu1].
  destruct ot2 as [[vvs2 tvs2] tvu2].
  eapply termrelnd₀_antired_left.
  { (* beta-reduce *)
    eapply evalStepStar.
    apply eval₀_to_eval.
    unfold inject, injectA; cbn.
    eapply eval_beta; now cbn.
    rewrite eq.
    cbn.
    crushTyping.
    change (eraseAnnot _) with (inject n τ₁) at 1.
    rewrite ia_unfolds_eraseAnnot.
    change (eraseAnnot _) with (inject n τ₂) at 2.
    rewrite ?inject_sub, unfolds_sub; crushValidTy.
    cbn.

    eapply evalStepTrans.
    eapply (evalstar_ctx' vspreds); I.inferContext; cbn; eauto using inject_value.
    cbn.

    eapply evalStepStar.
    eapply (I.eval_from_eval₀ (eval_proj₁ vvs1 vvs2)); I.inferContext; cbn; eauto using inject_value.
    eapply rt1n_refl.
  }
  cbn.

  destruct w.
  - destruct (inject_terminates n vτ₁ (conj vvs1 tvs1)) as (vs1' & vvs1' & es1).
    destruct (inject_terminates n vτ₂ (conj vvs2 tvs2)) as (vs2' & vvs2' & es2).
    eapply termrelnd₀_antired_left.
    { crushTyping.
      rewrite ?inject_sub; crushValidTy.
      eapply evalStepTrans.
      { eapply (evalstar_ctx' es1); I.inferContext; cbn; eauto using inject_value. }
      eapply evalStepTrans.
      { eapply (evalstar_ctx' vspreds); I.inferContext; cbn; eauto using inject_value. }
      eapply evalStepStar.
      { eapply (eval_from_eval₀ (eval_proj₂ vvs1 vvs2)); I.inferContext; cbn; eauto using inject_value. }
      eapply evalStepTrans.
      { eapply (evalstar_ctx' es2); I.inferContext; cbn; eauto using inject_value. }
      eapply rt1n_refl.
    }
    cbn.
    eapply valrel_termrelnd₀.
    destruct tvu1 as (vvu1 & tvu1).
    destruct tvu2 as (vvu2 & tvu2).
    rewrite isToEq_embed_leftinv in *.
    rewrite repEmul_embed_leftinv in *.

    eapply valrel_pEmulDV_unfoldn; crushValidTy.
    rewrite eq in *.

    eapply valrel_inProd''; crushValidTy.
    rewrite valrel_fixp; unfold valrel'; cbn.
    split.
    split; split; cbn; crushTyping; eauto.
    + eapply (I.preservation_star es1).
      crushTyping.
      crushTyping.

      eauto using injectT with typing uval_typing tyvalid.
    + eapply (I.preservation_star es2).
      crushTyping.
      eauto with typing uval_typing.
    + E.crushTyping.
    + eexists _; intuition.
      split; intros; exfalso; lia.
  -  assert (fw : w < S w) by lia.
     destruct (vr2 w fw) as (vr3 & vr4).
     fold embed in *.
     eapply dwp_invert_S in dwp.
     specialize (inj₁ w vs1 vu1 dwp vr3).
     specialize (inj₂ w vs2 vu2 dwp vr4).
     unfold inject, injectA; cbn.
     change (eraseAnnot _) with (inject n τ₁) at 1.
     change (eraseAnnot _) with (inject n τ₂).
     eapply (termrelnd₀_ectx' inj₁); I.inferContext; E.inferContext; [|now cbn].
     intros vs5 vu5 vr5.
     destruct (valrel_implies_Value vr5) as (vvs5 & vvu5).
     cbn.
     eapply termrelnd₀_antired_left.
     { (* beta-reduce *)
       eapply evalStepTrans.
       { eapply (evalstar_ctx' vspreds); I.inferContext; cbn; eauto using inject_value. }
       eapply evalStepStar.
       { eapply (eval_from_eval₀ (eval_proj₂ vvs1 vvs2)); I.inferContext; cbn; eauto using inject_value. }
       cbn.
       eapply rt1n_refl.
     }
     eapply (termrelnd₀_ectx' inj₂); I.inferContext; E.inferContext; cbn; eauto.
     intros vs6 vu6 vr6.
     eapply valrel_termrelnd₀.

    eapply valrel_pEmulDV_unfoldn; crushValidTy.
    rewrite eq in *.

     eapply valrel_inProd'', valrel_pair';
       try crushValidPTyMatch; crushValidTy.
Qed.

Lemma inject_tsum_works {n w d p τ₁ τ₂ vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tsum τ₁ τ₂ ->
  ValidTy τ₁ -> ValidTy τ₂ ->
  (forall w' vs1 vu1, inject_works_prop n w' d p vs1 vu1 τ₁) →
  (forall w' vs1 vu1, inject_works_prop n w' d p vs1 vu1 τ₂) →
  inject_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq vτ₁ vτ₂ inj₁ inj₂ dwp vr.
  destruct (valrel_implies_OfType vr) as [[vvs tvs] [vvu tvu]].

  destruct (unfolds_works vτ' vr) as (vs' & vvs' & vspreds & vr').
  rewrite eq in vr'.

  (* assert (w < S w) as fw by lia. *)
  (* assert (dir_world_prec n w d p) as dwp' by eauto using dwp_invert_S. *)

  cbn in vr'.
  assert (veτ₁ : ValidPTy (embed τ₁)) by eauto using ValidTy_implies_ValidPTy_embed.
  assert (veτ₂ : ValidPTy (embed τ₂)) by eauto using ValidTy_implies_ValidPTy_embed.

  destruct (valrel_ptsum_inversion veτ₁ veτ₂ vr') as (vs''' & vu' & [(? & ? & ot' & vrs)|(? & ? & ot' & vrs) ]);
    (* specialize (vrs w fw); *)
    subst; cbn in vvs.
  - eapply termrelnd₀_antired_left.
    { (* beta-reduce *)
      eapply evalStepStar.
      apply eval₀_to_eval.
      unfold inject, injectA; cbn.
      eauto with eval.
      rewrite eq.
      cbn.
      rewrite ia_unfolds_eraseAnnot.
      cbn.
      change (eraseAnnot _) with (inject n τ₁) at 1.
      change (eraseAnnot _) with (inject n τ₂).
      crushTyping.
      rewrite unfolds_sub.
      cbn.
      rewrite ?inject_sub; crushValidTy.
      eapply evalStepTrans.
      eapply (evalstar_ctx' vspreds); I.inferContext; cbn; try easy.
      eapply evalToStar.
      refine (eval_ctx₀ (I.pinl I.phole) _ I).
      crush.
    }
    cbn.
    repeat change (apTm ?ξ ?t) with t[ξ].
    rewrite ?inject_sub; crushValidTy.

    destruct w.
    + rewrite isToEq_embed_leftinv in *.
      assert (⟪ empty i⊢ I.inl vs''' : unfoldn (LMC τ') τ' ⟫) as tvs'.
      eapply (I.preservation_star vspreds); crush.
      { rewrite repEmul_embed_leftinv in *; eauto using unfolds_T. }
      rewrite eq in tvs'.
      inversion tvs'; subst.

      eapply (WtEq _ (U := unfoldn (LMC τ') τ')) in tvu; crushValidTy_with_UVal; eauto using ValidTy_unfoldn.
      2: { eapply tyeq_symm, ty_eq_unfoldn; crushValidTy. }
      rewrite eq in tvu.

      eapply E.invert_ty_inl in tvu; eauto with tyvalid.
      destruct tvu as (τ₁' & τ₂' & vτ₁₂ & vτ₂' & tyvu' & (tyeq₁ & tyeq₂)%tyeq_invert_tsum).

      cbn in vvs'.
      rewrite <-repEmul_embed_leftinv in H2.
      destruct (inject_terminates n vτ₁ (conj vvs' H2)) as (vs2 & vvs2 & es2).
      eapply termrelnd₀_antired_left.
      {eapply (evalstar_ctx' es2); I.inferContext; now cbn. }
      cbn.
      eapply valrel_termrelnd₀.

      eapply valrel_pEmulDV_unfoldn; crushValidTy.
      rewrite eq in *.

      eapply valrel_inSum''; crushValidTy.
      eapply valrel_inl''; try crushValidPTyMatch; crushValidTy.
      assert (tyvs2 : ⟪ empty i⊢ vs2 : repEmul (pEmulDV n p τ₁) ⟫).
      * eapply (I.preservation_star es2); eauto using ValidEnv_nil.
        I.crushTyping.
        cbn.
        rewrite repEmul_embed_leftinv.
        eapply injectT; crushValidTy.
      * repeat split; try assumption.
        cbn.
        refine (WtEq _ tyeq₁ _ _ tyvu'); try E.try_typed_terms_are_valid; eauto with tyvalid.
    + assert (fw : w < S w) by lia.
      specialize (vrs w fw).
      eapply dwp_invert_S in dwp.
      specialize (inj₁ w vs''' vu' dwp vrs).
      change (inl (inl ?t)) with (pctx_app t (pinl (pinl phole))).
      change (E.inl ?t) with (E.pctx_app t (E.pinl E.phole)).
      eapply termrelnd₀_ectx; cbn; eauto.
      intros vs2 vu2 vr2.
      cbn.
      eapply valrel_termrelnd₀.

      eapply valrel_pEmulDV_unfoldn; crushValidTy.
      rewrite eq in *.

      eapply valrel_inSum''; eauto using valrel_inSum'', valrel_inl'.
      eapply valrel_inl'; cbn; eauto using valrel_inSum'', valrel_inl', ValidTy_implies_ValidPTy_pEmulDV.
  - eapply termrelnd₀_antired_left.
    { (* beta-reduce *)
      eapply evalStepStar.
      apply eval₀_to_eval.
      unfold inject, injectA; cbn.
      eauto with eval.
      rewrite eq.
      cbn.
      rewrite ia_unfolds_eraseAnnot.
      cbn.
      change (eraseAnnot _) with (inject n τ₁) at 1.
      change (eraseAnnot _) with (inject n τ₂).
      crushTyping.
      rewrite unfolds_sub.
      cbn.
      rewrite ?inject_sub; crushValidTy.
      eapply evalStepTrans.
      eapply (evalstar_ctx' vspreds); I.inferContext; cbn; try easy.
      eapply evalToStar.
      refine (eval_ctx₀ (I.pinl I.phole) _ I).
      crush.
    }
    cbn.
    repeat change (apTm ?ξ ?t) with t[ξ].
    rewrite ?inject_sub; crushValidTy.

    destruct w.
    + rewrite isToEq_embed_leftinv in *.
      assert (⟪ empty i⊢ I.inr vs''' : unfoldn (LMC τ') τ' ⟫) as tvs'.
      eapply (I.preservation_star vspreds); crush.
      { rewrite repEmul_embed_leftinv in *; eauto using unfolds_T. }
      rewrite eq in tvs'.
      inversion tvs'; subst.

      eapply (WtEq _ (U := unfoldn (LMC τ') τ')) in tvu; crushValidTy_with_UVal; eauto using ValidTy_unfoldn.
      2: { eapply tyeq_symm, ty_eq_unfoldn; crushValidTy. }
      rewrite eq in tvu.

      eapply E.invert_ty_inr in tvu; eauto with tyvalid.
      destruct tvu as (τ₁' & τ₂' & vτ₁₂ & vτ₂' & tyvu' & (tyeq₁ & tyeq₂)%tyeq_invert_tsum).

      cbn in vvs'.
      rewrite <-repEmul_embed_leftinv in H2.
      destruct (inject_terminates n vτ₂ (conj vvs' H2)) as (vs2 & vvs2 & es2).
      eapply termrelnd₀_antired_left.
      {eapply (evalstar_ctx' es2); I.inferContext; now cbn. }
      cbn.
      eapply valrel_termrelnd₀.

      eapply valrel_pEmulDV_unfoldn; crushValidTy.
      rewrite eq in *.

      eapply valrel_inSum''; crushValidTy.
      eapply valrel_inr''; try crushValidPTyMatch; crushValidTy.
      assert (tyvs2 : ⟪ empty i⊢ vs2 : repEmul (pEmulDV n p τ₂) ⟫).
      * eapply (I.preservation_star es2); eauto using ValidEnv_nil.
        I.crushTyping.
        cbn.
        rewrite repEmul_embed_leftinv.
        eapply injectT; crushValidTy.
      * repeat split; try assumption.
        cbn.
        refine (WtEq _ tyeq₂ _ _ tyvu'); try E.try_typed_terms_are_valid; eauto with tyvalid.
    + assert (fw : w < S w) by lia.
      specialize (vrs w fw).
      eapply dwp_invert_S in dwp.
      specialize (inj₂ w vs''' vu' dwp vrs).
      change (inl (inr ?t)) with (pctx_app t (pinl (pinr phole))).
      change (E.inr ?t) with (E.pctx_app t (E.pinr E.phole)).
      eapply termrelnd₀_ectx; cbn; eauto.
      intros vs2 vu2 vr2.
      cbn.
      eapply valrel_termrelnd₀.

      eapply valrel_pEmulDV_unfoldn; crushValidTy.
      rewrite eq in *.

      eapply valrel_inSum''; eauto using valrel_inSum'', valrel_inl'.
      eapply valrel_inr'; cbn; eauto using valrel_inSum'', valrel_inl', ValidTy_implies_ValidPTy_pEmulDV.
Qed.


Lemma extract_tarr_works {n w d p τ₁ τ₂ vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tarr τ₁ τ₂ ->
  ValidTy τ₁ -> ValidTy τ₂ ->
  (forall w' vs' vu', w' < w → inject_works_prop n w' d p vs' vu' τ₁) →
  (forall w' vs' vu', w' < w → extract_works_prop n w' d p vs' vu' τ₂) →
  extract_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq vτ₁ vτ₂ inj₁ extr₂ dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  cbn -[UValIE] in tyvs, tyvu.

  eapply valrel_pEmulDV_unfoldn in vr; crushValidTy.
  rewrite eq in vr.

  destruct (invert_valrel_pEmulDV_for_caseUValArr vτ₁ vτ₂ vr) as [(vs2 & -> & es2 & vr2) | (-> & div)].

  - eapply termrelnd₀_antired.
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      rewrite folds_sub.
      cbn.
      change (eraseAnnot _) with (extract n τ₂) at 1.
      change (eraseAnnot _) with (inject n τ₁) at 2.
      change (eraseAnnot _) with (caseArr n (I.var 1) τ₁ τ₂) at 1.
      crushTyping.
      rewrite extract_sub, inject_sub, caseArr_sub; crushValidTy.
      cbn.
      eapply rt1n_refl.
    + eapply rt1n_refl.
    + eapply valrel_termrelnd₀.
      eapply folds_works; crushValidTy.
      rewrite eq.
      unshelve eapply valrel_ptarr_inversion in vr2; try crushValidPTyMatch; crushValidTy.
      destruct vr2 as (tsb & tub & τ'' & -> & [=] & vτ'' & tyeq & ttsb & ttub & trb); subst.
      cbn.
      rewrite <-(repEmul_embed_leftinv τ₁) at 2.
      refine (valrel_lambda _ _ _ _ _ _);
        crushOfType;
        repeat crushValidPTyMatch; I.crushTyping; E.crushTyping;
        rewrite ?isToEq_embed_leftinv, ?repEmul_embed_leftinv;
        try match goal with
          | [ |- ⟪ _ i⊢ inject _ _ : _ ⟫ ] => eapply injectT
          | [ |- ⟪ _ i⊢ extract _ _ : _ ⟫ ] => eapply extractT
          | [ |- ⟪ _ i⊢ caseArr _ _ _ _ : _ ⟫ ] => eapply caseArr_T
          end; try assumption.
      I.crushTyping; eauto using UValIE_valid.
      destruct (valrel_implies_Value H1) as (vvs & vvu).
      rewrite extract_sub, inject_sub, caseArr_sub; crushValidTy.
      cbn; crushTyping.
      rewrite <-ap_liftSub, <-up_liftSub, liftSub_wkm, apply_wkm_beta1_up_cancel.
      eapply termrel_antired_star.
      { eapply (evalstar_ctx' es2); I.inferContext; cbn; eauto using extract_value. }
      { eapply rt1n_refl. }
      cbn.

      pose proof (dwp3 := dwp_invert_S' dwp w' H).
      specialize (inj₁ w' vs vu H dwp3 H1).

      refine (termrelnd₀_ectx_sub (I.papp₂ _ (I.papp₂ _ I.phole)) _ inj₁ _);
        cbn; eauto using extract_value.

      intros vs2 vr2.
      destruct (valrel_implies_Value vr2) as (vvs2 & _).
      eapply termrel_antired_star_left.
      { eapply evalStepStar.
        eapply (eval_from_eval₀ (eval_beta vvs2)); I.inferContext; cbn; eauto using extract_value.
        eapply rt1n_refl.
      }
      cbn.

      specialize (trb w' vs2 vu H H0 vr2).
      eapply (termrel_ectx' trb); I.inferContext; E.inferContext; cbn; eauto using extract_value.

      intros w2 fw2 vs3 vu3 vr3.
      eapply termrel_size_right'.
      intros ineq.
      eapply termrelnd₀_termrel.
      eapply extr₂; crush.
      eauto using dwp_mono.
      specialize (ineq eq_refl).
      lia.
  - apply dwp_invert_imprecise in dwp; subst.
    eapply termrelnd₀_antired_left.
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      rewrite folds_sub.
      cbn.
      change (eraseAnnot _) with (extract n τ₂) at 1.
      change (eraseAnnot _) with (inject n τ₁) at 2.
      change (eraseAnnot _) with (caseArr n (I.var 1) τ₁ τ₂) at 1.
      crushTyping.
      rewrite inject_sub, extract_sub, caseArr_sub; crushValidTy.
      cbn.
      eapply rt1n_refl.
    + eapply valrel_termrelnd₀.
      eapply folds_works; crushValidTy.
      rewrite eq; cbn.

      eapply (WtEq _ (U := unfoldn (LMC τ') τ')) in tyvu;
        eauto using ty_eq_unfoldn, ValidTy_unfoldn.
      2: eapply tyeq_symm, ty_eq_unfoldn; crushValidTy.

      rewrite eq in tyvu.
      E.stlcCanForm; crushValidTy; eauto using tyeq_refl.
      destruct H as (τu2 & tyeq2 & vτu2 & -> & tyx).

      rewrite <-(repEmul_embed_leftinv τ₁) at 2.
      refine (valrel_lambda _ _ _ _ _ _);
        crushOfType;
        I.crushTyping;
        E.crushTyping;
        rewrite ?isToEq_embed_leftinv, ?repEmul_embed_leftinv in *;
        try match goal with
          | [ |- ⟪ _ i⊢ inject _ _ : _ ⟫ ] => eapply injectT
          | [ |- ⟪ _ i⊢ extract _ _ : _ ⟫ ] => eapply extractT
          | [ |- ⟪ _ i⊢ caseArr _ _ _ _ : _ ⟫ ] => eapply caseArr_T
          end;
        eauto using ValidTy_implies_ValidPTy_embed with tyeq tyvalid.
      rewrite eq in tyvs.
      refine (typing_ren tyvs (empty r▻ _) wkm (I.wtRen_wkm _ _)).
      eapply termrel_div_lt.
      rewrite extract_sub, inject_sub, caseArr_sub; crushValidTy.
      rewrite <-ap_liftSub, liftSub_wkm, apply_wkm_beta1_cancel.
      eapply (divergence_closed_under_evalcontext' div); I.inferContext; cbn; eauto using extract_value.
Qed.

Lemma fold_eval_inv {t1 t2} :
  fold_ t1 --> t2 -> exists t2', t2 = fold_ t2' /\ t1 --> t2'.
Proof.
  intros e.
  remember (fold_ t1) as t1o.
  destruct e as [C t1' t2' eval₀ eC].
  destruct C; inversion Heqt1o.
  - cbn in Heqt1o; subst.
    inversion eval₀.
  - exists (pctx_app t2' C).
    split; eauto with eval.
Qed.

Lemma folds_eval_inv {t1 t2 n} :
  folds n t1 --> t2 -> exists t2', t2 = folds n t2' /\ t1 --> t2'.
Proof.
  revert t2.
  induction n.
  - intros t2 e.
    exists t2; eauto.
  - cbn.
    intros t2 e.
    destruct (fold_eval_inv e) as (t2' & -> & e').
    destruct (IHn _ e') as (t2'' & -> & e'').
    exists t2''; eauto.
Qed.

Lemma folds_evalStar_inv {t1 t2 n} :
  folds n t1 -->* t2 -> exists t2', t2 = folds n t2' /\ t1 -->* t2'.
Proof.
  intros es.
  remember (folds n t1) as t1'.
  revert t1 Heqt1'.
  induction es.
  - intros t1 ->.
    exists t1; eauto with eval.
  - intros t1 ->.
    destruct (folds_eval_inv H) as (t3' & -> & es').
    destruct (IHes t3' eq_refl) as (t2' & -> & es'').
    exists t2'; eauto with eval.
Qed.

Lemma folds_evalStar_inv_value {t1 t2 n} :
  folds n t1 -->* t2 -> Value t1 -> t2 = folds n t1.
Proof.
  intros es vt1.
  destruct (folds_evalStar_inv es) as (t2' & -> & es').
  f_equal.
  symmetry.
  now eapply value_evalStar.
Qed.

Lemma fold_evalStar {t1 t2} :
  fold_ t1 --> t2 -> exists t2', t2 = fold_ t2' /\ t1 --> t2'.
Proof.
  intros e.
  remember (fold_ t1) as t1o.
  destruct e as [C t1' t2' eval₀ eC].
  destruct C; inversion Heqt1o.
  - cbn in Heqt1o; subst.
    inversion eval₀.
  - exists (pctx_app t2' C).
    split; eauto with eval.
Qed.


Lemma extract_tprod_works {n w d p τ₁ τ₂ vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tprod τ₁ τ₂ ->
  ValidTy τ₁ -> ValidTy τ₂ ->
  (forall w' vs1 vu1, extract_works_prop n w' d p vs1 vu1 τ₁) →
  (forall w' vs1 vu1, extract_works_prop n w' d p vs1 vu1 τ₂) →
  extract_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq vτ₁ vτ₂ extr₁ extr₂ dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  cbn -[UValIE] in tyvs, tyvu.

  eapply valrel_pEmulDV_unfoldn in vr; crushValidTy.
  rewrite eq in vr.

  eapply invert_valrel_pEmulDV_for_caseUValProd in vr; crushValidTy.
  destruct vr as [(vs1 & -> & es1 & vr1)|(-> & div)].

  - eapply termrelnd₀_antired.
    { eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      cbn.
      change (eraseAnnot _) with (extract n τ₁) at 1.
      change (eraseAnnot _) with (extract n τ₂) at 1.
      rewrite folds_sub.
      cbn. crushTyping.
      rewrite ?extract_sub; crushValidTy.
      eapply evalStepStar.
      { rewrite folds_folds_ctx.
        cbn in vvs.
        eapply (eval_from_eval₀ (eval_case_inl vvs)); I.inferContext.
        eapply ectx_cat; crush; eauto using folds_ectx, extract_value.
      }
      { eapply rt1n_refl. }
    }
    { eapply rt1n_refl. }
    rewrite ?pctx_cat_app.
    cbn.
    eapply valrel_ptprod_inversion  in vr1; try crushValidPTyMatch; crushValidTy.
    destruct vr1 as (vs11 & vs12 & vu11 & vu12 & -> & -> & ot11 & ot12 & vr1').
    destruct (OfType_implies_Value ot11) as (vvs11 & _).
    destruct (OfType_implies_Value ot12) as (vvs12 & _).

    eapply termrelnd₀_antired_left.
    { eapply evalToStar.
      eapply (I.eval_from_eval₀ (I.eval_proj₁ vvs11 vvs12)); I.inferContext; cbn; eauto using extract_value.
      repeat eapply ectx_cat; cbn; eauto using extract_value, folds_ectx.
    }
    rewrite ?pctx_cat_app, <-folds_folds_ctx.
    cbn.

    destruct d.
    + clear sz.
      intros vs2 vvs2 es2.

      rewrite folds_folds_ctx in es2.
      destruct (evalStar_ectx_inv (folds_ctx (LMC τ')) _ folds_ectx _ es2 vvs2) as (vs3 & vvs3 & es3 & es3').
      rewrite <-folds_folds_ctx in es3'.
      eapply folds_evalStar_inv_value in es3'; eauto; subst.

      destruct (evalStar_ectx_inv (I.ppair₁ I.phole _) _ I _ es3 (proj1 folds_Value vvs2)) as (vs11' & vvs11' & es11' & es4).
      cbn in es4.
      destruct (evalStar_ectx_inv (I.ppair₂ vs11' I.phole) _ (conj vvs11' I) _ es4 vvs3) as (vs12' & vvs12' & es12' & es5).
      cbn in es5.
      assert (vs3 = pair vs11' vs12') as ->.
      { remember (pair vs11' vs12').
        destruct es5; try reflexivity.
        subst.
        destruct (values_are_normal (t := pair vs11' vs12') (conj vvs11' vvs12') _ H).
      }
      clear es2 es3 es4 es5.
      assert (app (extract n τ₂)
            (proj₂ (caseof (inl (I.pair vs11 vs12)) (var 0) (Om (UValIE n τ₁ r× UValIE n τ₂)))) -->*
            app (extract n τ₂) vs12) as es12''.
      { eapply evalStepStar.
        eapply (eval_from_eval₀ (eval_case_inl (t := I.pair vs11 vs12) vvs)); I.inferContext; cbn; eauto using extract_value.
        eapply evalStepStar.
        eapply (eval_from_eval₀ (eval_proj₂ vvs11 vvs12)); I.inferContext; cbn; eauto using extract_value.
        eapply rt1n_refl.
      }
      pose proof (es13 := determinacyStar es12'' es12' (values_are_normal vvs12')).
      clear es12' es12''.

      exists (E.pair vu11 vu12).
      split; [|split]; eauto with eval.

      eapply folds_works; crushValidTy.
      rewrite eq.

      eapply valrel_pair''; fold embed; try crushValidPTyMatch; crushValidTy.
      destruct vvu.
      split; split; rewrite ?repEmul_embed_leftinv, ?isToEq_embed_leftinv; crushOfType.
      { eapply (I.preservation_star es11'); eauto using ValidEnv_nil.
        I.crushTyping; eauto using extractT; crushValidTy.
      }
      { intuition. }
      split; split; rewrite ?repEmul_embed_leftinv, ?isToEq_embed_leftinv; crushOfType.
      { eapply (I.preservation_star es13); eauto using ValidEnv_nil.
        I.crushTyping; eauto using extractT; crushValidTy.
      }
      { intuition. }
      { intuition. }
      { intros w' fw.
        destruct (vr1' w' fw) as (vr11 & vr12).
        pose proof (dwp_invert_S' dwp w' fw) as dwp2.
        assert (forall A, dir_lt = dir_gt -> A) as nsz2 by (intros A eq3; inversion eq3).
        destruct (extr₁ w' vs11 vu11 dwp2 (nsz2 _) vr11 _ vvs11' es11') as (vu1' & vvu1' & es11'' & vr11').
        destruct vvu as (vvu11 & vvu12).
        pose proof (E.value_evalStar vvu11 es11''); now subst.
      }
      { intros w' fw.
        destruct (vr1' w' fw) as (vr11 & vr12).
        pose proof (dwp_invert_S' dwp w' fw) as dwp2.
        assert (forall A, dir_lt = dir_gt -> A) as nsz2 by (intros A eq3; inversion eq3).
        destruct (extr₂ w' vs12 vu12 dwp2 (nsz2 _) vr12 _ vvs12' es13) as (vu2' & vvu2' & es12'' & vr12').
        destruct vvu as (vvu11 & vvu12).
        pose proof (E.value_evalStar vvu12 es12''); now subst.
      }
    + specialize (sz eq_refl).
      cbn in sz.
      assert (nlen : n <= n) by lia.
      destruct w; [exfalso; lia|].
      eapply dwp_invert_S in dwp.
      assert (sz1 : E.size vu11 <= w) by lia.
      assert (sz2 : E.size vu12 <= w) by lia.
      assert (fw : w < S w) by lia.
      destruct (vr1' w fw) as (vr11 & vr12).
      specialize (extr₁ w _ _ dwp (fun _ => sz1) vr11).
      specialize (extr₂ w _ _ dwp (fun _ => sz2) vr12).
      rewrite folds_folds_ctx.
      eapply (termrelnd₀_ectx' extr₁); I.inferContext; E.inferContext; try now cbn.
      2: { eapply ectx_cat; cbn; eauto using folds_ectx. }
      intros vs21 vu21 vr21.
      destruct (valrel_implies_Value vr21) as [vvs21 vvu21].
      refine (termrelnd₀_antired_left (d := dir_gt)_ _).
      { cbn.
        rewrite pctx_cat_app.
        eapply evalStepStar.
        eapply (eval_from_eval₀ (eval_case_inl (conj vvs11 vvs12 : Value (I.pair vs11 vs12)))); I.inferContext; cbn; eauto using extract_value.
        eapply ectx_cat; crush; eauto using extract_value, folds_ectx.
        rewrite pctx_cat_app.
        cbn.
        eapply evalToStar.
        eapply (eval_from_eval₀ (eval_proj₂ vvs11 vvs12)); I.inferContext; cbn; eauto using extract_value.
        repeat eapply ectx_cat; cbn; eauto using extract_value, folds_ectx.
      }
      rewrite ?pctx_cat_app.
      cbn -[termrelnd₀].

      eapply (termrelnd₀_ectx' extr₂); I.inferContext; E.inferContext; eauto.
      2: { eapply ectx_cat; cbn; eauto using folds_ectx. }
      2: { now cbn. }

      intros vs31 vu31 vr31.
      eapply (valrel_termrelnd₀ (d := dir_gt)).
      rewrite pctx_cat_app.
      cbn.
      rewrite <-folds_folds_ctx.
      eapply folds_works; crushValidTy.
      rewrite eq.
      eapply valrel_pair';
      eauto using ValidTy_implies_ValidPTy_embed.
  - apply dwp_invert_imprecise in dwp; subst.
    unfold caseProd, caseProd_pctx, caseUVal_pctx in div.
    cbn in div.
    intros vs' vvs' es.
    exfalso.
    refine (I.divergence_closed_under_evalstar _ _ (ex_intro _ vs' (conj vvs' es))).
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      cbn.
      change (eraseAnnot _) with (extract n τ₁) at 1.
      change (eraseAnnot _) with (extract n τ₂) at 1.
      rewrite folds_sub.
      cbn.
      crushTyping.
      repeat change (apTy ?ξ ?τ) with τ[ξ].
      rewrite ?extract_sub; crushValidTy.
      eapply rt1n_refl.
    + rewrite folds_folds_ctx.
      change (pair ?t1 ?t2) with (pctx_app t1 (ppair₁ phole t2)).
      change (app ?t1 ?t2) with (pctx_app t2 (papp₂ t1 phole)).
      change (proj₁ ?t) with (pctx_app t (pproj₁ phole)).
      rewrite <-?pctx_cat_app.
      eapply (divergence_closed_under_evalcontext _ div).
      repeat eapply ectx_cat; cbn; eauto using extract_value, folds_ectx.
Qed.

Lemma extract_tsum_works {n w d p τ₁ τ₂ vs vu τ'} :
  ValidTy τ' ->
  unfoldn (LMC τ') τ' = I.tsum τ₁ τ₂ ->
  ValidTy τ₁ -> ValidTy τ₂ ->
  (forall w' vs1 vu1, extract_works_prop n w' d p vs1 vu1 τ₁) →
  (forall w' vs2 vu2, extract_works_prop n w' d p vs2 vu2 τ₂) →
  extract_works_prop (S n) w d p vs vu τ'.
Proof.
  intros vτ' eq vτ₁ vτ₂ extr₁ extr₂ dwp sz vr.
  destruct (valrel_implies_OfType vr) as [[vvs tyvs] [vvu tyvu]].
  cbn -[UValIE] in tyvs, tyvu.

  eapply valrel_pEmulDV_unfoldn in vr; crushValidTy.
  rewrite eq in vr.

  eapply invert_valrel_pEmulDV_for_caseUValSum in vr; crushValidTy.
  destruct vr as [(vs1 & -> & es1 & vr1)|(-> & div)].

  - eapply termrelnd₀_antired.
    { eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      cbn.
      change (eraseAnnot _) with (extract n τ₁) at 2.
      change (eraseAnnot _) with (extract n τ₂) at 2.
      rewrite eraseAnnot_caseSumA.
      rewrite folds_sub.
      cbn. crushTyping.
      rewrite ?extract_sub; crushValidTy.
      rewrite caseSum_sub; cbn.
      rewrite folds_folds_ctx.
      eapply (evalstar_ctx' es1); I.inferContext; cbn.
      eapply ectx_cat; crush; eauto using folds_ectx.
    }
    { eapply rt1n_refl. }
    rewrite ?pctx_cat_app.
    cbn.
    eapply valrel_ptsum_inversion  in vr1; try crushValidPTyMatch; crushValidTy.
    destruct vr1 as (vs11 & vu11 & [(-> & -> & ot11 & vr11)|(-> & -> & ot11 & vr11)]).
    + destruct (OfType_implies_Value ot11) as (vvs11 & _).

      eapply termrelnd₀_antired_left.
      { eapply evalToStar.
        eapply (I.eval_from_eval₀ (I.eval_case_inl vvs11)); I.inferContext; cbn; eauto using extract_value.
        repeat eapply ectx_cat; cbn; eauto using extract_value, folds_ectx.
      }
      rewrite ?pctx_cat_app, <-folds_folds_ctx.
      cbn.
      crushTyping.
      rewrite extract_sub; crushValidTy.

      destruct d.
      * clear sz.
        intros vs2 vvs2 es2.

        rewrite folds_folds_ctx in es2.
        destruct (evalStar_ectx_inv (folds_ctx (LMC τ')) _ folds_ectx _ es2 vvs2) as (vs3 & vvs3 & es3 & es3').
        rewrite <-folds_folds_ctx in es3'.
        eapply folds_evalStar_inv_value in es3'; eauto; subst.

        destruct (evalStar_ectx_inv (I.pinl I.phole) _ I _ es3 vvs3) as (vs11' & vvs11' & es11' & es4).
        cbn in es4.
        assert (vs3 = inl vs11') as ->.
        { remember (inl vs11').
          destruct es4; try reflexivity.
          subst.
          destruct (values_are_normal (t := inl vs11') vvs11' _ H).
        }
        clear es2 es3 es4.
        exists (E.inl vu11).
        split; [|split]; eauto with eval.

        eapply folds_works; crushValidTy.
        rewrite eq.

        eapply valrel_inl''; fold embed; try crushValidPTyMatch; crushValidTy.
        split; split; rewrite ?repEmul_embed_leftinv, ?isToEq_embed_leftinv; crushOfType.
        { eapply (I.preservation_star es11'); eauto using ValidEnv_nil.
          I.crushTyping; eauto using extractT; crushValidTy.
        }
        { intuition. }
        { intros w' fw.
          specialize (vr11 w' fw).
          pose proof (dwp_invert_S' dwp w' fw) as dwp2.
          assert (forall A, dir_lt = dir_gt -> A) as nsz2 by (intros A eq3; inversion eq3).
          destruct (extr₁ w' vs11 vu11 dwp2 (nsz2 _) vr11 _ vvs11' es11') as (vu1' & vvu1' & es11'' & vr11').
          pose proof (E.value_evalStar vvu es11''); now subst.
        }
      * specialize (sz eq_refl).
        cbn in sz.
        assert (nlen : n <= n) by lia.
        destruct w; [exfalso; lia|].
        eapply dwp_invert_S in dwp.
        assert (sz1 : E.size vu11 <= w) by lia.
        assert (fw : w < S w) by lia.
        specialize (vr11 w fw).
        specialize (extr₁ w _ _ dwp (fun _ => sz1) vr11).
        rewrite folds_folds_ctx.
        eapply (termrelnd₀_ectx' extr₁); I.inferContext; E.inferContext; try now cbn.
        2: { eapply ectx_cat; cbn; eauto using folds_ectx. }
        intros vs21 vu21 vr21.
        eapply (valrel_termrelnd₀ (d := dir_gt)).
        rewrite pctx_cat_app; cbn.
        rewrite <-folds_folds_ctx.
        eapply folds_works; crushValidTy.
        rewrite eq.
        destruct (valrel_implies_Value vr21).
        eapply valrel_inl'; fold embed; try crushValidPTyMatch; crushValidTy.
    + destruct (OfType_implies_Value ot11) as (vvs11 & _).

      eapply termrelnd₀_antired_left.
      { eapply evalToStar.
        eapply (I.eval_from_eval₀ (I.eval_case_inr vvs11)); I.inferContext; cbn; eauto using extract_value.
        repeat eapply ectx_cat; cbn; eauto using extract_value, folds_ectx.
      }
      rewrite ?pctx_cat_app, <-folds_folds_ctx.
      cbn.
      crushTyping.
      rewrite extract_sub; crushValidTy.

      destruct d.
      * clear sz.
        intros vs2 vvs2 es2.

        rewrite folds_folds_ctx in es2.
        destruct (evalStar_ectx_inv (folds_ctx (LMC τ')) _ folds_ectx _ es2 vvs2) as (vs3 & vvs3 & es3 & es3').
        rewrite <-folds_folds_ctx in es3'.
        eapply folds_evalStar_inv_value in es3'; eauto; subst.

        destruct (evalStar_ectx_inv (I.pinr I.phole) _ I _ es3 vvs3) as (vs11' & vvs11' & es11' & es4).
        cbn in es4.
        assert (vs3 = inr vs11') as ->.
        { remember (inr vs11').
          destruct es4; try reflexivity.
          subst.
          destruct (values_are_normal (t := inr vs11') vvs11' _ H).
        }
        clear es2 es3 es4.
        exists (E.inr vu11).
        split; [|split]; eauto with eval.

        eapply folds_works; crushValidTy.
        rewrite eq.

        eapply valrel_inr''; fold embed; try crushValidPTyMatch; crushValidTy.
        split; split; rewrite ?repEmul_embed_leftinv, ?isToEq_embed_leftinv; crushOfType.
        { eapply (I.preservation_star es11'); eauto using ValidEnv_nil.
          I.crushTyping; eauto using extractT; crushValidTy.
        }
        { intuition. }
        { intros w' fw.
          specialize (vr11 w' fw).
          pose proof (dwp_invert_S' dwp w' fw) as dwp2.
          assert (forall A, dir_lt = dir_gt -> A) as nsz2 by (intros A eq3; inversion eq3).
          destruct (extr₂ w' vs11 vu11 dwp2 (nsz2 _) vr11 _ vvs11' es11') as (vu1' & vvu1' & es11'' & vr11').
          pose proof (E.value_evalStar vvu es11''); now subst.
        }
      * specialize (sz eq_refl).
        cbn in sz.
        assert (nlen : n <= n) by lia.
        destruct w; [exfalso; lia|].
        eapply dwp_invert_S in dwp.
        assert (sz1 : E.size vu11 <= w) by lia.
        assert (fw : w < S w) by lia.
        specialize (vr11 w fw).
        specialize (extr₂ w _ _ dwp (fun _ => sz1) vr11).
        rewrite folds_folds_ctx.
        eapply (termrelnd₀_ectx' extr₂); I.inferContext; E.inferContext; try now cbn.
        2: { eapply ectx_cat; cbn; eauto using folds_ectx. }
        intros vs21 vu21 vr21.
        eapply (valrel_termrelnd₀ (d := dir_gt)).
        rewrite pctx_cat_app; cbn.
        rewrite <-folds_folds_ctx.
        eapply folds_works; crushValidTy.
        rewrite eq.
        destruct (valrel_implies_Value vr21).
        eapply valrel_inr'; fold embed; try crushValidPTyMatch; crushValidTy.
  - apply dwp_invert_imprecise in dwp; subst.
    unfold caseProd, caseProd_pctx, caseUVal_pctx in div.
    cbn in div.
    intros vs' vvs' es.
    exfalso.
    refine (I.divergence_closed_under_evalstar _ _ (ex_intro _ vs' (conj vvs' es))).
    + eapply evalStepStar.
      refine (eval_ctx₀ phole (eval_beta _) I); eauto.
      rewrite eq.
      rewrite ia_folds_eraseAnnot.
      cbn.
      change (eraseAnnot _) with (extract n τ₁) at 2.
      change (eraseAnnot _) with (extract n τ₂) at 2.
      rewrite eraseAnnot_caseSumA.
      cbn.
      rewrite folds_sub.
      cbn.
      crushTyping.
      repeat change (apTy ?ξ ?τ) with τ[ξ].
      rewrite ?extract_sub; crushValidTy.
      eapply rt1n_refl.
    + rewrite folds_folds_ctx.
      rewrite caseSum_sub.
      cbn.
      change (caseof ?t1 ?t2 ?t3) with (pctx_app t1 (pcaseof₁ phole t2 t3)).
      change (app ?t1 ?t2) with (pctx_app t2 (papp₂ t1 phole)).
      rewrite <-?pctx_cat_app.
      eapply (divergence_closed_under_evalcontext _ div).
      repeat eapply ectx_cat; cbn; eauto using extract_value, folds_ectx.
Qed.

Lemma inject_works {n w d p τ vs vu} :
  ValidTy τ ->
  inject_works_prop n w d p vs vu τ
with extract_works {n w d p τ vs vu} :
  ValidTy τ ->
  extract_works_prop n w d p vs vu τ.
Proof.
  - intros vτ.
    revert n w vs vu.
    destruct n.
    + unfold inject_works_prop, inject, injectA.
      intros w vs vu dwp vr.
      refine (inject_zero_works dwp vr).
    + assert (ValidTy (unfoldn (LMC τ) τ)) as vτ' by eauto using ValidTy_unfoldn.
      remember (unfoldn (LMC τ) τ) as τ'.
      destruct τ';
      intros w vs vu dwp vr.
      * (* τ₁' ⇒ τ₂' *)
        eapply (inject_tarr_works vτ (eq_sym Heqτ')); intuition.
      * (* tunit *)
        eapply (inject_unit_works vτ (eq_sym Heqτ')); now assumption.
      * (* tbool *)
        eapply (inject_bool_works vτ (eq_sym Heqτ')); now assumption.
      * (* τ₁ r× τ₂ *)
        eapply (inject_tprod_works vτ (eq_sym Heqτ')); intuition.
      * (* τ₁ ⊎ τ₂ *)
        eapply (inject_tsum_works vτ (eq_sym Heqτ')); intuition.
      * assert (LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
        rewrite <-Heqτ' in H; cbn in H; exfalso; lia.
      * destruct vτ' as (cτ' & _).
        exfalso.
        eauto using I.closed_implies_not_var.
  - (* extract *)
    intros vτ.
    revert n w vs vu.
    destruct n.
    + unfold extract_works_prop, extract, extractA.
      intros w vs vu dwp vr.
      refine (extract_zero_works dwp vr).
    + assert (ValidTy (unfoldn (LMC τ) τ)) as vτ' by eauto using ValidTy_unfoldn.
      remember (unfoldn (LMC τ) τ) as τ'.
      destruct τ';
      intros w vs vu dwp vr.
      * (* τ₁' ⇒ τ₂' *)
        eapply (extract_tarr_works vτ (eq_sym Heqτ')); intuition.
      * (* tunit *)
        eapply (extract_unit_works vτ (eq_sym Heqτ')); now assumption.
      * (* tbool *)
        eapply (extract_bool_works vτ (eq_sym Heqτ')); now assumption.
      * (* τ₁ r× τ₂ *)
        eapply (extract_tprod_works vτ (eq_sym Heqτ')); intuition.
      * (* τ₁ ⊎ τ₂ *)
        eapply (extract_tsum_works vτ (eq_sym Heqτ')); intuition.
      * assert (LMC (unfoldn (LMC τ) τ) = 0) by (eapply unfoldn_LMC; crushValidTy).
        rewrite <-Heqτ' in H; cbn in H; exfalso; lia.
      * destruct vτ' as (cτ' & _).
        exfalso.
        eauto using I.closed_implies_not_var.
Qed.

Lemma inject_works_open {d n m τ ts tu Γ p} :
  ValidTy τ ->
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : embed τ ⟫ →
  ⟪ Γ ⊩ I.app (inject n τ) ts ⟦ d , m ⟧ tu : pEmulDV n p τ ⟫.
Proof.
  intros vτ dwp lr.
  destruct lr as (? & ? & lr).
  unfold OpenLRCtxN; split; [|split].
  - crushTyping.
    rewrite repEmul_embed_leftinv.
    eauto using injectT.
  - cbn.
    rewrite isToEq_embed_leftinv in H0.
    assumption.
  - intros w wm γs γu envrel.
    specialize (lr w wm γs γu envrel).

    cbn; crushTyping.
    rewrite inject_sub.

    eapply (termrel_ectx' lr); I.inferContext; E.inferContext;
      crush; eauto using inject_value.

    cbn.
    eapply termrel_size_right'.
    intros sz.
    eapply termrelnd₀_termrel.
    eapply inject_works; eauto using dwp_mono.
    crushValidTy.
Qed.
