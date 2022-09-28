Require Import UValFI.UVal.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.LemmasTyping.
Require Import StlcFix.SpecSyntax.
(* Require Import StlcFix.Fix. *)
Require Import StlcFix.StlcOmega.
Require Import StlcFix.Inst.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcIso.SpecTyping.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRelFI.LRFI.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import LogRelFI.LemmasInversion.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.PseudoTypeFI.
Require Export BacktransFI.UpgradeDowngrade.
Require Import Lia.


Section Intro.
  Definition inDwn_pctx (τ : I.Ty) (n : nat) := papp₂ (downgrade n 1 τ) (pinl phole).
  Definition inDwn_pctxA (τ : I.Ty) τ' (n : nat) := a_papp₂ (UValFI (S n) τ) (UValFI n τ) (downgradeA n 1 τ) (a_pinl τ' tunit a_phole).

  Definition inUnitDwn_pctx (n : nat) := inDwn_pctx I.tunit n.
  Definition inUnitDwn_pctxA (n : nat) := inDwn_pctxA I.tunit F.tunit n.
  Definition inUnitDwn (n : nat) (t : Tm) := pctx_app t (inUnitDwn_pctx n).
  Definition inUnitDwnA (n : nat) (t : TmA) := pctxA_app t (inUnitDwn_pctxA n).
  Definition inBoolDwn_pctx (n : nat) := inDwn_pctx I.tbool n.
  Definition inBoolDwn_pctxA (n : nat) := inDwn_pctxA I.tbool F.tbool n.
  Definition inBoolDwn (n : nat) (t : Tm) := pctx_app t (inBoolDwn_pctx n).
  Definition inBoolDwnA (n : nat) (t : TmA) := pctxA_app t (inBoolDwn_pctxA n).
  Definition inArrDwn_pctx (τ1 τ2 : I.Ty) (n : nat) := inDwn_pctx (I.tarr τ1 τ2) n.
  Definition inArrDwn_pctxA (τ1 τ2 : I.Ty) (n : nat) := inDwn_pctxA (I.tarr τ1 τ2) (F.tarr (UValFI n τ1) (UValFI n τ2)) n.
  Definition inArrDwn (τ1 τ2 : I.Ty) (n : nat) (t : Tm) := pctx_app t (inArrDwn_pctx τ1 τ2 n).
  Definition inArrDwnA (τ1 τ2 : I.Ty) (n : nat) (t : TmA) := pctxA_app t (inArrDwn_pctxA τ1 τ2 n).
  Definition inSumDwn_pctx (τ1 τ2 : I.Ty) (n : nat) := inDwn_pctx (I.tsum τ1 τ2) n.
  Definition inSumDwn_pctxA (τ1 τ2 : I.Ty) (n : nat) := inDwn_pctxA (I.tsum τ1 τ2) (F.tsum (UValFI n τ1) (UValFI n τ2)) n.
  Definition inSumDwn (τ1 τ2 : I.Ty) (n : nat) (t : Tm) := pctx_app t (inSumDwn_pctx τ1 τ2 n).
  Definition inSumDwnA (τ1 τ2 : I.Ty) (n : nat) (t : TmA) := pctxA_app t (inSumDwn_pctxA τ1 τ2 n).
  Definition inProdDwn_pctx (τ1 τ2 : I.Ty) (n : nat) := inDwn_pctx (I.tprod τ1 τ2) n.
  Definition inProdDwn_pctxA (τ1 τ2 : I.Ty) (n : nat) := inDwn_pctxA (I.tprod τ1 τ2) (F.tprod (UValFI n τ1) (UValFI n τ2)) n.
  Definition inProdDwn (τ1 τ2 : I.Ty) (n : nat) (t : Tm) := pctx_app t (inProdDwn_pctx τ1 τ2 n).
  Definition inProdDwnA (τ1 τ2 : I.Ty) (n : nat) (t : TmA) := pctxA_app t (inProdDwn_pctxA τ1 τ2 n).
  Definition inRecDwn_pctx (τ : I.Ty) (n : nat) := inDwn_pctx (I.trec τ) n.
  Definition inRecDwn_pctxA (τ : I.Ty) (n : nat) := inDwn_pctxA (I.trec τ) (UValFI n (τ[beta1 (trec τ)])) n.
  Definition inRecDwn (τ : I.Ty) (n : nat) (t : Tm) := pctx_app t (inRecDwn_pctx τ n).
  Definition inRecDwnA (τ : I.Ty) (n : nat) (t : TmA) := pctxA_app t (inRecDwn_pctxA τ n).
End Intro.

Arguments inUnitDwn n t : simpl never.
Arguments inBoolDwn n t : simpl never.
Arguments inSumDwn τ1 τ2 n t : simpl never.
Arguments inProdDwn τ1 τ2 n t : simpl never.
Arguments inArrDwn τ1 τ2 n t : simpl never.
Arguments inRecDwn τ n t : simpl never.
Arguments inUnitDwn_pctx n : simpl never.
Arguments inSumDwn_pctx τ1 τ2 n : simpl never.
Arguments inArrDwn_pctx τ1 τ2 n : simpl never.
Arguments inRecDwn_pctx τ n : simpl never.

Arguments inUnitDwnA n t : simpl never.
Arguments inBoolDwnA n t : simpl never.
Arguments inSumDwnA τ1 τ2 n t : simpl never.
Arguments inProdDwnA τ1 τ2 n t : simpl never.
Arguments inArrDwnA τ1 τ2 n t : simpl never.
Arguments inRecDwnA τ n t : simpl never.
Arguments inUnitDwn_pctxA n : simpl never.
Arguments inBoolDwn_pctxA n : simpl never.
Arguments inSumDwn_pctxA τ1 τ2 n : simpl never.
Arguments inProdDwn_pctxA τ1 τ2 n : simpl never.
Arguments inArrDwn_pctxA τ1 τ2 n : simpl never.
Arguments inRecDwn_pctxA τ n : simpl never.

Section IntroTypes.
  Lemma inUnitDwn_pctx_T {n Γ} : ⟪ ⊢ inUnitDwn_pctx n : Γ , tunit → Γ , UValFI n I.tunit ⟫.
  Proof.
    unfold inUnitDwn_pctx, inDwn_pctx.
    eauto using upgrade_T1, downgrade_T1, F.PCtxTyping with typing uval_typing.
  Qed.

  Lemma inUnitDwn_T {n t Γ} : ⟪ Γ ⊢ t : tunit ⟫ → ⟪ Γ ⊢ inUnitDwn n t : UValFI n I.tunit ⟫.
  Proof.
    unfold inUnitDwn.
    eauto using inUnitDwn_pctx_T with typing.
  Qed.

  Lemma inBoolDwn_pctx_T {n Γ} : ⟪ ⊢ inBoolDwn_pctx n : Γ , tbool → Γ , UValFI n I.tbool ⟫.
  Proof.
    unfold inBoolDwn_pctx, inDwn_pctx.
    eauto using upgrade_T1, downgrade_T1, F.PCtxTyping with typing uval_typing.
  Qed.

  Lemma inBoolDwn_T {n t Γ} : ⟪ Γ ⊢ t : tbool ⟫ → ⟪ Γ ⊢ inBoolDwn n t : UValFI n I.tbool ⟫.
  Proof.
    unfold inBoolDwn.
    eauto using inBoolDwn_pctx_T with typing.
  Qed.

  Lemma inSumDwn_pctx_T {n Γ τ1 τ2} : ⟪ ⊢ inSumDwn_pctx τ1 τ2 n : Γ , UValFI n τ1 ⊎ UValFI n τ2 → Γ , UValFI n (I.tsum τ1 τ2) ⟫.
  Proof.
    unfold inSumDwn_pctx, inDwn_pctx.
    eauto using upgrade_T1, downgrade_T1, F.PCtxTyping with typing uval_typing.
  Qed.

  Lemma inSumDwn_pctx_ectx {n τ1 τ2} : ECtx (inSumDwn_pctx τ1 τ2 n).
  Proof.
    unfold inSumDwn_pctx; simpl; eauto using downgrade_value.
  Qed.

  Lemma inSumDwn_T {n t Γ τ1 τ2} : ⟪ Γ ⊢ t : UValFI n τ1 ⊎ UValFI n τ2 ⟫ → ⟪ Γ ⊢ inSumDwn τ1 τ2 n t : UValFI n (I.tsum τ1 τ2) ⟫.
  Proof.
    unfold inSumDwn.
    eauto using inSumDwn_pctx_T with typing.
  Qed.

  Lemma inProdDwn_pctx_T {n Γ τ1 τ2} : ⟪ ⊢ inProdDwn_pctx τ1 τ2 n : Γ , UValFI n τ1 × UValFI n τ2 → Γ , UValFI n (I.tprod τ1 τ2) ⟫.
  Proof.
    unfold inProdDwn_pctx, inDwn_pctx.
    eauto using upgrade_T1, downgrade_T1, F.PCtxTyping with typing uval_typing.
  Qed.

  Lemma inProdDwn_pctx_ectx {n τ1 τ2} : ECtx (inProdDwn_pctx τ1 τ2 n).
  Proof.
    unfold inProdDwn_pctx; simpl; eauto using downgrade_value.
  Qed.

  Lemma inProdDwn_T {n t Γ τ1 τ2} : ⟪ Γ ⊢ t : UValFI n τ1 × UValFI n τ2 ⟫ → ⟪ Γ ⊢ inProdDwn τ1 τ2 n t : UValFI n (I.tprod τ1 τ2) ⟫.
  Proof.
    unfold inProdDwn.
    eauto using inProdDwn_pctx_T with typing.
  Qed.

  Lemma inArrDwn_pctx_T {n Γ τ1 τ2} : ⟪ ⊢ inArrDwn_pctx τ1 τ2 n : Γ , (UValFI n τ1 ⇒ UValFI n τ2) → Γ , UValFI n (I.tarr τ1 τ2) ⟫.
  Proof.
    unfold inArrDwn_pctx, inDwn_pctx.
    eauto using upgrade_T1, downgrade_T1, F.PCtxTyping with typing uval_typing.
  Qed.

  Lemma inArrDwn_T {n t Γ τ1 τ2} : ⟪ Γ ⊢ t : UValFI n τ1 ⇒ UValFI n τ2 ⟫ → ⟪ Γ ⊢ inArrDwn τ1 τ2 n t : UValFI n (I.tarr τ1 τ2) ⟫.
  Proof.
    unfold inArrDwn.
    eauto using inArrDwn_pctx_T with typing.
  Qed.

  Lemma inRecDwn_pctx_T {n Γ τ} : ⟪ ⊢ inRecDwn_pctx τ n : Γ , (UValFI n τ[beta1 (I.trec τ)]) → Γ , UValFI n (I.trec τ) ⟫.
  Proof.
    unfold inRecDwn_pctx, inDwn_pctx.
    eauto using upgrade_T1, downgrade_T1, F.PCtxTyping with typing uval_typing.
  Qed.

  Lemma inRecDwn_pctx_ectx {n τ} : ECtx (inRecDwn_pctx τ n).
  Proof.
    unfold inRecDwn_pctx; simpl; eauto using downgrade_value.
  Qed.

  Lemma inRecDwn_T {n t Γ τ} : ⟪ Γ ⊢ t : UValFI n τ[beta1 (I.trec τ)] ⟫ → ⟪ Γ ⊢ inRecDwn τ n t : UValFI n (I.trec τ) ⟫.
  Proof.
    unfold inRecDwn.
    eauto using inRecDwn_pctx_T with typing.
  Qed.

  Lemma inUnitDwn_pctxA_T {n Γ} : ⟪ a⊢ inUnitDwn_pctxA n : Γ , tunit → Γ , UValFI n I.tunit ⟫.
  Proof.
    unfold inUnitDwn_pctxA, inDwn_pctxA.
    eauto using upgrade_annot_T1, downgrade_annot_T1, F.PCtxTypingAnnot, F.AnnotTyping with typing uval_typing.
  Qed.

  Lemma inUnitDwnA_T {n t Γ} : ⟪ Γ a⊢ t : tunit ⟫ → ⟪ Γ a⊢ inUnitDwnA n t : UValFI n I.tunit ⟫.
  Proof.
    unfold inUnitDwnA.
    eauto using inUnitDwn_pctxA_T with typing.
  Qed.

  Lemma inBoolDwn_pctxA_T {n Γ} : ⟪ a⊢ inBoolDwn_pctxA n : Γ , tbool → Γ , UValFI n I.tbool ⟫.
  Proof.
    unfold inBoolDwn_pctxA, inDwn_pctxA.
    eauto using upgrade_annot_T1, downgrade_annot_T1, F.PCtxTypingAnnot, F.AnnotTyping with typing uval_typing.
  Qed.

  Lemma inBoolDwnA_T {n t Γ} : ⟪ Γ a⊢ t : tbool ⟫ → ⟪ Γ a⊢ inBoolDwnA n t : UValFI n I.tbool ⟫.
  Proof.
    unfold inBoolDwnA.
    eauto using inBoolDwn_pctxA_T with typing.
  Qed.

  Lemma inSumDwn_pctxA_T {n Γ τ1 τ2} : ⟪ a⊢ inSumDwn_pctxA τ1 τ2 n : Γ , UValFI n τ1 ⊎ UValFI n τ2 → Γ , UValFI n (I.tsum τ1 τ2) ⟫.
  Proof.
    unfold inSumDwn_pctxA, inDwn_pctxA.
    eauto using upgrade_annot_T1, downgrade_annot_T1, F.PCtxTypingAnnot with typing uval_typing.
  Qed.

  Lemma inProdDwn_pctxA_T {n Γ τ1 τ2} : ⟪ a⊢ inProdDwn_pctxA τ1 τ2 n : Γ , UValFI n τ1 × UValFI n τ2 → Γ , UValFI n (I.tprod τ1 τ2) ⟫.
  Proof.
    unfold inProdDwn_pctxA, inDwn_pctxA.
    eauto using upgrade_annot_T1, downgrade_annot_T1, F.PCtxTypingAnnot with typing uval_typing.
  Qed.

  (* Lemma inSumDwn_pctxA_ectx {n τ1 τ2} : ECtx (inSumDwn_pctxA τ1 τ2 n). *)
  (* Proof. *)
  (*   unfold inSumDwn_pctxA; simpl; eauto using downgrade_value. *)
  (* Qed. *)

  Lemma inSumDwnA_T {n t Γ τ1 τ2} : ⟪ Γ a⊢ t : UValFI n τ1 ⊎ UValFI n τ2 ⟫ → ⟪ Γ a⊢ inSumDwnA τ1 τ2 n t : UValFI n (I.tsum τ1 τ2) ⟫.
  Proof.
    unfold inSumDwnA.
    eauto using inSumDwn_pctxA_T with typing.
  Qed.

  Lemma inProdDwnA_T {n t Γ τ1 τ2} : ⟪ Γ a⊢ t : UValFI n τ1 × UValFI n τ2 ⟫ → ⟪ Γ a⊢ inProdDwnA τ1 τ2 n t : UValFI n (I.tprod τ1 τ2) ⟫.
  Proof.
    unfold inProdDwnA.
    eauto using inProdDwn_pctxA_T with typing.
  Qed.

  Lemma inArrDwn_pctxA_T {n Γ τ1 τ2} : ⟪ a⊢ inArrDwn_pctxA τ1 τ2 n : Γ , (UValFI n τ1 ⇒ UValFI n τ2) → Γ , UValFI n (I.tarr τ1 τ2) ⟫.
  Proof.
    unfold inArrDwn_pctxA, inDwn_pctxA.
    eauto using upgrade_annot_T1, downgrade_annot_T1, F.PCtxTypingAnnot with typing uval_typing.
  Qed.

  Lemma inArrDwnA_T {n t Γ τ1 τ2} : ⟪ Γ a⊢ t : UValFI n τ1 ⇒ UValFI n τ2 ⟫ → ⟪ Γ a⊢ inArrDwnA τ1 τ2 n t : UValFI n (I.tarr τ1 τ2) ⟫.
  Proof.
    unfold inArrDwnA.
    eauto using inArrDwn_pctxA_T with typing.
  Qed.

  Lemma inRecDwn_pctxA_T {n Γ τ} : ⟪ a⊢ inRecDwn_pctxA τ n : Γ , (UValFI n τ[beta1 (I.trec τ)]) → Γ , UValFI n (I.trec τ) ⟫.
  Proof.
    unfold inRecDwn_pctxA, inDwn_pctxA.
    eauto using upgrade_annot_T1, downgrade_annot_T1, F.PCtxTypingAnnot with typing uval_typing.
  Qed.

  (* Lemma inRecDwn_pctxA_ectx {n τ} : ECtx (inRecDwn_pctxA τ n). *)
  (* Proof. *)
  (*   unfold inRecDwn_pctxA; simpl; eauto using downgrade_value. *)
  (* Qed. *)

  Lemma inRecDwnA_T {n t Γ τ} : ⟪ Γ a⊢ t : UValFI n τ[beta1 (I.trec τ)] ⟫ → ⟪ Γ a⊢ inRecDwnA τ n t : UValFI n (I.trec τ) ⟫.
  Proof.
    unfold inRecDwnA.
    eauto using inRecDwn_pctxA_T with typing.
  Qed.

  Lemma eraseAnnot_inUnitDwnA {n t} :
    eraseAnnot (inUnitDwnA n t) = inUnitDwn n (eraseAnnot t).
  Proof.
    unfold inUnitDwnA, inUnitDwn, inUnitDwn_pctxA, inUnitDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_inBoolDwnA {n t} :
    eraseAnnot (inBoolDwnA n t) = inBoolDwn n (eraseAnnot t).
  Proof.
    unfold inBoolDwnA, inBoolDwn, inBoolDwn_pctxA, inBoolDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_inProdDwnA {n t τ1 τ2} :
    eraseAnnot (inProdDwnA n τ1 τ2 t) = inProdDwn n τ1 τ2 (eraseAnnot t).
  Proof.
    unfold inProdDwnA, inProdDwn, inProdDwn_pctxA, inProdDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_inSumDwnA {n t τ1 τ2} :
    eraseAnnot (inSumDwnA n τ1 τ2 t) = inSumDwn n τ1 τ2 (eraseAnnot t).
  Proof.
    unfold inSumDwnA, inSumDwn, inSumDwn_pctxA, inSumDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_inArrDwnA {n t τ1 τ2} :
    eraseAnnot (inArrDwnA n τ1 τ2 t) = inArrDwn n τ1 τ2 (eraseAnnot t).
  Proof.
    unfold inArrDwnA, inArrDwn, inArrDwn_pctxA, inArrDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_inRecDwnA {n t τ} :
    eraseAnnot (inRecDwnA n τ t) = inRecDwn n τ (eraseAnnot t).
  Proof.
    unfold inRecDwnA, inRecDwn, inRecDwn_pctxA, inRecDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_pctx_inUnitDwn_pctxA {n} :
    eraseAnnot_pctx (inUnitDwn_pctxA n) = inUnitDwn_pctx n.
  Proof.
    unfold inUnitDwn_pctxA, inUnitDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_pctx_inBoolDwn_pctxA {n} :
    eraseAnnot_pctx (inBoolDwn_pctxA n) = inBoolDwn_pctx n.
  Proof.
    unfold inBoolDwn_pctxA, inBoolDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_pctx_inProdDwn_pctxA {n τ1 τ2} :
    eraseAnnot_pctx (inProdDwn_pctxA n τ1 τ2) = inProdDwn_pctx n τ1 τ2.
  Proof.
    unfold inProdDwn_pctxA, inProdDwn_pctx, inProdDwn_pctxA, inProdDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_pctx_inSumDwn_pctxA {n τ1 τ2} :
    eraseAnnot_pctx (inSumDwn_pctxA n τ1 τ2) = inSumDwn_pctx n τ1 τ2.
  Proof.
    unfold inSumDwn_pctxA, inSumDwn_pctx, inSumDwn_pctxA, inSumDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_pctx_inArrDwn_pctxA {n τ1 τ2} :
    eraseAnnot_pctx (inArrDwn_pctxA n τ1 τ2) = inArrDwn_pctx n τ1 τ2.
  Proof.
    unfold inArrDwn_pctxA, inArrDwn_pctx, inArrDwn_pctxA, inArrDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.

  Lemma eraseAnnot_pctx_inRecDwn_pctxA {n τ} :
    eraseAnnot_pctx (inRecDwn_pctxA n τ) = inRecDwn_pctx n τ.
  Proof.
    unfold inRecDwn_pctxA, inRecDwn_pctx, inRecDwn_pctxA, inRecDwn_pctx.
    cbn.
    now rewrite downgrade_downgradeA.
  Qed.
End IntroTypes.

Hint Resolve inUnitDwn_T : uval_typing.
Hint Resolve inBoolDwn_T : uval_typing.
Hint Resolve inSumDwn_T : uval_typing.
Hint Resolve inProdDwn_T : uval_typing.
Hint Resolve inArrDwn_T : uval_typing.
Hint Resolve inRecDwn_T : uval_typing.
Hint Resolve inUnitDwn_pctx_T : uval_typing.
Hint Resolve inBoolDwn_pctx_T : uval_typing.
Hint Resolve inSumDwn_pctx_T : uval_typing.
Hint Resolve inProdDwn_pctx_T : uval_typing.
Hint Resolve inArrDwn_pctx_T : uval_typing.
Hint Resolve inRecDwn_pctx_T : uval_typing.
Hint Resolve inUnitDwnA_T : uval_typing.
Hint Resolve inBoolDwnA_T : uval_typing.
Hint Resolve inSumDwnA_T : uval_typing.
Hint Resolve inProdDwnA_T : uval_typing.
Hint Resolve inArrDwnA_T : uval_typing.
Hint Resolve inRecDwnA_T : uval_typing.
Hint Resolve inUnitDwn_pctxA_T : uval_typing.
Hint Resolve inBoolDwn_pctxA_T : uval_typing.
Hint Resolve inSumDwn_pctxA_T : uval_typing.
Hint Resolve inProdDwn_pctxA_T : uval_typing.
Hint Resolve inArrDwn_pctxA_T : uval_typing.
Hint Resolve inRecDwn_pctxA_T : uval_typing.


Section IntroProps.
  Lemma inUnitDwn_sub {n ts γs} :
    (inUnitDwn n ts)[γs] = 
    (inUnitDwn n (ts[γs])).
  Proof.
    unfold inUnitDwn, inUnitDwn_pctx.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply downgrade_sub.
  Qed.

  Lemma inBoolDwn_sub {n ts γs} :
    (inBoolDwn n ts)[γs] = 
    (inBoolDwn n (ts[γs])).
  Proof.
    unfold inBoolDwn, inBoolDwn_pctx.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply downgrade_sub.
  Qed.

  Lemma inSumDwn_sub {n ts γs τ1 τ2} :
    (inSumDwn τ1 τ2 n ts)[γs] =
    (inSumDwn τ1 τ2 n (ts[γs])).
  Proof.
    unfold inSumDwn, inSumDwn_pctx.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply downgrade_sub.
  Qed.

  Lemma inProdDwn_sub {n ts γs τ1 τ2} :
    (inProdDwn τ1 τ2 n ts)[γs] =
    (inProdDwn τ1 τ2 n (ts[γs])).
  Proof.
    unfold inProdDwn, inProdDwn_pctx.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply downgrade_sub.
  Qed.

  Lemma inArrDwn_sub {n ts γs τ1 τ2} :
    (inArrDwn τ1 τ2 n ts)[γs] =
    (inArrDwn τ1 τ2 n (ts[γs])).
  Proof.
    unfold inArrDwn, inArrDwn_pctx.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply downgrade_sub.
  Qed.

  Lemma inRecDwn_sub {n ts γs τ} :
    (inRecDwn τ n ts)[γs] =
    (inRecDwn τ n (ts[γs])).
  Proof.
    unfold inRecDwn, inRecDwn_pctx.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply downgrade_sub.
  Qed.

  Lemma termrel₀_inUnitDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w ptunit vs vu →
    termrel₀ d w (pEmulDV n p I.tunit) (inUnitDwn n vs) vu.
  Proof.
   intros dwp vr.
   unfold inUnitDwn.
   apply downgrade_works''; trivial.
   replace (n + 1) with (S n) by lia.
   apply valrel_inUnit'; trivial.
  Qed.

  Lemma termrel₀_inBoolDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w ptbool vs vu →
    termrel₀ d w (pEmulDV n p I.tbool) (inBoolDwn n vs) vu.
  Proof.
   intros dwp vr.
   unfold inBoolDwn.
   apply downgrade_works''; trivial.
   replace (n + 1) with (S n) by lia.
   apply valrel_inBool'; trivial.
  Qed.

  Lemma termrel₀_inSumDwn {d w n p vs vu τ1 τ2} :
    dir_world_prec n w d p →
    valrel d w (ptsum (pEmulDV n p τ1) (pEmulDV n p τ2)) vs vu →
    termrel₀ d w (pEmulDV n p (I.tsum τ1 τ2)) (inSumDwn τ1 τ2 n vs) vu.
  Proof.
   intros dwp vr.
   unfold inSumDwn.
   apply downgrade_works''; trivial.
   replace (n + 1) with (S n) by lia.
   now apply valrel_inSum''.
  Qed.

  Lemma termrel₀_inProdDwn {d w n p vs vu τ1 τ2} :
    dir_world_prec n w d p →
    valrel d w (ptprod (pEmulDV n p τ1) (pEmulDV n p τ2)) vs vu →
    termrel₀ d w (pEmulDV n p (I.tprod τ1 τ2)) (inProdDwn τ1 τ2 n vs) vu.
  Proof.
   intros dwp vr.
   unfold inProdDwn.
   apply downgrade_works''; trivial.
   replace (n + 1) with (S n) by lia.
   now apply valrel_inProd''.
  Qed.

  Lemma termrel₀_inRecDwn {d w n p vs vu τ} :
    dir_world_prec n w d p →
    valrel d w (pEmulDV n p (τ [beta1 (I.trec τ)])) vs vu →
    termrel₀ d w (pEmulDV n p (I.trec τ)) (inRecDwn τ n vs) (I.fold_ vu).
  Proof.
   intros dwp vr.
   unfold inRecDwn.
   apply downgrade_works''; trivial.
   replace (n + 1) with (S n) by lia.
   now eapply valrel_inRec'.
  Qed.

  Lemma termrel₀_inArrDwn {d w n p vs vu τ1 τ2} :
    dir_world_prec n w d p →
    valrel d w (ptarr (pEmulDV n p τ1) (pEmulDV n p τ2)) vs vu →
    termrel₀ d w (pEmulDV n p (I.tarr τ1 τ2)) (inArrDwn τ1 τ2 n vs) vu.
  Proof.
   intros dwp vr.
   unfold inArrDwn.
   apply downgrade_works''; trivial.
   replace (n + 1) with (S n) by lia.
   apply valrel_inArr; trivial.
  Qed.
End IntroProps.

Section Destruct.
  Definition caseUnitUp_pctx (n : nat) := pctx_cat (papp₂ (upgrade n 1 I.tunit) phole) caseUnit_pctx.
  Definition caseUnitUp_pctxA (n : nat) := pctxA_cat (a_papp₂ (UValFI n I.tunit) (UValFI (S n) I.tunit) (upgradeA n 1 I.tunit) a_phole) (caseUnit_pctxA n).
  Definition caseBoolUp_pctx (n : nat) := pctx_cat (papp₂ (upgrade n 1 I.tbool) phole) caseBool_pctx.
  Definition caseBoolUp_pctxA (n : nat) := pctxA_cat (a_papp₂ (UValFI n I.tbool) (UValFI (S n) I.tbool) (upgradeA n 1 I.tbool) a_phole) (caseBool_pctxA n).
  Definition caseSumUp_pctx (n : nat) (τ1 τ2 : I.Ty) := pctx_cat (papp₂ (upgrade n 1 (I.tsum τ1 τ2)) phole) (caseSum_pctx n τ1 τ2).
  Definition caseSumUp_pctxA (n : nat) (τ1 τ2 : I.Ty) := pctxA_cat (a_papp₂ (UValFI n (I.tsum τ1 τ2)) (UValFI (S n) (I.tsum τ1 τ2)) (upgradeA n 1 (I.tsum τ1 τ2)) a_phole) (caseSum_pctxA n τ1 τ2).
  Definition caseProdUp_pctx (n : nat) (τ1 τ2 : I.Ty) := pctx_cat (papp₂ (upgrade n 1 (I.tprod τ1 τ2)) phole) (caseProd_pctx n τ1 τ2).
  Definition caseProdUp_pctxA (n : nat) (τ1 τ2 : I.Ty) := pctxA_cat (a_papp₂ (UValFI n (I.tprod τ1 τ2)) (UValFI (S n) (I.tprod τ1 τ2)) (upgradeA n 1 (I.tprod τ1 τ2)) a_phole) (caseProd_pctxA n τ1 τ2).
  Definition caseArrUp_pctx (n : nat) (τ1 τ2 : I.Ty) := pctx_cat (papp₂ (upgrade n 1 (I.tarr τ1 τ2)) phole) (caseArr_pctx n τ1 τ2).
  Definition caseArrUp_pctxA (n : nat) (τ1 τ2 : I.Ty) := pctxA_cat (a_papp₂ (UValFI n (I.tarr τ1 τ2)) (UValFI (S n) (I.tarr τ1 τ2)) (upgradeA n 1 (I.tarr τ1 τ2)) a_phole) (caseArr_pctxA n τ1 τ2).
  Definition caseRecUp_pctx (n : nat) (τ : I.Ty) := pctx_cat (papp₂ (upgrade n 1 (I.trec τ)) phole) (caseRec_pctx n τ).
  Definition caseRecUp_pctxA (n : nat) (τ : I.Ty) := pctxA_cat (a_papp₂ (UValFI n (I.trec τ)) (UValFI (S n) (I.trec τ)) (upgradeA n 1 (I.trec τ)) a_phole) (caseRec_pctxA n τ).

  Definition caseUnitUp (n : nat) (t : Tm) := pctx_app t (caseUnitUp_pctx n).
  Definition caseUnitUpA (n : nat) (t : TmA) := pctxA_app t (caseUnitUp_pctxA n).
  Definition caseBoolUp (n : nat) (t : Tm) := pctx_app t (caseBoolUp_pctx n).
  Definition caseBoolUpA (n : nat) (t : TmA) := pctxA_app t (caseBoolUp_pctxA n).
  Definition caseSumUp  (n : nat) (t : Tm) (τ1 τ2 : I.Ty) := pctx_app t (caseSumUp_pctx n τ1 τ2).
  Definition caseSumUpA  (n : nat) (t : TmA) (τ1 τ2 : I.Ty) := pctxA_app t (caseSumUp_pctxA n τ1 τ2).
  Definition caseProdUp  (n : nat) (t : Tm) (τ1 τ2 : I.Ty) := pctx_app t (caseProdUp_pctx n τ1 τ2).
  Definition caseProdUpA  (n : nat) (t : TmA) (τ1 τ2 : I.Ty) := pctxA_app t (caseProdUp_pctxA n τ1 τ2).
  Definition caseArrUp  (n : nat) (t : Tm) (τ1 τ2 : I.Ty) := pctx_app t (caseArrUp_pctx n τ1 τ2).
  Definition caseArrUpA  (n : nat) (t : TmA) (τ1 τ2 : I.Ty) := pctxA_app t (caseArrUp_pctxA n τ1 τ2).
  Definition caseRecUp (n : nat) (t : Tm) (τ : I.Ty) := pctx_app t (caseRecUp_pctx n τ).
  Definition caseRecUpA (n : nat) (t : TmA) (τ : I.Ty) := pctxA_app t (caseRecUp_pctxA n τ).
End Destruct.

Arguments caseArrUp n t τ1 τ2: simpl never.
Arguments caseUnitUp n t : simpl never.
Arguments caseBoolUp n t : simpl never.
Arguments caseSumUp n t τ1 τ2 : simpl never.
Arguments caseProdUp n t τ1 τ2 : simpl never.
Arguments caseRecUp n t τ : simpl never.

Arguments caseArrUp_pctx n τ1 τ2: simpl never.
Arguments caseUnitUp_pctx n : simpl never.
Arguments caseBoolUp_pctx n : simpl never.
Arguments caseProdUp_pctx n τ1 τ2 : simpl never.
Arguments caseSumUp_pctx n τ1 τ2 : simpl never.
Arguments caseRecUp_pctx n τ : simpl never.

Arguments caseArrUpA n t τ1 τ2: simpl never.
Arguments caseUnitUpA n t : simpl never.
Arguments caseBoolUpA n t : simpl never.
Arguments caseProdUpA n t τ1 τ2 : simpl never.
Arguments caseSumUpA n t τ1 τ2 : simpl never.
Arguments caseRecUpA n t τ : simpl never.

Arguments caseArrUp_pctxA n τ1 τ2: simpl never.
Arguments caseUnitUp_pctxA n : simpl never.
Arguments caseBoolUp_pctxA n : simpl never.
Arguments caseProdUp_pctxA n τ1 τ2 : simpl never.
Arguments caseSumUp_pctxA n τ1 τ2 : simpl never.
Arguments caseRecUp_pctxA n τ : simpl never.

Section DestructTypes.
  Lemma caseUnitUp_pctx_T {n Γ} : ⟪ ⊢ caseUnitUp_pctx n : Γ , UValFI n I.tunit → Γ , tunit ⟫.
  Proof.
    unfold caseUnitUp_pctx.
    eauto using caseUnit_pctx_T, upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseUnitUp_T {n t Γ} : ⟪ Γ ⊢ t : UValFI n I.tunit ⟫ → ⟪ Γ ⊢ caseUnitUp n t : tunit ⟫.
  Proof.
    unfold caseUnitUp.
    eauto using caseUnitUp_pctx_T with typing.
  Qed.

  Lemma caseUnitUp_pctx_ectx {n} : ECtx (caseUnitUp_pctx n).
  Proof.
    unfold caseUnitUp_pctx; simpl; eauto using upgrade_value.
  Qed.

  Lemma caseBoolUp_pctx_T {n Γ} : ⟪ ⊢ caseBoolUp_pctx n : Γ , UValFI n I.tbool → Γ , tbool ⟫.
  Proof.
    unfold caseBoolUp_pctx.
    eauto using caseBool_pctx_T, upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseBoolUp_T {n t Γ} : ⟪ Γ ⊢ t : UValFI n I.tbool ⟫ → ⟪ Γ ⊢ caseBoolUp n t : tbool ⟫.
  Proof.
    unfold caseBoolUp.
    eauto using caseBoolUp_pctx_T with typing.
  Qed.

  Lemma caseBoolUp_pctx_ectx {n} : ECtx (caseBoolUp_pctx n).
  Proof.
    unfold caseBoolUp_pctx; simpl; eauto using upgrade_value.
  Qed.

  Lemma caseSumUp_pctx_T {n Γ τ1 τ2} : ⟪ ⊢ caseSumUp_pctx n τ1 τ2 : Γ , UValFI n (I.tsum τ1 τ2) → Γ , UValFI n τ1 ⊎ UValFI n τ2 ⟫.
  Proof.
    unfold caseSumUp_pctx.
    eauto using caseSum_pctx_T, upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseSumUp_pctx_ectx {n τ1 τ2} : ECtx (caseSumUp_pctx n τ1 τ2).
  Proof.
    unfold caseSumUp_pctx; simpl; eauto using upgrade_value.
  Qed.

  Lemma caseSumUp_T {n t Γ τ1 τ2} : ⟪ Γ ⊢ t : UValFI n (I.tsum τ1 τ2) ⟫ → ⟪ Γ ⊢ caseSumUp n t τ1 τ2 : UValFI n τ1 ⊎ UValFI n τ2 ⟫.
  Proof.
    unfold caseSumUp.
    eauto using caseSumUp_pctx_T with typing.
  Qed.

  Lemma caseProdUp_pctx_T {n Γ τ1 τ2} : ⟪ ⊢ caseProdUp_pctx n τ1 τ2 : Γ , UValFI n (I.tprod τ1 τ2) → Γ , UValFI n τ1 × UValFI n τ2 ⟫.
  Proof.
    unfold caseProdUp_pctx.
    eauto using caseProd_pctx_T, upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseProdUp_pctx_ectx {n τ1 τ2} : ECtx (caseProdUp_pctx n τ1 τ2).
  Proof.
    unfold caseProdUp_pctx; simpl; eauto using upgrade_value.
  Qed.

  Lemma caseProdUp_T {n t Γ τ1 τ2} : ⟪ Γ ⊢ t : UValFI n (I.tprod τ1 τ2) ⟫ → ⟪ Γ ⊢ caseProdUp n t τ1 τ2 : UValFI n τ1 × UValFI n τ2 ⟫.
  Proof.
    unfold caseProdUp.
    eauto using caseProdUp_pctx_T with typing.
  Qed.

  Lemma caseArrUp_pctx_T {n Γ τ1 τ2} : ⟪ ⊢ caseArrUp_pctx n τ1 τ2 : Γ , UValFI n (I.tarr τ1 τ2) → Γ , F.tarr (UValFI n τ1) (UValFI n τ2) ⟫.
  Proof.
    unfold caseArrUp_pctx.
    eauto using caseArr_pctx_T, upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseArrUp_pctx_ectx {n τ1 τ2} : ECtx (caseArrUp_pctx n τ1 τ2).
  Proof.
    unfold caseArrUp_pctx; simpl; eauto using upgrade_value.
  Qed.

  Lemma caseArrUp_T {n t Γ τ1 τ2} : ⟪ Γ ⊢ t : UValFI n (I.tarr τ1 τ2) ⟫ → ⟪ Γ ⊢ caseArrUp n t τ1 τ2 : UValFI n τ1 ⇒ UValFI n τ2 ⟫.
  Proof.
    unfold caseArrUp.
    eauto using caseArrUp_pctx_T with typing.
  Qed.

  Lemma caseRecUp_pctx_T {n Γ τ} : ⟪ ⊢ caseRecUp_pctx n τ : Γ , UValFI n (I.trec τ) → Γ , UValFI n τ[beta1 (I.trec τ)] ⟫.
  Proof.
    unfold caseRecUp_pctx.
    eauto using caseRec_pctx_T, upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseRecUp_pctx_ectx {n τ} : ECtx (caseRecUp_pctx n τ).
  Proof.
    unfold caseRecUp_pctx; simpl; eauto using upgrade_value.
  Qed.

  Lemma caseRecUp_T {n t Γ τ} : ⟪ Γ ⊢ t : UValFI n (I.trec τ) ⟫ → ⟪ Γ ⊢ caseRecUp n t τ : UValFI n τ[beta1 (I.trec τ)] ⟫.
  Proof.
    unfold caseRecUp.
    eauto using caseRecUp_pctx_T with typing.
  Qed.

  Lemma caseUnitUp_pctxA_T {n Γ} : ⟪ a⊢ caseUnitUp_pctxA n : Γ , UValFI n I.tunit → Γ , tunit ⟫.
  Proof.
    unfold caseUnitUp_pctxA.
    crushTypingA;
      fold (UValFI (S n) I.tunit);
      eauto with typing uval_typing.
  Qed.

  Lemma caseUnitUpA_T {n t Γ} : ⟪ Γ a⊢ t : UValFI n I.tunit ⟫ → ⟪ Γ a⊢ caseUnitUpA n t : tunit ⟫.
  Proof.
    unfold caseUnitUpA.
    eauto using caseUnitUp_pctxA_T with typing.
  Qed.

  Lemma caseBoolUp_pctxA_T {n Γ} : ⟪ a⊢ caseBoolUp_pctxA n : Γ , UValFI n I.tbool → Γ , tbool ⟫.
  Proof.
    unfold caseBoolUp_pctxA.
    crushTypingA;
      fold (UValFI (S n) I.tbool);
      eauto with typing uval_typing.
  Qed.

  Lemma caseBoolUpA_T {n t Γ} : ⟪ Γ a⊢ t : UValFI n I.tbool ⟫ → ⟪ Γ a⊢ caseBoolUpA n t : tbool ⟫.
  Proof.
    unfold caseBoolUpA.
    eauto using caseBoolUp_pctxA_T with typing.
  Qed.

  Lemma caseProdUp_pctxA_T {n Γ τ1 τ2} : ⟪ a⊢ caseProdUp_pctxA n τ1 τ2 : Γ , UValFI n (I.tprod τ1 τ2) → Γ , UValFI n τ1 × UValFI n τ2 ⟫.
  Proof.
    unfold caseProdUp_pctxA.
    eauto with typing uval_typing.
  Qed.

  Lemma caseProdUpA_T {n t Γ τ1 τ2} : ⟪ Γ a⊢ t : UValFI n (I.tprod τ1 τ2) ⟫ → ⟪ Γ a⊢ caseProdUpA n t τ1 τ2 : UValFI n τ1 × UValFI n τ2 ⟫.
  Proof.
    unfold caseProdUpA.
    eauto using caseProdUp_pctxA_T with typing.
  Qed.

  Lemma caseSumUp_pctxA_T {n Γ τ1 τ2} : ⟪ a⊢ caseSumUp_pctxA n τ1 τ2 : Γ , UValFI n (I.tsum τ1 τ2) → Γ , UValFI n τ1 ⊎ UValFI n τ2 ⟫.
  Proof.
    unfold caseSumUp_pctxA.
    eauto with typing uval_typing.
  Qed.

  Lemma caseSumUpA_T {n t Γ τ1 τ2} : ⟪ Γ a⊢ t : UValFI n (I.tsum τ1 τ2) ⟫ → ⟪ Γ a⊢ caseSumUpA n t τ1 τ2 : UValFI n τ1 ⊎ UValFI n τ2 ⟫.
  Proof.
    unfold caseSumUpA.
    eauto using caseSumUp_pctxA_T with typing.
  Qed.

  Lemma caseArrUp_pctxA_T {n Γ τ1 τ2} : ⟪ a⊢ caseArrUp_pctxA n τ1 τ2 : Γ , UValFI n (I.tarr τ1 τ2) → Γ , F.tarr (UValFI n τ1) (UValFI n τ2) ⟫.
  Proof.
    unfold caseArrUp_pctxA.
    eauto with typing.
  Qed.

  Lemma caseArrUpA_T {n t Γ τ1 τ2} : ⟪ Γ a⊢ t : UValFI n (I.tarr τ1 τ2) ⟫ → ⟪ Γ a⊢ caseArrUpA n t τ1 τ2 : UValFI n τ1 ⇒ UValFI n τ2 ⟫.
  Proof.
    unfold caseArrUpA.
    eauto using caseArrUp_pctxA_T with typing.
  Qed.

  Lemma caseRecUp_pctxA_T {n Γ τ} : ⟪ a⊢ caseRecUp_pctxA n τ : Γ , UValFI n (I.trec τ) → Γ , UValFI n τ[beta1 (I.trec τ)] ⟫.
  Proof.
    unfold caseRecUp_pctxA.
    eauto with typing.
  Qed.

  Lemma caseRecUpA_T {n t Γ τ} : ⟪ Γ a⊢ t : UValFI n (I.trec τ) ⟫ → ⟪ Γ a⊢ caseRecUpA n t τ : UValFI n τ[beta1 (I.trec τ)] ⟫.
  Proof.
    unfold caseRecUpA.
    eauto using caseRecUp_pctxA_T with typing.
  Qed.

  Lemma eraseAnnot_caseUnitUpA {n t} :
    eraseAnnot (caseUnitUpA n t) = caseUnitUp n (eraseAnnot t).
  Proof.
    unfold caseUnitUpA, caseUnitUp, caseUnitUp_pctx, caseUnitUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_caseBoolUpA {n t} :
    eraseAnnot (caseBoolUpA n t) = caseBoolUp n (eraseAnnot t).
  Proof.
    unfold caseBoolUpA, caseBoolUp, caseBoolUp_pctx, caseBoolUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_caseProdUpA {n t τ1 τ2} :
    eraseAnnot (caseProdUpA n t τ1 τ2) = caseProdUp n (eraseAnnot t) τ1 τ2.
  Proof.
    unfold caseProdUpA, caseProdUp, caseProdUp_pctx, caseProdUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_caseSumUpA {n t τ1 τ2} :
    eraseAnnot (caseSumUpA n t τ1 τ2) = caseSumUp n (eraseAnnot t) τ1 τ2.
  Proof.
    unfold caseSumUpA, caseSumUp, caseSumUp_pctx, caseSumUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_caseArrUpA {n t τ1 τ2} :
    eraseAnnot (caseArrUpA n t τ1 τ2) = caseArrUp n (eraseAnnot t) τ1 τ2.
  Proof.
    unfold caseArrUpA, caseArrUp, caseArrUp_pctx, caseArrUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_caseRecUpA {n t τ} :
    eraseAnnot (caseRecUpA n t τ) = caseRecUp n (eraseAnnot t) τ.
  Proof.
    unfold caseRecUpA, caseRecUp, caseRecUp_pctx, caseRecUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_pctx_caseUnitUp_pctxA {n} :
    eraseAnnot_pctx (caseUnitUp_pctxA n) = caseUnitUp_pctx n.
  Proof.
    unfold caseUnitUp_pctxA, caseUnitUp_pctx, caseUnitUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_pctx_caseBoolUp_pctxA {n} :
    eraseAnnot_pctx (caseBoolUp_pctxA n) = caseBoolUp_pctx n.
  Proof.
    unfold caseBoolUp_pctxA, caseBoolUp_pctx, caseBoolUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_pctx_caseProdUp_pctxA {n τ1 τ2} :
    eraseAnnot_pctx (caseProdUp_pctxA n τ1 τ2) = caseProdUp_pctx n τ1 τ2.
  Proof.
    unfold caseProdUp_pctxA, caseProdUp_pctx, caseProdUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_pctx_caseSumUp_pctxA {n τ1 τ2} :
    eraseAnnot_pctx (caseSumUp_pctxA n τ1 τ2) = caseSumUp_pctx n τ1 τ2.
  Proof.
    unfold caseSumUp_pctxA, caseSumUp_pctx, caseSumUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_pctx_caseArrUp_pctxA {n τ1 τ2} :
    eraseAnnot_pctx (caseArrUp_pctxA n τ1 τ2) = caseArrUp_pctx n τ1 τ2.
  Proof.
    unfold caseArrUp_pctxA, caseArrUp_pctx, caseArrUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

  Lemma eraseAnnot_pctx_caseRecUp_pctxA {n τ} :
    eraseAnnot_pctx (caseRecUp_pctxA n τ) = caseRecUp_pctx n τ.
  Proof.
    unfold caseRecUp_pctxA, caseRecUp_pctx, caseRecUp_pctxA.
    cbn.
    now rewrite upgrade_upgradeA.
  Qed.

End DestructTypes.

Hint Resolve caseUnitUp_T : uval_typing.
Hint Resolve caseBoolUp_T : uval_typing.
Hint Resolve caseSumUp_T : uval_typing.
Hint Resolve caseProdUp_T : uval_typing.
Hint Resolve caseArrUp_T : uval_typing.
Hint Resolve caseRecUp_T : uval_typing.
Hint Resolve caseUnitUp_pctx_T : uval_typing.
Hint Resolve caseBoolUp_pctx_T : uval_typing.
Hint Resolve caseSumUp_pctx_T : uval_typing.
Hint Resolve caseProdUp_pctx_T : uval_typing.
Hint Resolve caseArrUp_pctx_T : uval_typing.
Hint Resolve caseRecUp_pctx_T : uval_typing.
Hint Resolve caseUnitUpA_T : uval_typing.
Hint Resolve caseBoolUpA_T : uval_typing.
Hint Resolve caseSumUpA_T : uval_typing.
Hint Resolve caseProdUpA_T : uval_typing.
Hint Resolve caseArrUpA_T : uval_typing.
Hint Resolve caseRecUpA_T : uval_typing.
Hint Resolve caseUnitUp_pctxA_T : uval_typing.
Hint Resolve caseBoolUp_pctxA_T : uval_typing.
Hint Resolve caseSumUp_pctxA_T : uval_typing.
Hint Resolve caseProdUp_pctxA_T : uval_typing.
Hint Resolve caseArrUp_pctxA_T : uval_typing.
Hint Resolve caseRecUp_pctxA_T : uval_typing.


Local Ltac crush :=
  repeat (
      repeat match goal with
                 [ H : _ ∧ _ |- _] => destruct H as [? ?]
               | [ H : valrel _ _ ptunit _ _ |- _] => apply valrel_ptunit_inversion in H
               | [ H : valrel _ _ (ptsum _ _) _ _ |- _] => apply valrel_ptsum_inversion in H
               | [ H : valrel _ _ (ptarr _ _) _ _ |- _] => apply valrel_ptarr_inversion in H
               | [ |- clos_refl_trans_1n I.Tm I.eval I.unit _ ] => eapply rt1n_refl
             end; 
      repeat crushLRMatch;
      crushOfType;
      trivial;
      simpl);
  subst.

Section DestructProps.
  Lemma caseUnitUp_sub {n ts γs} :
    (caseUnitUp n ts)[γs] = 
    (caseUnitUp n (ts[γs])).
  Proof.
    unfold caseUnitUp, caseUnitUp_pctx, caseUnit_pctx.
    simpl.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply upgrade_sub.
  Qed.

  Lemma caseBoolUp_sub {n ts γs} :
    (caseBoolUp n ts)[γs] = 
    (caseBoolUp n (ts[γs])).
  Proof.
    unfold caseBoolUp, caseBoolUp_pctx, caseBool_pctx.
    simpl.
    cbn; repeat crushStlcSyntaxMatchH.
    eapply upgrade_sub.
  Qed.

  Lemma caseProdUp_sub {n ts γs τ1 τ2} :
    (caseProdUp n ts τ1 τ2)[γs] =
    (caseProdUp n (ts[γs]) τ1 τ2).
  Proof.
    unfold caseProdUp.
    simpl; repeat crushStlcSyntaxMatchH.
    eapply upgrade_sub.
  Qed.

  Lemma caseSumUp_sub {n ts γs τ1 τ2} :
    (caseSumUp n ts τ1 τ2)[γs] =
    (caseSumUp n (ts[γs]) τ1 τ2).
  Proof.
    unfold caseSumUp.
    simpl; repeat crushStlcSyntaxMatchH.
    eapply upgrade_sub.
  Qed.

  Lemma caseArrUp_sub {n ts γs τ1 τ2} :
    (caseArrUp n ts τ1 τ2)[γs] =
    (caseArrUp n (ts[γs]) τ1 τ2).
  Proof.
    unfold caseArrUp.
    simpl; repeat crushStlcSyntaxMatchH.
    eapply upgrade_sub.
  Qed.

  Lemma caseRecUp_sub {n ts γs τ} :
    (caseRecUp n ts τ)[γs] =
    (caseRecUp n (ts[γs]) τ).
  Proof.
    unfold caseRecUp.
    simpl; repeat crushStlcSyntaxMatchH.
    eapply upgrade_sub.
  Qed.

  (* pff how to shorten the following? *)
  Lemma invert_valrel_pEmulDV_for_caseUValUnit {d w n p vs vu} :
    valrel d w (pEmulDV (S n) p I.tunit) vs vu →
    (vs = (F.inl F.unit) ∧ vu = I.unit ∧
            caseUnit vs -->* F.unit) ∨
    (p = imprecise ∧ (caseUnit vs) ⇑).
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    simpl in H0, H2.

    apply invert_valrel_pEmulDV_unit in vr.
    destruct vr as [[? ?] | (? & ? & vr)]; 
      subst. unfold caseUnit.
    - right.
      eauto using caseUVal_eval_unk_diverges.
    - left.
      destruct (valrel_ptunit_inversion vr); subst.
      eauto using caseUVal_eval_left.
  Qed.

  (* Lemma termrel₀_caseUValUnit {d w n p vs vu}: *)
  (*   dir_world_prec n w d p → *)
  (*   valrel d w (pEmulDV (S n) p) vs vu → *)
  (*   termrel₀ d w ptunit (caseUnit vs) (U.seq vu U.unit). *)
  (* Proof. *)
  (*   unfold caseUnit. *)
  (*   intros dwp vr. *)
  (*   destruct (valrel_implies_Value vr). *)
  (*   apply invert_valrel_pEmulDV_for_caseUValUnit in vr. *)
  (*   destruct vr as [(? & ? & ?)|[(? & ?)|(? & ?)]]. *)
  (*   - subst. *)
  (*     eapply termrel₀_antired_star. *)
  (*     + eapply caseUVal_eval_unit; crush. *)
  (*     + eapply evalToStar. *)
  (*       eapply U.eval₀_ctxeval. *)
  (*       eauto with eval. *)
  (*     + simpl; eauto using valrel_in_termrel₀, valrel_unit. *)
  (*   - subst; eapply dwp_invert_imprecise in dwp; subst. *)
  (*     eapply (termreli₀_div_lt H2). *)
  (*   - apply (termreli₀_div_wrong H2). *)
  (*     right. *)
  (*     eauto using evalToStar, U.eval₀_to_eval with eval. *)
  (* Qed. *)

  Lemma invert_valrel_pEmulDV_for_caseUValBool {d w n p vs vu} :
    valrel d w (pEmulDV (S n) p I.tbool) vs vu →
    (∃ vs', vs = (inBool n vs') ∧
                caseBool vs -->* vs' ∧
                valrel d w ptbool vs' vu) ∨
    (p = imprecise ∧ (caseBool vs) ⇑).
  Proof.
    intros vr.
    apply invert_valrel_pEmulDV_bool in vr.
    destruct vr as [[? ?] | (vs' & cases)];
      subst; unfold caseBool.
    - right.
      eauto using divergence_closed_under_evalstar, caseUVal_eval_unk_diverges.
    - left. exists vs'.
      destruct cases as [-> vr].
      cbn; split; [|split]; trivial.
      destruct (valrel_implies_Value vr).
      eauto using caseUVal_eval_left.
  Qed.

  Lemma invert_valrel_pEmulDV_for_caseUValArr {d w n p vs vu τ1 τ2} :
    valrel d w (pEmulDV (S n) p (I.tarr τ1 τ2)) vs vu →
    (∃ vs', vs = (F.inl vs') ∧ 
                caseArr n vs τ1 τ2 -->* vs' ∧
                valrel d w (ptarr (pEmulDV n p τ1) (pEmulDV n p τ2)) vs' vu) ∨
    (p = imprecise ∧ (caseArr n vs τ1 τ2) ⇑).
  Proof.
    intros vr.
    apply invert_valrel_pEmulDV_arr in vr.
    destruct vr as [[? ?] | (vs' & ? & vr)]; 
      subst; unfold caseArr.
    - right.
      eauto using caseUVal_eval_unk_diverges.
    - left. exists vs'.
      destruct (valrel_implies_Value vr).
      eauto using caseUVal_eval_left.
  Qed.

  Lemma invert_valrel_pEmulDV_for_caseUValRec {d w n p vs vu τ} :
    valrel d w (pEmulDV (S n) p (I.trec τ)) vs (I.fold_ vu) →
    (∃ vs', vs = (F.inl vs') ∧
                caseRec n vs τ --> vs' ∧
                (forall w', w' < w -> valrel d w' (pEmulDV n p (τ [beta1 (trec τ)])) vs' vu)) ∨
    (p = imprecise ∧ (caseRec n vs τ) ⇑).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    unfold valrel' in vr.
    destruct vr as [ot vr].
    destruct vr as [(-> & ->)|(ts' & -> & tu' & equ & vr)];
      destruct (OfType_implies_Value ot) as (vts' & vvu).
    - right.
      eauto using caseRec_eval_unk_diverges.
    - left. exists ts'.
      inversion equ; subst; clear equ.
      split; [reflexivity|split;eauto].
      unfold caseRec, caseRec_pctx, caseUVal_pctx; cbn.
      eapply F.eval_eval₀.
      refine (eval_case_inl _).
      now cbn in vts'.
  Qed.

  Lemma invert_valrel_pEmulDV_for_caseUValProd {d w n p τ₁ τ₂ vs vu} :
    valrel d w (pEmulDV (S n) p (I.tprod τ₁ τ₂)) vs vu →
    (∃ vs', vs = (inProd n vs') ∧
                caseProd n vs τ₁ τ₂ -->* vs' ∧
                valrel d w (ptprod (pEmulDV n p τ₁) (pEmulDV n p τ₂)) vs' vu) ∨
    (p = imprecise ∧ (caseProd n vs τ₁ τ₂) ⇑).
  Proof.
    intros vr.
    apply invert_valrel_pEmulDV_prod in vr.
    destruct vr as [[? ?] | (vs' & -> & vr)];
      subst; unfold caseProd.
    - right.
      eauto using divergence_closed_under_evalstar, caseUVal_eval_unk_diverges.
    - left. exists vs'.
      crush.
      eapply evalToStar.
      destruct (valrel_implies_Value vr) as (vvs' & vvu).
      eapply (eval_ctx₀' (eval_case_inl vvs')); F.inferContext; now cbn.
  Qed.

  Lemma invert_valrel_pEmulDV_for_caseUValSum {d w n p vs vu τ1 τ2} :
    valrel d w (pEmulDV (S n) p (I.tsum τ1 τ2)) vs vu →
    (∃ vs', vs = (F.inl vs') ∧
                caseSum n vs τ1 τ2 -->* vs' ∧
                valrel d w (ptsum (pEmulDV n p τ1) (pEmulDV n p τ2)) vs' vu) ∨
    (p = imprecise ∧ (caseSum n vs τ1 τ2) ⇑).
  Proof.
    intros vr.
    apply invert_valrel_pEmulDV_sum in vr.
    destruct vr as [[? ?] | (vs' & ? & vr)];
      subst; unfold caseSum.
    - right.
      eauto using caseUVal_eval_unk_diverges.
    - left. exists vs'.
      destruct (valrel_implies_Value vr).
      eauto using caseUVal_eval_left.
  Qed.

  (* Lemma termrel₀_caseUValBool {d w n p vs vu}: *)
  (*   dir_world_prec n w d p → *)
  (*   valrel d w (pEmulDV (S n) p) vs vu → *)
  (*   termrel₀ d w ptbool (caseBool vs) (U.ite vu U.true U.false). *)
  (* Proof. *)
  (*   unfold caseBool. *)
  (*   intros dwp vr. *)
  (*   destruct (valrel_implies_Value vr). *)
  (*   apply invert_valrel_pEmulDV_for_caseUValBool in vr. *)
  (*   destruct vr as [(? & ? & ? & vr')|[(? & ?)|(? & ? & ?)]]. *)
  (*   - subst. *)
  (*     eapply termrel₀_antired_star. *)
  (*     + eapply caseUVal_eval_bool; crush. *)
  (*     + eapply evalToStar. *)
  (*       eapply U.eval₀_ctxeval. *)

  (*       destruct vr' as (ot & [(? & ?) | (? & ?)]); subst; *)
  (*       eauto with eval. *)
  (*     + cbn; eauto using valrel_in_termrel₀, valrel_unit. *)
  (*   - subst; eapply dwp_invert_imprecise in dwp; subst. *)
  (*     eapply (termreli₀_div_lt H2). *)
  (*   - apply (termreli₀_div_wrong H3). *)
  (*     right. *)
  (*     eauto using evalToStar, U.eval₀_to_eval with eval. *)
  (* Qed. *)

End DestructProps.

