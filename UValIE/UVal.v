Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.LemmasTyping.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.CanForm.
Require Import StlcEqui.Fix.
Require Import StlcEqui.Size.
Require Import StlcEqui.TypeSafety.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.CanForm.
Require Import StlcIso.Size.
(* Require Import StlcIso.StlcOmega. *)
Require Import StlcIso.TypeSafety.
Require Import StlcIso.Fix.
Require Import Common.Relations.
Require Import Lia.

Module I.
  Include RecTypes.SpecTypes.
  Include RecTypes.InstTy.
  Include RecTypes.Contraction.
  Include RecTypes.ValidTy.
  Include RecTypes.LemmasTypes.
  Include StlcIso.SpecEvaluation.
  Include StlcIso.SpecSyntax.
  Include StlcIso.SpecTyping.
  Include StlcIso.SpecAnnot.
  Include StlcIso.LemmasTyping.
  Include StlcIso.LemmasEvaluation.
  Include StlcIso.CanForm.
  Include StlcIso.Fix.
  Include StlcIso.Size.
  Include StlcIso.TypeSafety.
End I.

Module E.
  Include RecTypes.SpecTypes.
  Include RecTypes.InstTy.
  Include RecTypes.Contraction.
  Include RecTypes.ValidTy.
  Include RecTypes.LemmasTypes.
  Include StlcEqui.SpecEvaluation.
  Include StlcEqui.SpecSyntax.
  Include StlcEqui.SpecTyping.
  Include StlcEqui.LemmasTyping.
  Include StlcEqui.LemmasEvaluation.
  Include StlcEqui.CanForm.
  Include StlcEqui.Fix.
  Include StlcEqui.Size.
  Include StlcEqui.TypeSafety.
End E.

Definition UValIE' := fun (S : Ty -> Ty) (τ : Ty) =>
  let τl := match τ with
            | tunit => tunit
            | tbool => tbool
            | τ1 r⇒ τ2 => (S τ1) r⇒ (S τ2)
            | τ1 r× τ2 => (S τ1) r× (S τ2)
            | τ1 r⊎ τ2 => (S τ1) r⊎ (S τ2)
            | trec τ => tunit (* shouldn't be reachable *)
            | tvar i => tunit (* shouldn't be reachable *)
            end
  in τl r⊎ tunit.

Arguments UValIE'/ S τ.

Fixpoint UValIE (n : nat) (τ : Ty) {struct n} : Ty :=
  match n with
    | 0 => tunit
    | S n => UValIE' (UValIE n) (unfoldn (LMC τ) τ)
  end.

Arguments UValIE !n !τ.

Lemma UValIE_trec {n τ} :
  SimpleContr τ ->
  UValIE n (trec τ) = UValIE n (τ [beta1 (trec τ)]).
Proof.
  induction n.
  - reflexivity.
  - intros cτ.
    unfold UValIE; cbn.
    change (τ[beta1 (trec τ)]) with (unfoldOnce (trec τ)).
    rewrite (LMC_unfoldOnce (trec τ)).
    reflexivity.
    eauto with simple_contr_rec.
    cbn. eauto with arith.
Qed.

Lemma UValIE_is_tsum_tunit {n τ} :
  exists τ', UValIE (S n) τ = (τ' r⊎ tunit).
Proof.
  unfold UValIE; cbn.
  eauto.
Qed.

Lemma UValIE_unfoldOnce {n τ} :
  SimpleContr τ ->
  UValIE n τ = UValIE n (unfoldOnce τ).
Proof.
  intros crτ.
  destruct n; try reflexivity.
  destruct τ; try reflexivity.
  eapply UValIE_trec; now inversion crτ.
Qed.

Lemma UValIE_unfoldn {n m τ} :
  SimpleContr τ ->
  UValIE n τ = UValIE n (unfoldn m τ).
Proof.
  revert τ.
  induction m; intros τ crτ; try reflexivity.
  cbn.
  rewrite <- IHm; eauto with simple_contr_rec.
  now eapply UValIE_unfoldOnce.
Qed.

Lemma UValIE'_valid {F τ} :
  (forall τ, ValidTy τ → ValidTy (F τ)) →
  ValidTy τ → ValidTy (UValIE' F τ).
Proof.
  intro S_valid.
  destruct τ; intros; cbn; (apply ValidTy_sum; [| crushValidTy]).
  + apply ValidTy_arr; apply S_valid; crushValidTy.
  + apply ValidTy_unit.
  + apply ValidTy_bool.
  + apply ValidTy_prod; apply S_valid; crushValidTy.
  + apply ValidTy_sum; apply S_valid; crushValidTy.
  + (* technically this case is impossible but annoying to rule out *)
    apply ValidTy_unit.
  + inversion H; inversion H1.
Qed.

Lemma UValIE_valid {n τ} :
  ValidTy τ → ValidTy (UValIE n τ).
Proof.
  revert τ. induction n; intros.
    - unfold UValIE; cbn; crushValidTy.
    - pose proof (@UValIE'_valid (UValIE n)).
      assert (∀ τ : Ty, ValidTy τ → ValidTy (UValIE' (UValIE n) τ)).
        intros.
        unshelve eapply (H0 _ _ H1).
        exact IHn.
      destruct τ.
      (* take care of trec first *)
      6: {
        unfold UValIE.
        fold (UValIE n).
        apply (@UValIE'_valid (UValIE n)).
        exact IHn.
        exact (ValidTy_unfoldn H).
      }
      all:
        unfold UValIE, UValIE';
          cbn;
        (apply ValidTy_sum; [| crushValidTy]).
      + apply ValidTy_arr; apply IHn; crushValidTy.
      + apply ValidTy_unit.
      + apply ValidTy_bool.
      + apply ValidTy_prod; apply IHn; crushValidTy.
      + apply ValidTy_sum; apply IHn; crushValidTy.
      + destruct H as (_ & contr); inversion contr.
Qed.

Lemma UValIE'_preserves_ws' {F τ i} :
  (forall τ, ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ F τ ⟩ ) →
  ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ UValIE' F τ ⟩.
Proof.
  intro S_valid.
  destruct τ; intros; cbn; (constructor; [| constructor]).
  + inversion H; subst; constructor; crushValidTy.
  + constructor.
  + constructor.
  + inversion H; subst; constructor; crushValidTy.
  + inversion H; subst; constructor; crushValidTy.
  + (* technically this case is impossible but annoying to rule out *)
    constructor.
  + constructor.
Qed.

Lemma UValIE_preserves_ws {i n τ} :
  ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ UValIE n τ ⟩.
Proof.
  revert i τ. induction n; intros.
    - unfold UValIE; cbn; constructor.
    - pose proof (@UValIE'_preserves_ws' (UValIE n)).
      assert (∀ i τ, ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ UValIE' (UValIE n) τ ⟩).
        intros.
        eapply H0.
        intros.
        apply IHn.
        assumption.
        assumption.
      destruct τ.
      (* take care of trec first *)
      6: {
        unfold UValIE.
        fold (UValIE n).
        apply (@UValIE'_preserves_ws' (UValIE n)).
        exact (IHn i).
        apply unfoldn_preserves_ws; assumption.
      }
      all:
        try inversion H; subst;
        unfold UValIE, UValIE';
          cbn;
        (constructor; [| crushValidTy]);
        constructor; apply IHn; crushValidTy.
Qed.

Lemma UValIE'_preserves_contr {F τ} :
  (forall τ, SimpleContr τ → SimpleContr (F τ)) →
  (forall τ, SimpleRec τ → SimpleRec (F τ)) →
  SimpleContr τ → SimpleContr (UValIE' F τ).
Proof.
  intros S_contr S_rec contr;
  dependent destruction contr; cbn;
    do 3 constructor;
    apply S_rec; intuition.
Qed.

Lemma UValIE'_preserves_rec {F τ} :
  (forall τ, SimpleContr τ → SimpleContr (F τ)) →
  (forall τ, SimpleRec τ → SimpleRec (F τ)) →
  SimpleRec τ → SimpleRec (UValIE' F τ).
Proof.
  intros S_contr S_rec contr.
  destruct contr; constructor.
  - cbn. repeat constructor.
  - apply (UValIE'_preserves_contr S_contr S_rec H).
Qed.

Lemma UValIE_preserves_contr {n τ} :
  SimpleContr τ → SimpleContr (UValIE n τ)
with UValIE_preserves_rec {n τ} :
  SimpleRec τ → SimpleRec (UValIE n τ).
Proof.
  - revert τ. destruct n; intros.
    + unfold UValIE; cbn; constructor.
    + pose proof (@UValIE'_preserves_contr (UValIE n)).
      pose proof (@UValIE'_preserves_rec (UValIE n)).
      assert (∀ τ, SimpleContr τ → SimpleContr (UValIE' (UValIE n) τ)).
        intros.
        unshelve eapply (H0 _ _ _ H2).
        exact (UValIE_preserves_contr n).
        exact (UValIE_preserves_rec n).
      destruct τ.
      (* take care of trec first *)
      6: {
        unfold UValIE.
        fold (UValIE n).
        apply (@UValIE'_preserves_contr (UValIE n)).
        exact (UValIE_preserves_contr n).
        exact (UValIE_preserves_rec n).
        apply (SimpleContr_unfoldn _ _ H).
      }

      all:
        try inversion H; subst;
          unfold UValIE, UValIE';
          cbn;
          constructor; constructor; constructor;
          apply UValIE_preserves_rec; assumption.
  - revert τ. destruct n; intros.
    + unfold UValIE; cbn; do 2 constructor.
    + pose proof (@UValIE'_preserves_contr (UValIE n)).
      pose proof (@UValIE'_preserves_rec (UValIE n)).
      assert (∀ τ, SimpleContr τ → SimpleContr (UValIE' (UValIE n) τ)).
        intros.
        unshelve eapply (H0 _ _ _ H2).
        exact (UValIE_preserves_contr n).
        exact (UValIE_preserves_rec n).
      destruct τ.
      (* take care of trec first *)
      6: {
        unfold UValIE.
        fold (UValIE n).
        apply (@UValIE'_preserves_rec (UValIE n)).
        exact (UValIE_preserves_contr n).
        exact (UValIE_preserves_rec n).
        apply (SimpleRec_unfoldn _ _ H).
      }
      all:
        try inversion H; try inversion H3; subst;
          unfold UValIE, UValIE';
          cbn;
        constructor; constructor; constructor; constructor;
        apply UValIE_preserves_rec; assumption.
Qed.

Lemma UValIE_valid' {n τ} :
  ValidTy τ →
  ValidTy (UValIE' (UValIE n) (unfoldn (LMC τ) τ)).
Proof.
  intros.
  apply UValIE'_valid.
  - intros; now apply UValIE_valid.
  - now apply ValidTy_unfoldn.
Qed.

Ltac crushValidTyMatchUval :=
  match goal with
  | [ |- ValidTy (UValIE _ _) ] => eapply UValIE_valid
  end.
Ltac crushValidTy_with_UVal :=
  repeat (
      crushValidTyMatch2 + crushValidTyMatchUval
    ); try lia; eauto with ws wsi.

Definition unkUVal (n : nat) : I.Tm :=
  match n with
  | 0 => I.unit
  | _ => I.inr I.unit
  end.

Definition unkUValA (n : nat) (τ : Ty) : I.TmA :=
  match n with
  | 0 => I.ia_unit
  | (S n) => I.ia_inr (match unfoldn (LMC τ) τ with
      | tunit => tunit
      | tbool => tbool
      | τ1 r⇒ τ2 => (UValIE n τ1) r⇒ (UValIE n τ2)
      | τ1 r× τ2 => (UValIE n τ1) r× (UValIE n τ2)
      | τ1 r⊎ τ2 => (UValIE n τ1) r⊎ (UValIE n τ2)
      | trec τ => tunit
      | tvar i => tunit
      end) tunit I.ia_unit
  end.

Lemma unkUVal_unkUValA {n τ} : unkUVal n = eraseAnnot (unkUValA n τ).
Proof.
  destruct n;
  now cbn.
Qed.

Lemma unkUVal_Value (n : nat) : I.Value (unkUVal n).
Proof.
  case n; simpl; trivial.
Qed.

Lemma unkUValT {Γ n τ} : ValidTy τ → ⟪ Γ i⊢ unkUVal n : UValIE n τ ⟫.
Proof.
  induction n;
    eauto using I.Typing, E.Typing.
  unfold UValIE, UValIE'; cbn;
  I.crushTyping.
  epose proof (UValIE_valid' H);
  destruct (ValidTy_invert_sum H0) as (H' & _).
  exact H'.
Qed.

Lemma unkUValAT {Γ n τ} :
  ValidTy τ -> ⟪ Γ ia⊢ unkUValA n τ : UValIE n τ ⟫.
Proof.
  induction n;
    eauto using I.AnnotTyping.
  unfold UValIE, UValIE'; cbn;
  I.crushTypingIA;
  epose proof (UValIE_valid' H);
  destruct (ValidTy_invert_sum H0) as (H' & _).
  exact H'.
Qed.

#[export]
Hint Resolve unkUValT : uval_typing.
#[export]
Hint Resolve unkUValAT : uval_typing.

(* Definition constr_uvalie {Γ} (n : nat) (τ : E.Ty) (t : F.Tm) {P : ClosedTy τ} {Q : F.Typing Γ t (@UValFE n τ P)} : F.Tm := *)
(*   I.inl t. *)

(* Definition inUnit_pctx (n : nat) := pinr (pinl phole). *)
(* Definition inUnit (n : nat) (t : Tm) := pctx_app t (inUnit_pctx n). *)
(* Arguments inUnit_pctx / n. *)

(* Lemma inUnit_Value {n v} : Value v → Value (inUnit n v). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* Lemma inUnit_pctx_T {Γ n} : ⟪Unit_pctx n : Γ , tunit → Γ , UVal (S n) ⟫. *)
(* Proof. *)
(*   unfold inUnit_pctx. crushTyping. *)
(* Qed. *)

Lemma inUnitT {Γ n t} : ⟪ Γ i⊢ t : tunit ⟫ → ⟪ Γ i⊢ I.inl t : UValIE (S n) tunit ⟫.
Proof.
  intuition.
Qed.

(* Arguments inUnit n t : simpl never. *)

Definition inBool_pctx (n : nat) : PCtx := pinl phole.
Definition inBool (n : nat) (t : Tm): Tm := pctx_app t (inBool_pctx n).

Arguments inBool_pctx /n.

Lemma inBool_pctx_T {Γ n} : ⟪ i⊢ inBool_pctx n : Γ , tbool → Γ , UValIE (S n) tbool ⟫.
Proof.
  unfold inBool_pctx. unfold UValIE. crushTyping.
Qed.

Lemma inBoolT {Γ n t} : ⟪ Γ i⊢ t : tbool ⟫ → ⟪ Γ i⊢ inBool n t : UValIE (S n) tbool ⟫.
Proof.
  unfold inBool. eauto using inBool_pctx_T with typing.
Qed.

Lemma inBool_Value {n v} : Value v → Value (inBool n v).
Proof.
  simpl; trivial.
Qed.

Definition inProd_pctx (n : nat) : PCtx := pinl phole.
Definition inProd (n : nat) (t : Tm) : Tm := pctx_app t (inProd_pctx n).

Lemma inProd_pctx_T {Γ n τ₁ τ₂} : ⟪ i⊢ inProd_pctx n : Γ , UValIE n τ₁ r× UValIE n τ₂ → Γ , UValIE (S n) (E.tprod τ₁ τ₂)⟫.
Proof.
  unfold inProd_pctx. crushTyping.
Qed.

Lemma inProd_T {Γ n t τ₁ τ₂} : ⟪ Γ i⊢ t : UValIE n τ₁ r× UValIE n τ₂ ⟫ → ⟪ Γ i⊢ inProd n t : UValIE (S n) (E.tprod τ₁ τ₂) ⟫.
Proof.
  unfold inProd. eauto using inProd_pctx_T with typing.
Qed.

Lemma inProd_Value {n v} : Value v → Value (inProd n v).
Proof.
  simpl; trivial.
Qed.

(* Definition inArr_pctx (n : nat) : PCtx := pinr (pinr (pinr (pinr (pinl phole)))). *)
(* Definition inArr (n : nat) (t : Tm) : Tm := pctx_app t (inArr_pctx n). *)

(* Arguments inArr_pctx / n. *)

(* Lemma inArr_pctx_T {Γ n} : ⟪ ⊢ inArr_pctx n : Γ , UValFE n ⇒ UValFE n → Γ , UValFE (S n) ⟫. *)
(* Proof. *)
(*   unfold inArr_pctx. crushTyping. *)
(* Qed. *)

Lemma inArr_T {Γ n t τ τ'} : ⟪ Γ i⊢ t : tarr (UValIE n τ) (UValIE n τ') ⟫ → ⟪ Γ i⊢ inl t : UValIE (S n) (E.tarr τ τ') ⟫.
Proof.
  intuition.
Qed.

(* Lemma inArr_Value {n v} : Value v → Value (inArr n v). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* Definition inSum_pctx (n : nat) : PCtx := pinr (pinr (pinr (pinr (pinr phole)))). *)
(* Definition inSum (n : nat) (t : Tm) : Tm := pctx_app t (inSum_pctx n). *)

(* Lemma inSum_pctx_T {Γ n} : ⟪ ⊢ inSum_pctx n : Γ , UVal n ⊎ UVal n → Γ , UVal (S n) ⟫. *)
(* Proof. *)
(*   unfold inSum_pctx. crushTyping. *)
(* Qed. *)

Lemma inSum_T {Γ n t τ τ'} : ⟪ Γ i⊢ t : tsum (UValIE n τ) (UValIE n τ') ⟫ → ⟪ Γ i⊢ I.inl t : UValIE (S n) (tsum τ τ') ⟫.
Proof.
  intuition.
Qed.

(* Lemma inSum_Value {n v} : Value v → Value (inSum n v). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* (t : F.Tm) {P : F.Typing t (UValFE n tunit)} : F.Tm := *)
Definition case_uvalie_unit (n : nat) : I.Tm :=
  (* let P := UnitClosed 0 in *)
  let τ := UValIE (S n) tunit in
  let t := I.caseof (I.var 0) (I.var 0) (I.Om tunit) in
  I.abs τ t.

Definition case_uvalie_arr (n : nat) (τ1 τ2 : Ty) : I.Tm :=
  let τ := @UValIE (S n) (E.tarr τ1 τ2) in
  let τ' := tarr (UValIE n τ1) (UValIE n τ2) in
  let t := I.caseof (I.var 0) (I.var 0) (I.Om τ') in
  I.abs τ t.

Lemma uvalie_expand_arr {n τ1 τ2} :
  UValIE (S n) (τ1 r⇒ τ2) = (((UValIE n τ1) r⇒ (UValIE n τ2)) r⊎ tunit).
Proof.
  reflexivity.
Qed.

Lemma case_uval_arr_typing {Γ n τ1 τ2} :
  let τ := τ1 r⇒ τ2 in
  let uval_dest := case_uvalie_arr n τ1 τ2 in
  let arg_type := UValIE (S n) τ in
  let ret_type := (UValIE n τ1) r⇒ (UValIE n τ2) in
  let type := arg_type r⇒ ret_type in
  ValidTy τ → ⟪ Γ i⊢ uval_dest : type ⟫.
Proof.
  intros.
  destruct (ValidTy_invert_arr H) as (? & ?).
  assert (ValidTy ret_type) by (unfold ret_type; crushValidTy_with_UVal).
  unfold uval_dest.
  unfold type.
  unfold arg_type.
  unfold ret_type.
  (* unfold uval_dest, arg_type, ret_type, type, case_uvalie_arr. *)
  (* crushTyping. *)
  constructor.
  unfold τ.
  apply (@I.WtCaseof (evar Γ arg_type) (I.var 0) (I.var 0) (I.Om ret_type) ret_type tunit ret_type).
  unfold arg_type.
  unfold ret_type.
  constructor.
  simpl.
  constructor.
  constructor.
  constructor.
  apply wtOm_tau.
  all: crushValidTy_with_UVal.
Qed.

Definition case_uvalie_tsum (n : nat) (τ1 τ2 : Ty) : I.Tm :=
  let τ := UValIE (S n) (tsum τ1 τ2) in
  let τ' := tsum (UValIE n τ1) (@UValIE n τ2) in
  let t := I.caseof (I.var 0) (I.var 0) (I.Om τ') in
  I.abs τ t.

Definition case_uvalie_trec (n : nat) (τb : Ty) : I.Tm :=
  let τ_rec := E.trec τb in
  let τ := UValIE (S n) τ_rec in
  let τ' := UValIE n τb[beta1 τ_rec] in
  let t := I.caseof (I.var 0) (I.var 0) (I.Om τ') in
  I.abs τ t.

Definition caseV0 (case₁ : I.Tm) (case₂ : I.Tm) : I.Tm :=
  I.caseof (I.var 0) (case₁ [wkm↑]) (case₂[wkm↑]).

Lemma caseV0_T {Γ : Env} {τ₁ τ₂ τ : Ty} {case₁ case₂ : I.Tm} :
  ValidEnv Γ →
  ValidTy τ₁ →
  ValidTy τ₂ →
  Typing (evar Γ τ₁) case₁ τ →
  Typing (evar Γ τ₂) case₂ τ →
  Typing (evar Γ (tsum τ₁ τ₂)) (caseV0 case₁ case₂) τ.
Proof.
  unfold caseV0.
  I.crushTyping.
Qed.

#[export]
Hint Resolve caseV0_T : uval_typing.

Definition caseUVal_pctx (τ : Ty) := I.pcaseof₁ I.phole (I.var 0) (I.Om τ).
Definition caseUVal_pctxA (τ : Ty) := I.ia_pcaseof₁ τ tunit τ I.ia_phole (I.ia_var 0) (OmA τ).

Definition caseUnit_pctx := caseUVal_pctx tunit.
Definition caseUnit_pctxA (n : nat) := caseUVal_pctxA tunit.
Definition caseBool_pctx := caseUVal_pctx tbool.
Definition caseBool_pctxA (n : nat) := caseUVal_pctxA tbool.
Definition caseProd_pctx (n : nat) (τ1 τ2 : Ty) := caseUVal_pctx (tprod (UValIE n τ1) (UValIE n τ2)).
Definition caseProd_pctxA (n : nat) (τ1 τ2 : Ty) := caseUVal_pctxA (tprod (UValIE n τ1) (UValIE n τ2)).
Definition caseSum_pctx (n : nat) (τ1 τ2 : Ty) := caseUVal_pctx (tsum (UValIE n τ1) (UValIE n τ2)).
Definition caseSum_pctxA (n : nat) (τ1 τ2 : Ty) := caseUVal_pctxA (tsum (UValIE n τ1) (UValIE n τ2)).
Definition caseArr_pctx (n : nat) (τ1 τ2 : Ty) := caseUVal_pctx (tarr (UValIE n τ1) (UValIE n τ2)).
Definition caseArr_pctxA (n : nat) (τ1 τ2 : Ty) := caseUVal_pctxA (tarr (UValIE n τ1) (UValIE n τ2)).
Definition caseRec_pctx (n : nat) (τ : Ty) := caseUVal_pctx (UValIE n τ[beta1 (E.trec τ)]).
Definition caseRec_pctxA (n : nat) (τ : Ty) := caseUVal_pctxA (UValIE n τ[beta1 (E.trec τ)]).

Definition caseUVal (τ : Ty) (t : I.Tm) := I.pctx_app t (caseUVal_pctx τ).
Definition caseUValA (τ : Ty) (t : I.TmA) := I.pctxA_app t (caseUVal_pctxA τ).

(* Definition caseUValEqui (n : nat) (τ : Ty) (t : I.Tm) := caseUVal (UValIE n τ) t. *)
(* Definition caseUValEquiA (n : nat) (τ' τ : Ty) (t : I.Tm) := caseUVal (UValIE n τ) t. *)

Arguments caseUVal_pctx τ : simpl never.
Arguments caseUVal τ t : simpl never.

Definition caseUnit t := I.pctx_app t caseUnit_pctx.
Definition caseUnitA n t := I.pctxA_app t (caseUnit_pctxA n).
Definition caseBool t := I.pctx_app t caseBool_pctx.
Definition caseBoolA n t := I.pctxA_app t (caseBool_pctxA n).
Definition caseSum n t τ1 τ2 := I.pctx_app t (caseSum_pctx n τ1 τ2).
Definition caseSumA n t τ1 τ2 := I.pctxA_app t (caseSum_pctxA n τ1 τ2).
Definition caseProd n t τ1 τ2 := I.pctx_app t (caseProd_pctx n τ1 τ2).
Definition caseProdA n t τ1 τ2 := I.pctxA_app t (caseProd_pctxA n τ1 τ2).
Definition caseArr n t τ1 τ2 := I.pctx_app t (caseArr_pctx n τ1 τ2).
Definition caseArrA n t τ1 τ2 := I.pctxA_app t (caseArr_pctxA n τ1 τ2).
Definition caseRec n t τ := I.pctx_app t (caseRec_pctx n τ).
Definition caseRecA n t τ := I.pctxA_app t (caseRec_pctxA n τ).

Lemma caseUnit_pctx_T {Γ n} :
  ⟪ i⊢ caseUnit_pctx : Γ, UValIE (S n) tunit → Γ, tunit ⟫.
Proof.
  unfold caseUnit_pctx, caseUVal_pctx.
  eauto with typing uval_typing tyvalid.
Qed.

Lemma caseUnit_pctxA_T {Γ n} :
  ⟪ ia⊢ caseUnit_pctxA n : Γ, UValIE (S n) tunit → Γ, tunit ⟫.
Proof.
  unfold caseUnit_pctxA, caseUVal_pctxA.
  cbn.
  repeat constructor.
Qed.

Lemma caseUnit_T {Γ n t} :
  ⟪ Γ i⊢ t : UValIE (S n) tunit ⟫ →
  ⟪ Γ i⊢ caseUnit t : tunit ⟫.
Proof.
  unfold caseUnit; eauto using caseUnit_pctx_T with typing uval_typing.
Qed.

Lemma caseUnitA_T {Γ n t} :
  ⟪ Γ ia⊢ t : UValIE (S n) tunit ⟫ →
  ⟪ Γ ia⊢ caseUnitA n t : tunit ⟫.
Proof.
  unfold caseUnitA; eauto using caseUnit_pctxA_T with typing uval_typing tyvalid.
Qed.

Lemma caseUnit_pctx_ectx : ECtx caseUnit_pctx.
Proof. simpl; trivial. Qed.

Lemma caseBool_pctx_T {Γ n} :
  ⟪ i⊢ caseBool_pctx : Γ, UValIE (S n) E.tbool → Γ, tbool ⟫.
Proof.
  unfold caseBool_pctx, caseUVal_pctx.
  eauto with typing uval_typing tyvalid.
Qed.

Lemma caseBool_pctxA_T {Γ n} :
  ⟪ ia⊢ caseBool_pctxA n : Γ, UValIE (S n) E.tbool → Γ, tbool ⟫.
Proof.
  unfold caseBool_pctxA, caseUVal_pctxA.
  cbn.
  repeat constructor.
Qed.

Lemma caseBool_T {Γ n t} :
  ⟪ Γ i⊢ t : UValIE (S n) E.tbool ⟫ →
  ⟪ Γ i⊢ caseBool t : tbool ⟫.
Proof.
  unfold caseBool; eauto using caseBool_pctx_T with typing uval_typing.
Qed.

Lemma caseBoolA_T {Γ n t} :
  ⟪ Γ ia⊢ t : UValIE (S n) E.tbool ⟫ →
  ⟪ Γ ia⊢ caseBoolA n t : tbool ⟫.
Proof.
  unfold caseBoolA; eauto using caseBool_pctxA_T with typing uval_typing.
Qed.

Lemma caseBool_pctx_ectx : ECtx caseBool_pctx.
Proof. simpl; trivial. Qed.

Lemma caseSum_pctx_T {Γ n τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ i⊢ caseSum_pctx n τ1 τ2 : Γ, UValIE (S n) (tsum τ1 τ2) → Γ, tsum (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  econstructor;
  eauto using UValIE_valid with typing tyvalid.
Qed.

Lemma caseSum_pctxA_T {Γ n τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ ia⊢ caseSum_pctxA n τ1 τ2 : Γ, UValIE (S n) (tsum τ1 τ2) → Γ, tsum (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseSum_pctxA, caseUVal_pctxA.
  repeat crushTyping.
  assert (ValidTy (UValIE n τ1)) by apply (UValIE_valid H).
  assert (ValidTy (UValIE n τ2)) by apply (UValIE_valid H0).
  assert (ValidTy (trec (tvar 0 r⇒ (tunit r⇒ UValIE n τ1 r⊎ UValIE n τ2)[wkm]))) by (
      destruct H1 as (? & ?);
      destruct H2 as (? & ?);
    pose proof (wsClosed_invariant H1);
    pose proof (wsClosed_invariant H2);
    cbn;
    change (apTy ?ξ ?τ) with τ[ξ] in *;
    rewrite H5, H6;
    crushValidTy).
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  rewrite fizz.
  econstructor.
  econstructor.
  rewrite <-fizz.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  econstructor; crushValidTy.
  econstructor.
  econstructor.
  rewrite fizz.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  crushValidTy.
  crushValidTy.
  econstructor.
  rewrite <-fizz.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  rewrite fizz.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  crushValidTy.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  crushValidTy.
  econstructor.
  crushValidTy.
  crushValidTy.
Qed.

Lemma caseSum_T {Γ n t τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ Γ i⊢ t : UValIE (S n) (tsum τ1 τ2) ⟫ →
  ⟪ Γ i⊢ caseSum n t τ1 τ2 : tsum (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseSum; eauto using caseSum_pctx_T with typing uval_typing.
Qed.


Lemma caseSumA_T {Γ n t τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ Γ ia⊢ t : UValIE (S n) (tsum τ1 τ2) ⟫ →
  ⟪ Γ ia⊢ caseSumA n t τ1 τ2 : tsum (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseSumA; eauto using caseSum_pctxA_T with typing uval_typing.
Qed.


Lemma caseSum_pctx_ectx {n τ τ'} : ECtx (caseSum_pctx n τ τ').
Proof. simpl; trivial. Qed.

Lemma eraseAnnot_caseSumA {n t τ₁ τ₂} :
  eraseAnnot (caseSumA n t τ₁ τ₂) = caseSum n (eraseAnnot t) τ₁ τ₂.
Proof.
  now cbn.
Qed.

Lemma caseProd_pctx_T {Γ n τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ i⊢ caseProd_pctx n τ1 τ2 : Γ, UValIE (S n) (tprod τ1 τ2) → Γ, tprod (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  econstructor;
  eauto using UValIE_valid with typing tyvalid.
Qed.

Lemma caseProd_pctxA_T {Γ n τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ ia⊢ caseProd_pctxA n τ1 τ2 : Γ, UValIE (S n) (tprod τ1 τ2) → Γ, tprod (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseProd_pctxA, caseUVal_pctxA.
  repeat crushTyping.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eapply wtOmA_tau.
  eapply ValidTy_prod; apply UValIE_valid;
    crushValidTy.
  eapply ValidTy_prod; apply UValIE_valid.
  all: crushValidTy.
Qed.

Lemma caseProd_T {Γ n t τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ Γ i⊢ t : UValIE (S n) (tprod τ1 τ2) ⟫ →
  ⟪ Γ i⊢ caseProd n t τ1 τ2 : tprod (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseProd; eauto using caseProd_pctx_T with typing uval_typing tyvalid.
Qed.

Lemma caseProdA_T {Γ n t τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ Γ ia⊢ t : UValIE (S n) (tprod τ1 τ2) ⟫ →
  ⟪ Γ ia⊢ caseProdA n t τ1 τ2 : tprod (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseProdA; eauto using caseProd_pctxA_T with typing uval_typing.
Qed.

Lemma caseProd_pctx_ectx {n τ τ'} : ECtx (caseProd_pctx n τ τ').
Proof. simpl; trivial. Qed.

Lemma eraseAnnot_caseProdA {n t τ₁ τ₂} :
  eraseAnnot (caseProdA n t τ₁ τ₂) = caseProd n (eraseAnnot t) τ₁ τ₂.
Proof.
  now cbn.
Qed.


Lemma caseArr_pctx_T {Γ n τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ i⊢ caseArr_pctx n τ1 τ2 : Γ, UValIE (S n) (tarr τ1 τ2) → Γ, tarr (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  econstructor;
  eauto using UValIE_valid with typing tyvalid.
Qed.

Lemma caseArr_pctxA_T {Γ n τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ ia⊢ caseArr_pctxA n τ1 τ2 : Γ, UValIE (S n) (tarr τ1 τ2) → Γ, tarr (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseArr_pctxA, caseUVal_pctxA.
  cbn.
  constructor.
  constructor.
  constructor.
  constructor.
  eauto using wtOmA_tau, ValidTy_arr, UValIE_valid with typing tyvalid.
  eauto using wtOmA_tau, ValidTy_arr, UValIE_valid with typing tyvalid.
  crushValidTy.
Qed.

Lemma caseArr_T {Γ n t τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ Γ i⊢ t : UValIE (S n) (tarr τ1 τ2) ⟫ →
  ⟪ Γ i⊢ caseArr n t τ1 τ2 : tarr (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseArr; eauto using caseArr_pctx_T with typing uval_typing.
Qed.

Lemma caseArrA_T {Γ n t τ1 τ2} :
  ValidTy τ1 → ValidTy τ2 →
  ⟪ Γ ia⊢ t : UValIE (S n) (tarr τ1 τ2) ⟫ →
  ⟪ Γ ia⊢ caseArrA n t τ1 τ2 : tarr (UValIE n τ1) (UValIE n τ2) ⟫.
Proof.
  unfold caseArrA; eauto using caseArr_pctxA_T with typing uval_typing tyvalid.
Qed.

Lemma caseArr_pctx_ectx {n τ τ'} : ECtx (caseArr_pctx n τ τ').
Proof. simpl; trivial. Qed.

Lemma eraseAnnot_caseArrA {n t τ₁ τ₂} :
  eraseAnnot (caseArrA n t τ₁ τ₂) = caseArr n (eraseAnnot t) τ₁ τ₂.
Proof.
  now cbn.
Qed.

(* Lemma caseRec_pctx_T {Γ n τ} : *)
(*   ⟪ ⊢ caseRec_pctx n τ : Γ, UValIE (S n) (E.trec τ) → Γ, UValIE n τ[beta1 (E.trec τ)] ⟫. *)
(* Proof. *)
(*   unfold caseRec_pctx, caseUVal_pctx. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)

(* Lemma caseRec_T {Γ n t τ} : *)
(*   ⟪ Γ ⊢ t : UValIE (S n) (E.trec τ) ⟫ → *)
(*   ⟪ Γ ⊢ caseRec n t τ : UValIE n τ[beta1 (E.trec τ)] ⟫. *)
(* Proof. *)
(*   unfold caseRec; eauto using caseRec_pctx_T with typing uval_typing. *)
(* Qed. *)

(* Lemma caseRec_pctxA_T {Γ n τ} : *)
(*   ⟪ a⊢ caseRec_pctxA n τ : Γ, UValIE (S n) (E.trec τ) → Γ, UValIE n τ[beta1 (E.trec τ)] ⟫. *)
(* Proof. *)
(*   unfold caseRec_pctxA, caseUVal_pctxA. *)
(*   repeat constructor. *)
(* Qed. *)

(* Lemma caseRecA_T {Γ n t τ} : *)
(*   ⟪ Γ a⊢ t : UValIE (S n) (E.trec τ) ⟫ → *)
(*   ⟪ Γ a⊢ caseRecA n t τ : UValIE n τ[beta1 (E.trec τ)] ⟫. *)
(* Proof. *)
(*   unfold caseRecA; eauto using caseRec_pctxA_T with typing uval_typing. *)
(* Qed. *)

(* Lemma caseRec_pctx_ectx {n τ} : ECtx (caseRec_pctx n τ). *)
(* Proof. simpl; trivial. Qed. *)

(* Lemma eraseAnnot_caseRecA {n t τ} : *)
(*   eraseAnnot (caseRecA n t τ) = caseRec n (eraseAnnot t) τ. *)
(* Proof. *)
(*   now cbn. *)
(* Qed. *)

#[export]
Hint Resolve caseUnit_T : uval_typing.
#[export]
Hint Resolve caseSum_T : uval_typing.
#[export]
Hint Resolve caseArr_T : uval_typing.
(* #[export]
Hint Resolve caseRec_T : uval_typing. *)
#[export]
Hint Resolve caseUnitA_T : uval_typing.
#[export]
Hint Resolve caseSumA_T : uval_typing.
#[export]
Hint Resolve caseArrA_T : uval_typing.
(* #[export]
Hint Resolve caseRecA_T : uval_typing. *)

(* Lemma caseUVal_eval_bool {n tunk tcunit tcbool tcprod tcsum tcarr v} : *)
(*   Value v → *)
(*   caseUVal (inBool n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcbool [beta1 v]. *)
(* Proof. *)
(*   intros vv. *)
(*   unfold caseUVal, inBool; simpl. *)
(*   crushEvalsInCaseUVal. *)
(* Qed. *)


(* Lemma caseUVal_pctx_T {Γ n tunk tcunit tcbool tcprod tcsum tcarr τ} : *)
(*   ⟪ Γ ⊢ tunk : τ ⟫ → *)
(*   ⟪ Γ ▻ tunit ⊢ tcunit : τ ⟫ → *)
(*   ⟪ Γ ▻ tbool ⊢ tcbool : τ ⟫ → *)
(*   (* ⟪ Γ ▻ (UVal n × UVal n) ⊢ tcprod : τ ⟫ → *) *)
(*   ⟪ Γ ▻ (UVal n ⊎ UVal n) ⊢ tcsum : τ ⟫ → *)
(*   ⟪ Γ ▻ (UVal n ⇒ UVal n) ⊢ tcarr : τ ⟫ → *)
(*   ⟪ ⊢ caseUVal_pctx tunk tcunit tcbool tcprod tcsum tcarr : Γ , UVal (S n) → Γ , τ ⟫. *)
(* Proof. *)
(*   unfold caseUVal_pctx.  *)
(*   crushTyping. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)


(* Lemma caseUVal_T {Γ n tscrut tunk tcunit tcbool tcprod tcsum tcarr τ} : *)
(*   ⟪ Γ ⊢ tscrut : UVal (S n) ⟫ → *)
(*   ⟪ Γ ⊢ tunk : τ ⟫ → *)
(*   ⟪ Γ ▻ tunit ⊢ tcunit : τ ⟫ → *)
(*   ⟪ Γ ▻ tbool ⊢ tcbool : τ ⟫ → *)
(*   ⟪ Γ ▻ (UVal n × UVal n) ⊢ tcprod : τ ⟫ → *)
(*   ⟪ Γ ▻ (UVal n ⊎ UVal n) ⊢ tcsum : τ ⟫ → *)
(*   ⟪ Γ ▻ (UVal n ⇒ UVal n) ⊢ tcarr : τ ⟫ → *)
(*   ⟪ Γ ⊢ caseUVal tscrut tunk tcunit tcbool tcprod tcsum tcarr : τ ⟫. *)
(* Proof. *)
(*   unfold caseUVal.  *)
(*   eauto using caseUVal_pctx_T with typing. *)
(* Qed. *)

#[export]
Hint Resolve unkUValT : uval_typing.
#[export]
Hint Resolve inUnitT : uval_typing.
#[export]
Hint Resolve inBoolT : uval_typing.
#[export]
Hint Resolve inProd_T : uval_typing.
#[export]
Hint Resolve inSum_T : uval_typing.
#[export]
Hint Resolve inArr_T : uval_typing.
(* #[export]
Hint Resolve inUnit_pctx_T : uval_typing. *)
(* #[export]
Hint Resolve inBool_pctx_T : uval_typing. *)
(* #[export]
Hint Resolve inProd_pctx_T : uval_typing. *)
(* #[export]
Hint Resolve inSum_pctx_T : uval_typing. *)
(* #[export]
Hint Resolve inArr_pctx_T : uval_typing. *)
(* #[export]
Hint Resolve caseUVal_pctx_T : uval_typing. *)
(* #[export]
Hint Resolve caseUVal_T : uval_typing. *)

Local Ltac crush :=
  repeat (subst*;
          repeat rewrite
          (*   ?protect_wkm_beta1, ?protect_wkm2_beta1, *)
          (*   ?confine_wkm_beta1, ?confine_wkm2_beta1, *)
           ?apply_wkm_beta1_up_cancel;
          (*   ?apply_up_def_S; *)
          repeat crushDbLemmasMatchH;
          repeat crushDbSyntaxMatchH;
          repeat crushStlcSyntaxMatchH;
          repeat crushTypingMatchH2;
          repeat crushTypingMatchH;
          repeat match goal with
                     [ |- _ ∧ _ ] => split
                 end;
          trivial;
          eauto with ws typing uval_typing eval
         ).

Lemma caseV0_eval_inl {v case₁ case₂ : I.Tm}:
  I.Value v →
  I.eval (caseV0 case₁ case₂)[beta1 (I.inl v)] (case₁ [beta1 v]).
Proof.
  intros vv.
  unfold caseV0; apply I.eval₀_to_eval; crush.
  change ((I.caseof (I.var 0) case₁[wkm↑] case₂ [wkm↑])[beta1 (I.inl v)]) with
  (I.caseof (I.inl v) (case₁[wkm↑][(beta1 (I.inl v))↑]) (case₂[wkm↑][(beta1 (I.inl v))↑])).
  crush.
Qed.

Lemma caseV0_eval_inr {v case₁ case₂ : I.Tm}:
  I.Value v →
  I.eval (caseV0 case₁ case₂)[beta1 (I.inr v)] (case₂ [beta1 v]).
Proof.
  intros vv.
  unfold caseV0; apply I.eval₀_to_eval; crush.
  change ((I.caseof (I.var 0) case₁[wkm↑] case₂ [wkm↑])[beta1 (I.inr v)]) with
  (I.caseof (I.inr v) (case₁[wkm↑][(beta1 (I.inr v))↑]) (case₂[wkm↑][(beta1 (I.inr v))↑])).
  crush.
Qed.

Lemma caseV0_eval {v τ₁ τ₂ case₁ case₂}:
  I.Value v → Typing empty v (tsum τ₁ τ₂) →
  (exists v', v = I.inl v' ∧ I.eval (caseV0 case₁ case₂)[beta1 v] case₁[beta1 v']) ∨
  (exists v', v = I.inr v' ∧ I.eval (caseV0 case₁ case₂)[beta1 v] case₂[beta1 v']).
Proof.
  intros vv ty.
  I.stlcCanForm; [left|right]; exists x;
  crush; eauto using caseV0_eval_inl, caseV0_eval_inr.
Qed.

Local Ltac crushEvalsInCaseUVal :=
  repeat
    (match goal with
         [ |- (I.evalStar (I.caseof (I.inl _) _ _) _) ] => (eapply (evalStepStar _); [eapply I.eval₀_to_eval; crush|])
       | [ |- (I.evalStar (I.caseof (I.inr _) _ _) _) ] => (eapply (evalStepStar _); [eapply I.eval₀_to_eval; crush|])
       | [ |- (I.evalStar ((caseV0 _ _) [beta1 (I.inl _)]) _) ] => (eapply (evalStepStar _); [eapply caseV0_eval_inl; crush|])
       | [ |- (I.evalStar ((caseV0 _ _) [beta1 (I.inr _)]) _) ] => (eapply (evalStepStar _); [eapply caseV0_eval_inr; crush|])
       | [ |- (I.evalStar ?t ?t) ] => eauto with *
     end;
     try rewrite -> apply_wkm_beta1_cancel
    ).

Lemma caseUVal_eval_unk_diverges {n τ} :
  not (Terminating (caseUVal τ (unkUVal (S n)))).
Proof.
  unfold caseUVal, unkUVal; simpl.
  eapply I.divergence_closed_under_eval.
  apply I.eval₀_to_eval.
  apply I.eval_case_inr.
  simpl; trivial.
  apply Om_div.
Qed.

Lemma caseUnit_eval_unk_diverges {n} :
  (caseUnit (unkUVal (S n)))⇑.
Proof.
  unfold caseUnit, unkUVal; simpl.
  eapply I.divergence_closed_under_eval.
  apply I.eval₀_to_eval.
  apply I.eval_case_inr.
  simpl; trivial.
  apply Om_div.
Qed.

Lemma caseArr_eval_unk_diverges {n τ1 τ2} :
  (caseArr n (unkUVal (S n)) τ1 τ2)⇑.
Proof.
  unfold caseArr, unkUVal; simpl.
  eapply I.divergence_closed_under_eval.
  apply I.eval₀_to_eval.
  apply I.eval_case_inr.
  simpl; trivial.
  apply Om_div.
Qed.

Lemma caseSum_eval_unk_diverges {n τ1 τ2} :
  (caseSum n (unkUVal (S n)) τ1 τ2)⇑.
Proof.
  unfold caseSum, unkUVal; simpl.
  eapply I.divergence_closed_under_eval.
  apply I.eval₀_to_eval.
  apply I.eval_case_inr.
  simpl; trivial.
  apply Om_div.
Qed.

Lemma caseRec_eval_unk_diverges {n τ} :
  (caseRec n (unkUVal (S n)) τ)⇑.
Proof.
  unfold caseRec, unkUVal; simpl.
  eapply I.divergence_closed_under_eval.
  apply I.eval₀_to_eval.
  apply I.eval_case_inr.
  simpl; trivial.
  apply Om_div.
Qed.

Lemma caseUVal_eval_left {v τ}:
  Value v →
  caseUVal τ (I.inl v) -->* v.
Proof.
  intro vv.
  unfold caseUVal; simpl.
  eapply (evalStepStar _).
  apply eval₀_to_eval.
  apply eval_case_inl.
  simpl; trivial.
  eauto with eval.
Qed.


Lemma canonUValS_Unit {n v} :
  I.Value v →
  ⟪ empty i⊢ v : UValIE (S n) tunit ⟫ →
  (v = I.inl I.unit) ∨ (v = I.inr I.unit).
Proof.
  unfold UValIE.
  intros.
  destruct (I.can_form_tsum H H0) as [(? & ? & ?) | (? & ? & ?)];
  [left | right];
  assert (I.Value x) by (
    subst;
    cbn in H;
    assumption);
  pose proof (I.can_form_tunit H3 H2);
  rewrite H4 in H1;
  assumption.
Qed.

Lemma canonUValS_Bool {n v} :
  I.Value v →
  ⟪ empty i⊢ v : UValIE (S n) E.tbool ⟫ →
  (v = I.inl I.true) ∨ (v = I.inl I.false) ∨ (v = I.inr I.unit).
Proof.
  unfold UValIE.
  intros.
  destruct (I.can_form_tsum H H0) as [(? & ? & ?) | (? & ? & ?)];
  subst; cbn in H; I.stlcCanForm.
  - now left.
  - now right; left.
  - now right; right.
Qed.

Lemma canonUValS_Arr {n v τ τ'} :
  I.Value v →
  ⟪ empty i⊢ v : UValIE (S n) (tarr τ τ') ⟫ →
  (exists v', I.Value v' ∧ (v = I.inl v') ∧ ⟪ empty i⊢ v' : tarr (UValIE n τ) (UValIE n τ')⟫) ∨ (v = I.inr I.unit).
Proof.
  unfold UValIE.
  intros vv ty.
  destruct (I.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
  [left | right].

  exists x.
  split.
  subst.
  cbn in vv.
  assumption.
  split.
  assumption.
  assumption.

  assert (I.Value x) by (
                         subst;
                         cbn in vv;
                         assumption
                         ).

  pose proof (I.can_form_tunit H1 H0).
  rewrite H2 in H.
  assumption.
Qed.

Lemma canonUValS_Sum {n v τ τ'} :
  I.Value v →
  ⟪ empty i⊢ v : UValIE (S n) (tsum τ τ') ⟫ →
  (exists v', I.Value v' ∧ (v = I.inl v') ∧ ⟪ empty i⊢ v' : tsum (UValIE n τ) (UValIE n τ')⟫) ∨ (v = I.inr I.unit).
Proof.
  unfold UValIE.
  intros vv ty.
  destruct (I.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
  [left | right].

  exists x.
  split.
  subst.
  cbn in vv.
  assumption.
  split.
  assumption.
  assumption.

  assert (I.Value x) by (
                         subst;
                         cbn in vv;
                         assumption
                       ).

  pose proof (I.can_form_tunit H1 H0).
  rewrite H2 in H.
  assumption.
Qed.

Lemma canonUValS_Prod {n v τ τ'} :
  I.Value v →
  ⟪ empty i⊢ v : UValIE (S n) (tprod τ τ') ⟫ →
  (exists v', I.Value v' ∧ (v = I.inl v') ∧ ⟪ empty i⊢ v' : tprod (UValIE n τ) (UValIE n τ')⟫) ∨
  (v = I.inr I.unit).
Proof.
  unfold UValIE.
  intros vv ty.
  cbn in *.
  stlcCanForm.
  - left. exists (I.pair x0 x1).
    crush.
  - now right.
Qed.

(* Lemma canonUValS_Rec {n v τ} : *)
(*   I.Value v → *)
(*   ⟪ empty ⊢ v : UValIE (S n) (E.trec τ) ⟫ → *)
(*   (exists v', I.Value v' ∧ (v = I.inl v') ∧ ⟪ empty ⊢ v' : UValIE n τ[beta1 (E.trec τ)] ⟫) ∨ (v = I.inr I.unit). *)
(* Proof. *)
(*   unfold UValIE. *)
(*   intros vv ty. *)
(*   destruct (I.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)]; *)
(*   [left | right]. *)
(*   exists x. *)
(*   split. *)
(*   subst. *)
(*   cbn in vv. *)
(*   assumption. *)
(*   split. *)
(*   assumption. *)
(*   assumption. *)

(*   assert (I.Value x) by ( *)
(*                          subst; *)
(*                          cbn in vv; *)
(*                          assumption *)
(*                        ). *)
(*   pose proof (I.can_form_tunit H1 H0). *)
(*   rewrite H2 in H. *)
(*   assumption. *)
(* Qed. *)


(* Lemma canonUVal_Arr {n v τ τ'} : *)
(*   I.Value v → *)
(*   ⟪ empty ⊢ v : UValIE n (tarr τ τ') ⟫ → *)
(*   (v = I.unit) ∨ (exists v', I.Value v' ∧ (v = I.inl v') ∧ ⟪ empty ⊢ v' : tarr (UValIE n τ) (UValIE n τ')⟫) ∨ (v = I.inr I.unit). *)
(* Proof. *)
(*   intros. *)
(*   destruct n as [? | ?]. *)
(*   left. *)
(*   unfold UValIE in H0. *)
(*   I.stlcCanForm. *)
(*   reflexivity. *)

(*   right. *)
(*   apply (canonUValS_Arr H). *)


(* NOTE: for compatibility lemmas, we might need a UVal context and accompanying lemmas *)

(* Lemma canonUValS {n v} : *)
(*   ⟪ empty ⊢ v : UVal (S n) ⟫ → Value v → *)
(*   (v = unkUVal (S n)) ∨ *)
(*   (∃ v', v = inUnit n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tunit ⟫) ∨ *)
(*   (∃ v', v = inBool n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tbool ⟫) ∨ *)
(*   (∃ v', v = inProd n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n × UVal n ⟫) ∨ *)
(*   (∃ v', v = inSum n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n ⊎ UVal n ⟫) ∨ *)
(*   (∃ v', v = inArr n v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n ⇒ UVal n ⟫). *)
(* Proof. *)
(*   intros ty vv. *)
(*   unfold UVal in ty; simpl. *)
(*   (* Apply canonical form lemmas but only as far as we need. *) *)
(*   stlcCanForm1; *)
(*     [left|right;stlcCanForm1; *)
(*        [left|right;stlcCanForm1; *)
(*           [left|right;stlcCanForm1; *)
(*                 [left|right;stlcCanForm1; *)
(*                       [right|left]]]]]. *)
(*   - stlcCanForm; crush. *)
(*   - exists x0; crush. *)
(*   - exists x; crush. *)
(*   - exists x0; crush. *)
(*   - exists x; crush. *)
(*   - exists x; crush. *)
(* Qed. *)

(* Lemma canonUVal {n v} : *)
(*   ⟪ empty ⊢ v : UVal n ⟫ → Value v → *)
(*   (v = unkUVal n) ∨ *)
(*   ∃ n', n = S n' ∧  *)
(*         ((∃ v', v = inUnit n' v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tunit ⟫) ∨ *)
(*          (∃ v', v = inBool n' v' ∧ Value v' ∧ ⟪ empty ⊢ v' : tbool ⟫) ∨ *)
(*          (∃ v', v = inProd n' v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n' × UVal n' ⟫) ∨ *)
(*          (∃ v', v = inSum n' v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n' ⊎ UVal n' ⟫) ∨ *)
(*          (∃ v', v = inArr n' v' ∧ Value v' ∧ ⟪ empty ⊢ v' : UVal n' ⇒ UVal n' ⟫)). *)
(* Proof. *)
(*   intros ty vv. *)
(*   destruct n. *)
(*   - left. unfold UVal, unkUVal in *. stlcCanForm. trivial. *)
(*   - destruct (canonUValS ty vv) as [? | ?]. *)
(*     + left; crush. *)
(*     + right; crush.  *)
(* Qed. *)

(* Ltac canonUVal := *)
(*   match goal with *)
(*       [ H : Value ?v, H' : ⟪ empty ⊢ ?v : UVal 0 ⟫ |- _ ] => *)
(*       (unfold UVal in H'; stlcCanForm; subst) *)
(*     | [ H : Value ?v, H' : ⟪ empty ⊢ ?v : UVal (S _) ⟫ |- _ ] => *)
(*       (destruct (canonUValS H' H) as  *)
(*           [?| [(? & ? & ? & ?) *)
(*               |[(? & ? & ? & ?) *)
(*                |[(? & ? & ? & ?) *)
(*                 |[(? & ? & ? & ?) *)
(*                  |(? & ? & ? & ?)]]]]]; subst) *)
(*     | [ H : Value ?v, H' : ⟪ empty ⊢ ?v : UVal (S _ + _) ⟫ |- _ ] => *)
(*       (destruct (canonUValS H' H) as  *)
(*           [?| [(? & ? & ? & ?) *)
(*               |[(? & ? & ? & ?) *)
(*                |[(? & ? & ? & ?) *)
(*                 |[(? & ? & ? & ?) *)
(*                  |(? & ? & ? & ?)]]]]]; subst) *)
(*     | [ H : Value ?v, H' : ⟪ empty ⊢ ?v : UVal _ ⟫ |- _ ] => *)
(*       (destruct (canonUVal H' H) as  *)
(*           [?| (? & ? & [(? & ? & ? & ?) *)
(*                        |[(? & ? & ? & ?) *)
(*                         |[(? & ? & ? & ?) *)
(*                          |[(? & ? & ? & ?) *)
(*                           |(? & ? & ? & ?)]]]])]; subst) *)
(*   end. *)

(* Lemma caseUVal_eval_unk {n : nat} {tunk tcunit tcbool tcprod tcsum tcarr : I.Tm} : *)
(*   I.evalStar (caseUVal (I.inr I.unit) tunk tcunit tcbool tcprod tcsum tcarr) tunk. *)
(* Proof. *)
(*   unfold caseUVal, unkUVal; simpl. *)
(*   (* why doesn't crush do the following? *) *)
(*   assert (Value (inl unit)) by (simpl; trivial). *)
(*   crushEvalsInCaseUVal. *)
(*   eauto with *. *)
(* Qed. *)

(* Lemma caseUVal_eval_unit {n tunk tcunit tcbool tcprod tcsum tcarr v} : *)
(*   Value v → *)
(*   caseUVal (inUnit n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcunit [beta1 v]. *)
(* Proof. *)
(*   intros vv. *)
(*   unfold caseUVal, inUnit; simpl. *)
(*   crushEvalsInCaseUVal. *)
(* Qed. *)

(* Lemma caseUVal_eval_bool {n tunk tcunit tcbool tcprod tcsum tcarr v} : *)
(*   Value v → *)
(*   caseUVal (inBool n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcbool [beta1 v]. *)
(* Proof. *)
(*   intros vv. *)
(*   unfold caseUVal, inBool; simpl. *)
(*   crushEvalsInCaseUVal. *)
(* Qed. *)

(* Lemma caseUVal_eval_prod {n tunk tcunit tcbool tcprod tcsum tcarr v} : *)
(*   Value v → *)
(*   caseUVal (inProd n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcprod [beta1 v]. *)
(* Proof. *)
(*   intros vv. *)
(*   unfold caseUVal, inProd; simpl. *)
(*   crushEvalsInCaseUVal. *)
(* Qed. *)

(* Lemma caseUVal_eval_sum {n tunk tcunit tcbool tcprod tcsum tcarr v} : *)
(*   Value v → *)
(*   caseUVal (inSum n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcsum [beta1 v]. *)
(* Proof. *)
(*   intros vv. *)
(*   unfold caseUVal, inSum; simpl. *)
(*   crushEvalsInCaseUVal. *)
(* Qed. *)

(* Lemma caseUVal_eval_arr {n tunk tcunit tcbool tcprod tcsum tcarr v} : *)
(*   Value v → *)
(*   caseUVal (inArr n v) tunk tcunit tcbool tcprod tcsum tcarr -->* tcarr [beta1 v]. *)
(* Proof. *)
(*   intros vv. *)
(*   unfold caseUVal, inArr; simpl. *)
(*   crushEvalsInCaseUVal. *)
(* Qed. *)

(* Lemma caseUVal_sub {t tunk tcunit tcbool tcprod tcsum tcarr} γ : *)
(*   (caseUVal t tunk tcunit tcbool tcprod tcsum tcarr)[γ] = *)
(*   caseUVal (t[γ]) (tunk[γ]) (tcunit[γ↑]) (tcbool[γ↑]) (tcprod[γ↑]) (tcsum[γ↑]) (tcarr[γ↑]). *)
(* Proof. *)
(*   unfold caseUVal, caseUVal_pctx, caseV0. cbn.  *)
(*   crush;  *)
(*     rewrite <- ?apply_wkm_comm, <- ?(apply_wkm_up_comm);  *)
(*     reflexivity. *)
(* Qed. *)


(* Arguments caseUVal tscrut tunk tcunit tcbool tcprod tcsum tcarr : simpl never. *)
(* Arguments caseUVal_pctx tunk tcunit tcbool tcprod tcsum tcarr : simpl never. *)

(* Lemma caseUVal_pctx_ECtx {tunk tcunit tcbool tcprod tcsum tcarr} : *)
(*   ECtx (caseUVal_pctx tunk tcunit tcbool tcprod tcsum tcarr). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)


(* Definition caseUVal (n : nat) (tscrut tunk tcunit tcbool tcprod tcsum tcarr : Tm) := *)


(* Definition caseUnit_pctx := caseUVal_pctx (stlcOmega tunit) (var 0) (stlcOmega tunit) (stlcOmega tunit) (stlcOmega tunit) (stlcOmega tunit). *)
(* Definition caseBool_pctx := caseUVal_pctx (stlcOmega tbool) (stlcOmega tbool) (var 0) (stlcOmega tbool) (stlcOmega tbool) (stlcOmega tbool). *)
(* Definition caseProd_pctx n := caseUVal_pctx (stlcOmega (UVal n × UVal n)) (stlcOmega (UVal n × UVal n)) (stlcOmega (UVal n × UVal n)) (var 0) (stlcOmega (UVal n × UVal n)) (stlcOmega (UVal n × UVal n)). *)
(* Definition caseSum_pctx n := caseUVal_pctx (stlcOmega (UVal n ⊎ UVal n)) (stlcOmega (UVal n ⊎ UVal n)) (stlcOmega (UVal n ⊎ UVal n)) (stlcOmega (UVal n ⊎ UVal n)) (var 0) (stlcOmega (UVal n ⊎ UVal n)). *)
(* Definition caseArr_pctx n := caseUVal_pctx (stlcOmega (UVal n ⇒ UVal n)) (stlcOmega (UVal n ⇒ UVal n)) (stlcOmega (UVal n ⇒ UVal n)) (stlcOmega (UVal n ⇒ UVal n)) (stlcOmega (UVal n ⇒ UVal n)) (var 0). *)
(* Definition caseUnit t := pctx_app t caseUnit_pctx. *)
(* Definition caseBool t := pctx_app t caseBool_pctx. *)
(* Definition caseProd n t := pctx_app t (caseProd_pctx n). *)
(* Definition caseSum n t := pctx_app t (caseSum_pctx n). *)
(* Definition caseArr n t := pctx_app t (caseArr_pctx n). *)

(* Lemma caseUnit_pctx_ECtx : ECtx caseUnit_pctx. *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* Lemma caseBool_pctx_ECtx : ECtx caseBool_pctx. *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* Lemma caseProd_pctx_ECtx {n}: ECtx (caseProd_pctx n). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* Lemma caseSum_pctx_ECtx {n}: ECtx (caseSum_pctx n). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* Lemma caseArr_pctx_ECtx {n}: ECtx (caseArr_pctx n). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

Lemma caseUnit_sub {t γ} :
  (caseUnit t) [γ] = caseUnit (t [γ]).
Proof.
  unfold caseUnit; crush.
Qed.

(* Lemma caseBool_sub {t γ} : *)
(*   caseBool t [γ] = caseBool (t [γ]). *)
(* Proof. *)
(*   unfold caseBool; crush. *)
(* Qed. *)

(* Lemma caseProd_sub {n t γ} : *)
(*   caseProd n t [γ] = caseProd n (t [γ]). *)
(* Proof. *)
(*   unfold caseProd; crush. *)
(* Qed. *)

Lemma caseSum_sub {n t τ τ' γ} :
  (caseSum n t τ τ') [γ] = caseSum n (t [γ]) τ τ'.
Proof.
  unfold caseSum; crush.
Qed.

Lemma caseArr_sub {n t τ τ' γ} :
  (caseArr n t τ τ') [γ] = caseArr n (t [γ]) τ τ'.
Proof.
  unfold caseArr; crush.
Qed.

Lemma caseRec_sub {n t τ γ} :
  (caseRec n t τ) [γ] = caseRec n (t [γ]) τ.
Proof.
  unfold caseRec; crush.
Qed.

Arguments caseUnit t : simpl never.
Arguments caseSum n t τ1 τ2 : simpl never.
Arguments caseArr n t τ1 τ2 : simpl never.
Arguments caseRec n t τ : simpl never.

Arguments caseUnitA n t : simpl never.
Arguments caseSumA n t τ1 τ2 : simpl never.
Arguments caseArrA n t τ1 τ2 : simpl never.
Arguments caseRecA n t τ : simpl never.

(* Lemma caseUnit_pctx_T {Γ n} :  *)
(*   ⟪ ⊢ caseUnit_pctx : Γ , UVal (S n) → Γ , tunit ⟫. *)
(* Proof. *)
(*   unfold caseUnit_pctx. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)

(* Lemma caseUnit_T {Γ n t} :  *)
(*   ⟪ Γ ⊢ t : UVal (S n) ⟫ → ⟪ Γ ⊢ caseUnit t : tunit ⟫. *)
(* Proof. *)
(*   unfold caseUnit. *)
(*   eauto using caseUnit_pctx_T with typing. *)
(* Qed. *)

(* Lemma caseBool_pctx_T {Γ n} :  *)
(*   ⟪ ⊢ caseBool_pctx : Γ , UVal (S n) → Γ , tbool ⟫. *)
(* Proof. *)
(*   unfold caseBool_pctx. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)

(* Lemma caseBool_T {Γ n t} :  *)
(*   ⟪ Γ ⊢ t : UVal (S n) ⟫ → ⟪ Γ ⊢ caseBool t : tbool ⟫. *)
(* Proof. *)
(*   unfold caseBool. *)
(*   eauto using caseBool_pctx_T with typing. *)
(* Qed. *)

(* Lemma caseProd_pctx_T {Γ n} :  *)
(*   ⟪ ⊢ caseProd_pctx n : Γ , UVal (S n) → Γ , UVal n × UVal n ⟫. *)
(* Proof. *)
(*   unfold caseProd_pctx. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)

(* Lemma caseProd_T {Γ n t} :  *)
(*   ⟪ Γ ⊢ t : UVal (S n) ⟫ → ⟪ Γ ⊢ caseProd n t : UVal n × UVal n ⟫. *)
(* Proof. *)
(*   unfold caseProd. *)
(*   eauto using caseProd_pctx_T with typing. *)
(* Qed. *)

(* Lemma caseSum_pctx_T {Γ n} :  *)
(*   ⟪ ⊢ caseSum_pctx n : Γ , UVal (S n) → Γ , UVal n ⊎ UVal n ⟫. *)
(* Proof. *)
(*   unfold caseSum_pctx. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)

(* Lemma caseSum_T {Γ n t} :  *)
(*   ⟪ Γ ⊢ t : UVal (S n) ⟫ → ⟪ Γ ⊢ caseSum n t : UVal n ⊎ UVal n ⟫. *)
(* Proof. *)
(*   unfold caseSum. *)
(*   eauto using caseSum_pctx_T with typing. *)
(* Qed. *)

(* Lemma caseArr_pctx_T {Γ n} :  *)
(*   ⟪ ⊢ caseArr_pctx n : Γ , UVal (S n) → Γ , UVal n ⇒ UVal n ⟫. *)
(* Proof. *)
(*   unfold caseArr_pctx. *)
(*   eauto with typing uval_typing. *)
(* Qed. *)

(* Lemma caseArr_T {Γ n t} :  *)
(*   ⟪ Γ ⊢ t : UVal (S n) ⟫ → ⟪ Γ ⊢ caseArr n t : UVal n ⇒ UVal n ⟫. *)
(* Proof. *)
(*   unfold caseArr. *)
(*   eauto using caseArr_pctx_T with typing. *)
(* Qed. *)

Lemma UVal_eq {n τ1 τ2} :
  ValidTy τ1 -> ValidTy τ2 ->
  ⟪ τ1 ≗ τ2 ⟫ -> UValIE n τ1 = UValIE n τ2.
Proof.
  revert τ1 τ2.
  induction n; intros τ1 τ2 vτ1 vτ2 eq; [reflexivity|].
  unfold UValIE.
  assert (⟪ unfoldn (LMC τ1) τ1 ≗ unfoldn (LMC τ2) τ2 ⟫).
  {
    refine (eq_trans_contr _ _ (eq_trans_contr _ eq _)); crushValidTy.
    eapply ty_eq_peel_recs_left; crushValidTy.
    eapply tyeq_refl.
    eapply ty_eq_peel_recs; crushValidTy.
    eapply tyeq_refl.
  }
  assert (ValidTy (unfoldn (LMC τ1) τ1)) by eauto using ValidTy_unfoldn.
  assert (ValidTy (unfoldn (LMC τ2) τ2)) by eauto using ValidTy_unfoldn.
  assert (LMC (unfoldn (LMC τ1) τ1) = 0) by (eapply unfoldn_LMC; crushValidTy).
  assert (LMC (unfoldn (LMC τ2) τ2) = 0) by (eapply unfoldn_LMC; crushValidTy).
  destruct H; cbn; f_equal; f_equal; try eapply IHn; try assumption.
  now eapply ValidTy_invert_arr in H0.
  now eapply ValidTy_invert_arr in H1.
  now eapply ValidTy_invert_arr in H0.
  now eapply ValidTy_invert_arr in H1.
  now eapply ValidTy_invert_sum in H0.
  now eapply ValidTy_invert_sum in H1.
  now eapply ValidTy_invert_sum in H0.
  now eapply ValidTy_invert_sum in H1.
  now eapply ValidTy_invert_prod in H0.
  now eapply ValidTy_invert_prod in H1.
  now eapply ValidTy_invert_prod in H0.
  now eapply ValidTy_invert_prod in H1.
  exfalso; cbn in H2; lia.
  exfalso; cbn in H3; lia.
Qed.

Lemma UVal_sub {X : Type} {vrX : Vr X} {wkX : Wk X} {liftXTy : Lift X Ty} :
  forall n {σ : Sub X} τ, (UValIE n τ) [ σ ] = UValIE n τ.
Proof.
  intros n.
  induction n; [reflexivity|].
  intros σ τ.
  unfold UValIE.
  destruct (unfoldn (LMC τ) τ); cbn; repeat f_equal; now eapply IHn.
Qed.

Lemma UVal_eq_unfoldn {n τ} :
  ValidTy τ ->
  UValIE n τ = UValIE n (unfoldn (LMC τ) τ).
Proof.
  intros vτ.
  eapply UVal_eq;
  eauto using ValidTy_unfoldn.
  eapply tyeq_symm, ty_eq_unfoldn.
  crushValidTy.
Qed.
