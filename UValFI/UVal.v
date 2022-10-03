Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.CanForm.
Require Import StlcIso.Fix.
Require Import StlcIso.Size.
Require Import StlcIso.TypeSafety.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import StlcFix.Size.
Require Import StlcFix.StlcOmega.
Require Import StlcFix.TypeSafety.
Require Import Common.Relations.

Module F.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
  Include StlcFix.SpecAnnot.
  Include StlcFix.LemmasTyping.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.CanForm.
  Include StlcFix.Size.
  Include StlcFix.TypeSafety.
End F.

Module I.
  Include RecTypes.SpecTypes.
  Include RecTypes.InstTy.
  Include RecTypes.LemmasTypes.

  Include StlcIso.SpecEvaluation.
  Include StlcIso.SpecSyntax.
  Include StlcIso.SpecTyping.
  Include StlcIso.LemmasTyping.
  Include StlcIso.LemmasEvaluation.
  Include StlcIso.CanForm.
  Include StlcIso.Fix.
  Include StlcIso.Size.
  Include StlcIso.TypeSafety.
End I.

Definition UValFI' := fun (S : I.Ty -> F.Ty) (τ : I.Ty) =>
  let τl := match τ with
            | I.tunit => F.tunit
            | I.tbool => F.tbool
            | I.tarr τ1 τ2 as τ => F.tarr (S τ1) (S τ2)
            | I.tprod τ1 τ2 as τ => F.tprod (S τ1) (S τ2)
            | I.tsum τ1 τ2 =>
              let σ1 := S τ1 in
              let σ2 := S τ2 in
              F.tsum σ1 σ2
            | I.trec τ => S τ[beta1 (I.trec τ)]
            | I.tvar i => F.tunit
            end
  in F.tsum τl F.tunit.

Arguments UValFI'/ S τ.

Fixpoint UValFI (n : nat) (τ : I.Ty) {struct n} : F.Ty :=
  match n with
    | 0 => F.tunit
    | S n => UValFI' (UValFI n) τ
  end.

Arguments UValFI !n !τ.

Definition unkUVal (n : nat) : F.Tm :=
  match n with
  | 0 => F.unit
  | _ => F.inr F.unit
  end.

Definition unkUValA (n : nat) (τ : I.Ty) : F.TmA :=
  match n with
  | 0 => F.a_unit
  | (S n) => F.a_inr (match τ with
      | I.tunit => F.tunit
      | I.tbool => F.tbool
      | I.tarr τ1 τ2 as τ => F.tarr (UValFI n τ1) (UValFI n τ2)
      | I.tprod τ1 τ2 as τ => F.tprod (UValFI n τ1) (UValFI n τ2)
      | I.tsum τ1 τ2 =>
        let σ1 := UValFI n τ1 in
        let σ2 := UValFI n τ2 in
        F.tsum σ1 σ2
      | I.trec τ => UValFI n τ[beta1 (I.trec τ)]
      | I.tvar i => F.tunit
      end) F.tunit F.a_unit
  end.

Lemma unkUVal_unkUValA {n τ} : unkUVal n = eraseAnnot (unkUValA n τ).
Proof.
  destruct n;
  now cbn.
Qed.

Lemma unkUVal_Value (n : nat) : F.Value (unkUVal n).
Proof.
  case n; simpl; trivial.
Qed.

Lemma unkUValT {Γ n τ} : F.Typing Γ (unkUVal n) (UValFI n τ).
Proof.
  induction n;
  eauto using F.Typing.
Qed.

Lemma unkUValAT {Γ n τ} : F.AnnotTyping Γ (unkUValA n τ) (UValFI n τ).
Proof.
  induction n;
  eauto using F.AnnotTyping.
Qed.

#[export]
Hint Resolve unkUValT : uval_typing.
#[export]
Hint Resolve unkUValAT : uval_typing.

(* Definition constr_uvalfi {Γ} (n : nat) (τ : I.Ty) (t : F.Tm) {P : ClosedTy τ} {Q : F.Typing Γ t (@UValFI n τ P)} : F.Tm := *)
(*   F.inl t. *)

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

Lemma inUnitT {Γ n t} : ⟪ Γ ⊢ t : F.tunit ⟫ → ⟪ Γ ⊢ F.inl t : UValFI (S n) I.tunit ⟫.
Proof.
  intuition.
Qed.

(* Arguments inUnit n t : simpl never. *)

Definition inBool_pctx (n : nat) : PCtx := pinl phole.
Definition inBool (n : nat) (t : Tm): Tm := pctx_app t (inBool_pctx n).

Arguments inBool_pctx /n.

Lemma inBool_pctx_T {Γ n} : ⟪ ⊢ inBool_pctx n : Γ , tbool → Γ , UValFI (S n) I.tbool ⟫.
Proof.
  unfold inBool_pctx. unfold UValFI. crushTyping.
Qed.

Lemma inBoolT {Γ n t} : ⟪ Γ ⊢ t : tbool ⟫ → ⟪ Γ ⊢ inBool n t : UValFI (S n) I.tbool ⟫.
Proof.
  unfold inBool. eauto using inBool_pctx_T with typing.
Qed.

Lemma inBool_Value {n v} : Value v → Value (inBool n v).
Proof.
  simpl; trivial.
Qed.

Definition inProd_pctx (n : nat) : PCtx := pinl phole.
Definition inProd (n : nat) (t : Tm) : Tm := pctx_app t (inProd_pctx n).

Lemma inProd_pctx_T {Γ n τ₁ τ₂} : ⟪ ⊢ inProd_pctx n : Γ , UValFI n τ₁ × UValFI n τ₂ → Γ , UValFI (S n) (I.tprod τ₁ τ₂)⟫.
Proof.
  unfold inProd_pctx. crushTyping.
Qed.

Lemma inProd_T {Γ n t τ₁ τ₂} : ⟪ Γ ⊢ t : UValFI n τ₁ × UValFI n τ₂ ⟫ → ⟪ Γ ⊢ inProd n t : UValFI (S n) (I.tprod τ₁ τ₂) ⟫.
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

(* Lemma inArr_pctx_T {Γ n} : ⟪ ⊢ inArr_pctx n : Γ , UValFI n ⇒ UValFI n → Γ , UValFI (S n) ⟫. *)
(* Proof. *)
(*   unfold inArr_pctx. crushTyping. *)
(* Qed. *)

Lemma inArr_T {Γ n t τ τ'} : ⟪ Γ ⊢ t : F.tarr (UValFI n τ) (UValFI n τ') ⟫ → ⟪ Γ ⊢ F.inl t : UValFI (S n) (I.tarr τ τ') ⟫.
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

Lemma inSum_T {Γ n t τ τ'} : ⟪ Γ ⊢ t : F.tsum (UValFI n τ) (UValFI n τ') ⟫ → ⟪ Γ ⊢ F.inl t : UValFI (S n) (I.tsum τ τ') ⟫.
Proof.
  intuition.
Qed.

(* Lemma inSum_Value {n v} : Value v → Value (inSum n v). *)
(* Proof. *)
(*   simpl; trivial. *)
(* Qed. *)

(* (t : F.Tm) {P : F.Typing t (UValFI n I.tunit)} : F.Tm := *)
Definition case_uvalfi_unit (n : nat) : F.Tm :=
  let P := UnitClosed 0 in
  let τ := UValFI (S n) I.tunit in
  let t := F.caseof (F.var 0) (F.var 0) (F.Om F.tunit) in
  F.abs τ t.

Definition case_uvalfi_arr (n : nat) (τ1 τ2 : I.Ty) : F.Tm :=
  let τ := @UValFI (S n) (I.tarr τ1 τ2) in
  let τ' := F.tarr (UValFI n τ1) (UValFI n τ2) in
  let t := F.caseof (F.var 0) (F.var 0) (F.Om τ') in
  F.abs τ t.

Lemma uvalfi_expand_arr {n τ1 τ2} :
  UValFI (S n) (I.tarr τ1 τ2) = F.tsum (F.tarr (UValFI n τ1) (UValFI n τ2)) F.tunit.
Proof.
  reflexivity.
Qed.

Lemma case_uval_arr_typing {Γ n τ1 τ2} :
  let τ := I.tarr τ1 τ2 in
  let uval_dest := case_uvalfi_arr n τ1 τ2 in
  let arg_type := UValFI (S n) τ in
  let ret_type := F.tarr (UValFI n τ1) (UValFI n τ2) in
  let type := F.tarr arg_type ret_type in
  F.Typing Γ uval_dest type.
Proof.
  intros.
  unfold uval_dest.
  unfold type.
  unfold arg_type.
  unfold ret_type.
  (* unfold uval_dest, arg_type, ret_type, type, case_uvalfi_arr. *)
  (* crushTyping. *)
  constructor.
  unfold τ.
  apply (@F.WtCaseof (F.evar Γ arg_type) (F.var 0) (F.var 0) (F.Om ret_type) ret_type F.tunit ret_type).
  unfold arg_type.
  unfold ret_type.
  constructor.
  simpl.
  constructor.
  constructor.
  constructor.
  apply wtOm_tau.
Qed.


Definition case_uvalfi_tsum (n : nat) (τ1 τ2 : I.Ty) : F.Tm :=
  let τ := UValFI (S n) (I.tsum τ1 τ2) in
  let τ' := F.tsum (UValFI n τ1) (@UValFI n τ2) in
  let t := F.caseof (F.var 0) (F.var 0) (F.Om τ') in
  F.abs τ t.

Definition case_uvalfi_trec (n : nat) (τb : I.Ty) : F.Tm :=
  let τ_rec := I.trec τb in
  let τ := UValFI (S n) τ_rec in
  let τ' := UValFI n τb[beta1 τ_rec] in
  let t := F.caseof (F.var 0) (F.var 0) (F.Om τ') in
  F.abs τ t.

Definition caseV0 (case₁ : F.Tm) (case₂ : F.Tm) : F.Tm :=
  F.caseof (F.var 0) (case₁ [wkm↑]) (case₂[wkm↑]).

Lemma caseV0_T {Γ : F.Env} {τ₁ τ₂ τ : F.Ty} {case₁ case₂ : F.Tm} :
  F.Typing (F.evar Γ τ₁) case₁ τ →
  F.Typing (F.evar Γ τ₂) case₂ τ →
  F.Typing (F.evar Γ (F.tsum τ₁ τ₂)) (caseV0 case₁ case₂) τ.
Proof.
  unfold caseV0.
  F.crushTyping.
Qed.

#[export]
Hint Resolve caseV0_T : uval_typing.

Definition caseUVal_pctx (τ : F.Ty) := F.pcaseof₁ F.phole (F.var 0) (stlcOmega τ).
Definition caseUVal_pctxA (τ : F.Ty) := F.a_pcaseof₁ τ F.tunit τ F.a_phole (F.a_var 0) (stlcOmegaA τ).

Definition caseUnit_pctx := caseUVal_pctx F.tunit.
Definition caseUnit_pctxA (n : nat) := caseUVal_pctxA F.tunit.
Definition caseBool_pctx := caseUVal_pctx F.tbool.
Definition caseBool_pctxA (n : nat) := caseUVal_pctxA F.tbool.
Definition caseProd_pctx (n : nat) (τ1 τ2 : I.Ty) := caseUVal_pctx (F.tprod (UValFI n τ1) (UValFI n τ2)).
Definition caseProd_pctxA (n : nat) (τ1 τ2 : I.Ty) := caseUVal_pctxA (F.tprod (UValFI n τ1) (UValFI n τ2)).
Definition caseSum_pctx (n : nat) (τ1 τ2 : I.Ty) := caseUVal_pctx (F.tsum (UValFI n τ1) (UValFI n τ2)).
Definition caseSum_pctxA (n : nat) (τ1 τ2 : I.Ty) := caseUVal_pctxA (F.tsum (UValFI n τ1) (UValFI n τ2)).
Definition caseArr_pctx (n : nat) (τ1 τ2 : I.Ty) := caseUVal_pctx (F.tarr (UValFI n τ1) (UValFI n τ2)).
Definition caseArr_pctxA (n : nat) (τ1 τ2 : I.Ty) := caseUVal_pctxA (F.tarr (UValFI n τ1) (UValFI n τ2)).
Definition caseRec_pctx (n : nat) (τ : I.Ty) := caseUVal_pctx (UValFI n τ[beta1 (I.trec τ)]).
Definition caseRec_pctxA (n : nat) (τ : I.Ty) := caseUVal_pctxA (UValFI n τ[beta1 (I.trec τ)]).

Definition caseUVal (τ : F.Ty) (t : F.Tm) := F.pctx_app t (caseUVal_pctx τ).
Definition caseUValA (τ : F.Ty) (t : F.TmA) := F.pctxA_app t (caseUVal_pctxA τ).

(* Definition caseUValIso (n : nat) (τ : I.Ty) (t : F.Tm) := caseUVal (UValFI n τ) t. *)
(* Definition caseUValIsoA (n : nat) (τ' τ : I.Ty) (t : F.Tm) := caseUVal (UValFI n τ) t. *)

Arguments caseUVal_pctx τ : simpl never.
Arguments caseUVal τ t : simpl never.

Definition caseUnit t := F.pctx_app t caseUnit_pctx.
Definition caseUnitA n t := F.pctxA_app t (caseUnit_pctxA n).
Definition caseBool t := F.pctx_app t caseBool_pctx.
Definition caseBoolA n t := F.pctxA_app t (caseBool_pctxA n).
Definition caseSum n t τ1 τ2 := F.pctx_app t (caseSum_pctx n τ1 τ2).
Definition caseSumA n t τ1 τ2 := F.pctxA_app t (caseSum_pctxA n τ1 τ2).
Definition caseProd n t τ1 τ2 := F.pctx_app t (caseProd_pctx n τ1 τ2).
Definition caseProdA n t τ1 τ2 := F.pctxA_app t (caseProd_pctxA n τ1 τ2).
Definition caseArr n t τ1 τ2 := F.pctx_app t (caseArr_pctx n τ1 τ2).
Definition caseArrA n t τ1 τ2 := F.pctxA_app t (caseArr_pctxA n τ1 τ2).
Definition caseRec n t τ := F.pctx_app t (caseRec_pctx n τ).
Definition caseRecA n t τ := F.pctxA_app t (caseRec_pctxA n τ).

Lemma caseUnit_pctx_T {Γ n} :
  ⟪ ⊢ caseUnit_pctx : Γ, UValFI (S n) I.tunit → Γ, F.tunit ⟫.
Proof.
  unfold caseUnit_pctx, caseUVal_pctx.
  eauto with typing uval_typing.
Qed.

Lemma caseUnit_pctxA_T {Γ n} :
  ⟪ a⊢ caseUnit_pctxA n : Γ, UValFI (S n) I.tunit → Γ, F.tunit ⟫.
Proof.
  unfold caseUnit_pctxA, caseUVal_pctxA.
  cbn.
  repeat constructor.
Qed.

Lemma caseUnit_T {Γ n t} :
  ⟪ Γ ⊢ t : UValFI (S n) I.tunit ⟫ →
  ⟪ Γ ⊢ caseUnit t : F.tunit ⟫.
Proof.
  unfold caseUnit; eauto using caseUnit_pctx_T with typing uval_typing.
Qed.

Lemma caseUnitA_T {Γ n t} :
  ⟪ Γ a⊢ t : UValFI (S n) I.tunit ⟫ →
  ⟪ Γ a⊢ caseUnitA n t : F.tunit ⟫.
Proof.
  unfold caseUnitA; eauto using caseUnit_pctxA_T with typing uval_typing.
Qed.

Lemma caseUnit_pctx_ectx : ECtx caseUnit_pctx.
Proof. simpl; trivial. Qed.

Lemma caseBool_pctx_T {Γ n} :
  ⟪ ⊢ caseBool_pctx : Γ, UValFI (S n) I.tbool → Γ, F.tbool ⟫.
Proof.
  unfold caseBool_pctx, caseUVal_pctx.
  eauto with typing uval_typing.
Qed.

Lemma caseBool_pctxA_T {Γ n} :
  ⟪ a⊢ caseBool_pctxA n : Γ, UValFI (S n) I.tbool → Γ, F.tbool ⟫.
Proof.
  unfold caseBool_pctxA, caseUVal_pctxA.
  cbn.
  repeat constructor.
Qed.

Lemma caseBool_T {Γ n t} :
  ⟪ Γ ⊢ t : UValFI (S n) I.tbool ⟫ →
  ⟪ Γ ⊢ caseBool t : F.tbool ⟫.
Proof.
  unfold caseBool; eauto using caseBool_pctx_T with typing uval_typing.
Qed.

Lemma caseBoolA_T {Γ n t} :
  ⟪ Γ a⊢ t : UValFI (S n) I.tbool ⟫ →
  ⟪ Γ a⊢ caseBoolA n t : F.tbool ⟫.
Proof.
  unfold caseBoolA; eauto using caseBool_pctxA_T with typing uval_typing.
Qed.

Lemma caseBool_pctx_ectx : ECtx caseBool_pctx.
Proof. simpl; trivial. Qed.

Lemma caseSum_pctx_T {Γ n τ1 τ2} :
  ⟪ ⊢ caseSum_pctx n τ1 τ2 : Γ, UValFI (S n) (I.tsum τ1 τ2) → Γ, F.tsum (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseSum_pctx, caseUVal_pctx.
  eauto with typing uval_typing.
Qed.

Lemma caseSum_pctxA_T {Γ n τ1 τ2} :
  ⟪ a⊢ caseSum_pctxA n τ1 τ2 : Γ, UValFI (S n) (I.tsum τ1 τ2) → Γ, F.tsum (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseSum_pctxA, caseUVal_pctxA.
  repeat constructor.
Qed.


Lemma caseSum_T {Γ n t τ1 τ2} :
  ⟪ Γ ⊢ t : UValFI (S n) (I.tsum τ1 τ2) ⟫ →
  ⟪ Γ ⊢ caseSum n t τ1 τ2 : F.tsum (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseSum; eauto using caseSum_pctx_T with typing uval_typing.
Qed.


Lemma caseSumA_T {Γ n t τ1 τ2} :
  ⟪ Γ a⊢ t : UValFI (S n) (I.tsum τ1 τ2) ⟫ →
  ⟪ Γ a⊢ caseSumA n t τ1 τ2 : F.tsum (UValFI n τ1) (UValFI n τ2) ⟫.
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
  ⟪ ⊢ caseProd_pctx n τ1 τ2 : Γ, UValFI (S n) (I.tprod τ1 τ2) → Γ, F.tprod (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseProd_pctx, caseUVal_pctx.
  eauto with typing uval_typing.
Qed.

Lemma caseProd_pctxA_T {Γ n τ1 τ2} :
  ⟪ a⊢ caseProd_pctxA n τ1 τ2 : Γ, UValFI (S n) (I.tprod τ1 τ2) → Γ, F.tprod (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseProd_pctxA, caseUVal_pctxA.
  repeat constructor.
Qed.


Lemma caseProd_T {Γ n t τ1 τ2} :
  ⟪ Γ ⊢ t : UValFI (S n) (I.tprod τ1 τ2) ⟫ →
  ⟪ Γ ⊢ caseProd n t τ1 τ2 : F.tprod (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseProd; eauto using caseProd_pctx_T with typing uval_typing.
Qed.


Lemma caseProdA_T {Γ n t τ1 τ2} :
  ⟪ Γ a⊢ t : UValFI (S n) (I.tprod τ1 τ2) ⟫ →
  ⟪ Γ a⊢ caseProdA n t τ1 τ2 : F.tprod (UValFI n τ1) (UValFI n τ2) ⟫.
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
  ⟪ ⊢ caseArr_pctx n τ1 τ2 : Γ, UValFI (S n) (I.tarr τ1 τ2) → Γ, F.tarr (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseArr_pctx, caseUVal_pctx.
  eauto with typing uval_typing.
Qed.

Lemma caseArr_pctxA_T {Γ n τ1 τ2} :
  ⟪ a⊢ caseArr_pctxA n τ1 τ2 : Γ, UValFI (S n) (I.tarr τ1 τ2) → Γ, F.tarr (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseArr_pctxA, caseUVal_pctxA.
  repeat constructor.
Qed.

Lemma caseArr_T {Γ n t τ1 τ2} :
  ⟪ Γ ⊢ t : UValFI (S n) (I.tarr τ1 τ2) ⟫ →
  ⟪ Γ ⊢ caseArr n t τ1 τ2 : F.tarr (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseArr; eauto using caseArr_pctx_T with typing uval_typing.
Qed.

Lemma caseArrA_T {Γ n t τ1 τ2} :
  ⟪ Γ a⊢ t : UValFI (S n) (I.tarr τ1 τ2) ⟫ →
  ⟪ Γ a⊢ caseArrA n t τ1 τ2 : F.tarr (UValFI n τ1) (UValFI n τ2) ⟫.
Proof.
  unfold caseArrA; eauto using caseArr_pctxA_T with typing uval_typing.
Qed.

Lemma caseArr_pctx_ectx {n τ τ'} : ECtx (caseArr_pctx n τ τ').
Proof. simpl; trivial. Qed.

Lemma eraseAnnot_caseArrA {n t τ₁ τ₂} :
  eraseAnnot (caseArrA n t τ₁ τ₂) = caseArr n (eraseAnnot t) τ₁ τ₂.
Proof.
  now cbn.
Qed.

Lemma caseRec_pctx_T {Γ n τ} :
  ⟪ ⊢ caseRec_pctx n τ : Γ, UValFI (S n) (I.trec τ) → Γ, UValFI n τ[beta1 (I.trec τ)] ⟫.
Proof.
  unfold caseRec_pctx, caseUVal_pctx.
  eauto with typing uval_typing.
Qed.

Lemma caseRec_T {Γ n t τ} :
  ⟪ Γ ⊢ t : UValFI (S n) (I.trec τ) ⟫ →
  ⟪ Γ ⊢ caseRec n t τ : UValFI n τ[beta1 (I.trec τ)] ⟫.
Proof.
  unfold caseRec; eauto using caseRec_pctx_T with typing uval_typing.
Qed.

Lemma caseRec_pctxA_T {Γ n τ} :
  ⟪ a⊢ caseRec_pctxA n τ : Γ, UValFI (S n) (I.trec τ) → Γ, UValFI n τ[beta1 (I.trec τ)] ⟫.
Proof.
  unfold caseRec_pctxA, caseUVal_pctxA.
  repeat constructor.
Qed.

Lemma caseRecA_T {Γ n t τ} :
  ⟪ Γ a⊢ t : UValFI (S n) (I.trec τ) ⟫ →
  ⟪ Γ a⊢ caseRecA n t τ : UValFI n τ[beta1 (I.trec τ)] ⟫.
Proof.
  unfold caseRecA; eauto using caseRec_pctxA_T with typing uval_typing.
Qed.

Lemma caseRec_pctx_ectx {n τ} : ECtx (caseRec_pctx n τ).
Proof. simpl; trivial. Qed.

Lemma eraseAnnot_caseRecA {n t τ} :
  eraseAnnot (caseRecA n t τ) = caseRec n (eraseAnnot t) τ.
Proof.
  now cbn.
Qed.

#[export]
Hint Resolve caseUnit_T : uval_typing.
#[export]
Hint Resolve caseSum_T : uval_typing.
#[export]
Hint Resolve caseArr_T : uval_typing.
#[export]
Hint Resolve caseRec_T : uval_typing.
#[export]
Hint Resolve caseUnitA_T : uval_typing.
#[export]
Hint Resolve caseSumA_T : uval_typing.
#[export]
Hint Resolve caseArrA_T : uval_typing.
#[export]
Hint Resolve caseRecA_T : uval_typing.

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

Arguments UValFI n : simpl never.
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

Lemma caseV0_eval_inl {v case₁ case₂ : F.Tm}:
  F.Value v →
  F.eval (caseV0 case₁ case₂)[beta1 (F.inl v)] (case₁ [beta1 v]).
Proof.
  intros vv.
  unfold caseV0; apply F.eval₀_to_eval; crush.
  change ((F.caseof (F.var 0) case₁[wkm↑] case₂ [wkm↑])[beta1 (F.inl v)]) with
  (F.caseof (F.inl v) (case₁[wkm↑][(beta1 (F.inl v))↑]) (case₂[wkm↑][(beta1 (F.inl v))↑])).
  crush.
Qed.

Lemma caseV0_eval_inr {v case₁ case₂ : F.Tm}:
  F.Value v →
  F.eval (caseV0 case₁ case₂)[beta1 (F.inr v)] (case₂ [beta1 v]).
Proof.
  intros vv.
  unfold caseV0; apply F.eval₀_to_eval; crush.
  change ((F.caseof (F.var 0) case₁[wkm↑] case₂ [wkm↑])[beta1 (F.inr v)]) with
  (F.caseof (F.inr v) (case₁[wkm↑][(beta1 (F.inr v))↑]) (case₂[wkm↑][(beta1 (F.inr v))↑])).
  crush.
Qed.

Lemma caseV0_eval {v τ₁ τ₂ case₁ case₂}:
  F.Value v → F.Typing F.empty v (F.tsum τ₁ τ₂) →
  (exists v', v = F.inl v' ∧ F.eval (caseV0 case₁ case₂)[beta1 v] case₁[beta1 v']) ∨
  (exists v', v = F.inr v' ∧ F.eval (caseV0 case₁ case₂)[beta1 v] case₂[beta1 v']).
Proof.
  intros vv ty.
  F.stlcCanForm; [left|right]; exists x;
  crush; eauto using caseV0_eval_inl, caseV0_eval_inr.
Qed.

Local Ltac crushEvalsInCaseUVal :=
  repeat
    (match goal with
         [ |- (F.evalStar (F.caseof (F.inl _) _ _) _) ] => (eapply (evalStepStar _); [eapply F.eval₀_to_eval; crush|])
       | [ |- (F.evalStar (F.caseof (F.inr _) _ _) _) ] => (eapply (evalStepStar _); [eapply F.eval₀_to_eval; crush|])
       | [ |- (F.evalStar ((caseV0 _ _) [beta1 (F.inl _)]) _) ] => (eapply (evalStepStar _); [eapply caseV0_eval_inl; crush|])
       | [ |- (F.evalStar ((caseV0 _ _) [beta1 (F.inr _)]) _) ] => (eapply (evalStepStar _); [eapply caseV0_eval_inr; crush|])
       | [ |- (F.evalStar ?t ?t) ] => eauto with *
     end;
     try rewrite -> apply_wkm_beta1_cancel
    ).

Lemma caseUVal_eval_unk_diverges {n τ} :
  not (F.Terminating (caseUVal τ (unkUVal (S n)))).
Proof.
  unfold caseUVal, unkUVal; simpl.
  eapply F.divergence_closed_under_eval.
  apply F.eval₀_to_eval.
  apply F.eval_case_inr.
  simpl; trivial.
  apply stlcOmega_div.
Qed.

Lemma caseUnit_eval_unk_diverges {n} :
  (caseUnit (unkUVal (S n)))⇑.
Proof.
  unfold caseUnit, unkUVal; simpl.
  eapply F.divergence_closed_under_eval.
  apply F.eval₀_to_eval.
  apply F.eval_case_inr.
  simpl; trivial.
  apply stlcOmega_div.
Qed.

Lemma caseArr_eval_unk_diverges {n τ1 τ2} :
  (caseArr n (unkUVal (S n)) τ1 τ2)⇑.
Proof.
  unfold caseArr, unkUVal; simpl.
  eapply F.divergence_closed_under_eval.
  apply F.eval₀_to_eval.
  apply F.eval_case_inr.
  simpl; trivial.
  apply stlcOmega_div.
Qed.

Lemma caseSum_eval_unk_diverges {n τ1 τ2} :
  (caseSum n (unkUVal (S n)) τ1 τ2)⇑.
Proof.
  unfold caseSum, unkUVal; simpl.
  eapply F.divergence_closed_under_eval.
  apply F.eval₀_to_eval.
  apply F.eval_case_inr.
  simpl; trivial.
  apply stlcOmega_div.
Qed.

Lemma caseRec_eval_unk_diverges {n τ} :
  (caseRec n (unkUVal (S n)) τ)⇑.
Proof.
  unfold caseRec, unkUVal; simpl.
  eapply F.divergence_closed_under_eval.
  apply F.eval₀_to_eval.
  apply F.eval_case_inr.
  simpl; trivial.
  apply stlcOmega_div.
Qed.

Lemma caseUVal_eval_left {v τ}:
  Value v →
  caseUVal τ (F.inl v) -->* v.
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
  F.Value v →
  ⟪ F.empty ⊢ v : UValFI (S n) I.tunit ⟫ →
  (v = F.inl F.unit) ∨ (v = F.inr F.unit).
Proof.
  unfold UValFI.
  intros.
  destruct (F.can_form_tsum H H0) as [(? & ? & ?) | (? & ? & ?)];
  [left | right];
  assert (F.Value x) by (
    subst;
    cbn in H;
    assumption);
  pose proof (F.can_form_tunit H3 H2);
  rewrite H4 in H1;
  assumption.
Qed.

Lemma canonUValS_Bool {n v} :
  F.Value v →
  ⟪ F.empty ⊢ v : UValFI (S n) I.tbool ⟫ →
  (v = F.inl F.true) ∨ (v = F.inl F.false) ∨ (v = F.inr F.unit).
Proof.
  unfold UValFI.
  intros.
  destruct (F.can_form_tsum H H0) as [(? & ? & ?) | (? & ? & ?)];
  subst; cbn in H; F.stlcCanForm.
  - now left.
  - now right; left.
  - now right; right.
Qed.

Lemma canonUValS_Arr {n v τ τ'} :
  F.Value v →
  ⟪ F.empty ⊢ v : UValFI (S n) (I.tarr τ τ') ⟫ →
  (exists v', F.Value v' ∧ (v = F.inl v') ∧ ⟪ F.empty ⊢ v' : F.tarr (UValFI n τ) (UValFI n τ')⟫) ∨ (v = F.inr F.unit).
Proof.
  unfold UValFI.
  intros vv ty.
  destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
  [left | right].

  exists x.
  split.
  subst.
  cbn in vv.
  assumption.
  split.
  assumption.
  assumption.

  assert (F.Value x) by (
                         subst;
                         cbn in vv;
                         assumption
                         ).

  pose proof (F.can_form_tunit H1 H0).
  rewrite H2 in H.
  assumption.
Qed.

Lemma canonUValS_Sum {n v τ τ'} :
  F.Value v →
  ⟪ F.empty ⊢ v : UValFI (S n) (I.tsum τ τ') ⟫ →
  (exists v', F.Value v' ∧ (v = F.inl v') ∧ ⟪ F.empty ⊢ v' : F.tsum (UValFI n τ) (UValFI n τ')⟫) ∨ (v = F.inr F.unit).
Proof.
  unfold UValFI.
  intros vv ty.
  destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
  [left | right].

  exists x.
  split.
  subst.
  cbn in vv.
  assumption.
  split.
  assumption.
  assumption.

  assert (F.Value x) by (
                         subst;
                         cbn in vv;
                         assumption
                       ).

  pose proof (F.can_form_tunit H1 H0).
  rewrite H2 in H.
  assumption.
Qed.

Lemma canonUValS_Prod {n v τ τ'} :
  F.Value v →
  ⟪ F.empty ⊢ v : UValFI (S n) (I.tprod τ τ') ⟫ →
  (exists v', F.Value v' ∧ (v = F.inl v') ∧ ⟪ F.empty ⊢ v' : F.tprod (UValFI n τ) (UValFI n τ')⟫) ∨
  (v = F.inr F.unit).
Proof.
  unfold UValFI.
  intros vv ty.
  cbn in *.
  stlcCanForm.
  - left. exists (F.pair x0 x1).
    crush.
  - now right.
Qed.

Lemma canonUValS_Rec {n v τ} :
  F.Value v →
  ⟪ F.empty ⊢ v : UValFI (S n) (I.trec τ) ⟫ →
  (exists v', F.Value v' ∧ (v = F.inl v') ∧ ⟪ F.empty ⊢ v' : UValFI n τ[beta1 (I.trec τ)] ⟫) ∨ (v = F.inr F.unit).
Proof.
  unfold UValFI.
  intros vv ty.
  destruct (F.can_form_tsum vv ty) as [(? & ? & ?) | (? & ? & ?)];
  [left | right].
  exists x.
  split.
  subst.
  cbn in vv.
  assumption.
  split.
  assumption.
  assumption.

  assert (F.Value x) by (
                         subst;
                         cbn in vv;
                         assumption
                       ).
  pose proof (F.can_form_tunit H1 H0).
  rewrite H2 in H.
  assumption.
Qed.


(* Lemma canonUVal_Arr {n v τ τ'} : *)
(*   F.Value v → *)
(*   ⟪ F.empty ⊢ v : UValFI n (I.tarr τ τ') ⟫ → *)
(*   (v = F.unit) ∨ (exists v', F.Value v' ∧ (v = F.inl v') ∧ ⟪ F.empty ⊢ v' : F.tarr (UValFI n τ) (UValFI n τ')⟫) ∨ (v = F.inr F.unit). *)
(* Proof. *)
(*   intros. *)
(*   destruct n as [? | ?]. *)
(*   left. *)
(*   unfold UValFI in H0. *)
(*   F.stlcCanForm. *)
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

(* Lemma caseUVal_eval_unk {n : nat} {tunk tcunit tcbool tcprod tcsum tcarr : F.Tm} : *)
(*   F.evalStar (caseUVal (F.inr F.unit) tunk tcunit tcbool tcprod tcsum tcarr) tunk. *)
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

