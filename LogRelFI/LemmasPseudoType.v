Require StlcIso.TypeSafety.
Require Import StlcIso.LemmasTyping.
Require Import StlcFix.CanForm.
Require Import StlcFix.LemmasTyping.
(* Require Import StlcIso.LemmasScoping. *)
Require Export LogRelFI.PseudoTypeFI.
Require Import UValFI.UVal.

Section RepEmul.
  Lemma repEmul_embed_leftinv τ :
    repEmul (embed τ) = τ.
  Proof.
    induction τ; simpl; try f_equal; intuition.
  Qed.

  Lemma repEmulCtx_embedCtx_leftinv Γ :
    repEmulCtx (embedCtx Γ) = Γ.
  Proof.
    induction Γ; simpl; try f_equal; eauto using repEmul_embed_leftinv.
  Qed.
End RepEmul.

Ltac crushRepEmulEmbed :=
  match goal with
      [ |- context[ repEmul( embed ?τ) ] ] => rewrite -> (repEmul_embed_leftinv τ)
    | [ |- context[ repEmulCtx( embedCtx ?Γ) ] ] => rewrite -> (repEmulCtx_embedCtx_leftinv Γ)
  end.

(* TODO: equivalent section for fxToIs? *)

Lemma getevar_repEmulCtx {i τ Γ} :
  ⟪ i : τ ∈ repEmulCtx Γ ⟫ →
  exists τ', ⟪ i : τ' p∈ Γ ⟫ ∧ τ = repEmul τ'.
Proof.
  revert i. induction Γ as [|Γ IHΓ τ''];
  inversion 1; [idtac| destruct (IHΓ _ H4) as [? [? ?]]];
  eauto using GetEvarP.
Qed.

Lemma getevar_fxToIsCtx {i τ Γ} :
  ⟪ i : τ r∈ fxToIsCtx Γ ⟫ →
  exists τ', ⟪ i : τ' p∈ Γ ⟫ ∧ τ = fxToIs τ'.
Proof.
  revert i. induction Γ as [|Γ IHΓ τ''];
  inversion 1; [idtac| destruct (IHΓ _ H4) as [? [? ?]]];
  eauto using GetEvarP.
Qed.

Section OfType.

  Local Ltac crush :=
    unfold OfType, OfTypeStlcFix, OfTypeStlcIso; intros;
    repeat
      (subst;
       F.stlcCanForm;
       I.stlcCanForm;
       F.crushTyping;
       I.crushTyping;
       destruct_conjs;
       repeat
         match goal with
           | H: False |- _ => elim H
           | H: True  |- _ => clear H
           | H: _ ∧ _ |- _ => destruct  H
           | H: match ?tu with _ => _ end |- _ =>
             destruct tu eqn: ?; cbn in H
           | H: _ ∨ _ |- _ => destruct  H
           | [ |- _ ∧ _ ] => split
         end); eauto 20.

  Lemma OfType_unit : OfType ptunit F.unit I.unit.
  Proof. crush. Qed.

  Lemma OfType_true : OfType ptbool F.true I.true.
  Proof. crush. Qed.

  Lemma OfType_false : OfType ptbool F.false I.false.
  Proof. crush. Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (F.inl ts) (I.inl tu).
  Proof. crush. Qed.

  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (F.inr ts) (I.inr tu).
  Proof. crush. Qed.

  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (F.pair ts₁ ts₂) (I.pair tu₁ tu₂).
  Proof. crush. Qed.

  Lemma OfType_lambda {τ₁ τ₂ τ₁' τ₁'' tsb tub} :
    τ₁' = repEmul τ₁ →
    τ₁'' = fxToIs τ₁ ->
    ⟪ I.empty i⊢ I.abs (fxToIs τ₁) tub : I.tarr (fxToIs τ₁) (fxToIs τ₂) ⟫ →
    ⟪ F.empty ⊢ F.abs (repEmul τ₁) tsb : repEmul τ₁ ⇒ repEmul τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (F.abs τ₁' tsb) (I.abs τ₁'' tub).
  Proof. crush. Qed.

  Lemma OfType_inversion_ptunit {ts tu} :
    OfType ptunit ts tu →
    ts = F.unit ∧ tu = I.unit.
  Proof.
    crush.
  Qed.

  Lemma OfType_inversion_ptbool {ts tu} :
    OfType ptbool ts tu →
    ts = F.true ∧ tu = I.true ∨
    ts = F.true ∧ tu = I.false ∨
    ts = F.false ∧ tu = I.true ∨
    ts = F.false ∧ tu = I.false.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptsum {τ₁ τ₂ ts tu} :
    OfType (ptsum τ₁ τ₂) ts tu →
    ∃ ts' tu',
      ts = F.inl ts' ∧ tu = I.inl tu' ∧ OfType τ₁ ts' tu' ∨
      ts = F.inl ts' ∧ tu = I.inr tu' ∨
      ts = F.inr ts' ∧ tu = I.inl tu' ∨
      ts = F.inr ts' ∧ tu = I.inr tu' ∧ OfType τ₂ ts' tu'.
  Proof.
    crush.
  Qed.

  Lemma OfType_inversion_ptprod {τ₁ τ₂ ts tu} :
    OfType (ptprod τ₁ τ₂) ts tu →
    ∃ ts₁ tu₁ ts₂ tu₂,
      ts = F.pair ts₁ ts₂ ∧
      tu = I.pair tu₁ tu₂ ∧
      OfType τ₁ ts₁ tu₁ ∧
      OfType τ₂ ts₂ tu₂.
  Proof. crush. Qed.

  (* Lemma OfTypeUtlc_inversion_ptarr {τ₁ τ₂ tu} : *)
  (*   OfTypeUtlc (ptarr τ₁ τ₂) tu → *)
  (*   ∃ tu', tu = I.abs tu' ∧ ⟨ 1 ⊢ tu' ⟩. *)
  (* Proof. crush. Qed. *)

  (* Lemma OfTypeUtlc_inversion_ptprod {τ₁ τ₂ tu} : *)
  (*   OfTypeUtlc (ptprod τ₁ τ₂) tu → *)
  (*   ∃ tu₁ tu₂, tu = I.pair tu₁ tu₂ ∧ OfTypeUtlc τ₁ tu₁ ∧ OfTypeUtlc τ₂ tu₂. *)
  (* Proof. crush. Qed. *)

  (* Lemma OfTypeUtlc_inversion_ptsum {τ₁ τ₂ tu} : *)
  (*   OfTypeUtlc (ptsum τ₁ τ₂) tu → *)
  (*   ∃ tu', (tu = I.inl tu' ∧ OfTypeUtlc τ₁ tu') ∨ *)
  (*          (tu = I.inr tu' ∧ OfTypeUtlc τ₂ tu'). *)
  (* Proof. crush. Qed. *)

  Lemma OfType_inversion_ptarr {τ₁ τ₂ ts tu} :
    OfType (ptarr τ₁ τ₂) ts tu →
    ∃ ts' tu',
      ts = F.abs (repEmul τ₁) ts' ∧
      tu = I.abs (fxToIs τ₁) tu' ∧
      ⟪ F.empty ▻ repEmul τ₁ ⊢ ts' : repEmul τ₂ ⟫ ∧
      I.Typing (I.evar I.empty (fxToIs τ₁)) tu' (fxToIs τ₂).
  Proof. crush. Qed.

  Lemma OfType_inversion_pEmulDV {n p ts tu T} :
    OfType (pEmulDV n p T) ts tu →
    F.Value ts ∧ I.Value tu ∧
    ⟪ F.empty ⊢ ts : UValFI n T ⟫ ∧
    I.Typing I.empty tu T.
  Proof. crush. Qed.

  Lemma OfTypeStlcIso_implies_Value {τ tu} :
    OfTypeStlcIso τ tu →
    I.Value tu.
  Proof.
    crush.
  Qed.

  Lemma OfTypeStlcFix_implies_Value {τ ts} :
    OfTypeStlcFix τ ts →
    F.Value ts.
  Proof.
    crush.
  Qed.

  Lemma OfType_implies_Value {τ ts tu} :
    OfType τ ts tu →
    F.Value ts ∧ I.Value tu.
  Proof.
    crush.
  Qed.

  Lemma OfType_pEmulDV {n p ts tu T} :
    F.Value ts ∧ I.Value tu ∧
    ⟪ F.empty ⊢ ts : UValFI n T ⟫ →
    I.Typing I.empty tu T →
    OfType (pEmulDV n p T) ts tu.
  Proof. crush. Qed.

End OfType.

Ltac crushOfType :=
  repeat
    match goal with
      | [ H: OfType ptunit _ _ |- _ ] => apply OfType_inversion_ptunit in H
      | [ H: OfType ptbool _ _ |- _ ] => apply OfType_inversion_ptbool in H
      | [ H: OfType (ptsum _ _) _ _ |- _ ] => apply OfType_inversion_ptsum in H
      | [ H: OfType (ptprod _ _) _ _ |- _ ] => apply OfType_inversion_ptprod in H
      | [ H: OfType (ptarr _ _) _ _ |- _ ] => apply OfType_inversion_ptarr in H
      (* | [ H: OfTypeUtlc _ ?t |- ⟨ 0 ⊢ ?t ⟩ ] => exact (proj1 H) *)
      (* | [ H: OfTypeUtlc ?τ ?t |- OfTypeUtlc' ?τ ?t ] => exact (proj2 H) *)
      (* | [ H: OfTypeUtlc (ptarr _ _) _ |- _ ] => apply OfTypeUtlc_inversion_ptarr in H *)
      (* | [ H: OfTypeUtlc (ptprod _ _) _ |- _ ] => apply OfTypeUtlc_inversion_ptprod in H *)
      (* | [ H: OfTypeUtlc (ptsum _ _) _ |- _ ] => apply OfTypeUtlc_inversion_ptsum in H *)
      (* | [ H: OfType (pEmulDV _ _) _ _ |- _ ] => apply OfType_inversion_pEmulDV in H *)
      (* | [ H: OfTypeUtlc ptbool ?t  |- _ ] =>  change (OfTypeUtlc ptbool t) with (t = I.true ∨ t = I.false) in H *)
      (* | [ H: OfTypeUtlc ptunit ?t  |- _ ] => change (OfTypeUtlc ptunit t) with (t = I.unit) in H; subst t *)
      | [ |- OfType ptunit F.unit I.unit ] => apply OfType_unit
      | [ |- OfType ptbool F.true I.true ] => apply OfType_true
      | [ |- OfType ptbool F.false I.false ] => apply OfType_false
      | [ |- OfType (ptsum _ _) (F.inl _) (I.inl _)] => apply OfType_inl
      | [ |- OfType (ptsum _ _) (F.inr _) (I.inr _)] => apply OfType_inr
      | [ |- OfType (ptprod _ _) (F.pair _ _) (I.pair _ _) ] => apply OfType_pair
      | [ |- OfType (ptarr _ _) (F.abs _ _) (I.abs _ _) ] => apply OfType_lambda
      (* | [ |- OfTypeUtlc _ _ ] => split *)
      | [ |- OfType (pEmulDV _ _ _) _ _ ] => apply OfType_pEmulDV
    end.
