Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.LemmasTypes.

Require StlcEqui.TypeSafety.
Require Import StlcEqui.LemmasTyping.
Require Import StlcEqui.CanForm.
Require Import StlcFix.CanForm.
Require Import StlcFix.LemmasTyping.
(* Require Import StlcEqui.LemmasScoping. *)
Require Export LogRelFE.PseudoTypeFE.
Require Import UValFE.UVal.

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

Section ValidTy.

  Fixpoint ValidPTy (τ : PTy) : Prop :=
    match τ with
    | ptarr τ1 τ2 => ValidPTy τ1 /\ ValidPTy τ2
    | ptunit => True
    | ptbool => True
    | ptprod τ1 τ2 => ValidPTy τ1 /\ ValidPTy τ2
    | ptsum τ1 τ2 => ValidPTy τ1 /\ ValidPTy τ2
    | pEmulDV n p τ => ValidTy τ
    end.

  Lemma ValidPTy_invert_ptarr {τ1 τ2} :
    ValidPTy (ptarr τ1 τ2) ->
    ValidPTy τ1 /\ ValidPTy τ2.
  Proof.
    now induction 1.
  Qed.
  Hint Resolve ValidPTy_invert_ptarr : tyvalid_inv.

  Lemma ValidPTy_invert_ptprod {τ1 τ2} :
    ValidPTy (ptprod τ1 τ2) ->
    ValidPTy τ1 /\ ValidPTy τ2.
  Proof.
    now induction 1.
  Qed.
  Hint Resolve ValidPTy_invert_ptprod : tyvalid_inv.

  Lemma ValidPTy_invert_ptsum {τ1 τ2} :
    ValidPTy (ptsum τ1 τ2) ->
    ValidPTy τ1 /\ ValidPTy τ2.
  Proof.
    now induction 1.
  Qed.
  Hint Resolve ValidPTy_invert_ptsum : tyvalid_inv.

  Lemma ValidPTy_invert_pEmulDV {n p τ} :
    ValidPTy (pEmulDV n p τ) ->
    ValidTy τ.
  Proof.
    now induction 1.
  Qed.
  Hint Resolve ValidPTy_invert_pEmulDV : tyvalid_inv.

  Lemma validTy_fxToIs {τ} : ValidPTy τ -> ValidTy (fxToIs τ).
  Proof.
    induction τ;
      intros vpτ;
      cbn in vpτ;
      destruct_conjs;
      repeat match goal with
      | H: ValidPTy ?τ, H2: ValidPTy ?τ -> _ |- _ => specialize (H2 H)
      end;
      cbn;
      crushValidTy.
  Qed.

  Lemma validPTy_embed {τ} : ValidPTy (embed τ).
  Proof.
    induction τ; now cbn.
  Qed.

  Definition ValidPEnv (Γ : PEnv) : Prop :=
    ∀ i τ, ⟪ i : τ p∈ Γ ⟫ → ValidPTy τ.
  (* Inductive ValidPEnv : PEnv → Prop := *)
  (* | ValidPEnvEmpty : ValidPEnv pempty *)
  (* | ValidPEnvEvar {Γ τ} : *)
  (*   ValidPEnv Γ → *)
  (*   ValidPTy τ → *)
  (*   ValidPEnv (Γ p▻ τ). *)

  Lemma ValidPEnvEmpty : ValidPEnv pempty.
  Proof.
    intros i τ x; inversion x.
  Qed.

  Lemma ValidPEnvCons {Γ τ} : ValidPEnv Γ → ValidPTy τ → ValidPEnv (Γ p▻ τ).
  Proof.
    intros vΓ vτ i τ' x.
    inversion x; subst; try assumption.
    eapply (vΓ _ _ H3).
  Qed.

  Lemma validPEnv_embedCtx {Γ} : ValidPEnv (embedCtx Γ).
  Proof.
    induction Γ; eauto using ValidPEnvEmpty, ValidPEnvCons, validPTy_embed.
  Qed.

End ValidTy.


Section OfType.

  Local Ltac crush :=
    unfold OfType, OfTypeStlcFix, OfTypeStlcEqui; intros;
    repeat
      (subst;
       F.stlcCanForm;
       E.stlcCanForm;
       F.crushTyping;
       E.crushTyping;
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
         | |- ValidTy (fxToIs _) => eapply validTy_fxToIs
         end); eauto.

  Lemma OfType_unit : OfType ptunit F.unit E.unit.
  Proof. crush. Qed.

  Lemma OfType_true : OfType ptbool F.true E.true.
  Proof. crush. Qed.

  Lemma OfType_false : OfType ptbool F.false E.false.
  Proof. crush. Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (F.inl ts) (E.inl tu).
  Proof. crush. Qed.

  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (F.inr ts) (E.inr tu).
  Proof. crush. Qed.

  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (F.pair ts₁ ts₂) (E.pair tu₁ tu₂).
  Proof. crush. Qed.

  Lemma OfType_lambda {τ₁ τ₂ τ₁' τ₁'' tsb tub} :
    ValidPTy τ₁ -> ValidPTy τ₂ -> ValidTy τ₁'' ->
    τ₁' = repEmul τ₁ →
    ⟪ τ₁'' ≗ fxToIs τ₁ ⟫ ->
    ⟪ E.empty e⊢ E.abs (fxToIs τ₁) tub : E.tarr (fxToIs τ₁) (fxToIs τ₂) ⟫ →
    ⟪ F.empty ⊢ F.abs (repEmul τ₁) tsb : repEmul τ₁ ⇒ repEmul τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (F.abs τ₁' tsb) (E.abs τ₁'' tub).
  Proof.
    crush;
      eauto using ValidTy_arr, validTy_fxToIs.
    eapply E.invert_ty_abs in H4; crushValidTy.
    destruct_conjs.
    eapply tyeq_invert_tarr in H7.
    destruct_conjs.
    eapply E.eqctx_implies_eqty.
    - constructor.
      eapply tyeq_symm.
      exact H3.
      constructor.
    - eauto using validTy_fxToIs with tyvalid.
    - eauto using validTy_fxToIs with tyvalid.
    - refine (WtEq _ _ _ _ H8);
      eauto using typed_terms_are_valid, validTy_fxToIs with tyvalid.
  Qed.

  Lemma OfType_inversion_ptunit {ts tu} :
    OfType ptunit ts tu →
    ts = F.unit ∧ tu = E.unit.
  Proof.
    crush.
  Qed.

  Lemma OfType_inversion_ptbool {ts tu} :
    OfType ptbool ts tu →
    ts = F.true ∧ tu = E.true ∨
    ts = F.true ∧ tu = E.false ∨
    ts = F.false ∧ tu = E.true ∨
    ts = F.false ∧ tu = E.false.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptsum {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType (ptsum τ₁ τ₂) ts tu →
    ∃ ts' tu',
      ts = F.inl ts' ∧ tu = E.inl tu' ∧ OfType τ₁ ts' tu' ∨
      ts = F.inl ts' ∧ tu = E.inr tu' ∨
      ts = F.inr ts' ∧ tu = E.inl tu' ∨
      ts = F.inr ts' ∧ tu = E.inr tu' ∧ OfType τ₂ ts' tu'.
  Proof.
    crush.
    - repeat eexists. left. crush.
    - repeat eexists. right. left. crush.
    - repeat eexists. right. right. left. crush.
    - repeat eexists. right. right. right. crush.
  Qed.

  Lemma OfType_inversion_ptprod {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType (ptprod τ₁ τ₂) ts tu →
    ∃ ts₁ tu₁ ts₂ tu₂,
      ts = F.pair ts₁ ts₂ ∧
      tu = E.pair tu₁ tu₂ ∧
      OfType τ₁ ts₁ tu₁ ∧
      OfType τ₂ ts₂ tu₂.
  Proof. crush. repeat eexists; crush. Qed.

  (* Lemma OfTypeUtlc_inversion_ptarr {τ₁ τ₂ tu} : *)
  (*   OfTypeUtlc (ptarr τ₁ τ₂) tu → *)
  (*   ∃ tu', tu = E.abs tu' ∧ ⟨ 1 ⊢ tu' ⟩. *)
  (* Proof. crush. Qed. *)

  (* Lemma OfTypeUtlc_inversion_ptprod {τ₁ τ₂ tu} : *)
  (*   OfTypeUtlc (ptprod τ₁ τ₂) tu → *)
  (*   ∃ tu₁ tu₂, tu = E.pair tu₁ tu₂ ∧ OfTypeUtlc τ₁ tu₁ ∧ OfTypeUtlc τ₂ tu₂. *)
  (* Proof. crush. Qed. *)

  (* Lemma OfTypeUtlc_inversion_ptsum {τ₁ τ₂ tu} : *)
  (*   OfTypeUtlc (ptsum τ₁ τ₂) tu → *)
  (*   ∃ tu', (tu = E.inl tu' ∧ OfTypeUtlc τ₁ tu') ∨ *)
  (*          (tu = E.inr tu' ∧ OfTypeUtlc τ₂ tu'). *)
  (* Proof. crush. Qed. *)

  Lemma OfType_inversion_ptarr {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    OfType (ptarr τ₁ τ₂) ts tu →
    ∃ ts' tu' τ₁',
      ts = F.abs (repEmul τ₁) ts' ∧
      tu = E.abs τ₁' tu' ∧
        ValidTy τ₁' /\
        ⟪ τ₁' ≗ fxToIs τ₁ ⟫ /\
      ⟪ F.empty ▻ repEmul τ₁ ⊢ ts' : repEmul τ₂ ⟫ ∧
        ⟪ E.empty r▻ fxToIs τ₁ e⊢ tu' : fxToIs τ₂ ⟫.
  Proof.
    crush.
    - eapply ValidTy_arr; crush.
    - repeat eexists; crush;
      crushValidTy.
  Qed.

  Lemma OfType_inversion_pEmulDV {n p ts tu T} :
    OfType (pEmulDV n p T) ts tu →
    F.Value ts ∧ E.Value tu ∧
    ⟪ F.empty ⊢ ts : UValFE n T ⟫ ∧
    E.Typing E.empty tu T.
  Proof. crush. Qed.

  Lemma OfTypeStlcEqui_implies_Value {τ tu} :
    OfTypeStlcEqui τ tu →
    E.Value tu.
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
    F.Value ts ∧ E.Value tu.
  Proof.
    crush.
  Qed.

  Lemma OfType_pEmulDV {n p ts tu T} :
    F.Value ts ∧ E.Value tu ∧
    ⟪ F.empty ⊢ ts : UValFE n T ⟫ →
    E.Typing E.empty tu T →
    OfType (pEmulDV n p T) ts tu.
  Proof. crush. Qed.

End OfType.

Ltac crushOfType :=
  repeat
    (match goal with
     | [ H: OfType _ _ _ |- ValidPTy _ ] => clear H   (* prevent an infinite loop *)
      | [ H: OfType ptunit _ _ |- _ ] => apply OfType_inversion_ptunit in H
      | [ H: OfType ptbool _ _ |- _ ] => apply OfType_inversion_ptbool in H
      | [ H: OfType (ptsum ?τ₁ ?τ₂) _ _ |- _ ] => apply OfType_inversion_ptsum in H
      | [ H: OfType (ptprod ?τ₁ ?τ₂) _ _ |- _ ] => apply OfType_inversion_ptprod in H
      | [ H: OfType (ptarr ?τ₁ ?τ₂) _ _ |- _ ] => apply OfType_inversion_ptarr in H
      | [ |- OfType ptunit F.unit E.unit ] => apply OfType_unit
      | [ |- OfType ptbool F.true E.true ] => apply OfType_true
      | [ |- OfType ptbool F.false E.false ] => apply OfType_false
      | [ |- OfType (ptsum _ _) (F.inl _) (E.inl _)] => apply OfType_inl
      | [ |- OfType (ptsum _ _) (F.inr _) (E.inr _)] => apply OfType_inr
      | [ |- OfType (ptprod _ _) (F.pair _ _) (E.pair _ _) ] => apply OfType_pair
      | [ |- OfType (ptarr _ _) (F.abs _ _) (E.abs _ _) ] => apply OfType_lambda
      (* | [ |- OfTypeUtlc _ _ ] => split *)
      | [ |- OfType (pEmulDV _ _ _) _ _ ] => apply OfType_pEmulDV
    end; try assumption; try reflexivity).
