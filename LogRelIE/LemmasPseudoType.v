Require Export Db.Spec.
Require Export Db.Lemmas.

Require Export LogRelIE.PseudoType.
Require Export LogRelIE.InstPTy.
Require Export LogRelIE.Contraction.
Require Export LogRelIE.ValidPTy.

Require Import StlcIso.LemmasTyping.
Require Import StlcEqui.LemmasTyping.

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Require Import UValIE.UVal.

(* Require StlcEqui.TypeSafety. *)
(* Require Import StlcEqui.LemmasTyping. *)
(* Require Import StlcIso.CanForm. *)
(* Require Import StlcIso.LemmasTyping. *)
(* (* Require Import StlcIso.LemmasScoping. *) *)
(* Require Export LogRelIE.PseudoType. *)
(* Require Import UValIE.UVal. *)
(* Require Import LogRelIE.ValidPTy. *)

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

  Lemma repEmul_ren {ζ : Sub Ix} {τ} :
    repEmul (τ [ ζ ]) = (repEmul τ) [ ζ ].
  Proof.
    revert ζ.
    induction τ; intros ζ; cbn; f_equal; eauto using (@UVal_sub Ix).
  Qed.

  Lemma repEmul_sub {τ σ} :
    repEmul τ [σ] = (repEmul τ) [σ >-> repEmul].
  Proof.
    revert σ;
    induction τ; intros; cbn; repeat I.crushStlcSyntaxMatchH; f_equal; eauto.
    - transitivity ((repEmul τ) [ σ↑ >-> repEmul]).
      eapply IHτ.
      change (apTy ?ξ ?τ) with τ[ξ] in *.
      f_equal.
      extensionality i.
      destruct i.
      now cbn.
      cbn.
      now rewrite repEmul_ren.
    - now rewrite UVal_sub.
  Qed.

End RepEmul.

Section IsToEq.
  Lemma isToEq_embed_leftinv τ :
    isToEq (embed τ) = τ.
  Proof.
    induction τ; simpl; try f_equal; intuition.
  Qed.

  Lemma isToEqCtx_embedCtx_leftinv Γ :
    isToEqCtx (embedCtx Γ) = Γ.
  Proof.
    induction Γ; simpl; try f_equal; eauto using isToEq_embed_leftinv.
  Qed.

  Lemma isToEq_ren {ζ : Sub Ix} {δ τ} :
    ⟨ δ ⊢ τ ⟩ ->
    isToEq (τ [ ζ ]) = (isToEq τ) [ ζ ].
  Proof.
    revert δ ζ.
    induction τ; intros δ ζ wsτ ; cbn; try inversion wsτ; subst; f_equal; eauto using (@UVal_sub Ix).
    eapply eq_sym, wsClosed_invariant.
    exact H0.
  Qed.

  Lemma isToEq_preserves_ws {i τ} :
    ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ isToEq τ ⟩.
  Proof.
    induction 1; cbn; try econstructor; eauto.
    eapply WsTy_mono; try eassumption; lia.
  Qed.

  Lemma isToEq_sub {τ σ δ δ'} :
    ⟨ δ ⊢ τ ⟩ ->
    ⟨ σ : δ => δ' ⟩ ->
    isToEq τ [σ] = (isToEq τ) [σ >-> isToEq].
  Proof.
    revert δ δ' σ;
    induction τ; intros δ δ' σ wsτ wsσ; try inversion wsτ; subst; cbn; repeat I.crushStlcSyntaxMatchH; f_equal; eauto.
    - transitivity ((isToEq τ) [ σ↑ >-> isToEq]).
      eapply IHτ; eauto using (wsSub_up (X := PTy)).
      change (apTy ?ξ ?τ) with τ[ξ] in *.
      eapply ( wsApExt (isToEq_preserves_ws H0)).
      intros i iδ.
      destruct i; cbn; [now idtac|].
      inversion iδ; subst.
      now eapply isToEq_ren, wsσ.
    - now rewrite wsClosed_invariant.
  Qed.

End IsToEq.

Ltac crushRepEmulEmbed :=
  match goal with
      [ |- context[ repEmul( embed ?τ) ] ] => rewrite -> (repEmul_embed_leftinv τ)
    | [ |- context[ repEmulCtx( embedCtx ?Γ) ] ] => rewrite -> (repEmulCtx_embedCtx_leftinv Γ)
  end.

Lemma getevar_repEmulCtx {i τ Γ} :
  ⟪ i : τ r∈ repEmulCtx Γ ⟫ →
  exists τ', ⟪ i : τ' p∈ Γ ⟫ ∧ τ = repEmul τ'.
Proof.
  revert i. induction Γ as [|Γ IHΓ τ''];
  inversion 1; [idtac| destruct (IHΓ _ H4) as [? [? ?]]];
  eauto using GetEvarP.
Qed.

Lemma getevar_isToEqCtx {i τ Γ} :
  ⟪ i : τ r∈ isToEqCtx Γ ⟫ →
  exists τ', ⟪ i : τ' p∈ Γ ⟫ ∧ τ = isToEq τ'.
Proof.
  revert i. induction Γ as [|Γ IHΓ τ''];
  inversion 1; [idtac| destruct (IHΓ _ H4) as [? [? ?]]];
  eauto using GetEvarP.
Qed.

Lemma closed_implies_not_ptvar {i} :
  ⟨ 0 ⊢ ptvar i ⟩ → False.
Proof.
  intros.
  inversion H.
  inversion H1.
Qed.
#[export]
Hint Resolve closed_implies_not_ptvar : cpty.

Lemma closed_arr_implies_closed_argpty {τ τ'} :
  ⟨ 0 ⊢ τ p⇒ τ' ⟩ → ⟨ 0 ⊢ τ ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_arr_implies_closed_argpty : cpty.

Lemma closed_arr_implies_closed_retpty {τ τ'} :
  ⟨ 0 ⊢ τ p⇒ τ' ⟩ → ⟨ 0 ⊢ τ' ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_arr_implies_closed_retpty : cpty.

Lemma closed_arr_implies_closed_argpty_eq {τ τ1 τ2} :
  ⟨ 0 ⊢ τ ⟩ →
  τ = (τ1 p⇒ τ2) →
  ⟨ 0 ⊢ τ1 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_arr_implies_closed_argpty H).
Qed.
#[export]
Hint Resolve closed_arr_implies_closed_argpty_eq : cpty.

Lemma closed_psum_implies_closed_lhs {τ τ'} :
 ⟨ 0 ⊢ τ p⊎ τ' ⟩ → ⟨ 0 ⊢ τ ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_psum_implies_closed_lhs : cpty.

Lemma closed_psum_implies_closed_rhs {τ τ'} :
 ⟨ 0 ⊢ τ p⊎ τ' ⟩ → ⟨ 0 ⊢ τ' ⟩.
Proof.
  inversion 1; assumption.
Qed.
#[export]
Hint Resolve closed_psum_implies_closed_rhs : cpty.

Lemma closed_psum_implies_closed_lhs_eq {τ τ1 τ2} :
 ⟨ 0 ⊢ τ ⟩ →
  τ = (τ1 p⊎ τ2) →
 ⟨ 0 ⊢ τ1 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_psum_implies_closed_lhs H).
Qed.

Lemma closed_psum_implies_closed_rhs_eq {τ τ1 τ2} :
 ⟨ 0 ⊢ τ ⟩ →
  τ = (τ1 p⊎ τ2) →
 ⟨ 0 ⊢ τ2 ⟩.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_psum_implies_closed_rhs H).
Qed.

Lemma Closed_SimplePRec_SimplePContr {τ} : ⟨ 0 ⊢ τ ⟩ -> SimplePRec τ -> SimplePContr τ.
Proof.
  intros cty rty.
  destruct rty; [|assumption].
  exfalso. eauto with cpty.
Qed.

Lemma Closed_SimplePRec_PValid {τ} : ⟨ 0 ⊢ τ ⟩ -> SimplePRec τ -> ValidPTy τ.
Proof.
  split; eauto using Closed_SimplePRec_SimplePContr.
Qed.

Section ValidPTy.

  Lemma ValidPTy_arr {τ1 τ2} : ValidPTy τ1 → ValidPTy τ2 → ValidPTy (τ1 p⇒ τ2).
  Proof.
    intros [τ1_cl τ1_contr] [τ2_cl τ2_contr].
    split; eauto with simple_contr_rec simple_p_contr_rec.
    now constructor.
  Qed.
  Hint Resolve ValidPTy_arr : ptyvalid.

  Lemma ValidPTy_invert_arr {τ1 τ2} : ValidPTy (τ1 p⇒ τ2) -> ValidPTy τ1 /\ ValidPTy τ2.
  Proof.
    intros [τ_cl τ_contr].
    inversion τ_cl; subst.
    inversion τ_contr; subst.
    eauto using Closed_SimplePRec_PValid.
  Qed.
  Hint Resolve ValidPTy_invert_arr : ptyvalid_inv.

  Lemma ValidPTy_prod {τ1 τ2} : ValidPTy τ1 -> ValidPTy τ2 -> ValidPTy (τ1 p× τ2).
  Proof.
    intros [τ1_cl τ1_contr] [τ2_cl τ2_contr].
    split; eauto with simple_contr_rec simple_p_contr_rec.
    now constructor.
  Qed.
  Hint Resolve ValidPTy_prod : ptyvalid.

  Lemma ValidPTy_invert_prod {τ1 τ2} : ValidPTy (τ1 p× τ2) → ValidPTy τ1 ∧ ValidPTy τ2.
  Proof.
    intros [τ_cl τ_contr].
    inversion τ_cl; subst.
    inversion τ_contr; subst.
    eauto using Closed_SimplePRec_PValid.
  Qed.
  Hint Resolve ValidPTy_invert_prod : ptyvalid_inv.

  Lemma ValidPTy_sum {τ1 τ2} : ValidPTy τ1 → ValidPTy τ2 → ValidPTy (τ1 p⊎ τ2).
  Proof.
    intros [τ1_cl τ1_contr] [τ2_cl τ2_contr].
    split; eauto with simple_contr_rec simple_p_contr_rec.
    now constructor.
  Qed.
  Hint Resolve ValidPTy_sum : ptyvalid.

  Lemma ValidPTy_invert_sum {τ1 τ2} : ValidPTy (τ1 p⊎ τ2) → ValidPTy τ1 ∧ ValidPTy τ2.
  Proof.
    intros [τ_cl τ_contr].
    inversion τ_cl; subst.
    inversion τ_contr; subst.
    eauto using Closed_SimplePRec_PValid.
  Qed.
  Hint Resolve ValidPTy_invert_sum : ptyvalid_inv.

  Lemma ValidPTy_unit : ValidPTy ptunit.
  Proof.
    split; now constructor.
  Qed.
  Hint Resolve ValidPTy_unit : ptyvalid.

  Lemma ValidPTy_bool : ValidPTy ptbool.
  Proof.
    split; now constructor.
  Qed.
  Hint Resolve ValidPTy_bool : ptyvalid.

  Lemma ValidPTy_rec {τ} : ⟨ 1 ⊢ τ ⟩ → SimplePContr τ → ValidPTy (ptrec τ).
  Proof.
    intros τ_cl τ_contr.
    split; eauto with simple_p_contr_rec.
    now constructor.
  Qed.
  Hint Resolve ValidPTy_rec : ptyvalid.

  Lemma ValidPTy_invert_rec {τ} : ValidPTy (ptrec τ) → ⟨ 1 ⊢ τ ⟩ ∧ SimplePContr τ.
  Proof.
    intros [τ_cl τ_contr].
    split.
    - inversion τ_cl; subst; assumption.
    - inversion τ_contr; subst; assumption.
  Qed.
  Hint Resolve ValidPTy_invert_rec : ptyvalid_inv.

End ValidPTy.

Lemma repEmul_preserves_ws {i τ} :
  ⟨ i ⊢ τ ⟩ → ⟨ i ⊢ repEmul τ ⟩.
Proof.
  induction 1; cbn; try econstructor; eauto.
  eapply UValIE_preserves_ws, WsTy_mono; try eassumption; lia.
Qed.

Lemma repEmul_preserves_contr {τ} : SimplePContr τ → SimpleContr (repEmul τ)
with repEmul_preserves_rec {τ} : SimplePRec τ → SimpleRec (repEmul τ).
Proof.
  - destruct 1; cbn; try (constructor; fail).
    + constructor; apply repEmul_preserves_rec; assumption.
    + constructor; apply repEmul_preserves_rec; assumption.
    + constructor; apply repEmul_preserves_rec; assumption.
    + constructor. apply repEmul_preserves_contr; assumption.
    + apply (UValIE_preserves_contr H).
  - destruct 1; constructor; apply repEmul_preserves_contr; assumption.
Qed.

Lemma isToEq_preserves_contr {τ} : SimplePContr τ → SimpleContr (isToEq τ)
with isToEq_preserves_rec {τ} : SimplePRec τ → SimpleRec (isToEq τ).
Proof.
  - destruct 1; cbn; try (constructor; fail).
    + constructor; apply isToEq_preserves_rec; assumption.
    + constructor; apply isToEq_preserves_rec; assumption.
    + constructor; apply isToEq_preserves_rec; assumption.
    + constructor; apply isToEq_preserves_contr; assumption.
    + assumption.
  - destruct 1; constructor; apply isToEq_preserves_contr; assumption.
Qed.

Lemma ValidPTy_implies_ValidTy_repEmul {τ} :
  ValidPTy τ → ValidTy (repEmul τ).
Proof.
  induction τ; intros; cbn.
  - apply ValidPTy_invert_arr in H as (? & ?);
    apply ValidTy_arr;
      eauto with tyvalid.
  - apply ValidTy_unit.
  - apply ValidTy_bool.
  - apply ValidPTy_invert_prod in H as (? & ?);
      eauto with tyvalid.
  - apply ValidPTy_invert_sum in H as (? & ?);
      eauto with tyvalid.
  - apply ValidPTy_invert_rec in H as (? & ?).
    apply ValidTy_rec.
    apply (repEmul_preserves_ws H).
    apply (repEmul_preserves_contr H0).
  - exfalso; inversion H; inversion H0; inversion H3.
  - apply UValIE_valid;
    destruct H as (τ_cl & τ_contr);
      split; [inversion τ_cl | inversion τ_contr];
      assumption.
Qed.

Lemma ValidPTy_implies_ValidTy_isToEq {τ} :
  ValidPTy τ → ValidTy (isToEq τ).
Proof.
  induction τ; intros; cbn.
  - apply ValidPTy_invert_arr in H as (? & ?);
    apply ValidTy_arr;
      eauto with tyvalid.
  - apply ValidTy_unit.
  - apply ValidTy_bool.
  - apply ValidPTy_invert_prod in H as (? & ?);
      eauto with tyvalid.
  - apply ValidPTy_invert_sum in H as (? & ?);
      eauto with tyvalid.
  - apply ValidPTy_invert_rec in H as (? & ?).
    apply ValidTy_rec.
    apply (isToEq_preserves_ws H).
    apply (isToEq_preserves_contr H0).
  - exfalso; inversion H; inversion H0; inversion H3.
  - destruct H as (? & ?).
    split; [inversion H | inversion H0]; subst; assumption.
Qed.

Section Embed.
  Lemma ValidTy_implies_ValidPTy_pEmulDV {n p τ} :
    ValidTy τ → ValidPTy (pEmulDV n p τ).
  Proof.
    intro vτ.
    destruct vτ as (τ_cl & τ_contr).
    split; now constructor.
  Qed.
  Hint Resolve ValidTy_implies_ValidPTy_pEmulDV : ptyvalid.

  Lemma ws_embed {τ n} :
    ⟨ n ⊢ τ ⟩ -> ⟨ n ⊢ embed τ ⟩.
  Proof.
    induction 1; cbn; try econstructor; eauto.
  Qed.

  Lemma embed_ren {τ} {σ : Sub Ix} :
    embed τ [σ] = (embed τ) [σ].
  Proof.
    revert σ.
    induction τ; intros; cbn; f_equal; eauto.
  Qed.

  Lemma embed_sub {τ σ} :
    embed τ [σ] = (embed τ) [σ >-> embed].
  Proof.
    revert σ;
    induction τ; intros; cbn; repeat I.crushStlcSyntaxMatchH; f_equal; eauto.
    transitivity ((embed τ) [ σ↑ >-> embed]).
    eapply IHτ.
    change (apPTy ?ξ ?τ) with τ[ξ] in *.
    f_equal.
    extensionality i.
    destruct i.
    now cbn.
    cbn.
    now rewrite embed_ren.
  Qed.

  Lemma SimpleContr_implies_SimplePContr_embed {τ} :
    SimpleContr τ -> SimplePContr (embed τ)
  with  SimpleRec_implies_SimplePRec_embed {τ} :
    SimpleRec τ -> SimplePRec (embed τ).
  Proof.
    - induction 1; cbn; econstructor; eauto.
    - induction 1; cbn; econstructor; eauto.
  Qed.

  Lemma ValidTy_implies_ValidPTy_embed {τ} :
    ValidTy τ -> ValidPTy (embed τ).
  Proof.
    unfold ValidTy, ValidPTy.
    intros [wsτ cτ].
    split.
    - now eapply ws_embed.
    - now eapply SimpleContr_implies_SimplePContr_embed.
  Qed.
  Hint Resolve ValidTy_implies_ValidPTy_embed : ptyvalid.

  Lemma ValidEnv_implies_ValidPEnv_embedCtx {Γ} :
    ValidEnv Γ -> ValidPEnv (embedCtx Γ).
  Proof.
    induction Γ; cbn; eauto with ptyvalid.
    intros [vΓ vτ]%ValidEnv_invert_cons;
    eauto using ValidTy_implies_ValidPTy_embed with ptyvalid.
  Qed.
  Hint Resolve ValidTy_implies_ValidPTy_embed : ptyvalid.
End Embed.

Ltac crushValidPTyMatch :=
  match goal with
  | [ H : ValidPTy (ptarr _ _) |- _ ] => eapply ValidPTy_invert_arr in H
  | [ H : ValidPTy (ptprod _ _) |- _ ] => eapply ValidPTy_invert_prod in H
  | [ H : ValidPTy (ptsum _ _) |- _ ] => eapply ValidPTy_invert_sum in H
  | [ H : ValidPTy (ptrec _) |- _ ] => eapply ValidPTy_invert_rec in H
  | [ |- ValidPTy (embed _) ] => eapply ValidTy_implies_ValidPTy_embed
  | [ |- ValidTy (isToEq ?τ) ] => eapply ValidPTy_implies_ValidTy_isToEq
  | [ |- ValidTy (repEmul ?τ) ] => eapply ValidPTy_implies_ValidTy_repEmul
  | [ |- ValidPTy (pEmulDV _ _ _) ] => eapply ValidTy_implies_ValidPTy_pEmulDV
  | [ |- ValidPTy (?τ₁ p⇒ ?τ₂) ] => eapply ValidPTy_arr
  | [ |- ValidPTy (ptrec _) ] => eapply ValidPTy_rec
  | [ |- ValidPEnv (embedCtx _) ] => eapply ValidEnv_implies_ValidPEnv_embedCtx
  | [ |- SimplePContr (embed _) ] => eapply SimpleContr_implies_SimplePContr_embed
  | [ |- ⟨ _ ⊢ embed _ ⟩ ] => eapply ws_embed
  end.
Section OfType.

  Local Ltac crush :=
    unfold OfType, OfTypeStlcIso, OfTypeStlcEqui; intros;
    repeat
      (subst;
       I.stlcCanForm;
       E.stlcCanForm;
       try apply ValidPTy_implies_ValidTy_repEmul;
       try apply ValidPTy_implies_ValidTy_isToEq;
       I.crushTyping;
       E.crushTyping;
       (* try apply ValidPTy_implies_ValidTy_repEmul; *)
       (* try apply ValidPTy_implies_ValidTy_isToEq; *)
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

  Lemma OfType_unit : OfType ptunit I.unit E.unit.
  Proof. crush. Qed.

  Lemma OfType_true : OfType ptbool I.true E.true.
  Proof. crush. Qed.

  Lemma OfType_false : OfType ptbool I.false E.false.
  Proof. crush. Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (I.inl ts) (E.inl tu).
  Proof.
    crush.
  Qed.

  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (I.inr ts) (E.inr tu).
  Proof. crush. Qed.

  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (I.pair ts₁ ts₂) (E.pair tu₁ tu₂).
  Proof. crush. Qed.

  Lemma OfType_lambda {τ₁ τ₂ τ₁' τ₁'' tsb tub} :
    τ₁' = repEmul τ₁ →
    ⟪ τ₁'' ≗ isToEq τ₁ ⟫ ->
    ValidTy τ₁'' ->
    ⟪ empty i⊢ I.abs (repEmul τ₁) tsb : repEmul τ₁ r⇒ repEmul τ₂ ⟫ →
    ⟪ empty e⊢ E.abs (isToEq τ₁) tub : isToEq τ₁ r⇒ isToEq τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (I.abs τ₁' tsb) (E.abs τ₁'' tub).
  Proof.
    assert (ValidEnv empty) by eauto with tyvalid.
    crush.
    repeat crushValidTyMatch2; try_typed_terms_are_valid; crush.
    refine (E.eqctx_implies_eqty _ _ _ _ _ _ _ H9); crush.
    constructor; crush.
    now eapply tyeq_symm.
  Qed.

  Lemma OfType_fold_ {τ ts tu} :
    ValidPTy (ptrec τ) →
    OfType (τ [beta1 (ptrec τ)]) ts tu →
    OfType (ptrec τ) (I.fold_ ts) tu.
  Proof. crush.
         - rewrite repEmul_sub in H3.
           enough (beta1 (ptrec τ) >-> repEmul = beta1 (trec (repEmul τ))) as <- by assumption.
           extensionality i.
           destruct i; now cbn.
         - now eapply (ValidPTy_implies_ValidTy_repEmul (τ := ptrec τ)).
         - assert (ValidTy (trec (isToEq τ))) as vμτ by now eapply (ValidPTy_implies_ValidTy_isToEq (τ := ptrec τ)).
           assert (ValidTy (isToEq (τ [beta1 (ptrec τ)]))) as vμτu by now eapply ValidPTy_implies_ValidTy_isToEq, ValidPTy_unfold_trec.
           refine (WtEq _ _ _ _ H2); try assumption.
           eapply EqMuR.
           destruct H.
           inversion H; subst.
           assert ⟨ beta1 (ptrec τ) : 1 => 0 ⟩ as wsbμτ by now eapply (wsSub_sub_beta1 (X := PTy)).
           rewrite (isToEq_sub H6 wsbμτ).
           enough (beta1 (ptrec τ) >-> isToEq = beta1 (trec (isToEq τ))) as -> by eapply tyeq_refl.
           extensionality i.
           destruct i; now cbn.
  Qed.

  Lemma OfType_inversion_ptunit {ts tu} :
    OfType ptunit ts tu →
    ts = I.unit ∧ tu = E.unit.
  Proof.
    crush.
  Qed.

  Lemma OfType_inversion_ptbool {ts tu} :
    OfType ptbool ts tu →
    ts = I.true ∧ tu = E.true ∨
    ts = I.true ∧ tu = E.false ∨
    ts = I.false ∧ tu = E.true ∨
    ts = I.false ∧ tu = E.false.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptsum {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType (ptsum τ₁ τ₂) ts tu →
    ∃ ts' tu',
      ts = I.inl ts' ∧ tu = E.inl tu' ∧ OfType τ₁ ts' tu' ∨
      ts = I.inl ts' ∧ tu = E.inr tu' ∨
      ts = I.inr ts' ∧ tu = E.inl tu' ∨
      ts = I.inr ts' ∧ tu = E.inr tu' ∧ OfType τ₂ ts' tu'.
  Proof.
    crush.
  Qed.

  Lemma OfType_inversion_ptprod {τ₁ τ₂ ts tu} :
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType (ptprod τ₁ τ₂) ts tu →
    ∃ ts₁ tu₁ ts₂ tu₂,
      ts = I.pair ts₁ ts₂ ∧
      tu = E.pair tu₁ tu₂ ∧
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
    ValidPTy τ₁ → ValidPTy τ₂ →
    OfType (τ₁ p⇒ τ₂) ts tu →
    ∃ ts' tu' τ₁',
      ts = I.abs (repEmul τ₁) ts' ∧
      tu = E.abs τ₁' tu' ∧
        ValidTy τ₁' ∧
        ⟪ τ₁' ≗ isToEq τ₁ ⟫ ∧
      ⟪ empty r▻ repEmul τ₁ i⊢ ts' : repEmul τ₂ ⟫ ∧
      ⟪ empty r▻ isToEq τ₁ e⊢ tu' : isToEq τ₂ ⟫.
  Proof.
    crush. eapply ValidTy_arr; crush.
  Qed.

  Lemma OfType_inversion_ptrec {τ ts tu} :
    ValidPTy (ptrec τ) →
    OfType (ptrec τ) ts tu →
    ∃ ts₁,
      ts = I.fold_ ts₁ ∧
      OfType (τ [beta1 (ptrec τ)]) ts₁ tu.
  Proof. crush.
         eexists; split; [reflexivity|].
         crush.
         - rewrite repEmul_sub.
           replace (beta1 (ptrec τ) >-> repEmul) with (beta1 (X := vrTy) (trec (repEmul τ))).
           assumption.
           extensionality i.
           destruct i; now cbn.
         - refine (WtEq _ _ _ _ H2).
           + eapply EqMuL.
             enough (⟨ 1 ⊢ τ ⟩) as wsτ.
             enough (⟨ beta1 (ptrec τ) : 1 => 0 ⟩) as wsbeta.
             rewrite (isToEq_sub wsτ wsbeta).
             enough (beta1 (trec (isToEq τ)) = beta1 (ptrec τ) >-> isToEq) as <-.
             now eapply tyeq_refl.
             extensionality i.
             destruct i; now cbn.
             eapply (wsSub_sub_beta1 (X := PTy)).
             now destruct H.
             destruct H.
             inversion H; now subst.
           + now eapply (ValidPTy_implies_ValidTy_isToEq (τ := ptrec τ)).
           + eapply (ValidPTy_implies_ValidTy_isToEq (τ := τ [ beta1 (ptrec τ)])).
             now eapply ValidPTy_unfold_trec.
  Qed.

  Lemma OfType_inversion_pEmulDV {n p ts tu τ} :
    OfType (pEmulDV n p τ) ts tu →
    I.Value ts ∧ E.Value tu ∧
    ⟪ empty i⊢ ts : UValIE n τ ⟫ ∧
    ⟪ empty e⊢ tu : τ ⟫.
  Proof. crush. Qed.

  Lemma OfTypeStlcIso_implies_Value {τ ts} :
    OfTypeStlcIso τ ts →
    I.Value ts.
  Proof.
    crush.
  Qed.

  Lemma OfTypeStlcEqui_implies_Value {τ tu} :
    OfTypeStlcEqui τ tu →
    E.Value tu.
  Proof.
    crush.
  Qed.

  Lemma OfType_implies_Value {τ ts tu} :
    OfType τ ts tu →
    I.Value ts ∧ E.Value tu.
  Proof.
    crush.
  Qed.

  Lemma OfType_pEmulDV {n p ts tu τ} :
    I.Value ts ∧ E.Value tu ∧
    ⟪ empty i⊢ ts : UValIE n τ ⟫ →
    ⟪ empty e⊢ tu : τ ⟫ →
    OfType (pEmulDV n p τ) ts tu.
  Proof. crush. Qed.

End OfType.

Ltac crushOfType :=
  repeat
    (match goal with
      | [ H: OfType _ _ _ |- ValidPTy _ ] => clear H (* prevent an infinite loop *)
      | [ H: OfType ptunit _ _ |- _ ] => apply OfType_inversion_ptunit in H
      | [ H: OfType ptbool _ _ |- _ ] => apply OfType_inversion_ptbool in H
      | [ H: OfType (ptrec _) _ _ |- _ ] => apply OfType_inversion_ptrec in H
      | [ H: OfType (_ p⊎ _) _ _ |- _ ] => apply OfType_inversion_ptsum in H
      | [ H: OfType (_ p× _) _ _ |- _ ] => apply OfType_inversion_ptprod in H
      | [ H: OfType (_ p⇒ _) _ _ |- _ ] => apply OfType_inversion_ptarr in H
      | [ H: OfType (pEmulDV _ _ _) _ _ |- _ ] => apply OfType_inversion_pEmulDV in H
      | [ |- OfType ptunit I.unit E.unit ] => apply OfType_unit
      | [ |- OfType ptbool I.true E.true ] => apply OfType_true
      | [ |- OfType ptbool I.false E.false ] => apply OfType_false
      | [ |- OfType (_ p⊎ _) (I.inl _) (E.inl _)] => apply OfType_inl
      | [ |- OfType (_ p⊎ _) (I.inr _) (E.inr _)] => apply OfType_inr
      | [ |- OfType (ptrec _) (I.fold_ _) _] => apply OfType_fold_
      | [ |- OfType (_ p× _) (I.pair _ _) (E.pair _ _) ] => apply OfType_pair
      | [ |- OfType (_ p⇒ _) (I.abs _ _) (E.abs _ _) ] => apply OfType_lambda
      (* | [ |- OfTypeUtlc _ _ ] => split *)
      | [ |- OfType (pEmulDV _ _ _) _ _ ] => apply OfType_pEmulDV
    end; try assumption; try reflexivity).
