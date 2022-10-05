Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.LemmasTypes.
(* Require Import StlcFix.SpecScoping. *)
(* Require Import StlcFix.LemmasScoping. *)
(* Require Import StlcFix.DecideEval. *)
Require Import LogRelFI.PseudoType.
Require Import LogRelFI.LemmasPseudoType.
Require Import LogRelFI.LR.
Require Import LogRelFI.LemmasLR.
Require Import LogRelFI.LemmasIntro.
Require Import Lia.
Require Import Db.Lemmas.

Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.SpecAnnot.
Require Import StlcFix.LemmasTyping.
Require Import StlcFix.LemmasEvaluation.
Require Import StlcFix.CanForm.
Require Import StlcFix.SpecEquivalent.
Require Import StlcFix.Size.

Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.CanForm.
Require Import StlcIso.Fix.
Require Import StlcIso.SpecEquivalent.
Require Import StlcIso.Size.

Module F.
  Include StlcFix.SpecEvaluation.
  Include StlcFix.SpecSyntax.
  Include StlcFix.SpecTyping.
  Include StlcFix.SpecAnnot.
  Include StlcFix.LemmasTyping.
  Include StlcFix.LemmasEvaluation.
  Include StlcFix.CanForm.
  Include StlcFix.Size.
End F.

Module I.
  Include RecTypes.SpecTypes.
  Include RecTypes.InstTy.
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
End I.

Fixpoint compfi_ty (τ : F.Ty) : I.Ty :=
  match τ with
    | F.tunit => I.tunit
    | F.tbool => I.tbool
    | F.tprod τ1 τ2 => I.tprod (compfi_ty τ1) (compfi_ty τ2)
    | F.tarr τ1 τ2 => I.tarr (compfi_ty τ1) (compfi_ty τ2)
    | F.tsum τ1 τ2 => I.tsum (compfi_ty τ1) (compfi_ty τ2)
  end.

Fixpoint compfi_env (Γ : F.Env) : I.Env :=
  match Γ with
    | F.empty => I.empty
    | F.evar Γ τ => I.evar (compfi_env Γ) (compfi_ty τ)
  end.

Fixpoint compfi (t : F.Tm) : I.Tm :=
  match t with
    | F.var x => I.var x
    | F.abs τ t => I.abs (compfi_ty τ) (compfi t)
    | F.app t1 t2 => I.app (compfi t1) (compfi t2)
    | F.unit => I.unit
    | F.true => I.true
    | F.false => I.false
    | F.ite t1 t2 t3 => I.ite (compfi t1) (compfi t2) (compfi t3)
    | F.pair t1 t2 => I.pair (compfi t1) (compfi t2)
    | F.proj₁ t => I.proj₁ (compfi t)
    | F.proj₂ t => I.proj₂ (compfi t)
    | F.inl t => I.inl (compfi t)
    | F.inr t => I.inr (compfi t)
    | F.caseof t1 t2 t3 => I.caseof (compfi t1) (compfi t2) (compfi t3)
    | F.seq t1 t2 => I.seq (compfi t1) (compfi t2)
    | F.fixt τ1 τ2 t => I.app (I.ufix (compfi_ty τ1) (compfi_ty τ2)) (compfi t)
  end.

Fixpoint compfi_annot (t : F.TmA) : I.TmA :=
  match t with
    | F.a_var x => I.ia_var x
    | F.a_abs τ₁ τ₂ t => I.ia_abs (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t)
    | F.a_app τ₁ τ₂ t1 t2 => I.ia_app (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t1) (compfi_annot t2)
    | F.a_unit => I.ia_unit
    | F.a_true => I.ia_true
    | F.a_false => I.ia_false
    | F.a_ite τ t1 t2 t3 => I.ia_ite (compfi_ty τ) (compfi_annot t1) (compfi_annot t2) (compfi_annot t3)
    | F.a_pair τ₁ τ₂ t1 t2 => I.ia_pair (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t1) (compfi_annot t2)
    | F.a_proj₁ τ₁ τ₂ t => I.ia_proj₁ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t)
    | F.a_proj₂ τ₁ τ₂ t => I.ia_proj₂ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t)
    | F.a_inl τ₁ τ₂ t => I.ia_inl (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t)
    | F.a_inr τ₁ τ₂ t => I.ia_inr (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t)
    | F.a_caseof τ₁ τ₂ τ t1 t2 t3 => I.ia_caseof (compfi_ty τ₁) (compfi_ty τ₂) (compfi_ty τ) (compfi_annot t1) (compfi_annot t2) (compfi_annot t3)
    | F.a_seq τ t₁ t₂ => I.ia_seq (compfi_ty τ) (compfi_annot t₁) (compfi_annot t₂)
    | F.a_fixt τ1 τ2 t => I.ia_app (tarr (tarr (compfi_ty τ1) (compfi_ty τ2)) (tarr (compfi_ty τ1) (compfi_ty τ2))) (tarr (compfi_ty τ1) (compfi_ty τ2)) (I.ufix_annot (compfi_ty τ1) (compfi_ty τ2)) (compfi_annot t)
  end.

(* The two compiler definitions are the same modulo type annotations. *)
Lemma compfi_compfi_annot {t} :
  compfi (F.eraseAnnot t) = I.eraseAnnot (compfi_annot t).
Proof.
  induction t; cbn; f_equal; try assumption; try reflexivity.
Qed.

Fixpoint compfi_pctx_annot (C : F.PCtxA) : I.PCtxA :=
  match C with
  | F.a_phole => I.ia_phole
  | F.a_pabs τ₁ τ₂ C => I.ia_pabs (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C)
  | F.a_papp₁ τ₁ τ₂ C t => I.ia_papp₁ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C) (compfi_annot t)
  | F.a_papp₂ τ₁ τ₂ t C => I.ia_papp₂ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t) (compfi_pctx_annot C)
  | F.a_pite₁ τ C t₂ t₃ => I.ia_pite₁ (compfi_ty τ) (compfi_pctx_annot C) (compfi_annot t₂) (compfi_annot t₃)
  | F.a_pite₂ τ t₁ C t₃ => I.ia_pite₂ (compfi_ty τ) (compfi_annot t₁) (compfi_pctx_annot C) (compfi_annot t₃)
  | F.a_pite₃ τ t₁ t₂ C => I.ia_pite₃ (compfi_ty τ) (compfi_annot t₁) (compfi_annot t₂) (compfi_pctx_annot C)
  | F.a_ppair₁ τ₁ τ₂ C t => I.ia_ppair₁ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C) (compfi_annot t)
  | F.a_ppair₂ τ₁ τ₂ t C => I.ia_ppair₂ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_annot t) (compfi_pctx_annot C)
  | F.a_pproj₁ τ₁ τ₂ C => I.ia_pproj₁ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C)
  | F.a_pproj₂ τ₁ τ₂ C => I.ia_pproj₂ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C)
  | F.a_pinl τ₁ τ₂ C => I.ia_pinl (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C)
  | F.a_pinr τ₁ τ₂ C => I.ia_pinr (compfi_ty τ₁) (compfi_ty τ₂) (compfi_pctx_annot C)
  | F.a_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ => I.ia_pcaseof₁ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_ty τ) (compfi_pctx_annot C) (compfi_annot t₂) (compfi_annot t₃)
  | F.a_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ => I.ia_pcaseof₂ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_ty τ) (compfi_annot t₁) (compfi_pctx_annot C) (compfi_annot t₃)
  | F.a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => I.ia_pcaseof₃ (compfi_ty τ₁) (compfi_ty τ₂) (compfi_ty τ) (compfi_annot t₁) (compfi_annot t₂) (compfi_pctx_annot C)
  | F.a_pseq₁ τ C t₂ => I.ia_pseq₁ (compfi_ty τ) (compfi_pctx_annot C) (compfi_annot t₂)
  | F.a_pseq₂ τ t₁ C => I.ia_pseq₂ (compfi_ty τ) (compfi_annot t₁) (compfi_pctx_annot C)
  | F.a_pfixt τ₁ τ₂ C => I.ia_papp₂ (tarr (tarr (compfi_ty τ₁) (compfi_ty τ₂)) (tarr (compfi_ty τ₁) (compfi_ty τ₂)))
                                   (tarr (compfi_ty τ₁) (compfi_ty τ₂))
                                   (I.ufix_annot (compfi_ty τ₁) (compfi_ty τ₂))
                                   (compfi_pctx_annot C)
  end.

Lemma smoke_test_compiler :
  (compfi_annot F.a_unit) = I.ia_unit.
Proof.
  simpl. reflexivity.
Qed.

Lemma compfi_getevar_works {i τ Γ} :
  ⟪ i : τ ∈ Γ ⟫ →
  ⟪ i : compfi_ty τ r∈ compfi_env Γ ⟫.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma validTy_compfi_ty {τ} : ValidTy (compfi_ty τ).
Proof.
  induction τ; cbn.
  - now apply ValidTy_arr.
  - now apply ValidTy_unit.
  - now apply ValidTy_bool.
  - now apply ValidTy_prod.
  - now apply ValidTy_sum.
Qed.

Lemma compfi_typing_works {Γ t τ} :
  ⟪ Γ ⊢ t : τ ⟫ →
  ⟪ compfi_env Γ i⊢ compfi t : compfi_ty τ ⟫.
Proof.
  induction 1; F.crushTyping; I.crushTyping; eauto using I.AnnotTyping, compfi_getevar_works, I.ufix_typing, validTy_compfi_ty.
Qed.

Lemma compfi_annot_typing_works {Γ t τ} :
  ⟪ Γ a⊢ t : τ ⟫ →
  ⟪ compfi_env Γ ia⊢ compfi_annot t : compfi_ty τ ⟫.
Proof.
  induction 1; F.crushTyping; I.crushTyping; eauto using I.AnnotTyping, compfi_getevar_works, I.ufix_annot_typing, validTy_compfi_ty.
Qed.

Lemma compfi_pctx_annot_typing_works {C Γ Γ' τ τ'} :
  ⟪ a⊢ C : Γ, τ → Γ', τ' ⟫ →
  ⟪ ia⊢ compfi_pctx_annot C : compfi_env Γ, compfi_ty τ →
  compfi_env Γ', compfi_ty τ' ⟫.
Proof.
  induction 1; eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty.
  - eapply compfi_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty with tyvalid.
  - eapply compfi_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty with tyvalid.
  - eapply compfi_annot_typing_works in H0, H1.
    eauto using PCtxTypingAnnot, compfi_typing_works.
  - eapply compfi_annot_typing_works in H, H1.
    eauto using PCtxTypingAnnot, compfi_typing_works.
  - eapply compfi_annot_typing_works in H, H0.
    eauto using PCtxTypingAnnot, compfi_typing_works.
  - eapply compfi_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compfi_typing_works.
  - eapply compfi_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compfi_typing_works.
  - eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty with tyvalid.
  - eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty with tyvalid.
  - eapply compfi_annot_typing_works in H0, H1.
    eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty.
  - eapply compfi_annot_typing_works in H, H1.
    eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty.
  - eapply compfi_annot_typing_works in H, H0.
    eauto using PCtxTypingAnnot, compfi_typing_works, validTy_compfi_ty.
  - eapply compfi_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compfi_typing_works, I.ufix_annot_typing.
  - eapply compfi_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compfi_typing_works, I.ufix_annot_typing.
  - eauto using PCtxTypingAnnot, compfi_typing_works, I.ufix_annot_typing, validTy_compfi_ty with tyvalid2.
    cbn.
    constructor; eauto using ufix_annot_typing, validTy_compfi_ty with tyvalid.
Qed.

Lemma compileCtx_works {Γ i τ} :
  F.GetEvar Γ i τ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP.
Qed.

Local Ltac crush :=
  cbn in * |- ;
  repeat
    (cbn;
     repeat crushLRMatch;
     crushOfType;
     F.crushTyping;
     I.crushTyping;
     repeat crushRepEmulEmbed;
     repeat crushRecTypesMatchH;
     repeat F.crushStlcSyntaxMatchH;
     repeat I.crushStlcSyntaxMatchH;
     subst;
     trivial
    ); try lia; eauto.

Lemma compiler_is_fxToIs_embed :
  ∀ τ : F.Ty, compfi_ty τ = fxToIs (embed τ).
Proof.
  induction τ; simpl;
    try rewrite IHτ1; try rewrite IHτ2;
      reflexivity.
Qed.

Lemma compiler_is_fxToIs_embed_env :
  ∀ Γ : F.Env, compfi_env Γ = fxToIsCtx (embedCtx Γ).
Proof.
  induction Γ; crush; apply compiler_is_fxToIs_embed.
Qed.

Section CompatibilityLemmas.


  Lemma compat_lambda {Γ τ' ts d n tu τ} :
    ValidPTy τ -> ValidPTy τ' -> ValidPEnv Γ ->
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs (repEmul τ') ts) ⟦ d , n ⟧ (I.abs (fxToIs τ') tu) : ptarr τ' τ ⟫.
  Proof.
    crush.
    - eauto using I.wtSub_up, envrel_implies_WtSub_iso, validTy_fxToIs.
    - eauto using I.wtSub_up, envrel_implies_WtSub_iso, validTy_fxToIs.
    - eauto using I.wtSub_up, envrel_implies_WtSub_iso, validTy_fxToIs.
    - eauto using F.wtSub_up, envrel_implies_WtSub, validTy_fxToIs.
    - repeat eexists; try reflexivity.
      intros w' fw vs vu szvu vr.
      rewrite -> ?ap_comp.
      apply H4; [lia|].
      eauto using extend_envrel, envrel_mono.
  Qed.

  Lemma compat_lambda_embed {Γ τ' ts d n tu τ} :
    ValidPEnv Γ -> ValidPTy τ ->
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs τ' ts) ⟦ d , n ⟧ (I.abs (fxToIs (embed τ')) tu) : ptarr (embed τ') τ ⟫.
  Proof.
    intros vΓ vτ.
    rewrite <- (repEmul_embed_leftinv τ') at 2.
    apply compat_lambda; eauto using validPTy_embed.
  Qed.

  Lemma compat_lambda_embed' {Γ τ' ts d n tu τ} :
    ValidPEnv Γ -> ValidPTy τ ->
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (F.abs τ' ts) ⟦ d , n ⟧ (I.abs (compfi_ty τ') tu) : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite (compiler_is_fxToIs_embed τ').
    apply compat_lambda_embed.
  Qed.

  Lemma compat_unit {Γ d n} :
    ⟪ Γ ⊩ F.unit ⟦ d , n ⟧ I.unit : ptunit ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_true {Γ d n} :
    ⟪ Γ ⊩ F.true ⟦ d , n ⟧ I.true : ptbool ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_false {Γ d n} :
    ⟪ Γ ⊩ F.false ⟦ d , n ⟧ I.false : ptbool ⟫.
  Proof.
    crush.
  Qed.

  Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ F.pair ts₁ ts₂ ⟦ d , n ⟧ I.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫.
  Proof.
    crush.
    apply termrel_pair; crush.
    refine (H5 w' _ _ _ _); unfold lev in *; try lia.
    eauto using envrel_mono.
  Qed.

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ F.app ts₁ ts₂ ⟦ d , n ⟧ I.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_app _ _); crush.
    refine (H5 w' _ _ _ _); unfold lev in *; try lia.
    crush.
  Qed.

  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ F.inl ts ⟦ d , n ⟧ I.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush; eauto using validTy_fxToIs.
    refine (termrel_inl _ _ _); crush.
  Qed.

  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ F.inr ts ⟦ d , n ⟧ I.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush; eauto using validTy_fxToIs.
    refine (termrel_inr _ _ _); crush.
  Qed.

  Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ F.seq ts₁ ts₂ ⟦ d , n ⟧ I.seq tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    apply termrel_seq; crush.
    refine (H4 w' _ _ _ _); crush.
  Qed.

  Lemma compat_proj₂ {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ F.proj₂ ts ⟦ d , n ⟧ I.proj₂ tu : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_proj₂ _); crush.
  Qed.

  Lemma compat_proj₁ {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ F.proj₁ ts ⟦ d , n ⟧ I.proj₁ tu : τ₁ ⟫.
  Proof.
    crush.
    refine (termrel_proj₁ _); crush.
  Qed.

  Lemma compat_ite {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptbool ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ F.ite ts₁ ts₂ ts₃ ⟦ d , n ⟧ I.ite tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    crush.
    apply termrel_ite; crush.
    - refine (H5 w' _ _ _ _); crush.
    - refine (H3 w' _ _ _ _); crush.
  Qed.

  Lemma compat_caseof {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ₁ τ₂ τ} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptsum τ₁ τ₂ ⟫ →
    ⟪ Γ p▻ τ₁ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ p▻ τ₂ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ F.caseof ts₁ ts₂ ts₃ ⟦ d , n ⟧ I.caseof tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂.
    crush;
    try now apply validTy_fxToIs.
    refine (termrel_caseof _ _ _); crush;
    rewrite -> ?ap_comp.
    - refine (H5 w' _ _ _ _); crush.
    - refine (H3 w' _ _ _ _); crush.
  Qed.

  Lemma compat_fix {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂) ⟫ →
    ⟪ Γ ⊩ F.fixt (repEmul τ₁) (repEmul τ₂) ts ⟦ d , n ⟧ I.app (I.ufix (fxToIs τ₁) (fxToIs τ₂)) tu : ptarr τ₁ τ₂ ⟫.
  Proof.
    crush.
    - eauto using I.ufix_typing, validTy_fxToIs.
    - refine (termrel_fix _ _ _); crush.
  Qed.

  Lemma compat_fix' {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ →
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (F.tarr (F.tarr τ₁ τ₂) (F.tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ F.fixt τ₁ τ₂ ts ⟦ d , n ⟧ I.app (I.ufix (compfi_ty τ₁) (compfi_ty τ₂)) tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    intros vΓ tr.
    rewrite <- (repEmul_embed_leftinv τ₁) at 1.
    rewrite <- (repEmul_embed_leftinv τ₂) at 1.
    rewrite (compiler_is_fxToIs_embed τ₁) at 1.
    rewrite (compiler_is_fxToIs_embed τ₂) at 1.
    apply compat_fix; eauto using validPTy_embed.
  Qed.

  Lemma compat_fix'' {Γ d n ts tu τ₁ τ₂} :
    ValidPEnv Γ →
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed (F.tarr (F.tarr τ₁ τ₂) (F.tarr τ₁ τ₂)) ⟫ →
    ⟪ Γ ⊩ F.fixt τ₁ τ₂ ts ⟦ d , n ⟧ I.app (I.ufix (fxToIs (embed τ₁)) (fxToIs (embed τ₂))) tu : ptarr (embed τ₁) (embed τ₂) ⟫.
  Proof.
    rewrite <- (compiler_is_fxToIs_embed τ₁) at 1.
    rewrite <- (compiler_is_fxToIs_embed τ₂) at 1.
    exact compat_fix'.
  Qed.

  Lemma compfi_correct {Γ d n ts τ} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compfi ts : embed τ ⟫.
  Proof.
    induction 1;
      cbn -[I.ufix_annot I.ufix₁_annot];
      rewrite ?compiler_is_fxToIs_embed, ?eraseAnnot_ufix;
      eauto using compat_inl
      , compat_inr
      , compat_pair
      , compat_lambda_embed
      , compat_app
      , compat_false, compat_true
      , compat_var
      , compat_unit
      , embedCtx_works
      , compat_seq
      , compat_ite, compat_proj₁, compat_proj₂
      , compat_caseof
      , compat_fix''
      , validPTy_embed
      , validPEnv_embedCtx.
  Qed.

  Lemma compfi_correct' {Γ d n ts τ τ'} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    τ' = embed τ ->
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compfi ts : τ' ⟫.
  Proof.
    intros; subst; now eapply compfi_correct.
  Qed.

  Lemma compfi_annot_correct {Γ d n ts τ} :
    ⟪ Γ a⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ F.eraseAnnot ts ⟦ d , n ⟧ I.eraseAnnot (compfi_annot ts) : embed τ ⟫.
  Proof.
    induction 1;
      cbn -[I.ufix_annot I.ufix₁_annot];
      rewrite ?compiler_is_fxToIs_embed, ?eraseAnnot_ufix;
      eauto using compat_inl
      , compat_inr
      , compat_pair
      , compat_lambda_embed
      , compat_app
      , compat_false, compat_true
      , compat_var
      , compat_unit
      , embedCtx_works
      , compat_seq
      , compat_ite, compat_proj₁, compat_proj₂
      , compat_caseof
      , compat_fix''
      , validPTy_embed
      , validPEnv_embedCtx.
  Qed.

  Lemma compfi_ctx_correct {Γ Γ' d n C τ τ'} :
    ⟪ a⊢ C : Γ , τ → Γ' , τ'⟫ →
    ⟪ ⊩ F.eraseAnnot_pctx C ⟦ d , n ⟧ eraseAnnot_pctx (compfi_pctx_annot C) : embedCtx Γ , embed τ → embedCtx Γ' , embed τ' ⟫.
  Proof.
    intros ty; unfold OpenLRCtxN; split; [|split];
      rewrite <-?compiler_is_fxToIs_embed in *;
      rewrite <-?compiler_is_fxToIs_embed_env in *;
      rewrite ?repEmul_embed_leftinv in *;
      rewrite ?repEmulCtx_embedCtx_leftinv in *;
      eauto using F.eraseAnnot_pctxT, I.eraseAnnot_pctxT, compfi_pctx_annot_typing_works, F.pctxtyping_app, F.eraseAnnot_pctxT, I.pctxtyping_app, I.eraseAnnot_pctxT.

    induction ty; simpl;
    intros ts tu lr;
      try assumption; (* deal with phole *)
      specialize (IHty ts tu lr);
      rewrite <-?compfi_compfi_annot;
      repeat (try match goal with
             | [ |- ⟪_⊩ F.abs _ _ ⟦d,n⟧ I.abs _ _ : _ ⟫ ] => eapply compat_lambda_embed'
             | [ |- ⟪_⊩ F.app _ _ ⟦d,n⟧ I.app _ _ : _ ⟫ ] => eapply compat_app
             | [ |- ⟪_⊩ F.ite _ _ _ ⟦d,n⟧ I.ite _ _ _ : _ ⟫ ] => eapply compat_ite
             | [ |- ⟪_⊩ F.pair _ _ ⟦d,n⟧ I.pair _ _ : _ ⟫ ] => eapply compat_pair
             | [ |- ⟪_⊩ F.inl _ ⟦d,n⟧ I.inl _ : _ ⟫ ] => eapply compat_inl
             | [ |- ⟪_⊩ F.inr _ ⟦d,n⟧ I.inr _ : _ ⟫ ] => eapply compat_inr
             | [ |- ⟪_⊩ F.proj₁ _ ⟦d,n⟧ I.proj₁ _ : _ ⟫ ] => eapply compat_proj₁
             | [ |- ⟪_⊩ F.proj₂ _ ⟦d,n⟧ I.proj₂ _ : _ ⟫ ] => eapply compat_proj₂
             | [ |- ⟪_⊩ F.fixt _ _ _ ⟦d,n⟧ _ : _ ⟫ ] => eapply compat_fix'
             | [ |- ⟪_⊩ F.caseof _ _ _ ⟦d,n⟧ I.caseof _ _ _ : _ ⟫ ] => eapply compat_caseof
             | [ |- ⟪_⊩ F.seq _ _ ⟦d,n⟧ I.seq _ _ : _ ⟫ ] => eapply compat_seq
             (* | [ |- context[ ptarr (embed ?τ1) (embed ?τ2) ]] => *)
             (*   change (ptarr (embed τ1) (embed τ2)) with (embed (F.tarr τ1 τ2)) *)
             | [ |- ⟪_⊩ _ ⟦d,n⟧ compfi _ : _ ⟫ ] => eapply compfi_correct'
             | [ |- ⟪ _ ⊢ F.eraseAnnot _ : _ ⟫ ] => eapply F.eraseAnnotT
             | [ |- ⟪ _ ⊢ I.eraseAnnot _ : _ ⟫ ] => eapply I.eraseAnnotT
              end;
              eauto using validPTy_embed, validPEnv_embedCtx;
              try eassumption;
              fold embed;
              try reflexivity;
              change (embedCtx ?Γ p▻ embed ?τ) with (embedCtx (Γ ▻ τ))).
  Qed.

End CompatibilityLemmas.

Lemma equivalenceReflection {Γ t₁ t₂ τ} :
  ⟪ Γ ⊢ t₁ : τ ⟫ →
  ⟪ Γ ⊢ t₂ : τ ⟫ →
  ⟪ compfi_env Γ i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫ →
  ⟪ Γ ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂} τ,
            ⟪ Γ ⊢ t₁ : τ ⟫ →
            ⟪ Γ ⊢ t₂ : τ ⟫ →
            ⟪ compfi_env Γ i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫ →
            ∀ C τ', ⟪ a⊢ C : Γ , τ → F.empty, τ' ⟫ →
                    F.Terminating (F.pctx_app t₁ (F.eraseAnnot_pctx C)) → F.Terminating (F.pctx_app t₂ (F.eraseAnnot_pctx C))) as Hltor
  by (intros t₁ t₂ τ ty1 ty2 eq C τ';
      assert (⟪ compfi_env Γ i⊢ compfi t₂ ≃ compfi t₁ : compfi_ty τ ⟫)
        by (apply I.pctx_equiv_symm; assumption);
  split;
  refine (Hltor _ _ τ _ _ _ C τ' _); assumption).

  intros t₁ t₂ τ ty1 ty2 eq C τ' tyC term.

  destruct (F.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ embedCtx Γ ⊩ t₁ ⟦ dir_lt , S n ⟧ compfi t₁ : embed τ ⟫) as lrt₁ by exact (compfi_correct ty1).

  assert (⟪ ⊩ (F.eraseAnnot_pctx C) ⟦ dir_lt , S n ⟧ I.eraseAnnot_pctx (compfi_pctx_annot C) : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_lt
      by apply (compfi_ctx_correct tyC).

  apply lrC_lt in lrt₁.

  assert (I.Terminating (I.pctx_app (compfi t₁) (I.eraseAnnot_pctx (compfi_pctx_annot C))))
    as termu₁ by (apply (adequacy_lt lrt₁ termN); lia).

  assert (I.Terminating (I.pctx_app (compfi t₂) (I.eraseAnnot_pctx (compfi_pctx_annot C)))).
  eapply eq; try assumption; eauto using compfi_pctx_annot_typing_works, validTy_compfi_ty.
  apply (compfi_pctx_annot_typing_works tyC).

  destruct (I.Terminating_TermHor H) as [n' termN']; clear H.

  assert (⟪ ⊩ F.eraseAnnot_pctx C ⟦ dir_gt , S n' ⟧ I.eraseAnnot_pctx (compfi_pctx_annot C) : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_gt
    by (apply (compfi_ctx_correct tyC)).

  assert (⟪ embedCtx Γ ⊩ t₂ ⟦ dir_gt , S n' ⟧ compfi t₂ : embed τ ⟫) as lrt₂ by exact (compfi_correct ty2).

  apply lrC_gt in lrt₂.

  apply (adequacy_gt lrt₂ termN'); lia.
Qed.

Lemma equivalenceReflectionEmpty {t₁ t₂ τ} :
  ⟪ F.empty ⊢ t₁ : τ ⟫ →
  ⟪ F.empty ⊢ t₂ : τ ⟫ →
  ⟪ I.empty i⊢ compfi t₁ ≃ compfi t₂ : compfi_ty τ ⟫ →
  ⟪ F.empty ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  apply @equivalenceReflection.
Qed.

