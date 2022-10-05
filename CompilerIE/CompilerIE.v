Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.LemmasTypes.
(* Require Import StlcFix.SpecScoping. *)
(* Require Import StlcFix.LemmasScoping. *)
(* Require Import StlcFix.DecideEval. *)
Require Import UValIE.UVal.
Require Import LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import Lia.
Require Import Db.Lemmas.

Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.CanForm.
Require Import StlcIso.SpecEquivalent.
Require Import StlcIso.Size.

Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.SpecAnnot.
Require Import StlcEqui.LemmasTyping.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.CanForm.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.Size.

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
  Include StlcIso.Size.
End I.

Module E.
  Include RecTypes.SpecTypes.
  Include RecTypes.InstTy.
  Include RecTypes.LemmasTypes.

  Include StlcEqui.SpecEvaluation.
  Include StlcEqui.SpecSyntax.
  Include StlcEqui.SpecTyping.
  Include StlcEqui.SpecAnnot.
  Include StlcEqui.LemmasTyping.
  Include StlcEqui.LemmasEvaluation.
  Include StlcEqui.CanForm.
  Include StlcEqui.Size.
End E.

Fixpoint compie (t : I.Tm) : E.Tm :=
  match t with
    | I.var x => E.var x
    | I.abs τ t => E.abs τ (compie t)
    | I.app t1 t2 => E.app (compie t1) (compie t2)
    | I.unit => E.unit
    | I.true => E.true
    | I.false => E.false
    | I.ite t1 t2 t3 => E.ite (compie t1) (compie t2) (compie t3)
    | I.pair t1 t2 => E.pair (compie t1) (compie t2)
    | I.proj₁ t => E.proj₁ (compie t)
    | I.proj₂ t => E.proj₂ (compie t)
    | I.inl t => E.inl (compie t)
    | I.inr t => E.inr (compie t)
    | I.caseof t1 t2 t3 => E.caseof (compie t1) (compie t2) (compie t3)
    | I.seq t1 t2 => E.seq (compie t1) (compie t2)
    | I.fold_ t => compie t
    | I.unfold_ t => compie t
  end.

Fixpoint compie_annot (t : I.TmA) : E.TmA :=
  match t with
    | I.ia_var x => E.ea_var x
    | I.ia_abs τ₁ τ₂ t => E.ea_abs τ₁ τ₂ (compie_annot t)
    | I.ia_app τ₁ τ₂ t1 t2 => E.ea_app τ₁ τ₂ (compie_annot t1) (compie_annot t2)
    | I.ia_unit => E.ea_unit
    | I.ia_true => E.ea_true
    | I.ia_false => E.ea_false
    | I.ia_ite τ t1 t2 t3 => E.ea_ite τ (compie_annot t1) (compie_annot t2) (compie_annot t3)
    | I.ia_pair τ₁ τ₂ t1 t2 => E.ea_pair τ₁ τ₂ (compie_annot t1) (compie_annot t2)
    | I.ia_proj₁ τ₁ τ₂ t => E.ea_proj₁ τ₁ τ₂ (compie_annot t)
    | I.ia_proj₂ τ₁ τ₂ t => E.ea_proj₂ τ₁ τ₂ (compie_annot t)
    | I.ia_inl τ₁ τ₂ t => E.ea_inl τ₁ τ₂ (compie_annot t)
    | I.ia_inr τ₁ τ₂ t => E.ea_inr τ₁ τ₂ (compie_annot t)
    | I.ia_caseof τ₁ τ₂ τ t1 t2 t3 => E.ea_caseof τ₁ τ₂ τ (compie_annot t1) (compie_annot t2) (compie_annot t3)
    | I.ia_seq τ t₁ t₂ => E.ea_seq (τ) (compie_annot t₁) (compie_annot t₂)
    | I.ia_fold_ τ t => E.ea_coerce τ[beta1 (trec τ)] (compie_annot t)
    | I.ia_unfold_ τ t => E.ea_coerce (trec τ) (compie_annot t)
  end.

(* The two compiler definitions are the same modulo type annotations. *)
Lemma compie_compie_annot {t} :
  compie (I.eraseAnnot t) = E.eraseAnnot (compie_annot t).
Proof.
  induction t; cbn; f_equal; try assumption; try reflexivity.
Qed.

Fixpoint compie_pctx_annot (C : I.PCtxA) : E.PCtxA :=
  match C with
  | I.ia_phole => E.ea_phole
  | I.ia_pabs τ₁ τ₂ C => E.ea_pabs τ₁ τ₂ (compie_pctx_annot C)
  | I.ia_papp₁ τ₁ τ₂ C t => E.ea_papp₁ τ₁ τ₂ (compie_pctx_annot C) (compie_annot t)
  | I.ia_papp₂ τ₁ τ₂ t C => E.ea_papp₂ τ₁ τ₂ (compie_annot t) (compie_pctx_annot C)
  | I.ia_pite₁ τ C t₂ t₃ => E.ea_pite₁ τ (compie_pctx_annot C) (compie_annot t₂) (compie_annot t₃)
  | I.ia_pite₂ τ t₁ C t₃ => E.ea_pite₂ τ (compie_annot t₁) (compie_pctx_annot C) (compie_annot t₃)
  | I.ia_pite₃ τ t₁ t₂ C => E.ea_pite₃ τ (compie_annot t₁) (compie_annot t₂) (compie_pctx_annot C)
  | I.ia_ppair₁ τ₁ τ₂ C t => E.ea_ppair₁ τ₁ τ₂ (compie_pctx_annot C) (compie_annot t)
  | I.ia_ppair₂ τ₁ τ₂ t C => E.ea_ppair₂ τ₁ τ₂ (compie_annot t) (compie_pctx_annot C)
  | I.ia_pproj₁ τ₁ τ₂ C => E.ea_pproj₁ τ₁ τ₂ (compie_pctx_annot C)
  | I.ia_pproj₂ τ₁ τ₂ C => E.ea_pproj₂ τ₁ τ₂ (compie_pctx_annot C)
  | I.ia_pinl τ₁ τ₂ C => E.ea_pinl τ₁ τ₂ (compie_pctx_annot C)
  | I.ia_pinr τ₁ τ₂ C => E.ea_pinr τ₁ τ₂ (compie_pctx_annot C)
  | I.ia_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ => E.ea_pcaseof₁ τ₁ τ₂ τ (compie_pctx_annot C) (compie_annot t₂) (compie_annot t₃)
  | I.ia_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ => E.ea_pcaseof₂ τ₁ τ₂ τ (compie_annot t₁) (compie_pctx_annot C) (compie_annot t₃)
  | I.ia_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => E.ea_pcaseof₃ τ₁ τ₂ τ (compie_annot t₁) (compie_annot t₂) (compie_pctx_annot C)
  | I.ia_pseq₁ τ C t₂ => E.ea_pseq₁ τ (compie_pctx_annot C) (compie_annot t₂)
  | I.ia_pseq₂ τ t₁ C => E.ea_pseq₂ τ (compie_annot t₁) (compie_pctx_annot C)
  | I.ia_pfold τ C => E.ea_pcoerce (τ[beta1 (trec τ)]) (compie_pctx_annot C)
  | I.ia_punfold τ C => E.ea_pcoerce (trec τ) (compie_pctx_annot C)
  end.

Lemma smoke_test_compiler :
  (compie_annot I.ia_unit) = E.ea_unit.
Proof.
  simpl. reflexivity.
Qed.

Lemma compie_typing_works {Γ t τ} :
  ⟪ Γ i⊢ t : τ ⟫ →
  ⟪ Γ e⊢ compie t : τ ⟫.
Proof.
  induction 1; I.crushTyping; E.crushTyping; eauto using I.AnnotTyping, E.AnnotTyping;
    inversion H0 as (cl & cr);
    inversion cr; subst;
    econstructor;
    [| | | | apply tyeq_symm | | |];
    try apply ty_eq_unfoldrec;
    try assumption;
    eauto using ValidTy_unfold_trec, tyeq_refl.
Qed.

Lemma compie_annot_typing_works {Γ t τ} :
  ⟪ Γ ia⊢ t : τ ⟫ →
  ⟪ Γ ea⊢ compie_annot t : τ ⟫.
Proof.
  induction 1; I.crushTyping; E.crushTyping; eauto using I.AnnotTyping, E.AnnotTyping;
    inversion H0 as (cl & cr);
    inversion cr; subst;
    econstructor;
    [| | | | apply tyeq_symm | | |];
    try apply ty_eq_unfoldrec;
    try assumption;
    eauto using ValidTy_unfold_trec, tyeq_refl.
Qed.

Lemma compie_pctx_annot_typing_works {C Γ Γ' τ τ'} :
  ⟪ ia⊢ C : Γ, τ → Γ', τ' ⟫ →
  ⟪ ea⊢ compie_pctx_annot C : Γ, τ →
  Γ', τ' ⟫.
Proof.
  induction 1; eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H1.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H1.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H0, H1.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H, H1.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H, H0.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H0, H1.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H, H1.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H, H0.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eauto using PCtxTypingAnnot, compie_typing_works.
    cbn.
    econstructor.
    apply ty_eq_unfoldrec.
    crushValidTy.
    exact IHPCtxTypingAnnot.
    apply ValidTy_unfold_trec.
    apply ValidTy_rec.
    assert (0 ≤ 1) as H' by lia.
    eapply (WsTy_mono H').
    crushValidTy.
    crushValidTy.
    apply ValidTy_rec.
    assert (0 ≤ 1) as H' by lia.
    eapply (WsTy_mono H').
    crushValidTy.
    crushValidTy.
  - cbn.
    econstructor.
    apply tyeq_symm.
    apply ty_eq_unfoldrec.
    crushValidTy.
    exact IHPCtxTypingAnnot.
    assumption.
    now apply ValidTy_unfold_trec.
  - eapply compie_annot_typing_works in H0.
    eauto using PCtxTypingAnnot, compie_typing_works.
  - eapply compie_annot_typing_works in H.
    eauto using PCtxTypingAnnot, compie_typing_works.
Qed.

Local Ltac crush :=
  cbn in * |- ;
  repeat
    (cbn;
     repeat crushLRMatch2;
     try assumption;
     crushOfType;
     I.crushTyping;
     E.crushTyping;
     repeat crushValidPTyMatch;
     repeat crushValidTyMatch2;
     repeat crushRepEmulEmbed;
     repeat I.crushStlcSyntaxMatchH;
     repeat E.crushStlcSyntaxMatchH;
     subst); try lia; auto.

Section CompatibilityLemmas.

  Lemma compat_lambda {Γ τ' ts d n τ} {tu : E.Tm}:
    ValidPEnv Γ -> ValidPTy τ' -> ValidPTy τ ->
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (I.abs (repEmul τ') ts) ⟦ d , n ⟧ (E.abs (isToEq τ') tu) : ptarr τ' τ ⟫.
  Proof.
    intros vΓ vτ' vτ.
    repeat (try crushLRMatch; crush).
    - eauto using I.wtSub_up, envrel_implies_WtSub_iso.
    - eauto using E.wtSub_up, envrel_implies_WtSub_equi.
    - repeat eexists; try reflexivity.
      intros w' fw vs vu szvu vr.
      rewrite -> ?ap_comp.
      apply H3; crush.
  Qed.

  Lemma compat_lambda_embed {Γ τ' ts d n tu τ} :
    ValidPEnv Γ -> ValidTy τ' -> ValidPTy τ ->
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (I.abs τ' ts) ⟦ d , n ⟧ (E.abs (isToEq (embed τ')) tu) : ptarr (embed τ') τ ⟫.
  Proof.
    intros vΓ vτ' vτ.
    rewrite <- (repEmul_embed_leftinv τ') at 2.
    apply compat_lambda; crush.
  Qed.

  Lemma compat_lambda_embed' {Γ τ' ts d n tu τ} :
    ValidPEnv Γ -> ValidTy τ' -> ValidPTy τ ->
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (I.abs τ' ts) ⟦ d , n ⟧ (E.abs τ' tu) : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite <-(isToEq_embed_leftinv τ') at 4.
    now apply compat_lambda_embed.
  Qed.

  Lemma compat_unit {Γ d n} :
    ⟪ Γ ⊩ I.unit ⟦ d , n ⟧ E.unit : ptunit ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
  Qed.

  Lemma compat_true {Γ d n} :
    ⟪ Γ ⊩ I.true ⟦ d , n ⟧ E.true : ptbool ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
  Qed.

  Lemma compat_false {Γ d n} :
    ⟪ Γ ⊩ I.false ⟦ d , n ⟧ E.false : ptbool ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
  Qed.

  Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ I.pair ts₁ ts₂ ⟦ d , n ⟧ E.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    apply termrel_pair; crush.
    refine (H7 w' _ _ _ _); unfold lev in *; try lia.
    eauto using envrel_mono.
  Qed.

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ I.app ts₁ ts₂ ⟦ d , n ⟧ E.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂.
    repeat (try crushLRMatch; crush).
    refine (termrel_app vτ₁ _ _ _); crush.
    refine (H4 _ _ _ _ _); crush.
  Qed.

  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ I.inl ts ⟦ d , n ⟧ E.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    eapply termrel_inl; crush.
  Qed.

  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ I.inr ts ⟦ d , n ⟧ E.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    refine (termrel_inr _ _ _); crush.
  Qed.

  Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} :
    ValidPEnv Γ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ I.seq ts₁ ts₂ ⟦ d , n ⟧ E.seq tu₁ tu₂ : τ₂ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    apply termrel_seq; crush.
    refine (H6 w' _ _ _ _); crush.
  Qed.

  Lemma compat_proj₂ {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ I.proj₂ ts ⟦ d , n ⟧ E.proj₂ tu : τ₂ ⟫.
  Proof.
    intros vτ₁ vτ₂.
    repeat (try crushLRMatch; crush).
    refine (termrel_proj₂ vτ₁ _ _); crush.
  Qed.

  Lemma compat_proj₁ {Γ d n ts tu τ₁ τ₂} :
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptprod τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ I.proj₁ ts ⟦ d , n ⟧ E.proj₁ tu : τ₁ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    refine (termrel_proj₁ _ _ _); crush.
  Qed.

  Lemma compat_ite {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ} :
    ValidPEnv Γ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptbool ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ I.ite ts₁ ts₂ ts₃ ⟦ d , n ⟧ E.ite tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    apply termrel_ite; crush.
    - refine (H8 w' _ _ _ _); crush.
    - refine (H6 w' _ _ _ _); crush.
  Qed.

  Lemma compat_caseof {Γ d n ts₁ tu₁ ts₂ tu₂ ts₃ tu₃ τ₁ τ₂ τ} :
    ValidPEnv Γ ->
    ValidPTy τ₁ -> ValidPTy τ₂ ->
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptsum τ₁ τ₂ ⟫ →
    ⟪ Γ p▻ τ₁ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ ⟫ →
    ⟪ Γ p▻ τ₂ ⊩ ts₃ ⟦ d , n ⟧ tu₃ : τ ⟫ →
    ⟪ Γ ⊩ I.caseof ts₁ ts₂ ts₃ ⟦ d , n ⟧ E.caseof tu₁ tu₂ tu₃ : τ ⟫.
  Proof.
    intros vΓ vτ₁ vτ₂ rel₁ rel₂ rel₃.
    split; [|split].
    - unfold OpenLRN in *.
      crush.
    - unfold OpenLRN in *.
      crush.
    - intros.
      simpl.
      refine (termrel_caseof vτ₁ _ _ _ _);
        repeat (try crushLRMatch; crush);
        rewrite -> ?ap_comp.
      + refine (H8 w' _ _ _ _); crush.
      + refine (H5 w' _ _ _ _); crush.
  Qed.

  Lemma compat_unfold_ {Γ d n ts tu τ} :
    ValidPTy (ptrec τ) ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : ptrec τ ⟫ →
    ⟪ Γ ⊩ I.unfold_ ts ⟦ d , n ⟧ tu : τ [beta1 (ptrec τ)] ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    - rewrite repEmul_sub.
      replace (beta1 (ptrec τ) >-> repEmul) with (beta1 (trec (repEmul τ))) by (extensionality i; destruct i; now cbn).
      eapply I.WtUnfold; crushValidTy; eauto using repEmul_preserves_ws, repEmul_preserves_contr.
    - refine (E.WtEq _ _ _ _ H2).
      eapply EqMuL.
      enough ⟨ beta1 (ptrec τ) : 1 => 0 ⟩ as wsbμτ.
      rewrite (isToEq_sub H wsbμτ).
      replace (beta1 (ptrec τ) >-> isToEq) with (beta1 (trec (isToEq τ))) by (extensionality i; destruct i; now cbn).
      now eapply tyeq_refl.
      refine (wsSub_sub_beta1 _ _ _).
      now constructor.
      eauto using ValidTy_rec, isToEq_preserves_ws, isToEq_preserves_contr.
      eapply ValidPTy_implies_ValidTy_isToEq, ValidPTy_unfold_trec; crush.
    - eapply termrel_unfold_; crush.
  Qed.

  Lemma compat_fold_ {Γ d n ts tu τ} :
    ValidPTy (ptrec τ) ->
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ [beta1 (ptrec τ)] ⟫ →
    ⟪ Γ ⊩ I.fold_ ts ⟦ d , n ⟧ tu : ptrec τ ⟫.
  Proof.
    repeat (try crushLRMatch; crush).
    - rewrite repEmul_sub in H0.
      now replace (beta1 (ptrec τ) >-> repEmul) with (beta1 (trec (repEmul τ))) in H0 by (extensionality i; destruct i; now cbn).
    - eapply (ValidPTy_implies_ValidTy_repEmul (τ := ptrec τ)).
      crush.
    - refine (E.WtEq _ _ _ _ H2).
      eapply EqMuR.
      enough ⟨ beta1 (ptrec τ) : 1 => 0 ⟩ as wsbμτ.
      rewrite (isToEq_sub H wsbμτ).
      replace (beta1 (ptrec τ) >-> isToEq) with (beta1 (trec (isToEq τ))) by (extensionality i; destruct i; now cbn).
      now eapply tyeq_refl.
      refine (wsSub_sub_beta1 _ _ _).
      now constructor.
      eapply ValidPTy_implies_ValidTy_isToEq, ValidPTy_unfold_trec; crush.
      eapply (ValidPTy_implies_ValidTy_isToEq (τ := ptrec τ)); crush.
    - eapply termrel_fold_; crush.
  Qed.

  Ltac crushCompatMatch :=
    match goal with
    | [ |- ⟪ _ ⊩ I.abs _ _ ⟦ _ , _ ⟧ E.abs _ _ : _ ⟫ ] => eapply compat_lambda_embed'
    | [ |- ⟪ _ ⊩ I.app _ _ ⟦ _ , _ ⟧ E.app _ _ : _ ⟫ ] => eapply compat_app
    | [ |- ⟪ _ ⊩ I.seq _ _ ⟦ _ , _ ⟧ E.seq _ _ : _ ⟫ ] => eapply compat_seq
    | [ |- ⟪ _ ⊩ I.var _ ⟦ _ , _ ⟧ E.var _ : _ ⟫ ] => eapply compat_var
    | [ |- ⟪ _ ⊩ I.inl _ ⟦ _ , _ ⟧ E.inl _ : _ ⟫ ] => eapply compat_inl
    | [ |- ⟪ _ ⊩ I.inr _ ⟦ _ , _ ⟧ E.inr _ : _ ⟫ ] => eapply compat_inr
    | [ |- ⟪ _ ⊩ I.proj₁ _ ⟦ _ , _ ⟧ E.proj₁ _ : _ ⟫ ] => eapply compat_proj₁
    | [ |- ⟪ _ ⊩ I.proj₂ _ ⟦ _ , _ ⟧ E.proj₂ _ : _ ⟫ ] => eapply compat_proj₂
    | [ |- ⟪ _ ⊩ I.unit ⟦ _ , _ ⟧ E.unit : _ ⟫ ] => eapply compat_unit
    | [ |- ⟪ _ ⊩ I.true ⟦ _ , _ ⟧ E.true : _ ⟫ ] => eapply compat_true
    | [ |- ⟪ _ ⊩ I.false ⟦ _ , _ ⟧ E.false : _ ⟫ ] => eapply compat_false
    | [ |- ⟪ _ ⊩ I.pair _ _ ⟦ _ , _ ⟧ E.pair _ _ : _ ⟫ ] => eapply compat_pair
    | [ |- ⟪ _ ⊩ I.ite _ _ _ ⟦ _ , _ ⟧ E.ite _ _ _ : _ ⟫ ] => eapply compat_ite
    | [ |- ⟪ _ ⊩ I.caseof _ _ _ ⟦ _ , _ ⟧ E.caseof _ _ _ : _ ⟫ ] => eapply compat_caseof
    | [ |- ⟪ _ ⊩ I.unfold_ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => eapply compat_unfold_
    | [ |- ⟪ _ ⊩ I.fold_ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => eapply compat_fold_
    end.

  Ltac tryValidTyFromTyping :=
    try match goal with
    | [ H : ⟪ _ i⊢ _ : ?τ ⟫ |- ValidTy ?τ ] => refine (I.typed_terms_are_valid _ _ _ H)
    | [ H : ⟪ _ ia⊢ _ : ?τ ⟫ |- ValidTy ?τ ] => refine (I.typed_terms_are_valid _ _ _ (I.eraseAnnotT H))
    end.

Local Ltac crush2 :=
  cbn in * |- ;
  repeat
    (cbn;
     tryValidTyFromTyping;
     try crushCompatMatch;
     try crushLRMatch2;
     try assumption;
     crushOfType;
     I.crushTyping;
     E.crushTyping;
     try crushValidPTyMatch;
     try crushValidTyMatch2;
     try crushRepEmulEmbed;
     try I.crushStlcSyntaxMatchH;
     try E.crushStlcSyntaxMatchH;
     subst); try lia; auto.

  Lemma compie_correct {Γ d n ts τ} :
    ValidEnv Γ -> ValidTy τ ->
    ⟪ Γ i⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compie ts : embed τ ⟫.
  Proof.
    intros vΓ vτ.
    induction 1;
      cbn;
      rewrite ?compiler_is_isToEq_embed, ?eraseAnnot_ufix;
      crush2;
      auto using embedCtx_works with ptyvalid.
    2: eapply IHTyping1; crush2.
    2: eapply IHTyping2; crush2.
    3: eapply IHTyping; crush2.
    4: eapply IHTyping; crush2.
    all: repeat (crushValidPTyMatch; tryValidTyFromTyping; try assumption).
    - eapply I.ValidTy_invert_prod.
      eauto using I.typed_terms_are_valid.
    - refine (proj1 (I.ValidTy_invert_prod _)).
      eauto using I.typed_terms_are_valid.
    - replace (embed (τ[beta1 (trec τ)])) with (embed τ) [beta1 (ptrec (embed τ))] in IHTyping.
      eapply IHTyping; crush.
      enough (beta1 (trec τ) >-> embed = beta1 (ptrec (embed τ))) as <-.
      now rewrite embed_sub.
      extensionality i; destruct i; now cbn.
    - replace (embed (τ[beta1 (trec τ)])) with (embed τ) [beta1 (ptrec (embed τ))].
      eapply compat_unfold_; crush.
      enough (beta1 (trec τ) >-> embed = beta1 (ptrec (embed τ))) as <-.
      now rewrite embed_sub.
      extensionality i; destruct i; now cbn.
  Qed.

  Lemma compie_correct' {Γ d n ts τ τ'} :
    ValidEnv Γ -> ValidTy τ ->
    ⟪ Γ i⊢ ts : τ ⟫ →
    τ' = embed τ ->
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ compie ts : τ' ⟫.
  Proof.
    intros; subst; now eapply compie_correct.
  Qed.

  Lemma compie_annot_correct {Γ d n ts τ} :
    ValidEnv Γ -> ValidTy τ ->
    ⟪ Γ ia⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ I.eraseAnnot ts ⟦ d , n ⟧ E.eraseAnnot (compie_annot ts) : embed τ ⟫.
  Proof.
    intros vΓ vτ.
    induction 1;
      cbn.
    - eapply compat_var, embedCtx_works; crush.
    - eapply compat_lambda_embed'; crush.
    - pose proof (I.typed_terms_are_valid _ _ vΓ (I.eraseAnnotT H)).
      pose proof (I.typed_terms_are_valid _ _ vΓ (I.eraseAnnotT H0)).
      eapply compat_app; crush; now crushValidPTyMatch.
    - eapply compat_unit; crush.
    - eapply compat_true; crush.
    - eapply compat_false; crush.
    - eapply compat_ite; crush.
    - eapply compat_pair; crush.
    - pose proof (I.typed_terms_are_valid _ _ vΓ (I.eraseAnnotT H)).
      eapply compat_proj₁; crush.
      crush.
    - pose proof (I.typed_terms_are_valid _ _ vΓ (I.eraseAnnotT H)).
      eapply compat_proj₂; crush.
      crush.
    - eapply compat_inl; crush.
    - eapply compat_inr; crush.
    - eapply compat_caseof; crush.
      crush.
      crush.
    - eapply compat_fold_; crush.
      rewrite embed_sub in IHAnnotTyping.
      enough ((beta1 (trec τ) >-> embed) = (beta1 (ptrec (embed τ)))) as <-.
      eapply IHAnnotTyping; crush.
      extensionality i; destruct i; now cbn.
    - rewrite embed_sub.
      enough ((beta1 (trec τ) >-> embed) = (beta1 (ptrec (embed τ)))) as ->.
      eapply compat_unfold_; crush.
      extensionality i; destruct i; now cbn.
    - eapply compat_seq; crush.
  Qed.

  Lemma compie_ctx_correct {Γ Γ' d n C τ τ'} :
    ValidEnv Γ -> ValidEnv Γ' -> ValidTy τ -> ValidTy τ' ->
    ⟪ ia⊢ C : Γ , τ → Γ' , τ'⟫ →
    ⟪ ⊩ I.eraseAnnot_pctx C ⟦ d , n ⟧ eraseAnnot_pctx (compie_pctx_annot C) : embedCtx Γ , embed τ → embedCtx Γ' , embed τ' ⟫.
  Proof.
    intros vΓ vΓ' vτ vτ' ty; unfold OpenLRCtxN; split; [|split].
    - rewrite ?repEmul_embed_leftinv in *.
      rewrite ?repEmulCtx_embedCtx_leftinv in *.
      now eapply I.eraseAnnot_pctxT.
    - rewrite ?isToEqCtx_embedCtx_leftinv.
      rewrite ?isToEq_embed_leftinv.
      now eapply E.eraseAnnot_pctxT, compie_pctx_annot_typing_works.
    - induction ty; intros ts tu trel; cbn.
      + crush.
      + eapply compat_lambda_embed'; crush.
      + pose proof (I.typed_terms_are_valid _ _ vΓ' (I.eraseAnnotT H0)).
        eapply compat_app; crush.
        crush.
        eapply compie_annot_correct; crush.
      + pose proof (I.typed_terms_are_valid _ _ vΓ' (I.eraseAnnotT H1)).
        eapply compat_app; crush.
        crush.
        change (embed τ₁ p⇒ embed τ₂) with (embed (tarr τ₁ τ₂)).
        eapply compie_annot_correct; crush.
      + eapply compat_ite; crush.
        eapply compie_annot_correct; crush.
        eapply compie_annot_correct; crush.
      + eapply compat_ite; crush.
        change ptbool with (embed tbool).
        eapply compie_annot_correct; crush.
        eapply compie_annot_correct; crush.
      + eapply compat_ite; crush.
        change ptbool with (embed tbool).
        eapply compie_annot_correct; crush.
        eapply compie_annot_correct; crush.
      + eapply compat_pair; crush.
        eapply compie_annot_correct; crush.
      + eapply compat_pair; crush.
        eapply compie_annot_correct; crush.
      + eapply compat_proj₁; crush.
        crush.
      + eapply compat_proj₂; crush.
        crush.
      + eapply compat_inl; crush.
      + eapply compat_inr; crush.
      + eapply compat_caseof; crush.
        crush. crush.
        change (embedCtx Γ0 p▻ embed τ₁) with (embedCtx (evar Γ0 τ₁)).
        eapply compie_annot_correct; crush.
        change (embedCtx Γ0 p▻ embed τ₂) with (embedCtx (evar Γ0 τ₂)).
        eapply compie_annot_correct; crush.
      + eapply (compat_caseof (τ₂ := embed τ₂)); crush.
        crush.
        change (embed τ₁ p⊎ embed τ₂) with (embed (tsum τ₁ τ₂)).
        eapply compie_annot_correct; crush.
        change (embedCtx Γ0 p▻ embed τ₂) with (embedCtx (evar Γ0 τ₂)).
        eapply compie_annot_correct; crush.
      + eapply (compat_caseof (τ₁ := embed τ₁)); crush.
        crush.
        change (embed τ₁ p⊎ embed τ₂) with (embed (tsum τ₁ τ₂)).
        eapply compie_annot_correct; crush.
        change (embedCtx Γ0 p▻ embed τ₁) with (embedCtx (evar Γ0 τ₁)).
        eapply compie_annot_correct; crush.
      + eapply compat_fold_; crush.
        rewrite embed_sub in IHty.
        replace (beta1 (trec τ0) >-> embed) with (beta1 (ptrec (embed τ0))) in IHty.
        eapply IHty; crush.
        extensionality i; destruct i; now cbn.
      + rewrite embed_sub.
        replace (beta1 (trec τ0) >-> embed) with (beta1 (ptrec (embed τ0))).
        eapply compat_unfold_; crush.
        extensionality i; destruct i; now cbn.
      + eapply compat_seq; crush.
        eapply compie_annot_correct; crush.
      + eapply compat_seq; crush.
        change ptunit with (embed tunit).
        eapply compie_annot_correct; crush.
    Qed.

End CompatibilityLemmas.

Lemma equivalenceReflection {Γ t₁ t₂ τ} :
  ValidEnv Γ -> ValidTy τ ->
  ⟪ Γ i⊢ t₁ : τ ⟫ →
  ⟪ Γ i⊢ t₂ : τ ⟫ →
  ⟪ Γ e⊢ compie t₁ ≃ compie t₂ : τ ⟫ →
  ⟪ Γ i⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂} τ,
             ValidEnv Γ -> ValidTy τ ->
            ⟪ Γ i⊢ t₁ : τ ⟫ →
            ⟪ Γ i⊢ t₂ : τ ⟫ →
            ⟪ Γ e⊢ compie t₁ ≃ compie t₂ : τ ⟫ →
            ∀ C τ', ⟪ ia⊢ C : Γ , τ → I.empty, τ' ⟫ →
                    I.Terminating (I.pctx_app t₁ (I.eraseAnnot_pctx C)) → I.Terminating (I.pctx_app t₂ (I.eraseAnnot_pctx C))) as Hltor.
  { intros t₁ t₂ τ vΓ vτ ty1 ty2 eq C τ'.
    assert (⟪ Γ e⊢ compie t₂ ≃ compie t₁ : τ ⟫) by (now apply E.pctx_equiv_symm).
    split;
      now refine (Hltor _ _ τ _ _ _ _ _ C τ' _).
  }

  intros t₁ t₂ τ vΓ vτ ty1 ty2 eq C τ' tyC term.
  assert (ValidTy τ') as vτ'.
  { eapply (I.typed_terms_are_valid _ _ ValidEnv_nil).
    eapply (I.pctxtyping_app ty1).
    eapply (I.eraseAnnot_pctxT tyC).
  }

  destruct (I.Terminating_TermHor term) as [n termN]; clear term.

  assert (⟪ embedCtx Γ ⊩ t₁ ⟦ dir_lt , S n ⟧ compie t₁ : embed τ ⟫) as lrt₁ by exact (compie_correct vΓ vτ ty1).

  assert (⟪ ⊩ (I.eraseAnnot_pctx C) ⟦ dir_lt , S n ⟧ E.eraseAnnot_pctx (compie_pctx_annot C) : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_lt
      by apply (compie_ctx_correct vΓ ValidEnv_nil vτ vτ' tyC).

  apply lrC_lt in lrt₁.

  assert (E.Terminating (E.pctx_app (compie t₁) (E.eraseAnnot_pctx (compie_pctx_annot C))))
    as termu₁.
  { apply (adequacy_lt lrt₁ termN).
    lia.
  }

  assert (E.Terminating (E.pctx_app (compie t₂) (E.eraseAnnot_pctx (compie_pctx_annot C)))).
  { eapply (eq _ _ vτ'); try assumption.
    now eapply compie_pctx_annot_typing_works.
  }

  destruct (E.Terminating_TermHor H) as [n' termN']; clear H.

  assert (⟪ ⊩ I.eraseAnnot_pctx C ⟦ dir_gt , S n' ⟧ E.eraseAnnot_pctx (compie_pctx_annot C) : embedCtx Γ , embed τ → pempty , embed τ' ⟫) as lrC_gt
    by (apply (compie_ctx_correct vΓ ValidEnv_nil vτ vτ' tyC)).

  assert (⟪ embedCtx Γ ⊩ t₂ ⟦ dir_gt , S n' ⟧ compie t₂ : embed τ ⟫) as lrt₂ by exact (compie_correct vΓ vτ ty2).

  apply lrC_gt in lrt₂.

  apply (adequacy_gt lrt₂ termN'); lia.
Qed.

Lemma equivalenceReflectionEmpty {t₁ t₂ τ} :
  ValidTy τ ->
  ⟪ I.empty i⊢ t₁ : τ ⟫ →
  ⟪ I.empty i⊢ t₂ : τ ⟫ →
  ⟪ E.empty e⊢ compie t₁ ≃ compie t₂ : τ ⟫ →
  ⟪ I.empty i⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  apply @equivalenceReflection; crushValidTy.
Qed.

Print Assumptions equivalenceReflectionEmpty.
