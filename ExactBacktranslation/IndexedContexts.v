Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.AnnotatedGlobalCoercions.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcEqui.SpecAnnot.

Module ICI := StlcIso.SpecSyntax.
Module ICIA := StlcIso.SpecAnnot.
Module ICE := StlcEqui.SpecAnnot.

(** Certificate-indexed one-hole contexts.  This is deliberately structural:
    the hole is never encoded by abstracting it into a function, so plugging
    and compilation preserve the source CBV evaluation position. *)
Inductive ICCtx : Set :=
| icc_hole
| icc_abs (A B : Ty) (C : ICCtx)
| icc_app1 (A B : Ty) (C : ICCtx) (x : ICTm)
| icc_app2 (A B : Ty) (f : ICTm) (C : ICCtx)
| icc_ite1 (A : Ty) (C : ICCtx) (x y : ICTm)
| icc_ite2 (A : Ty) (b : ICTm) (C : ICCtx) (y : ICTm)
| icc_ite3 (A : Ty) (b x : ICTm) (C : ICCtx)
| icc_pair1 (A B : Ty) (C : ICCtx) (y : ICTm)
| icc_pair2 (A B : Ty) (x : ICTm) (C : ICCtx)
| icc_proj1 (A B : Ty) (C : ICCtx)
| icc_proj2 (A B : Ty) (C : ICCtx)
| icc_inl (A B : Ty) (C : ICCtx)
| icc_inr (A B : Ty) (C : ICCtx)
| icc_case1 (A B R : Ty) (C : ICCtx) (l r : ICTm)
| icc_case2 (A B R : Ty) (s : ICTm) (C : ICCtx) (r : ICTm)
| icc_case3 (A B R : Ty) (s l : ICTm) (C : ICCtx)
| icc_seq1 (A : Ty) (C : ICCtx) (y : ICTm)
| icc_seq2 (A : Ty) (x : ICTm) (C : ICCtx)
| icc_coerce (A B : Ty) (d : ClosedCastEq A B) (C : ICCtx).

Fixpoint plug_indexed (t : ICTm) (C : ICCtx) : ICTm :=
  match C with
  | icc_hole => t
  | icc_abs A B C0 => ic_abs A B (plug_indexed t C0)
  | icc_app1 A B C0 x => ic_app A B (plug_indexed t C0) x
  | icc_app2 A B f C0 => ic_app A B f (plug_indexed t C0)
  | icc_ite1 A C0 x y => ic_ite A (plug_indexed t C0) x y
  | icc_ite2 A b C0 y => ic_ite A b (plug_indexed t C0) y
  | icc_ite3 A b x C0 => ic_ite A b x (plug_indexed t C0)
  | icc_pair1 A B C0 y => ic_pair A B (plug_indexed t C0) y
  | icc_pair2 A B x C0 => ic_pair A B x (plug_indexed t C0)
  | icc_proj1 A B C0 => ic_proj1 A B (plug_indexed t C0)
  | icc_proj2 A B C0 => ic_proj2 A B (plug_indexed t C0)
  | icc_inl A B C0 => ic_inl A B (plug_indexed t C0)
  | icc_inr A B C0 => ic_inr A B (plug_indexed t C0)
  | icc_case1 A B R C0 l r => ic_case A B R (plug_indexed t C0) l r
  | icc_case2 A B R s C0 r => ic_case A B R s (plug_indexed t C0) r
  | icc_case3 A B R s l C0 => ic_case A B R s l (plug_indexed t C0)
  | icc_seq1 A C0 y => ic_seq A (plug_indexed t C0) y
  | icc_seq2 A x C0 => ic_seq A x (plug_indexed t C0)
  | icc_coerce A B d C0 => ic_coerce A B d (plug_indexed t C0)
  end.

Fixpoint erase_indexed_context (C : ICCtx) : ICE.PCtxA :=
  match C with
  | icc_hole => ICE.ea_phole
  | icc_abs A B C0 => ICE.ea_pabs A B (erase_indexed_context C0)
  | icc_app1 A B C0 x => ICE.ea_papp₁ A B (erase_indexed_context C0)
      (erase_indexed_certificate x)
  | icc_app2 A B f C0 => ICE.ea_papp₂ A B
      (erase_indexed_certificate f) (erase_indexed_context C0)
  | icc_ite1 A C0 x y => ICE.ea_pite₁ A (erase_indexed_context C0)
      (erase_indexed_certificate x) (erase_indexed_certificate y)
  | icc_ite2 A b C0 y => ICE.ea_pite₂ A (erase_indexed_certificate b)
      (erase_indexed_context C0) (erase_indexed_certificate y)
  | icc_ite3 A b x C0 => ICE.ea_pite₃ A (erase_indexed_certificate b)
      (erase_indexed_certificate x) (erase_indexed_context C0)
  | icc_pair1 A B C0 y => ICE.ea_ppair₁ A B (erase_indexed_context C0)
      (erase_indexed_certificate y)
  | icc_pair2 A B x C0 => ICE.ea_ppair₂ A B
      (erase_indexed_certificate x) (erase_indexed_context C0)
  | icc_proj1 A B C0 => ICE.ea_pproj₁ A B (erase_indexed_context C0)
  | icc_proj2 A B C0 => ICE.ea_pproj₂ A B (erase_indexed_context C0)
  | icc_inl A B C0 => ICE.ea_pinl A B (erase_indexed_context C0)
  | icc_inr A B C0 => ICE.ea_pinr A B (erase_indexed_context C0)
  | icc_case1 A B R C0 l r => ICE.ea_pcaseof₁ A B R
      (erase_indexed_context C0) (erase_indexed_certificate l)
      (erase_indexed_certificate r)
  | icc_case2 A B R s C0 r => ICE.ea_pcaseof₂ A B R
      (erase_indexed_certificate s) (erase_indexed_context C0)
      (erase_indexed_certificate r)
  | icc_case3 A B R s l C0 => ICE.ea_pcaseof₃ A B R
      (erase_indexed_certificate s) (erase_indexed_certificate l)
      (erase_indexed_context C0)
  | icc_seq1 A C0 y => ICE.ea_pseq₁ A (erase_indexed_context C0)
      (erase_indexed_certificate y)
  | icc_seq2 A x C0 => ICE.ea_pseq₂ A (erase_indexed_certificate x)
      (erase_indexed_context C0)
  | icc_coerce A B d C0 => ICE.ea_pcoerce A (erase_indexed_context C0)
  end.

Definition erase_indexed_context_raw (C : ICCtx) : StlcEqui.SpecSyntax.PCtx :=
  ICE.eraseAnnot_pctx (erase_indexed_context C).

Definition erase_indexed_term_raw (t : ICTm) : StlcEqui.SpecSyntax.Tm :=
  ICE.eraseAnnot (erase_indexed_certificate t).

Fixpoint compile_indexed_context (C : ICCtx) : ICI.PCtx :=
  match C with
  | icc_hole => ICI.phole
  | icc_abs A B C0 => ICI.pabs A (compile_indexed_context C0)
  | icc_app1 A B C0 x => ICI.papp₁ (compile_indexed_context C0)
      (compile_indexed x)
  | icc_app2 A B f C0 => ICI.papp₂ (compile_indexed f)
      (compile_indexed_context C0)
  | icc_ite1 A C0 x y => ICI.pite₁ (compile_indexed_context C0)
      (compile_indexed x) (compile_indexed y)
  | icc_ite2 A b C0 y => ICI.pite₂ (compile_indexed b)
      (compile_indexed_context C0) (compile_indexed y)
  | icc_ite3 A b x C0 => ICI.pite₃ (compile_indexed b)
      (compile_indexed x) (compile_indexed_context C0)
  | icc_pair1 A B C0 y => ICI.ppair₁ (compile_indexed_context C0)
      (compile_indexed y)
  | icc_pair2 A B x C0 => ICI.ppair₂ (compile_indexed x)
      (compile_indexed_context C0)
  | icc_proj1 A B C0 => ICI.pproj₁ (compile_indexed_context C0)
  | icc_proj2 A B C0 => ICI.pproj₂ (compile_indexed_context C0)
  | icc_inl A B C0 => ICI.pinl (compile_indexed_context C0)
  | icc_inr A B C0 => ICI.pinr (compile_indexed_context C0)
  | icc_case1 A B R C0 l r => ICI.pcaseof₁ (compile_indexed_context C0)
      (compile_indexed l) (compile_indexed r)
  | icc_case2 A B R s C0 r => ICI.pcaseof₂ (compile_indexed s)
      (compile_indexed_context C0) (compile_indexed r)
  | icc_case3 A B R s l C0 => ICI.pcaseof₃ (compile_indexed s)
      (compile_indexed l) (compile_indexed_context C0)
  | icc_seq1 A C0 y => ICI.pseq₁ (compile_indexed_context C0)
      (compile_indexed y)
  | icc_seq2 A x C0 => ICI.pseq₂ (compile_indexed x)
      (compile_indexed_context C0)
  | icc_coerce A B d C0 => ICI.papp₂ (compile_global_up d)
      (compile_indexed_context C0)
  end.

(** Direct, computational annotation insertion for structural contexts. *)
Fixpoint compile_indexed_context_annot (C : ICCtx) : ICIA.PCtxA :=
  match C with
  | icc_hole => ICIA.ia_phole
  | icc_abs A B C0 => ICIA.ia_pabs A B
      (compile_indexed_context_annot C0)
  | icc_app1 A B C0 x => ICIA.ia_papp₁ A B
      (compile_indexed_context_annot C0) (compile_indexed_annot x)
  | icc_app2 A B f C0 => ICIA.ia_papp₂ A B
      (compile_indexed_annot f) (compile_indexed_context_annot C0)
  | icc_ite1 A C0 x y => ICIA.ia_pite₁ A
      (compile_indexed_context_annot C0)
      (compile_indexed_annot x) (compile_indexed_annot y)
  | icc_ite2 A b C0 y => ICIA.ia_pite₂ A
      (compile_indexed_annot b) (compile_indexed_context_annot C0)
      (compile_indexed_annot y)
  | icc_ite3 A b x C0 => ICIA.ia_pite₃ A
      (compile_indexed_annot b) (compile_indexed_annot x)
      (compile_indexed_context_annot C0)
  | icc_pair1 A B C0 y => ICIA.ia_ppair₁ A B
      (compile_indexed_context_annot C0) (compile_indexed_annot y)
  | icc_pair2 A B x C0 => ICIA.ia_ppair₂ A B
      (compile_indexed_annot x) (compile_indexed_context_annot C0)
  | icc_proj1 A B C0 => ICIA.ia_pproj₁ A B
      (compile_indexed_context_annot C0)
  | icc_proj2 A B C0 => ICIA.ia_pproj₂ A B
      (compile_indexed_context_annot C0)
  | icc_inl A B C0 => ICIA.ia_pinl A B
      (compile_indexed_context_annot C0)
  | icc_inr A B C0 => ICIA.ia_pinr A B
      (compile_indexed_context_annot C0)
  | icc_case1 A B R C0 l r => ICIA.ia_pcaseof₁ A B R
      (compile_indexed_context_annot C0)
      (compile_indexed_annot l) (compile_indexed_annot r)
  | icc_case2 A B R s C0 r => ICIA.ia_pcaseof₂ A B R
      (compile_indexed_annot s) (compile_indexed_context_annot C0)
      (compile_indexed_annot r)
  | icc_case3 A B R s l C0 => ICIA.ia_pcaseof₃ A B R
      (compile_indexed_annot s) (compile_indexed_annot l)
      (compile_indexed_context_annot C0)
  | icc_seq1 A C0 y => ICIA.ia_pseq₁ A
      (compile_indexed_context_annot C0) (compile_indexed_annot y)
  | icc_seq2 A x C0 => ICIA.ia_pseq₂ A
      (compile_indexed_annot x) (compile_indexed_context_annot C0)
  | icc_coerce A B d C0 => ICIA.ia_papp₂ A B
      (compile_global_up_annot d) (compile_indexed_context_annot C0)
  end.

Reserved Notation "⟪ icc⊢ C : Gamma0 , A0 → Gamma , A ⟫"
  (at level 0, C at level 98, Gamma0 at level 98, A0 at level 98,
   Gamma at level 98, A at level 98).

Inductive ICCtxTyping (Gamma0 : Env) (A0 : Ty) :
    Env -> ICCtx -> Ty -> Prop :=
| ICC_Hole : ⟪icc⊢ icc_hole : Gamma0, A0 → Gamma0, A0⟫
| ICC_Abs {Gamma A B C} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma r▻ A, B⟫ -> ValidTy A ->
    ⟪icc⊢ icc_abs A B C : Gamma0, A0 → Gamma, tarr A B⟫
| ICC_App1 {Gamma A B C x} :
    ValidTy B ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma, tarr A B⟫ ->
    ⟪Gamma ic⊢ x : A⟫ ->
    ⟪icc⊢ icc_app1 A B C x : Gamma0, A0 → Gamma, B⟫
| ICC_App2 {Gamma A B f C} :
    ValidTy A -> ValidTy B ->
    ⟪Gamma ic⊢ f : tarr A B⟫ ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
    ⟪icc⊢ icc_app2 A B f C : Gamma0, A0 → Gamma, B⟫
| ICC_Ite1 {Gamma A C x y} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, tbool⟫ ->
    ⟪Gamma ic⊢ x : A⟫ -> ⟪Gamma ic⊢ y : A⟫ ->
    ⟪icc⊢ icc_ite1 A C x y : Gamma0, A0 → Gamma, A⟫
| ICC_Ite2 {Gamma A b C y} :
    ⟪Gamma ic⊢ b : tbool⟫ ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
    ⟪Gamma ic⊢ y : A⟫ ->
    ⟪icc⊢ icc_ite2 A b C y : Gamma0, A0 → Gamma, A⟫
| ICC_Ite3 {Gamma A b x C} :
    ⟪Gamma ic⊢ b : tbool⟫ -> ⟪Gamma ic⊢ x : A⟫ ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
    ⟪icc⊢ icc_ite3 A b x C : Gamma0, A0 → Gamma, A⟫
| ICC_Pair1 {Gamma A B C y} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ -> ⟪Gamma ic⊢ y : B⟫ ->
    ⟪icc⊢ icc_pair1 A B C y : Gamma0, A0 → Gamma, tprod A B⟫
| ICC_Pair2 {Gamma A B x C} :
    ⟪Gamma ic⊢ x : A⟫ -> ⟪icc⊢ C : Gamma0, A0 → Gamma, B⟫ ->
    ⟪icc⊢ icc_pair2 A B x C : Gamma0, A0 → Gamma, tprod A B⟫
| ICC_Proj1 {Gamma A B C} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, tprod A B⟫ ->
    ValidTy (tprod A B) ->
    ⟪icc⊢ icc_proj1 A B C : Gamma0, A0 → Gamma, A⟫
| ICC_Proj2 {Gamma A B C} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, tprod A B⟫ ->
    ValidTy (tprod A B) ->
    ⟪icc⊢ icc_proj2 A B C : Gamma0, A0 → Gamma, B⟫
| ICC_Inl {Gamma A B C} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ -> ValidTy B ->
    ⟪icc⊢ icc_inl A B C : Gamma0, A0 → Gamma, tsum A B⟫
| ICC_Inr {Gamma A B C} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, B⟫ -> ValidTy A ->
    ⟪icc⊢ icc_inr A B C : Gamma0, A0 → Gamma, tsum A B⟫
| ICC_Case1 {Gamma A B R C l r} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, tsum A B⟫ ->
    ⟪Gamma r▻ A ic⊢ l : R⟫ -> ⟪Gamma r▻ B ic⊢ r : R⟫ ->
    ValidTy A -> ValidTy B ->
    ⟪icc⊢ icc_case1 A B R C l r : Gamma0, A0 → Gamma, R⟫
| ICC_Case2 {Gamma A B R s C r} :
    ⟪Gamma ic⊢ s : tsum A B⟫ ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma r▻ A, R⟫ ->
    ⟪Gamma r▻ B ic⊢ r : R⟫ -> ValidTy A -> ValidTy B ->
    ⟪icc⊢ icc_case2 A B R s C r : Gamma0, A0 → Gamma, R⟫
| ICC_Case3 {Gamma A B R s l C} :
    ⟪Gamma ic⊢ s : tsum A B⟫ -> ⟪Gamma r▻ A ic⊢ l : R⟫ ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma r▻ B, R⟫ ->
    ValidTy A -> ValidTy B ->
    ⟪icc⊢ icc_case3 A B R s l C : Gamma0, A0 → Gamma, R⟫
| ICC_Seq1 {Gamma A C y} :
    ⟪icc⊢ C : Gamma0, A0 → Gamma, tunit⟫ -> ⟪Gamma ic⊢ y : A⟫ ->
    ⟪icc⊢ icc_seq1 A C y : Gamma0, A0 → Gamma, A⟫
| ICC_Seq2 {Gamma A x C} :
    ⟪Gamma ic⊢ x : tunit⟫ -> ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
    ⟪icc⊢ icc_seq2 A x C : Gamma0, A0 → Gamma, A⟫
| ICC_Coerce {Gamma A B d C} :
    ValidTy A -> ValidTy B ->
    ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
    ⟪icc⊢ icc_coerce A B d C : Gamma0, A0 → Gamma, B⟫
where "⟪ icc⊢ C : Gamma0 , A0 → Gamma , A ⟫" :=
  (ICCtxTyping Gamma0 A0 Gamma C A).

Theorem erase_indexed_context_typing {Gamma0 A0 Gamma C A} :
  ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
  ⟪ea⊢ erase_indexed_context C : Gamma0, A0 → Gamma, A⟫.
Proof.
  induction 1; cbn;
    eauto using ICE.PCtxTypingAnnot, erase_indexed_certificate_typing,
      casteq_sound.
Qed.

Theorem compile_indexed_context_typing {Gamma0 A0 Gamma C A} :
  ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
  ⟪i⊢ compile_indexed_context C : Gamma0, A0 → Gamma, A⟫.
Proof.
  induction 1; cbn;
    eauto using StlcIso.SpecTyping.PCtxTyping, compile_indexed_typing.
  eapply StlcIso.SpecTyping.WtPAppr.
  - now apply compile_global_up_typing.
  - exact IHICCtxTyping.
Qed.

Theorem compile_indexed_context_annot_typing
    {Gamma0 A0 Gamma C A} :
  ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
  ICIA.PCtxTypingAnnot Gamma0 A0 Gamma
    (compile_indexed_context_annot C) A.
Proof.
  induction 1; cbn;
    eauto using ICIA.PCtxTypingAnnot, compile_indexed_annot_typing.
  eapply ICIA.ia_WtPAppr.
  - exact H.
  - exact H0.
  - now apply compile_global_up_annot_typing.
  - exact IHICCtxTyping.
Qed.

Theorem erase_compile_indexed_context_annot (C : ICCtx) :
  ICIA.eraseAnnot_pctx (compile_indexed_context_annot C) =
  compile_indexed_context C.
Proof.
  induction C; cbn -[compile_global_up_annot];
    repeat rewrite erase_compile_indexed_annot;
    try rewrite erase_compile_global_up_annot;
    congruence.
Qed.

Theorem plug_indexed_typing {Gamma0 t A0 Gamma C A} :
  ⟪Gamma0 ic⊢ t : A0⟫ ->
  ⟪icc⊢ C : Gamma0, A0 → Gamma, A⟫ ->
  ⟪Gamma ic⊢ plug_indexed t C : A⟫.
Proof.
  intros Ht HC. induction HC; cbn;
    eauto using ICTyping.
Qed.

Theorem compile_plug_indexed t C :
  compile_indexed (plug_indexed t C) =
  ICI.pctx_app (compile_indexed t) (compile_indexed_context C).
Proof. induction C; cbn; congruence. Qed.

Theorem compile_plug_indexed_annot t C :
  compile_indexed_annot (plug_indexed t C) =
  ICIA.pctxA_app (compile_indexed_annot t)
    (compile_indexed_context_annot C).
Proof. induction C; cbn; congruence. Qed.

Theorem erase_plug_indexed t C :
  erase_indexed_term_raw (plug_indexed t C) =
  StlcEqui.SpecSyntax.pctx_app
    (erase_indexed_term_raw t) (erase_indexed_context_raw C).
Proof.
  unfold erase_indexed_term_raw, erase_indexed_context_raw.
  induction C; cbn; congruence.
Qed.

(** In particular, a conversion around the hole is compiled as an ordinary
    application around that same hole position. *)
Lemma compile_indexed_context_coerce_strict A B d C :
  compile_indexed_context (icc_coerce A B d C) =
  ICI.papp₂ (compile_global_up d) (compile_indexed_context C).
Proof. reflexivity. Qed.

Lemma compile_indexed_context_annot_coerce_strict A B d C :
  compile_indexed_context_annot (icc_coerce A B d C) =
  ICIA.ia_papp₂ A B (compile_global_up_annot d)
    (compile_indexed_context_annot C).
Proof. reflexivity. Qed.
