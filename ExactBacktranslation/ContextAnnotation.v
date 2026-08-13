Require Import StlcIso.SpecAnnot.
Require Import StlcIso.SpecEquivalent.
Require Import ExactBacktranslation.IndexedContexts.

Module IA := StlcIso.SpecAnnot.

(** A raw typing derivation carries enough type information to recover a
    fully annotated term.  This is a proof-level reification only; compiler
    computation never eliminates a typing proof in [Prop]. *)
Theorem iso_typing_has_annotation {Gamma t A} :
  StlcIso.SpecTyping.Typing Gamma t A ->
  exists ta, IA.AnnotTyping Gamma ta A /\ IA.eraseAnnot ta = t.
Proof.
  induction 1.
  - exists (IA.ia_var i). split; [now constructor|reflexivity].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_abs τ₁ τ₂ ta). split; [now constructor|cbn; congruence].
  - destruct IHTyping1 as (ta1 & Hta1 & He1).
    destruct IHTyping2 as (ta2 & Hta2 & He2).
    exists (IA.ia_app τ₁ τ₂ ta1 ta2). split;
      [now constructor|cbn; congruence].
  - exists IA.ia_unit. split; [constructor|reflexivity].
  - exists IA.ia_true. split; [constructor|reflexivity].
  - exists IA.ia_false. split; [constructor|reflexivity].
  - destruct IHTyping1 as (ta1 & Hta1 & He1).
    destruct IHTyping2 as (ta2 & Hta2 & He2).
    destruct IHTyping3 as (ta3 & Hta3 & He3).
    exists (IA.ia_ite T ta1 ta2 ta3). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping1 as (ta1 & Hta1 & He1).
    destruct IHTyping2 as (ta2 & Hta2 & He2).
    exists (IA.ia_pair τ₁ τ₂ ta1 ta2). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_proj₁ τ₁ τ₂ ta). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_proj₂ τ₁ τ₂ ta). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_inl τ₁ τ₂ ta). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_inr τ₁ τ₂ ta). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping1 as (ta1 & Hta1 & He1).
    destruct IHTyping2 as (ta2 & Hta2 & He2).
    destruct IHTyping3 as (ta3 & Hta3 & He3).
    exists (IA.ia_caseof τ₁ τ₂ T ta1 ta2 ta3). split;
      [now constructor|cbn; congruence].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_fold_ τ ta). split; [now constructor|cbn; congruence].
  - destruct IHTyping as (ta & Hta & He).
    exists (IA.ia_unfold_ τ ta). split; [now constructor|cbn; congruence].
  - destruct IHTyping1 as (ta1 & Hta1 & He1).
    destruct IHTyping2 as (ta2 & Hta2 & He2).
    exists (IA.ia_seq T ta1 ta2). split;
      [now constructor|cbn; congruence].
Qed.

Corollary compile_indexed_has_annotation {Gamma t A} :
  IndexedCompiler.ICTyping Gamma t A ->
  exists ta, IA.AnnotTyping Gamma ta A /\
    IA.eraseAnnot ta = IndexedCompiler.compile_indexed t.
Proof.
  intros Ht. exists (IndexedCompiler.compile_indexed_annot t). split.
  - now apply IndexedCompiler.compile_indexed_annot_typing.
  - apply IndexedCompiler.erase_compile_indexed_annot.
Qed.

(** The witness is now the compiler's computational annotated output itself;
    no typing proof is eliminated to construct it. *)
Theorem compile_indexed_context_has_annotation
    {Gamma0 A0 Gamma C A} :
  ICCtxTyping Gamma0 A0 Gamma C A ->
  exists Ca, IA.PCtxTypingAnnot Gamma0 A0 Gamma Ca A /\
    IA.eraseAnnot_pctx Ca = compile_indexed_context C.
Proof.
  intros HC. exists (compile_indexed_context_annot C). split.
  - now apply compile_indexed_context_annot_typing.
  - apply erase_compile_indexed_context_annot.
Qed.

Lemma iso_contextual_equivalence_compiled_context
    {t1 t2 A C R} :
  StlcIso.SpecEquivalent.PCtxEquivalent empty t1 t2 A ->
  ValidTy R -> ICCtxTyping empty A empty C R ->
  (StlcIso.SpecEvaluation.Terminating
      (StlcIso.SpecSyntax.pctx_app t1 (compile_indexed_context C)) <->
   StlcIso.SpecEvaluation.Terminating
      (StlcIso.SpecSyntax.pctx_app t2 (compile_indexed_context C))).
Proof.
  intros Heq VR HC.
  rewrite <- !erase_compile_indexed_context_annot.
  exact (Heq (compile_indexed_context_annot C) R VR
    (compile_indexed_context_annot_typing HC)).
Qed.
