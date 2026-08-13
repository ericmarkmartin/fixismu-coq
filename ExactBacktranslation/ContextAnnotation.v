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
  intros Ht. apply iso_typing_has_annotation.
  now apply IndexedCompiler.compile_indexed_typing.
Qed.

(** The exact context compiler also has a fully annotated presentation.
    The presentation is built structurally from the indexed source context;
    generated coercions are annotated from their checked ordinary-Iso typing
    derivations. *)
Theorem compile_indexed_context_has_annotation
    {Gamma0 A0 Gamma C A} :
  ICCtxTyping Gamma0 A0 Gamma C A ->
  exists Ca, IA.PCtxTypingAnnot Gamma0 A0 Gamma Ca A /\
    IA.eraseAnnot_pctx Ca = compile_indexed_context C.
Proof.
  induction 1.
  - exists IA.ia_phole. split; [constructor|reflexivity].
  - destruct IHICCtxTyping as (Ca & HCa & He).
    exists (IA.ia_pabs A B Ca). split; [now constructor|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H1) as (ta & Hta & Het).
    exists (IA.ia_papp₁ A B Ca ta). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H1) as (ta & Hta & Het).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_papp₂ A B ta Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H0) as (ta1 & Hta1 & He1).
    destruct (compile_indexed_has_annotation H1) as (ta2 & Hta2 & He2).
    exists (IA.ia_pite₁ A Ca ta1 ta2). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H) as (ta1 & Hta1 & He1).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H1) as (ta2 & Hta2 & He2).
    exists (IA.ia_pite₂ A ta1 Ca ta2). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H) as (ta1 & Hta1 & He1).
    destruct (compile_indexed_has_annotation H0) as (ta2 & Hta2 & He2).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pite₃ A ta1 ta2 Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H0) as (ta & Hta & Het).
    exists (IA.ia_ppair₁ A B Ca ta). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H) as (ta & Hta & Het).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_ppair₂ A B ta Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pproj₁ A B Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pproj₂ A B Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pinl A B Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pinr A B Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H0) as (ta1 & Hta1 & He1).
    destruct (compile_indexed_has_annotation H1) as (ta2 & Hta2 & He2).
    exists (IA.ia_pcaseof₁ A B R Ca ta1 ta2). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H) as (ta1 & Hta1 & He1).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H1) as (ta2 & Hta2 & He2).
    exists (IA.ia_pcaseof₂ A B R ta1 Ca ta2). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H) as (ta1 & Hta1 & He1).
    destruct (compile_indexed_has_annotation H0) as (ta2 & Hta2 & He2).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pcaseof₃ A B R ta1 ta2 Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (compile_indexed_has_annotation H0) as (ta & Hta & Het).
    exists (IA.ia_pseq₁ A Ca ta). split;
      [econstructor; eauto|cbn; congruence].
  - destruct (compile_indexed_has_annotation H) as (ta & Hta & Het).
    destruct IHICCtxTyping as (Ca & HCa & HeC).
    exists (IA.ia_pseq₂ A ta Ca). split;
      [econstructor; eauto|cbn; congruence].
  - destruct IHICCtxTyping as (Ca & HCa & HeC).
    destruct (iso_typing_has_annotation
      (@GlobalCoercions.compile_global_up_typing Gamma A B d H H0))
      as (ta & Hta & Het).
    exists (IA.ia_papp₂ A B ta Ca). split;
      [econstructor; eauto|cbn; congruence].
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
  destruct (compile_indexed_context_has_annotation HC)
    as (Ca & HCa & Herase).
  rewrite <- !Herase. exact (Heq Ca R VR HCa).
Qed.
