Require Import ExactBacktranslation.EquiToIndexed.
Require Import ExactBacktranslation.EquiContextFrontend.
Require Import ExactBacktranslation.IndexedContexts.
Require Import ExactBacktranslation.ExactMutualBacktranslation.
Require Import ExactBacktranslation.RoundTrip.
Require Import CompilerIE.Compiler.
Require Import StlcEqui.SpecAnnot.
Require Import StlcEqui.SpecEquivalent.
Require StlcIso.SpecEquivalent.

Module EAC := StlcEqui.SpecAnnot.
Module CIEC := CompilerIE.Compiler.

Lemma erase_equi_to_indexed_raw {Gamma t A} :
  EAC.AnnotTyping Gamma t A ->
  erase_indexed_raw (equi_to_indexed A t) = EAC.eraseAnnot t.
Proof.
  intros Ht. unfold erase_indexed_raw.
  now rewrite (erase_equi_to_indexed_annot Ht).
Qed.

Lemma erase_equi_context_to_indexed_raw {Gamma0 A0 Gamma C A} :
  EAC.PCtxTypingAnnot Gamma0 A0 Gamma C A ->
  erase_indexed_context_raw (equi_context_to_indexed A C) =
    EAC.eraseAnnot_pctx C.
Proof.
  intros HC. unfold erase_indexed_context_raw.
  now rewrite (erase_equi_context_to_indexed_annot HC).
Qed.

(** Exact compiler correctness for the repository's ordinary annotated Equi
    source language.  Equality certificates are inferred, not supplied by
    the caller. *)
Theorem exact_equi_annot_roundtrip {t A} :
  EAC.AnnotTyping empty t A ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CIEC.compie (compile_equi_annot A t)) (EAC.eraseAnnot t) A.
Proof.
  intros Ht. unfold compile_equi_annot.
  pose proof (exact_equi_roundtrip (equi_to_indexed_typing Ht)) as Hround.
  now rewrite (erase_equi_to_indexed_raw Ht) in Hround.
Qed.

(** Exact, structural context backtranslation for the existing annotated
    source contexts.  No abstraction around the hole is introduced. *)
Theorem exact_equi_annot_context_backtranslation {t C A R} :
  EAC.AnnotTyping empty t A ->
  EAC.PCtxTypingAnnot empty A empty C R ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CIEC.compie
      (StlcIso.SpecSyntax.pctx_app (compile_equi_annot A t)
        (compile_equi_context_annot R C)))
    (StlcEqui.SpecSyntax.pctx_app (EAC.eraseAnnot t)
      (EAC.eraseAnnot_pctx C)) R.
Proof.
  intros Ht HC.
  unfold compile_equi_annot, compile_equi_context_annot.
  pose proof (exact_indexed_context_backtranslation
    (equi_to_indexed_typing Ht)
    (equi_context_to_indexed_typing HC)) as Hround.
  rewrite (erase_equi_to_indexed_raw Ht) in Hround.
  rewrite (erase_equi_context_to_indexed_raw HC) in Hround.
  exact Hround.
Qed.

Theorem exact_equi_annot_full_abstraction {t1 t2 A} :
  EAC.AnnotTyping empty t1 A ->
  EAC.AnnotTyping empty t2 A ->
  (StlcEqui.SpecEquivalent.PCtxEquivalent empty
      (EAC.eraseAnnot t1) (EAC.eraseAnnot t2) A <->
   StlcIso.SpecEquivalent.PCtxEquivalent empty
      (compile_equi_annot A t1) (compile_equi_annot A t2) A).
Proof.
  intros Ht1 Ht2. unfold compile_equi_annot.
  pose proof (exact_indexed_full_abstraction
    (equi_to_indexed_typing Ht1)
    (equi_to_indexed_typing Ht2)) as Hfa.
  rewrite (erase_equi_to_indexed_raw Ht1) in Hfa.
  rewrite (erase_equi_to_indexed_raw Ht2) in Hfa.
  exact Hfa.
Qed.
