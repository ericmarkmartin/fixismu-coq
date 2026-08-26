Require Import ExactBacktranslation.SemanticBridge.
Require Import ExactBacktranslation.ExactContextLR.
Require Import ExactBacktranslation.ContextAnnotation.
Require Import ExactBacktranslation.EquiContextFrontend.
Require Import ExactBacktranslation.IsoToIndexed.
Require Import ExactBacktranslation.IndexedContexts.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.RoundTrip.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import CompilerIE.Compiler.
Require Import StlcEqui.SpecEquivalent.
Require StlcIso.SpecEquivalent.
Require Import StlcIso.SpecAnnot.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasLR.
From Stdlib Require Import Lia.

Module EMI := StlcIso.SpecSyntax.
Module EME := StlcEqui.SpecSyntax.
Module EMIA := StlcIso.SpecAnnot.
Module EMEA := StlcEqui.SpecAnnot.

(** The original erasure compiler translates contexts structurally and
    commutes definitionally with plugging. *)
Theorem compie_plug_annotated_context i C :
  CompilerIE.Compiler.compie
    (EMI.pctx_app i (EMIA.eraseAnnot_pctx C)) =
  EME.pctx_app (CompilerIE.Compiler.compie i)
    (EMEA.eraseAnnot_pctx (CompilerIE.Compiler.compie_pctx_annot C)).
Proof.
  induction C; cbn;
    rewrite ?IHC, ?CompilerIE.Compiler.compie_compie_annot;
    reflexivity.
Qed.

(** Direct closure of a shared cross-language mediator under an arbitrary
    Equi context.  The context is compiled exactly once by [G_C]; no
    observation index occurs in its syntax. *)
Lemma exact_shared_iso_mediator_termination
    {ts tu1 tu2 A R}
    (Hgt : forall n,
      ⟪pempty ⊩ ts ⟦dir_gt,n⟧ tu1 : embed A⟫)
    (Hlt : forall n,
      ⟪pempty ⊩ ts ⟦dir_lt,n⟧ tu2 : embed A⟫)
    {C} (HC : EMEA.PCtxTypingAnnot empty A empty C R) :
    StlcEqui.SpecEvaluation.Terminating
      (EME.pctx_app tu1 (EMEA.eraseAnnot_pctx C)) ->
    StlcEqui.SpecEvaluation.Terminating
      (EME.pctx_app tu2 (EMEA.eraseAnnot_pctx C)).
Proof.
  intros Hterm.
  pose proof (equi_context_to_indexed_typing HC) as HCI.
  destruct (StlcEqui.Size.Terminating_TermHor Hterm) as [n Hn].
  pose proof (compile_indexed_context_correct ValidEnv_nil ValidEnv_nil HCI
    dir_gt (S n)) as Hctx1.
  unfold erase_indexed_context_raw in Hctx1.
  rewrite (erase_equi_context_to_indexed_annot HC) in Hctx1.
  pose proof (proj2 (proj2 Hctx1) ts tu1 (Hgt (S n))) as Hfull1.
  assert (Hiso : StlcIso.SpecEvaluation.Terminating
    (EMI.pctx_app ts
      (compile_indexed_context (equi_context_to_indexed R C)))).
  { eapply adequacy_gt; [exact Hfull1|exact Hn|]. lia. }
  destruct (StlcIso.Size.Terminating_TermHor Hiso) as [m Hm].
  pose proof (compile_indexed_context_correct ValidEnv_nil ValidEnv_nil HCI
    dir_lt (S m)) as Hctx2.
  unfold erase_indexed_context_raw in Hctx2.
  rewrite (erase_equi_context_to_indexed_annot HC) in Hctx2.
  pose proof (proj2 (proj2 Hctx2) ts tu2 (Hlt (S m))) as Hfull2.
  eapply adequacy_lt; [exact Hfull2|exact Hm|]. lia.
Qed.

Theorem exact_shared_iso_mediator_contextual
    {ts tu1 tu2 A}
    (H1 : forall dir n,
      ⟪pempty ⊩ ts ⟦dir,n⟧ tu1 : embed A⟫)
    (H2 : forall dir n,
      ⟪pempty ⊩ ts ⟦dir,n⟧ tu2 : embed A⟫) :
  StlcEqui.SpecEquivalent.PCtxEquivalent empty tu1 tu2 A.
Proof.
  intros C R _ HC. split; intro Hterm.
  - exact (@exact_shared_iso_mediator_termination ts tu1 tu2 A R
      (H1 dir_gt) (H2 dir_lt) C HC Hterm).
  - exact (@exact_shared_iso_mediator_termination ts tu2 tu1 A R
      (H2 dir_gt) (H1 dir_lt) C HC Hterm).
Qed.

Theorem generated_cast_contextually_identity : CastIdentity.
Proof.
  unfold CastIdentity. intros A B d VA VB.
  eapply exact_shared_iso_mediator_contextual.
  - intros dir n. now apply erased_cast_lr.
  - intros dir n. now apply generated_cast_lr_all_worlds.
Qed.

Theorem generated_down_cast_contextually_identity {A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CompilerIE.Compiler.compie (compile_global_down d))
    (equi_identity B) (tarr B A).
Proof.
  intros VA VB. eapply exact_shared_iso_mediator_contextual.
  - intros dir n. now apply erased_down_cast_lr.
  - intros dir n. now apply generated_down_cast_lr_all_worlds.
Qed.

Theorem exact_equi_roundtrip {t A} :
  ICTyping empty t A ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CompilerIE.Compiler.compie (compile_indexed t))
    (erase_indexed_raw t) A.
Proof.
  intros Ht. refine (@exact_shared_iso_mediator_contextual
    (compile_indexed t)
    (CompilerIE.Compiler.compie (compile_indexed t))
    (erase_indexed_raw t) A _ _).
  - intros dir n. change (OpenLRN dir n (embedCtx empty)
      (compile_indexed t) (CompilerIE.Compiler.compie (compile_indexed t))
      (embed A)).
    eapply CompilerIE.Compiler.compie_correct.
    + exact ValidEnv_nil.
    + exact (indexed_typing_valid ValidEnv_nil Ht).
    + now apply compile_indexed_typing.
  - intros dir n. exact (compile_indexed_correct ValidEnv_nil Ht dir n).
Qed.

Corollary exact_equi_roundtrip_expansion {t A} :
  ICTyping empty t A ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (roundtrip_expansion t) (erase_indexed_raw t) A.
Proof.
  intros Ht. rewrite <- compiler_erasure_is_roundtrip_expansion.
  now apply exact_equi_roundtrip.
Qed.

Theorem exact_indexed_context_backtranslation {t C A R} :
  ICTyping empty t A -> ICCtxTyping empty A empty C R ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CompilerIE.Compiler.compie
      (EMI.pctx_app (compile_indexed t) (compile_indexed_context C)))
    (EME.pctx_app (erase_indexed_raw t) (erase_indexed_context_raw C)) R.
Proof.
  intros Ht HC. rewrite <- compile_plug_indexed, <- erase_plug_indexed.
  apply exact_equi_roundtrip. exact (plug_indexed_typing Ht HC).
Qed.

Lemma equi_contextual_trans {Gamma t1 t2 t3 A} :
  StlcEqui.SpecEquivalent.PCtxEquivalent Gamma t1 t2 A ->
  StlcEqui.SpecEquivalent.PCtxEquivalent Gamma t2 t3 A ->
  StlcEqui.SpecEquivalent.PCtxEquivalent Gamma t1 t3 A.
Proof.
  intros H12 H23 C R VR HC. split; intro Hterm.
  - apply (proj1 (H23 C R VR HC)), (proj1 (H12 C R VR HC)), Hterm.
  - apply (proj2 (H12 C R VR HC)), (proj2 (H23 C R VR HC)), Hterm.
Qed.

Lemma iso_contextual_trans {Gamma t1 t2 t3 A} :
  StlcIso.SpecEquivalent.PCtxEquivalent Gamma t1 t2 A ->
  StlcIso.SpecEquivalent.PCtxEquivalent Gamma t2 t3 A ->
  StlcIso.SpecEquivalent.PCtxEquivalent Gamma t1 t3 A.
Proof.
  intros H12 H23 C R VR HC. split; intro Hterm.
  - apply (proj1 (H23 C R VR HC)), (proj1 (H12 C R VR HC)), Hterm.
  - apply (proj2 (H12 C R VR HC)), (proj2 (H23 C R VR HC)), Hterm.
Qed.

Lemma exact_indexed_equivalence_reflection_termination
    {t1 t2 A R}
    (Ht1 : ICTyping empty t1 A)
    (Ht2 : ICTyping empty t2 A)
    (Heq : StlcIso.SpecEquivalent.PCtxEquivalent empty
      (compile_indexed t1) (compile_indexed t2) A)
    {C} (VR : ValidTy R)
    (HC : EMEA.PCtxTypingAnnot empty A empty C R) :
    StlcEqui.SpecEvaluation.Terminating
      (EME.pctx_app (erase_indexed_raw t1) (EMEA.eraseAnnot_pctx C)) ->
    StlcEqui.SpecEvaluation.Terminating
      (EME.pctx_app (erase_indexed_raw t2) (EMEA.eraseAnnot_pctx C)).
Proof.
  intros Hterm.
  pose proof (equi_context_to_indexed_typing HC) as HCI.
  destruct (StlcEqui.Size.Terminating_TermHor Hterm) as [n Hn].
  pose proof (compile_indexed_context_correct ValidEnv_nil ValidEnv_nil HCI
    dir_gt (S n)) as Hctx1.
  unfold erase_indexed_context_raw in Hctx1.
  rewrite (erase_equi_context_to_indexed_annot HC) in Hctx1.
  pose proof (proj2 (proj2 Hctx1) _ _
    (compile_indexed_correct ValidEnv_nil Ht1 dir_gt (S n))) as Hfull1.
  assert (Hi1 : StlcIso.SpecEvaluation.Terminating
    (EMI.pctx_app (compile_indexed t1)
      (compile_indexed_context (equi_context_to_indexed R C)))).
  { eapply adequacy_gt; [exact Hfull1|exact Hn|]. lia. }
  pose proof (proj1 (iso_contextual_equivalence_compiled_context
    Heq VR HCI) Hi1) as Hi2.
  destruct (StlcIso.Size.Terminating_TermHor Hi2) as [m Hm].
  pose proof (compile_indexed_context_correct ValidEnv_nil ValidEnv_nil HCI
    dir_lt (S m)) as Hctx2.
  unfold erase_indexed_context_raw in Hctx2.
  rewrite (erase_equi_context_to_indexed_annot HC) in Hctx2.
  pose proof (proj2 (proj2 Hctx2) _ _
    (compile_indexed_correct ValidEnv_nil Ht2 dir_lt (S m))) as Hfull2.
  eapply adequacy_lt; [exact Hfull2|exact Hm|]. lia.
Qed.

(** Equivalence reflection for [G], proved by compiling each arbitrary source
    Equi observing context with [G_C] and applying the assumed target Iso
    contextual equivalence to that structural context. *)
Theorem exact_indexed_equivalence_reflection {t1 t2 A} :
  ICTyping empty t1 A -> ICTyping empty t2 A ->
  StlcIso.SpecEquivalent.PCtxEquivalent empty
    (compile_indexed t1) (compile_indexed t2) A ->
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (erase_indexed_raw t1) (erase_indexed_raw t2) A.
Proof.
  intros Ht1 Ht2 Heq C R VR HC. split; intro Hterm.
  - exact (@exact_indexed_equivalence_reflection_termination
      t1 t2 A R Ht1 Ht2 Heq C VR HC Hterm).
  - exact (@exact_indexed_equivalence_reflection_termination
      t2 t1 A R Ht2 Ht1
      (StlcIso.SpecEquivalent.pctx_equiv_symm Heq) C VR HC Hterm).
Qed.

Theorem exact_iso_roundtrip_reflection {t i A} :
  ICTyping empty t A -> StlcIso.SpecTyping.Typing empty i A ->
  erase_indexed_raw t = CompilerIE.Compiler.compie i ->
  StlcIso.SpecEquivalent.PCtxEquivalent empty (compile_indexed t) i A.
Proof.
  intros Ht Hi Herase.
  eapply CompilerIE.Compiler.equivalenceReflectionEmpty.
  - exact (indexed_typing_valid ValidEnv_nil Ht).
  - now apply compile_indexed_typing.
  - exact Hi.
  - pose proof (exact_equi_roundtrip Ht) as Hround.
    now rewrite Herase in Hround.
Qed.

Corollary erase_iso_to_indexed_raw {Gamma t A} :
  EMIA.AnnotTyping Gamma t A ->
  erase_indexed_raw (iso_to_indexed t) =
    CompilerIE.Compiler.compie (EMIA.eraseAnnot t).
Proof.
  intros Ht. unfold erase_indexed_raw.
  rewrite (erase_iso_to_indexed_annot Ht).
  symmetry. apply CompilerIE.Compiler.compie_compie_annot.
Qed.

Theorem exact_iso_roundtrip_annot {t A} :
  EMIA.AnnotTyping empty t A ->
  StlcIso.SpecEquivalent.PCtxEquivalent empty
    (compile_indexed (iso_to_indexed t)) (EMIA.eraseAnnot t) A.
Proof.
  intros Ht. eapply exact_iso_roundtrip_reflection.
  - now apply iso_to_indexed_typing.
  - now apply EMIA.eraseAnnotT.
  - exact (@erase_iso_to_indexed_raw empty t A Ht).
Qed.

Theorem exact_indexed_full_abstraction {t1 t2 A} :
  ICTyping empty t1 A -> ICTyping empty t2 A ->
  (StlcEqui.SpecEquivalent.PCtxEquivalent empty
      (erase_indexed_raw t1) (erase_indexed_raw t2) A <->
   StlcIso.SpecEquivalent.PCtxEquivalent empty
      (compile_indexed t1) (compile_indexed t2) A).
Proof.
  intros Ht1 Ht2. split; intro Heq.
  - eapply CompilerIE.Compiler.equivalenceReflectionEmpty.
    + exact (indexed_typing_valid ValidEnv_nil Ht1).
    + now apply compile_indexed_typing.
    + now apply compile_indexed_typing.
    + eapply equi_contextual_trans; [apply exact_equi_roundtrip, Ht1|].
      eapply equi_contextual_trans; [exact Heq|].
      now apply StlcEqui.SpecEquivalent.pctx_equiv_symm,
        exact_equi_roundtrip.
  - now apply exact_indexed_equivalence_reflection.
Qed.

(** Full abstraction of [F], now proved by using [G] and [G_C] as its exact
    backtranslation.  The reverse implication uses [F_C], the structural
    erasure context compiler already present in [CompilerIE]. *)
Theorem exact_iso_annot_full_abstraction {t1 t2 A} :
  EMIA.AnnotTyping empty t1 A -> EMIA.AnnotTyping empty t2 A ->
  (StlcIso.SpecEquivalent.PCtxEquivalent empty
      (EMIA.eraseAnnot t1) (EMIA.eraseAnnot t2) A <->
   StlcEqui.SpecEquivalent.PCtxEquivalent empty
      (CompilerIE.Compiler.compie (EMIA.eraseAnnot t1))
      (CompilerIE.Compiler.compie (EMIA.eraseAnnot t2)) A).
Proof.
  intros Ht1 Ht2. split; intro Heq.
  - pose proof (iso_to_indexed_typing Ht1) as Hp1.
    pose proof (iso_to_indexed_typing Ht2) as Hp2.
    assert (HG : StlcIso.SpecEquivalent.PCtxEquivalent empty
      (compile_indexed (iso_to_indexed t1))
      (compile_indexed (iso_to_indexed t2)) A).
    { eapply iso_contextual_trans; [now apply exact_iso_roundtrip_annot|].
      eapply iso_contextual_trans; [exact Heq|].
      now apply StlcIso.SpecEquivalent.pctx_equiv_symm,
        exact_iso_roundtrip_annot. }
    pose proof (exact_indexed_equivalence_reflection Hp1 Hp2 HG) as HE.
    now rewrite (erase_iso_to_indexed_raw Ht1),
      (erase_iso_to_indexed_raw Ht2) in HE.
  - eapply CompilerIE.Compiler.equivalenceReflectionEmpty.
    + eapply StlcIso.LemmasTyping.typed_terms_are_valid;
        [exact ValidEnv_nil|exact (EMIA.eraseAnnotT Ht1)].
    + exact (EMIA.eraseAnnotT Ht1).
    + exact (EMIA.eraseAnnotT Ht2).
    + exact Heq.
Qed.
