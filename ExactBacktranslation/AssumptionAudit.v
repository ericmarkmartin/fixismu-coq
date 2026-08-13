Require Import ExactBacktranslation.Decision.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.SemanticBridge.
Require Import ExactBacktranslation.ExactContextLR.
Require Import ExactBacktranslation.ContextAnnotation.
Require Import ExactBacktranslation.ExactMutualBacktranslation.
Require Import ExactBacktranslation.ExactCompiler.

(** Build-time audit of the public exact-compiler results. *)
Goal True. idtac "=== casteq_sound ===". exact I. Qed.
Print Assumptions casteq_sound.
Goal True. idtac "=== decide_casteq_complete ===". exact I. Qed.
Print Assumptions decide_casteq_complete.
Goal True. idtac "=== compile_global_up_typing ===". exact I. Qed.
Print Assumptions compile_global_up_typing.
Goal True. idtac "=== compile_global_down_typing ===". exact I. Qed.
Print Assumptions compile_global_down_typing.
Goal True. idtac "=== generated_cast_lr_all_worlds ===". exact I. Qed.
Print Assumptions generated_cast_lr_all_worlds.
Goal True. idtac "=== generated_cast_contextually_identity ===". exact I. Qed.
Print Assumptions generated_cast_contextually_identity.
Goal True. idtac "=== generated_down_cast_contextually_identity ===". exact I. Qed.
Print Assumptions generated_down_cast_contextually_identity.
Goal True. idtac "=== compile_indexed_context_correct ===". exact I. Qed.
Print Assumptions compile_indexed_context_correct.
Goal True. idtac "=== compile_indexed_context_has_annotation ===". exact I. Qed.
Print Assumptions compile_indexed_context_has_annotation.
Goal True. idtac "=== exact_equi_annot_roundtrip ===". exact I. Qed.
Print Assumptions exact_equi_annot_roundtrip.
Goal True. idtac "=== exact_equi_annot_context_backtranslation ===". exact I. Qed.
Print Assumptions exact_equi_annot_context_backtranslation.
Goal True. idtac "=== exact_equi_annot_full_abstraction ===". exact I. Qed.
Print Assumptions exact_equi_annot_full_abstraction.
Goal True. idtac "=== exact_iso_roundtrip_annot ===". exact I. Qed.
Print Assumptions exact_iso_roundtrip_annot.
Goal True. idtac "=== exact_indexed_equivalence_reflection ===". exact I. Qed.
Print Assumptions exact_indexed_equivalence_reflection.
Goal True. idtac "=== exact_indexed_full_abstraction ===". exact I. Qed.
Print Assumptions exact_indexed_full_abstraction.
Goal True. idtac "=== exact_iso_annot_full_abstraction ===". exact I. Qed.
Print Assumptions exact_iso_annot_full_abstraction.
