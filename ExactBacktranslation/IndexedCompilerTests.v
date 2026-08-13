Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.StructuralCoercionTests.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.AnnotatedGlobalCoercions.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcEqui.SpecAnnot.

Module IATest := StlcIso.SpecAnnot.

Definition indexed_cyclic_cast_var : ICTm :=
  ic_coerce cycle_t_i cycle_s_i cyclic_cast_i (ic_var 0).

Lemma indexed_cyclic_cast_var_typing :
  ⟪ empty r▻ cycle_t_i ic⊢ indexed_cyclic_cast_var : cycle_s_i ⟫.
Proof.
  unfold indexed_cyclic_cast_var. apply IC_WtCoerce.
  - exact cycle_t_i_valid.
  - exact cycle_s_i_valid.
  - apply IC_WtVar. constructor.
Qed.

Example indexed_cyclic_compiler_output_typed :
  ⟪ empty r▻ cycle_t_i i⊢ compile_indexed indexed_cyclic_cast_var : cycle_s_i ⟫.
Proof. exact (compile_indexed_typing indexed_cyclic_cast_var_typing). Qed.

Example indexed_cyclic_annotated_compiler_output_typed :
  IATest.AnnotTyping (empty r▻ cycle_t_i)
    (compile_indexed_annot indexed_cyclic_cast_var) cycle_s_i.
Proof.
  exact (compile_indexed_annot_typing indexed_cyclic_cast_var_typing).
Qed.

Example indexed_cyclic_annotation_erases_to_raw_compiler :
  IATest.eraseAnnot (compile_indexed_annot indexed_cyclic_cast_var) =
  compile_indexed indexed_cyclic_cast_var.
Proof. apply erase_compile_indexed_annot. Qed.

Example indexed_cyclic_certificate_erasure_typed :
  ⟪ empty r▻ cycle_t_i ea⊢
      erase_indexed_certificate indexed_cyclic_cast_var : cycle_s_i ⟫.
Proof.
  exact (erase_indexed_certificate_typing indexed_cyclic_cast_var_typing).
Qed.

Example indexed_cyclic_compilation_is_strict :
  compile_indexed indexed_cyclic_cast_var =
  I.app (compile_global_up cyclic_cast_i) (I.var 0).
Proof. reflexivity. Qed.

Example indexed_cyclic_annotated_compilation_is_strict :
  compile_indexed_annot indexed_cyclic_cast_var =
  IATest.ia_app cycle_t_i cycle_s_i
    (compile_global_up_annot cyclic_cast_i) (IATest.ia_var 0).
Proof. reflexivity. Qed.
