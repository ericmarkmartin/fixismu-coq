Require Import ExactBacktranslation.SemanticBridge.
Require Import ExactBacktranslation.ExactMutualBacktranslation.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.IndexedContexts.
Require Import ExactBacktranslation.StructuralCoercionTests.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.RoundTrip.
Require Import LogRelIE.LR.

(** This instance contains an actual [ce_back], so the world-one bridge also
    exercises termination of the globally tied heterogeneous bundle. *)
Example cyclic_generated_cast_lr_one dir :
  OpenLRN dir 1 pempty (compile_global_up cyclic_cast_i)
    (equi_identity cycle_t_i) (embed (tarr cycle_t_i cycle_s_i)).
Proof.
  apply generated_cast_lr_one.
  - exact cycle_t_i_valid.
  - exact cycle_s_i_valid.
Qed.

Example cyclic_generated_cast_lr_every_world dir n :
  OpenLRN dir n pempty (compile_global_up cyclic_cast_i)
    (equi_identity cycle_t_i) (embed (tarr cycle_t_i cycle_s_i)).
Proof.
  apply generated_cast_lr_all_worlds.
  - exact cycle_t_i_valid.
  - exact cycle_s_i_valid.
Qed.

Example cyclic_erased_cast_is_contextually_identity :
  StlcEqui.SpecEquivalent.PCtxEquivalent CE.empty
    (CompilerIE.Compiler.compie (compile_global_up cyclic_cast_i))
    (equi_identity cycle_t_i) (tarr cycle_t_i cycle_s_i).
Proof.
  apply generated_cast_contextually_identity.
  - exact cycle_t_i_valid.
  - exact cycle_s_i_valid.
Qed.

Example cyclic_erased_down_cast_is_contextually_identity :
  StlcEqui.SpecEquivalent.PCtxEquivalent CE.empty
    (CompilerIE.Compiler.compie (compile_global_down cyclic_cast_i))
    (equi_identity cycle_s_i) (tarr cycle_s_i cycle_t_i).
Proof.
  apply generated_down_cast_contextually_identity.
  - exact cycle_t_i_valid.
  - exact cycle_s_i_valid.
Qed.

Definition indexed_direct_cast_function : ICTm :=
  ic_abs direct_l_i direct_r_i
    (ic_coerce direct_l_i direct_r_i direct_cast_i (ic_var 0)).

Lemma indexed_direct_cast_function_typing :
  ⟪empty ic⊢ indexed_direct_cast_function :
      tarr direct_l_i direct_r_i⟫.
Proof.
  unfold indexed_direct_cast_function.
  apply IC_WtAbs.
  - exact direct_l_i_valid.
  - apply IC_WtCoerce.
    + exact direct_l_i_valid.
    + unfold direct_r_i. split; constructor.
    + apply IC_WtVar. constructor.
Qed.

Example direct_cast_program_exact_roundtrip :
  StlcEqui.SpecEquivalent.PCtxEquivalent CE.empty
    (CompilerIE.Compiler.compie
      (compile_indexed indexed_direct_cast_function))
    (erase_indexed_raw indexed_direct_cast_function)
    (tarr direct_l_i direct_r_i).
Proof. exact (exact_equi_roundtrip indexed_direct_cast_function_typing). Qed.

Example direct_cast_program_compiler_full_abstraction :
  StlcIso.SpecEquivalent.PCtxEquivalent empty
    (compile_indexed indexed_direct_cast_function)
    (compile_indexed indexed_direct_cast_function)
    (tarr direct_l_i direct_r_i).
Proof.
  apply (proj1 (exact_indexed_full_abstraction
    indexed_direct_cast_function_typing
    indexed_direct_cast_function_typing)).
  intros C R VR HC. reflexivity.
Qed.

Definition closed_arrow_left : ICTm :=
  ic_abs direct_l_i tunit ic_unit.

Lemma closed_arrow_left_typing :
  ⟪empty ic⊢ closed_arrow_left : arrow_l_i⟫.
Proof.
  unfold closed_arrow_left, arrow_l_i.
  apply IC_WtAbs; [exact direct_l_i_valid|apply IC_WtUnit].
Qed.

Definition arrow_conversion_context : ICCtx :=
  icc_coerce arrow_l_i arrow_r_i arrow_cast_i icc_hole.

Lemma arrow_conversion_context_typing :
  ⟪icc⊢ arrow_conversion_context :
      empty, arrow_l_i → empty, arrow_r_i⟫.
Proof.
  unfold arrow_conversion_context.
  apply ICC_Coerce.
  - unfold arrow_l_i. apply RecTypes.LemmasTypes.ValidTy_arr;
      [exact direct_l_i_valid|].
    split; constructor.
  - unfold arrow_r_i, direct_r_i. repeat constructor.
  - apply ICC_Hole.
Qed.

Example arrow_context_backtranslation_is_exact :
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CompilerIE.Compiler.compie
      (StlcIso.SpecSyntax.pctx_app (compile_indexed closed_arrow_left)
        (compile_indexed_context arrow_conversion_context)))
    (StlcEqui.SpecSyntax.pctx_app (erase_indexed_raw closed_arrow_left)
      (erase_indexed_context_raw arrow_conversion_context))
    arrow_r_i.
Proof.
  exact (exact_indexed_context_backtranslation
    closed_arrow_left_typing arrow_conversion_context_typing).
Qed.
