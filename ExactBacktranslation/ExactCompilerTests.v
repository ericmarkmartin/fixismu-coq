Require Import ExactBacktranslation.ExactCompiler.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.Decision.
Require Import ExactBacktranslation.EquiToIndexed.
Require Import ExactBacktranslation.EquiContextFrontend.
Require Import ExactBacktranslation.StructuralCoercionTests.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import StlcEqui.SpecAnnot.

Module EATest := StlcEqui.SpecAnnot.

(** The source syntax contains no certificate. *)
Definition ordinary_cyclic_cast_function : EATest.TmA :=
  EATest.ea_abs cycle_t_i cycle_s_i
    (EATest.ea_coerce cycle_t_i (EATest.ea_var 0)).

Lemma ordinary_cyclic_cast_function_typing :
  EATest.AnnotTyping empty ordinary_cyclic_cast_function
    (tarr cycle_t_i cycle_s_i).
Proof.
  unfold ordinary_cyclic_cast_function.
  apply EATest.ea_WtAbs; [exact cycle_t_i_valid|].
  eapply EATest.ea_WtCoerce.
  - exact (casteq_sound cyclic_cast_i).
  - exact cycle_t_i_valid.
  - exact cycle_s_i_valid.
  - apply EATest.ea_WtVar. constructor.
Qed.

Example ordinary_cyclic_compiler_infers_certificate :
  exists d,
    decide_casteq cycle_t_i cycle_s_i = Some d /\
    compile_equi_annot (tarr cycle_t_i cycle_s_i)
      ordinary_cyclic_cast_function =
      StlcIso.SpecSyntax.abs cycle_t_i
        (StlcIso.SpecSyntax.app (compile_global_up d)
          (StlcIso.SpecSyntax.var 0)).
Proof. vm_compute. eauto. Qed.

Example ordinary_cyclic_compiler_typed :
  StlcIso.SpecTyping.Typing empty
    (compile_equi_annot (tarr cycle_t_i cycle_s_i)
      ordinary_cyclic_cast_function)
    (tarr cycle_t_i cycle_s_i).
Proof. exact (compile_equi_annot_typing
  ordinary_cyclic_cast_function_typing). Qed.

Example ordinary_cyclic_exact_roundtrip :
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CompilerIE.Compiler.compie
      (compile_equi_annot (tarr cycle_t_i cycle_s_i)
        ordinary_cyclic_cast_function))
    (EATest.eraseAnnot ordinary_cyclic_cast_function)
    (tarr cycle_t_i cycle_s_i).
Proof. exact (exact_equi_annot_roundtrip
  ordinary_cyclic_cast_function_typing). Qed.

Example ordinary_cyclic_exact_full_abstraction :
  (StlcEqui.SpecEquivalent.PCtxEquivalent empty
      (EATest.eraseAnnot ordinary_cyclic_cast_function)
      (EATest.eraseAnnot ordinary_cyclic_cast_function)
      (tarr cycle_t_i cycle_s_i) <->
   StlcIso.SpecEquivalent.PCtxEquivalent empty
      (compile_equi_annot (tarr cycle_t_i cycle_s_i)
        ordinary_cyclic_cast_function)
      (compile_equi_annot (tarr cycle_t_i cycle_s_i)
        ordinary_cyclic_cast_function)
      (tarr cycle_t_i cycle_s_i)).
Proof.
  exact (exact_equi_annot_full_abstraction
    ordinary_cyclic_cast_function_typing
    ordinary_cyclic_cast_function_typing).
Qed.

Definition ordinary_arrow_cast_context : EATest.PCtxA :=
  EATest.ea_pcoerce arrow_l_i EATest.ea_phole.

Lemma ordinary_arrow_cast_context_typing :
  EATest.PCtxTypingAnnot empty arrow_l_i empty
    ordinary_arrow_cast_context arrow_r_i.
Proof.
  unfold ordinary_arrow_cast_context.
  eapply EATest.ea_WtPCoerce.
  - exact (casteq_sound arrow_cast_i).
  - apply EATest.ea_WtPHole.
  - unfold arrow_l_i. apply RecTypes.LemmasTypes.ValidTy_arr;
      [exact direct_l_i_valid|constructor; constructor].
  - unfold arrow_r_i, direct_r_i. repeat constructor.
Qed.

Example ordinary_context_backtranslation_is_structural :
  exists d,
    decide_casteq arrow_l_i arrow_r_i = Some d /\
    compile_equi_context_annot arrow_r_i ordinary_arrow_cast_context =
      StlcIso.SpecSyntax.papp₂ (compile_global_up d)
        StlcIso.SpecSyntax.phole.
Proof. vm_compute. eauto. Qed.

Example ordinary_context_backtranslation_is_exact :
  StlcEqui.SpecEquivalent.PCtxEquivalent empty
    (CompilerIE.Compiler.compie
      (StlcIso.SpecSyntax.pctx_app
        (compile_equi_annot arrow_l_i
          (EATest.ea_abs direct_l_i tunit EATest.ea_unit))
        (compile_equi_context_annot arrow_r_i
          ordinary_arrow_cast_context)))
    (StlcEqui.SpecSyntax.pctx_app
      (EATest.eraseAnnot
        (EATest.ea_abs direct_l_i tunit EATest.ea_unit))
      (EATest.eraseAnnot_pctx ordinary_arrow_cast_context)) arrow_r_i.
Proof.
  eapply exact_equi_annot_context_backtranslation.
  - apply EATest.ea_WtAbs; [exact direct_l_i_valid|constructor].
  - exact ordinary_arrow_cast_context_typing.
Qed.
