Require Import ExactBacktranslation.RoundTrip.
Require Import ExactBacktranslation.GlobalCoercionTests.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import ExactBacktranslation.StructuralCoercionTests.
Require Import StlcEqui.SpecTyping.

Example direct_erased_cast_typed :
  ⟪ CE.empty e⊢ CompilerIE.Compiler.compie (compile_global_up direct_cast_i) :
      tarr direct_l_i direct_r_i ⟫.
Proof.
  apply erased_global_up_typing.
  - exact direct_l_i_valid.
  - unfold direct_r_i. eauto with tyvalid cty simple_contr_rec.
Qed.

Example direct_heterogeneous_identity_typed :
  ⟪ CE.empty e⊢ equi_identity direct_l_i : tarr direct_l_i direct_r_i ⟫.
Proof.
  apply (equi_identity_heterogeneous_typing direct_cast_i).
  - exact direct_l_i_valid.
  - unfold direct_r_i. eauto with tyvalid cty simple_contr_rec.
Qed.

Definition cast_free_identity : ICTm := ic_abs tunit tunit (ic_var 0).

Example cast_free_identity_roundtrip :
  CompilerIE.Compiler.compie (compile_indexed cast_free_identity) =
  erase_indexed_raw cast_free_identity.
Proof.
  apply cast_free_roundtrip_exact. unfold cast_free_identity.
  constructor. constructor.
Qed.
