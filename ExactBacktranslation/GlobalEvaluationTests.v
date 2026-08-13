Require Import ExactBacktranslation.GlobalEvaluation.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import ExactBacktranslation.StructuralCoercionTests.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import StlcIso.SpecEvaluation.

Example cyclic_bundle_terminates :
  StlcIso.SpecEvaluation.Terminating
    (tied_certificate_bundle cyclic_cast_i).
Proof. apply tied_certificate_bundle_terminates. Qed.

Example cyclic_forward_cast_terminates :
  StlcIso.SpecEvaluation.Terminating (compile_global_up cyclic_cast_i).
Proof.
  apply compile_global_up_terminates;
    [exact cycle_t_i_valid|exact cycle_s_i_valid].
Qed.

Example cyclic_reverse_cast_terminates :
  StlcIso.SpecEvaluation.Terminating (compile_global_down cyclic_cast_i).
Proof.
  apply compile_global_down_terminates;
    [exact cycle_t_i_valid|exact cycle_s_i_valid].
Qed.
