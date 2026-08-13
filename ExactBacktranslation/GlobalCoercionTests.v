Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.StructuralCoercionTests.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import ExactBacktranslation.CastCommon.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.Fix.

Example direct_global_up_typed :
  ⟪ empty i⊢ (compile_global_up direct_cast_i) : tarr direct_l_i direct_r_i ⟫.
Proof.
  apply compile_global_up_typing.
  - exact direct_l_i_valid.
  - unfold direct_r_i. eauto with tyvalid cty simple_contr_rec.
Qed.

Example arrow_global_up_typed :
  ⟪ empty i⊢ (compile_global_up arrow_cast_i) : tarr arrow_l_i arrow_r_i ⟫.
Proof.
  apply compile_global_up_typing.
  - unfold arrow_l_i. apply ValidTy_arr; [exact direct_l_i_valid|].
    eauto with tyvalid cty simple_contr_rec.
  - unfold arrow_r_i, direct_r_i. eauto with tyvalid cty simple_contr_rec.
Qed.

Example product_sum_global_up_typed :
  ⟪ empty i⊢ (compile_global_up product_sum_cast_i) :
      tarr product_sum_l_i product_sum_r_i ⟫.
Proof.
  apply compile_global_up_typing.
  - unfold product_sum_l_i.
    eauto 8 using direct_l_i_valid with tyvalid cty simple_contr_rec.
  - unfold product_sum_r_i, direct_r_i.
    eauto 8 with tyvalid cty simple_contr_rec.
Qed.

Example cyclic_global_up_typed :
  ⟪ empty i⊢ (compile_global_up cyclic_cast_i) : tarr cycle_t_i cycle_s_i ⟫.
Proof.
  apply compile_global_up_typing; [exact cycle_t_i_valid|exact cycle_s_i_valid].
Qed.

Example cyclic_global_down_typed :
  ⟪ empty i⊢ (compile_global_down cyclic_cast_i) : tarr cycle_s_i cycle_t_i ⟫.
Proof.
  apply compile_global_down_typing; [exact cycle_t_i_valid|exact cycle_s_i_valid].
Qed.

(** Unfolding shows that the cyclic cast is tied at the top-level bundle. The
    recursive bundle builder itself contains no invocation of [ufix]. *)
Example cyclic_global_pair_is_single_tie :
  compile_global_pair cyclic_cast_i =
  certificate_root cyclic_cast_i
    (tm_app
      (tm_app (ufix tunit (certificate_bundle_ty cyclic_cast_i))
              (global_bundle_functional cyclic_cast_i)) unit)
    cast_terms_nil.
Proof. reflexivity. Qed.
