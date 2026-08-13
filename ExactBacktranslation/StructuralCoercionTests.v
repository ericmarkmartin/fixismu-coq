Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import RecTypes.LemmasTypes.
Require Import StlcIso.SpecTyping.

Lemma direct_l_i_valid : ValidTy direct_l_i.
Proof. unfold direct_l_i. apply ValidTy_rec; constructor. Qed.

Example direct_structural_up_typed :
  ⟪ empty i⊢ (compile_closed_up direct_cast_i) : tarr direct_l_i direct_r_i ⟫.
Proof.
  apply compile_closed_up_typing.
  - exact direct_l_i_valid.
  - unfold direct_r_i. eauto with tyvalid cty simple_contr_rec.
Qed.

Definition arrow_l_i := tarr direct_l_i tunit.
Definition arrow_r_i := tarr direct_r_i tunit.

Definition arrow_cast_i : ClosedCastEq arrow_l_i arrow_r_i.
Proof.
  apply ce_step, cn_arr.
  - apply ce_step, cn_mu_l. apply ce_step, cn_unit.
  - apply ce_step, cn_unit.
Defined.

Example arrow_structural_up_typed :
  ⟪ empty i⊢ (compile_closed_up arrow_cast_i) : tarr arrow_l_i arrow_r_i ⟫.
Proof.
  apply compile_closed_up_typing.
  - unfold arrow_l_i. apply ValidTy_arr; [exact direct_l_i_valid|].
    eauto with tyvalid cty simple_contr_rec.
  - unfold arrow_r_i, direct_r_i. eauto with tyvalid cty simple_contr_rec.
Qed.

Definition product_sum_l_i :=
  tprod direct_l_i (tsum direct_l_i tunit).
Definition product_sum_r_i :=
  tprod direct_r_i (tsum direct_r_i tunit).

Definition product_sum_cast_i :
  ClosedCastEq product_sum_l_i product_sum_r_i.
Proof.
  apply ce_step, cn_prod.
  - apply ce_step, cn_mu_l. apply ce_step, cn_unit.
  - apply ce_step, cn_sum.
    + apply ce_step, cn_mu_l. apply ce_step, cn_unit.
    + apply ce_step, cn_unit.
Defined.

Example product_sum_structural_up_typed :
  ⟪ empty i⊢ (compile_closed_up product_sum_cast_i) :
      tarr product_sum_l_i product_sum_r_i ⟫.
Proof.
  apply compile_closed_up_typing.
  - unfold product_sum_l_i.
    eauto 8 using direct_l_i_valid with tyvalid cty simple_contr_rec.
  - unfold product_sum_r_i, direct_r_i.
    eauto 8 with tyvalid cty simple_contr_rec.
Qed.

Lemma cycle_t_i_valid : ValidTy cycle_t_i.
Proof.
  unfold cycle_t_i. apply ValidTy_rec; repeat constructor.
Qed.

Lemma cycle_s_i_valid : ValidTy cycle_s_i.
Proof.
  unfold cycle_s_i. apply ValidTy_rec; repeat constructor.
Qed.

Example cyclic_structural_up_typed :
  ⟪ empty i⊢ (compile_closed_up cyclic_cast_i) : tarr cycle_t_i cycle_s_i ⟫.
Proof.
  apply compile_closed_up_typing; [exact cycle_t_i_valid|exact cycle_s_i_valid].
Qed.

Example cyclic_structural_down_typed :
  ⟪ empty i⊢ (compile_closed_down cyclic_cast_i) : tarr cycle_s_i cycle_t_i ⟫.
Proof.
  apply compile_closed_down_typing; [exact cycle_t_i_valid|exact cycle_s_i_valid].
Qed.
