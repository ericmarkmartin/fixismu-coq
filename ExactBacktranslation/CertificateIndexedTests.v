Require Import ExactBacktranslation.CertificateIndexed.

Definition direct_l_i : Ty := trec tunit.
Definition direct_r_i : Ty := tunit.

Definition direct_cast_i : ClosedCastEq direct_l_i direct_r_i.
Proof.
  apply ce_step, cn_mu_l.
  apply ce_step, cn_unit.
Defined.

Example direct_cast_i_sound : Tyeq direct_l_i direct_r_i.
Proof. exact (casteq_sound direct_cast_i). Qed.

Definition cycle_t_i : Ty := trec (tarr tunit (tvar 0)).
Definition cycle_s_i : Ty := trec (tarr tunit (tarr tunit (tvar 0))).

Definition cyclic_cast_i : ClosedCastEq cycle_t_i cycle_s_i.
Proof.
  apply ce_step, cn_mu_l.
  apply ce_step, cn_mu_r.
  - constructor.
  - apply ce_step, cn_arr.
    + apply ce_step, cn_unit.
    + apply ce_step, cn_mu_l.
      apply ce_step, cn_arr.
      * apply ce_step, cn_unit.
      * apply ce_back.
        apply assumed_there, assumed_there, assumed_there, assumed_there.
        apply assumed_here.
Defined.

Example cyclic_cast_i_sound : Tyeq cycle_t_i cycle_s_i.
Proof. exact (casteq_sound cyclic_cast_i). Qed.

Example search_finds_direct :
  exists d, search_closed_bounded 3 direct_l_i direct_r_i = Some d.
Proof. cbn. eauto. Qed.

Example search_finds_cycle :
  exists d, search_closed_bounded 8 cycle_t_i cycle_s_i = Some d.
Proof. cbn. eauto. Qed.
