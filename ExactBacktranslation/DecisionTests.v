Require Import ExactBacktranslation.Decision.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.CertificateIndexedTests.
Require Import ExactBacktranslation.StructuralCoercionTests.

Definition decision_succeeds (A B : Ty) : bool :=
  match decide_casteq A B with
  | Some _ => true
  | None => false
  end.

(** These examples execute the endpoint-derived decision procedure.  None of
    them supplies a hand-written certificate or a user-selected fuel bound. *)
Example decide_direct_unfold_executes :
  decision_succeeds direct_l_i direct_r_i = true.
Proof. vm_compute. reflexivity. Qed.

Example decide_under_arrow_executes :
  decision_succeeds arrow_l_i arrow_r_i = true.
Proof. vm_compute. reflexivity. Qed.

Example decide_products_and_sums_executes :
  decision_succeeds product_sum_l_i product_sum_r_i = true.
Proof. vm_compute. reflexivity. Qed.

Example decide_genuinely_cyclic_executes :
  decision_succeeds cycle_t_i cycle_s_i = true.
Proof. vm_compute. reflexivity. Qed.

Example decide_rejects_distinct_heads :
  decide_casteq tunit tbool = None.
Proof. vm_compute. reflexivity. Qed.

Example decide_cycle_produces_sound_certificate :
  exists d : ClosedCastEq cycle_t_i cycle_s_i,
    decide_casteq cycle_t_i cycle_s_i = Some d /\
    Tyeq cycle_t_i cycle_s_i.
Proof.
  destruct (decide_casteq_complete cycle_t_i cycle_s_i
    cycle_t_i_valid cycle_s_i_valid (casteq_sound cyclic_cast_i))
    as [d Hd].
  exists d. split; [exact Hd|now apply casteq_sound].
Qed.
