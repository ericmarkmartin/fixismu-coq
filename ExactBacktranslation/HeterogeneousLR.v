Require Import ExactBacktranslation.CertificateIndexed.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcEqui.SpecSyntax.
Require StlcEqui.SpecEvaluation.
Require StlcEqui.LemmasEvaluation.
Require Import StlcEqui.SpecTyping.
From Stdlib Require Import Arith.PeanoNat Lia.

Module HI := StlcIso.SpecSyntax.
Module HIE := StlcIso.SpecEvaluation.
Module HE := StlcEqui.SpecSyntax.
Module HEE := StlcEqui.SpecEvaluation.

(** Lift a relation on final values to possibly-computing terms. Both
    directions are included because contextual equivalence observes
    termination in either direction. *)
Definition term_lift (R : HI.Tm -> HE.Tm -> Prop)
  (ti : HI.Tm) (te : HE.Tm) : Prop :=
  (forall vi, HIE.Value vi -> HIE.evalStar ti vi ->
     exists ve, HEE.Value ve /\ HEE.evalStar te ve /\ R vi ve) /\
  (forall ve, HEE.Value ve -> HEE.evalStar te ve ->
     exists vi, HIE.Value vi /\ HIE.evalStar ti vi /\ R vi ve).

(** Canonicalize a focus after following any backreference.  In particular,
    the canonical forms of an ancestor step and a backedge to that ancestor
    are definitionally the same. *)
Definition focus_node {A B} (nf : NodeFocus A B) : Focus A B :=
  match nf with
  | node_focus node fs => focus (ce_step node) fs
  end.

Lemma expose_focus_node {A B} (nf : NodeFocus A B) :
  expose (focus_node nf) = nf.
Proof.
  destruct nf. cbn [focus_node expose]. reflexivity.
Qed.

Definition normalize_focus {A B} (f : Focus A B) : Focus A B :=
  focus_node (expose f).

Lemma normalize_focus_idempotent {A B} (f : Focus A B) :
  normalize_focus (normalize_focus f) = normalize_focus f.
Proof.
  unfold normalize_focus.
  now rewrite expose_focus_node.
Qed.

Lemma normalize_focus_back_here {H A B} (node : CastNode H A B)
  (fs : Frames H) :
  normalize_focus
    (focus (ce_back assumed_here) (frames_cons node fs)) =
  normalize_focus (focus (ce_step node) fs).
Proof. reflexivity. Qed.

(** Values related across the two endpoints of a regular-tree equality.
    [Focus] supplies the finite cyclic proof and its ancestor frames;
    [observe] follows backreferences until it exposes one constructor. *)
Fixpoint cast_value (n : nat) {A B} (f : Focus A B)
  (vi : HI.Tm) (ve : HE.Tm) : Prop :=
  match n with
  | O =>
      ⟪ empty i⊢ vi : A ⟫ /\ ⟪ empty e⊢ ve : B ⟫
  | S k =>
      cast_value k (normalize_focus f) vi ve
      /\ match observe (normalize_focus f) with
      | ev_unit _ => vi = HI.unit /\ ve = HE.unit
      | ev_bool _ =>
              (vi = HI.true /\ ve = HE.true) \/
              (vi = HI.false /\ ve = HE.false)
      | ev_var _ _ => False
      | ev_arr _ A1 A2 B1 B2 dom cod =>
              exists ti te,
                vi = HI.abs A1 ti /\ ve = HE.abs B1 te /\
                forall vai vae,
                  HIE.Value vai -> HEE.Value vae ->
                  cast_value k dom vai vae ->
                  term_lift
                    (cast_value k cod)
                    (HI.app vi vai) (HE.app ve vae)
      | ev_prod _ A1 A2 B1 B2 fstc sndc =>
              exists vi1 vi2 ve1 ve2,
                vi = HI.pair vi1 vi2 /\ ve = HE.pair ve1 ve2 /\
                cast_value k fstc vi1 ve1 /\
                cast_value k sndc vi2 ve2
      | ev_sum _ A1 A2 B1 B2 lc rc =>
              (exists vil vel,
                  vi = HI.inl vil /\ ve = HE.inl vel /\
                  cast_value k lc vil vel) \/
              (exists vir ver,
                  vi = HI.inr vir /\ ve = HE.inr ver /\
                  cast_value k rc vir ver)
      | ev_mu_l _ body B0 child =>
          exists vi', vi = HI.fold_ vi' /\ cast_value k child vi' ve
      | ev_mu_r _ A0 body child => cast_value k child vi ve
      end
  end.

Definition cast_term n {A B} (f : Focus A B)
  (ti : HI.Tm) (te : HE.Tm) : Prop :=
  term_lift (cast_value n f) ti te.

Definition closed_cast_value n {A B} (d : ClosedCastEq A B) :=
  cast_value n (focus d frames_nil).

Definition closed_cast_term n {A B} (d : ClosedCastEq A B) :=
  cast_term n (focus d frames_nil).

(** Dual orientation used by the forward compiler cast: an Iso value at the
    right endpoint is compared with an Equi value at the left endpoint. *)
Fixpoint cast_value_up (n : nat) {A B} (f : Focus A B)
  (vi : HI.Tm) (ve : HE.Tm) : Prop :=
  match n with
  | O =>
      ⟪ empty i⊢ vi : B ⟫ /\ ⟪ empty e⊢ ve : A ⟫
  | S k =>
      cast_value_up k (normalize_focus f) vi ve
      /\ match observe (normalize_focus f) with
      | ev_unit _ => vi = HI.unit /\ ve = HE.unit
      | ev_bool _ =>
          (vi = HI.true /\ ve = HE.true) \/
          (vi = HI.false /\ ve = HE.false)
      | ev_var _ _ => False
      | ev_arr _ A1 A2 B1 B2 dom cod =>
          exists ti te,
            vi = HI.abs B1 ti /\ ve = HE.abs A1 te /\
            forall vai vae,
              HIE.Value vai -> HEE.Value vae ->
              cast_value_up k dom vai vae ->
              term_lift (cast_value_up k cod)
                (HI.app vi vai) (HE.app ve vae)
      | ev_prod _ A1 A2 B1 B2 fstc sndc =>
          exists vi1 vi2 ve1 ve2,
            vi = HI.pair vi1 vi2 /\ ve = HE.pair ve1 ve2 /\
            cast_value_up k fstc vi1 ve1 /\
            cast_value_up k sndc vi2 ve2
      | ev_sum _ A1 A2 B1 B2 lc rc =>
          (exists vil vel,
              vi = HI.inl vil /\ ve = HE.inl vel /\
              cast_value_up k lc vil vel) \/
          (exists vir ver,
              vi = HI.inr vir /\ ve = HE.inr ver /\
              cast_value_up k rc vir ver)
      | ev_mu_l _ body B0 child => cast_value_up k child vi ve
      | ev_mu_r _ A0 body child =>
          exists vi', vi = HI.fold_ vi' /\ cast_value_up k child vi' ve
      end
  end.

Definition cast_term_up n {A B} (f : Focus A B)
  (ti : HI.Tm) (te : HE.Tm) : Prop :=
  term_lift (cast_value_up n f) ti te.

Definition closed_cast_value_up n {A B} (d : ClosedCastEq A B) :=
  cast_value_up n (focus d frames_nil).

Definition closed_cast_term_up n {A B} (d : ClosedCastEq A B) :=
  cast_term_up n (focus d frames_nil).

(** Ordinary endpoint relations, threaded through the same certificate focus.
    They are the input relations for the two generated casts: the forward cast
    maps [endpoint_value_left] to [cast_value_up], while the reverse cast maps
    [endpoint_value_right] to [cast_value]. *)
Fixpoint endpoint_value_left (n : nat) {A B} (f : Focus A B)
  (vi : HI.Tm) (ve : HE.Tm) : Prop :=
  match n with
  | O =>
      ⟪ empty i⊢ vi : A ⟫ /\ ⟪ empty e⊢ ve : A ⟫
  | S k =>
      endpoint_value_left k (normalize_focus f) vi ve
      /\ match observe (normalize_focus f) with
      | ev_unit _ => vi = HI.unit /\ ve = HE.unit
      | ev_bool _ =>
          (vi = HI.true /\ ve = HE.true)
          \/ (vi = HI.false /\ ve = HE.false)
      | ev_var _ _ => False
      | ev_arr _ A1 A2 B1 B2 dom cod =>
          exists ti te,
            vi = HI.abs A1 ti /\ ve = HE.abs A1 te
            /\ forall vai vae,
              HIE.Value vai -> HEE.Value vae ->
              endpoint_value_left k dom vai vae ->
              term_lift (endpoint_value_left k cod)
                (HI.app vi vai) (HE.app ve vae)
      | ev_prod _ A1 A2 B1 B2 fstc sndc =>
          exists vi1 vi2 ve1 ve2,
            vi = HI.pair vi1 vi2
            /\ ve = HE.pair ve1 ve2
            /\ endpoint_value_left k fstc vi1 ve1
            /\ endpoint_value_left k sndc vi2 ve2
      | ev_sum _ A1 A2 B1 B2 lc rc =>
          (exists vil vel,
              vi = HI.inl vil
              /\ ve = HE.inl vel
              /\ endpoint_value_left k lc vil vel)
          \/ (exists vir ver,
              vi = HI.inr vir
              /\ ve = HE.inr ver
              /\ endpoint_value_left k rc vir ver)
      | ev_mu_l _ body B0 child =>
          exists vi',
            vi = HI.fold_ vi' /\ endpoint_value_left k child vi' ve
      | ev_mu_r _ A0 body child => endpoint_value_left k child vi ve
      end
  end.

Fixpoint endpoint_value_right (n : nat) {A B} (f : Focus A B)
  (vi : HI.Tm) (ve : HE.Tm) : Prop :=
  match n with
  | O =>
      ⟪ empty i⊢ vi : B ⟫ /\ ⟪ empty e⊢ ve : B ⟫
  | S k =>
      endpoint_value_right k (normalize_focus f) vi ve
      /\ match observe (normalize_focus f) with
      | ev_unit _ => vi = HI.unit /\ ve = HE.unit
      | ev_bool _ =>
          (vi = HI.true /\ ve = HE.true)
          \/ (vi = HI.false /\ ve = HE.false)
      | ev_var _ _ => False
      | ev_arr _ A1 A2 B1 B2 dom cod =>
          exists ti te,
            vi = HI.abs B1 ti /\ ve = HE.abs B1 te
            /\ forall vai vae,
              HIE.Value vai -> HEE.Value vae ->
              endpoint_value_right k dom vai vae ->
              term_lift (endpoint_value_right k cod)
                (HI.app vi vai) (HE.app ve vae)
      | ev_prod _ A1 A2 B1 B2 fstc sndc =>
          exists vi1 vi2 ve1 ve2,
            vi = HI.pair vi1 vi2
            /\ ve = HE.pair ve1 ve2
            /\ endpoint_value_right k fstc vi1 ve1
            /\ endpoint_value_right k sndc vi2 ve2
      | ev_sum _ A1 A2 B1 B2 lc rc =>
          (exists vil vel,
              vi = HI.inl vil
              /\ ve = HE.inl vel
              /\ endpoint_value_right k lc vil vel)
          \/ (exists vir ver,
              vi = HI.inr vir
              /\ ve = HE.inr ver
              /\ endpoint_value_right k rc vir ver)
      | ev_mu_l _ body B0 child => endpoint_value_right k child vi ve
      | ev_mu_r _ A0 body child =>
          exists vi',
            vi = HI.fold_ vi' /\ endpoint_value_right k child vi' ve
      end
  end.

Definition endpoint_term_left n {A B} (f : Focus A B)
  (ti : HI.Tm) (te : HE.Tm) : Prop :=
  term_lift (endpoint_value_left n f) ti te.

Definition endpoint_term_right n {A B} (f : Focus A B)
  (ti : HI.Tm) (te : HE.Tm) : Prop :=
  term_lift (endpoint_value_right n f) ti te.

Definition closed_endpoint_value_left n {A B} (d : ClosedCastEq A B) :=
  endpoint_value_left n (focus d frames_nil).

Definition closed_endpoint_value_right n {A B} (d : ClosedCastEq A B) :=
  endpoint_value_right n (focus d frames_nil).

Definition closed_endpoint_term_left n {A B} (d : ClosedCastEq A B) :=
  endpoint_term_left n (focus d frames_nil).

Definition closed_endpoint_term_right n {A B} (d : ClosedCastEq A B) :=
  endpoint_term_right n (focus d frames_nil).

Lemma cast_value_normalize n {A B} (f : Focus A B) vi ve :
  cast_value n (normalize_focus f) vi ve <-> cast_value n f vi ve.
Proof.
  destruct n; [tauto|].
  cbn. now rewrite normalize_focus_idempotent.
Qed.

Lemma cast_value_up_normalize n {A B} (f : Focus A B) vi ve :
  cast_value_up n (normalize_focus f) vi ve <->
  cast_value_up n f vi ve.
Proof.
  destruct n; [tauto|].
  cbn. now rewrite normalize_focus_idempotent.
Qed.

Lemma endpoint_value_left_normalize n {A B} (f : Focus A B) vi ve :
  endpoint_value_left n (normalize_focus f) vi ve <->
  endpoint_value_left n f vi ve.
Proof.
  destruct n; [tauto|].
  cbn. now rewrite normalize_focus_idempotent.
Qed.

Lemma endpoint_value_right_normalize n {A B} (f : Focus A B) vi ve :
  endpoint_value_right n (normalize_focus f) vi ve <->
  endpoint_value_right n f vi ve.
Proof.
  destruct n; [tauto|].
  cbn. now rewrite normalize_focus_idempotent.
Qed.

Lemma cast_value_back_here n {H A B} (node : CastNode H A B) fs vi ve :
  cast_value n
    (focus (ce_back assumed_here) (frames_cons node fs)) vi ve <->
  cast_value n (focus (ce_step node) fs) vi ve.
Proof.
  split; intros Hrel.
  - apply (proj1 (cast_value_normalize n
      (focus (ce_step node) fs) vi ve)).
    rewrite <- normalize_focus_back_here.
    now apply (proj2 (cast_value_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
  - apply (proj1 (cast_value_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
    rewrite normalize_focus_back_here.
    now apply (proj2 (cast_value_normalize n
      (focus (ce_step node) fs) vi ve)).
Qed.

Lemma cast_value_up_back_here n {H A B} (node : CastNode H A B) fs vi ve :
  cast_value_up n
    (focus (ce_back assumed_here) (frames_cons node fs)) vi ve <->
  cast_value_up n (focus (ce_step node) fs) vi ve.
Proof.
  split; intros Hrel.
  - apply (proj1 (cast_value_up_normalize n
      (focus (ce_step node) fs) vi ve)).
    rewrite <- normalize_focus_back_here.
    now apply (proj2 (cast_value_up_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
  - apply (proj1 (cast_value_up_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
    rewrite normalize_focus_back_here.
    now apply (proj2 (cast_value_up_normalize n
      (focus (ce_step node) fs) vi ve)).
Qed.

Lemma endpoint_value_left_back_here n {H A B}
  (node : CastNode H A B) fs vi ve :
  endpoint_value_left n
    (focus (ce_back assumed_here) (frames_cons node fs)) vi ve <->
  endpoint_value_left n (focus (ce_step node) fs) vi ve.
Proof.
  split; intros Hrel.
  - apply (proj1 (endpoint_value_left_normalize n
      (focus (ce_step node) fs) vi ve)).
    rewrite <- normalize_focus_back_here.
    now apply (proj2 (endpoint_value_left_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
  - apply (proj1 (endpoint_value_left_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
    rewrite normalize_focus_back_here.
    now apply (proj2 (endpoint_value_left_normalize n
      (focus (ce_step node) fs) vi ve)).
Qed.

Lemma endpoint_value_right_back_here n {H A B}
  (node : CastNode H A B) fs vi ve :
  endpoint_value_right n
    (focus (ce_back assumed_here) (frames_cons node fs)) vi ve <->
  endpoint_value_right n (focus (ce_step node) fs) vi ve.
Proof.
  split; intros Hrel.
  - apply (proj1 (endpoint_value_right_normalize n
      (focus (ce_step node) fs) vi ve)).
    rewrite <- normalize_focus_back_here.
    now apply (proj2 (endpoint_value_right_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
  - apply (proj1 (endpoint_value_right_normalize n
      (focus (ce_back assumed_here) (frames_cons node fs)) vi ve)).
    rewrite normalize_focus_back_here.
    now apply (proj2 (endpoint_value_right_normalize n
      (focus (ce_step node) fs) vi ve)).
Qed.

(** Pointwise action is easier to compose through the deterministic CBV
    evaluator than a term relation.  The lemmas below lift it back to
    [term_lift] whenever the input pair consists of values. *)
Definition forward_value_action n {A B} (f : Focus A B) (up : HI.Tm) : Prop :=
  forall m, m <= n -> forall vi ve,
    HIE.Value vi ->
    HEE.Value ve ->
    endpoint_value_left m f vi ve ->
    exists vo,
      HIE.Value vo /\ HIE.evalStar (HI.app up vi) vo
      /\ cast_value_up m f vo ve.

Definition reverse_value_action n {A B} (f : Focus A B)
  (down : HI.Tm) : Prop :=
  forall m, m <= n -> forall vi ve,
    HIE.Value vi ->
    HEE.Value ve ->
    endpoint_value_right m f vi ve ->
    exists vo,
      HIE.Value vo /\ HIE.evalStar (HI.app down vi) vo
      /\ cast_value m f vo ve.

Definition cast_pair_value_action n {A B} (f : Focus A B)
  (p : HI.Tm) : Prop :=
  forward_value_action n f (HI.proj₁ p)
  /\ reverse_value_action n f (HI.proj₂ p).

(** The two recovery laws are essential under negative type positions.  An
    arrow's forward cast applies the domain [down] to an already cross-related
    argument; dually its reverse cast applies [up]. *)
Definition forward_recovery_action n {A B} (f : Focus A B)
  (up : HI.Tm) : Prop :=
  forall m, m <= n -> forall vi ve,
    HIE.Value vi -> HEE.Value ve ->
    cast_value m f vi ve ->
    exists vo,
      HIE.Value vo /\ HIE.evalStar (HI.app up vi) vo
      /\ endpoint_value_right m f vo ve.

Definition reverse_recovery_action n {A B} (f : Focus A B)
  (down : HI.Tm) : Prop :=
  forall m, m <= n -> forall vi ve,
    HIE.Value vi -> HEE.Value ve ->
    cast_value_up m f vi ve ->
    exists vo,
      HIE.Value vo /\ HIE.evalStar (HI.app down vi) vo
      /\ endpoint_value_left m f vo ve.

Definition cast_pair_full_action n {A B} (f : Focus A B)
  (p : HI.Tm) : Prop :=
  cast_pair_value_action n f p /\
  (forward_recovery_action n f (HI.proj₁ p) /\
   reverse_recovery_action n f (HI.proj₂ p)).

Lemma forward_value_action_normalize n {A B} (f : Focus A B) up :
  forward_value_action n (normalize_focus f) up <->
  forward_value_action n f up.
Proof.
  unfold forward_value_action. split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (endpoint_value_left_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (cast_value_up_normalize m f vo ve)).
  - apply (proj1 (endpoint_value_left_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (cast_value_up_normalize m f vo ve)).
Qed.

Lemma reverse_value_action_normalize n {A B} (f : Focus A B) down :
  reverse_value_action n (normalize_focus f) down <->
  reverse_value_action n f down.
Proof.
  unfold reverse_value_action. split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (endpoint_value_right_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (cast_value_normalize m f vo ve)).
  - apply (proj1 (endpoint_value_right_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (cast_value_normalize m f vo ve)).
Qed.

Lemma cast_pair_value_action_normalize n {A B} (f : Focus A B) p :
  cast_pair_value_action n (normalize_focus f) p <->
  cast_pair_value_action n f p.
Proof.
  unfold cast_pair_value_action.
  now rewrite forward_value_action_normalize,
              reverse_value_action_normalize.
Qed.

Lemma forward_recovery_action_normalize n {A B} (f : Focus A B) up :
  forward_recovery_action n (normalize_focus f) up <->
  forward_recovery_action n f up.
Proof.
  unfold forward_recovery_action.
  split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (cast_value_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (endpoint_value_right_normalize m f vo ve)).
  - apply (proj1 (cast_value_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (endpoint_value_right_normalize m f vo ve)).
Qed.

Lemma reverse_recovery_action_normalize n {A B} (f : Focus A B) down :
  reverse_recovery_action n (normalize_focus f) down <->
  reverse_recovery_action n f down.
Proof.
  unfold reverse_recovery_action.
  split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (cast_value_up_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (endpoint_value_left_normalize m f vo ve)).
  - apply (proj1 (cast_value_up_normalize m f vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (endpoint_value_left_normalize m f vo ve)).
Qed.

Lemma cast_pair_full_action_normalize n {A B} (f : Focus A B) p :
  cast_pair_full_action n (normalize_focus f) p <->
  cast_pair_full_action n f p.
Proof.
  unfold cast_pair_full_action.
  now rewrite cast_pair_value_action_normalize,
    forward_recovery_action_normalize, reverse_recovery_action_normalize.
Qed.

Lemma forward_value_action_back_here n {H A B}
  (node : CastNode H A B) fs up :
  forward_value_action n
    (focus (ce_back assumed_here) (frames_cons node fs)) up <->
  forward_value_action n (focus (ce_step node) fs) up.
Proof.
  unfold forward_value_action.
  split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (endpoint_value_left_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (cast_value_up_back_here m node fs vo ve)).
  - apply (proj1 (endpoint_value_left_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (cast_value_up_back_here m node fs vo ve)).
Qed.

Lemma reverse_value_action_back_here n {H A B}
  (node : CastNode H A B) fs down :
  reverse_value_action n
    (focus (ce_back assumed_here) (frames_cons node fs)) down <->
  reverse_value_action n (focus (ce_step node) fs) down.
Proof.
  unfold reverse_value_action.
  split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (endpoint_value_right_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (cast_value_back_here m node fs vo ve)).
  - apply (proj1 (endpoint_value_right_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (cast_value_back_here m node fs vo ve)).
Qed.

Lemma cast_pair_value_action_back_here n {H A B}
  (node : CastNode H A B) fs p :
  cast_pair_value_action n
    (focus (ce_back assumed_here) (frames_cons node fs)) p <->
  cast_pair_value_action n (focus (ce_step node) fs) p.
Proof.
  unfold cast_pair_value_action.
  now rewrite forward_value_action_back_here,
              reverse_value_action_back_here.
Qed.

Lemma forward_recovery_action_back_here n {H A B}
  (node : CastNode H A B) fs up :
  forward_recovery_action n
    (focus (ce_back assumed_here) (frames_cons node fs)) up <->
  forward_recovery_action n (focus (ce_step node) fs) up.
Proof.
  unfold forward_recovery_action.
  split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (cast_value_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (endpoint_value_right_back_here m node fs vo ve)).
  - apply (proj1 (cast_value_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (endpoint_value_right_back_here m node fs vo ve)).
Qed.

Lemma reverse_recovery_action_back_here n {H A B}
  (node : CastNode H A B) fs down :
  reverse_recovery_action n
    (focus (ce_back assumed_here) (frames_cons node fs)) down <->
  reverse_recovery_action n (focus (ce_step node) fs) down.
Proof.
  unfold reverse_recovery_action.
  split; intros Hact m Hmn vi ve Hvi Hve Hin.
  - apply (proj2 (cast_value_up_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj1 (endpoint_value_left_back_here m node fs vo ve)).
  - apply (proj1 (cast_value_up_back_here m node fs vi ve)) in Hin.
    destruct (Hact m Hmn vi ve Hvi Hve Hin)
      as (vo & Hvo & Heval & Hout).
    exists vo. repeat split; try assumption.
    now apply (proj2 (endpoint_value_left_back_here m node fs vo ve)).
Qed.

Lemma cast_pair_full_action_back_here n {H A B}
  (node : CastNode H A B) fs p :
  cast_pair_full_action n
    (focus (ce_back assumed_here) (frames_cons node fs)) p <->
  cast_pair_full_action n (focus (ce_step node) fs) p.
Proof.
  unfold cast_pair_full_action.
  now rewrite cast_pair_value_action_back_here,
    forward_recovery_action_back_here, reverse_recovery_action_back_here.
Qed.

Lemma forward_value_action_mono {n m A B} (f : Focus A B) up :
  m <= n ->
  forward_value_action n f up ->
  forward_value_action m f up.
Proof.
  intros Hmn Haction j Hjm. apply Haction. lia.
Qed.

Lemma reverse_value_action_mono {n m A B} (f : Focus A B) down :
  m <= n ->
  reverse_value_action n f down ->
  reverse_value_action m f down.
Proof.
  intros Hmn Haction j Hjm. apply Haction. lia.
Qed.

Lemma cast_pair_value_action_mono {n m A B} (f : Focus A B) p :
  m <= n ->
  cast_pair_value_action n f p ->
  cast_pair_value_action m f p.
Proof.
  intros Hmn [Hup Hdown]. split.
  - intros j Hj. apply Hup. lia.
  - intros j Hj. apply Hdown. lia.
Qed.

Lemma forward_recovery_action_mono {n m A B} (f : Focus A B) up :
  m <= n ->
  forward_recovery_action n f up ->
  forward_recovery_action m f up.
Proof. intros Hmn Haction j Hjm. apply Haction. lia. Qed.

Lemma reverse_recovery_action_mono {n m A B} (f : Focus A B) down :
  m <= n ->
  reverse_recovery_action n f down ->
  reverse_recovery_action m f down.
Proof. intros Hmn Haction j Hjm. apply Haction. lia. Qed.

Lemma cast_pair_full_action_mono {n m A B} (f : Focus A B) p :
  m <= n ->
  cast_pair_full_action n f p ->
  cast_pair_full_action m f p.
Proof.
  intros Hmn [Hordinary [Hforward Hreverse]]. split.
  - exact (@cast_pair_value_action_mono n m A B f p Hmn Hordinary).
  - split.
    + exact (@forward_recovery_action_mono n m A B
        f (HI.proj₁ p) Hmn Hforward).
    + exact (@reverse_recovery_action_mono n m A B
        f (HI.proj₂ p) Hmn Hreverse).
Qed.

Lemma term_lift_mono {R S : HI.Tm -> HE.Tm -> Prop} {ti te} :
  (forall vi ve, R vi ve -> S vi ve) ->
  term_lift R ti te -> term_lift S ti te.
Proof.
  intros HRS [HL HR]. split.
  - intros vi Hvi Hei. destruct (HL vi Hvi Hei) as (ve & Hve & Hee & Hrel).
    exists ve. repeat split; eauto.
  - intros ve Hve Hee. destruct (HR ve Hve Hee) as (vi & Hvi & Hei & Hrel).
    exists vi. repeat split; eauto.
Qed.

Lemma forward_value_action_term {n m A B} (f : Focus A B) up vi ve :
  forward_value_action n f up ->
  m <= n ->
  HIE.Value vi ->
  HEE.Value ve ->
  endpoint_value_left m f vi ve ->
  cast_term_up m f (HI.app up vi) ve.
Proof.
  intros Haction Hmn Hvi Hve Hrel.
  destruct (Haction m Hmn vi ve Hvi Hve Hrel)
    as (vo & Hvo & Heval & Hcross).
  split.
  - intros vo' Hvo' Heval'.
    assert (Hvo'vo : HIE.evalStar vo' vo).
    { eapply StlcIso.LemmasEvaluation.determinacyStar; eauto.
      now apply StlcIso.LemmasEvaluation.values_are_normal. }
    assert (vo' = vo).
    { now apply StlcIso.LemmasEvaluation.value_evalStar. }
    subst vo'. exists ve. repeat split; try assumption. constructor.
  - intros ve' Hve' Hee.
    assert (ve = ve').
    { now apply StlcEqui.LemmasEvaluation.value_evalStar. }
    subst ve'. exists vo. repeat split; try assumption.
Qed.

Lemma reverse_value_action_term {n m A B} (f : Focus A B) down vi ve :
  reverse_value_action n f down ->
  m <= n ->
  HIE.Value vi ->
  HEE.Value ve ->
  endpoint_value_right m f vi ve ->
  cast_term m f (HI.app down vi) ve.
Proof.
  intros Haction Hmn Hvi Hve Hrel.
  destruct (Haction m Hmn vi ve Hvi Hve Hrel)
    as (vo & Hvo & Heval & Hcross).
  split.
  - intros vo' Hvo' Heval'.
    assert (Hvo'vo : HIE.evalStar vo' vo).
    { eapply StlcIso.LemmasEvaluation.determinacyStar; eauto.
      now apply StlcIso.LemmasEvaluation.values_are_normal. }
    assert (vo' = vo).
    { now apply StlcIso.LemmasEvaluation.value_evalStar. }
    subst vo'. exists ve. repeat split; try assumption. constructor.
  - intros ve' Hve' Hee.
    assert (ve = ve').
    { now apply StlcEqui.LemmasEvaluation.value_evalStar. }
    subst ve'. exists vo. repeat split; try assumption.
Qed.

Lemma cast_value_mono :
  forall n m A B (f : Focus A B) vi ve,
    m <= n -> cast_value n f vi ve -> cast_value m f vi ve.
Proof.
  induction n as [|n IH]; intros m A B f vi ve Hmn Hrel.
  - assert (m = 0) by lia. subst m. exact Hrel.
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct m as [|m].
    + exact (IH 0 A B (normalize_focus f) vi ve (le_0_n n) Hprev).
    + destruct (Nat.eq_dec m n) as [->|Hneq].
      * split; assumption.
      * apply (proj1 (cast_value_normalize (S m) f vi ve)).
        eapply IH; [lia|exact Hprev].
Qed.

Lemma cast_value_up_mono :
  forall n m A B (f : Focus A B) vi ve,
    m <= n -> cast_value_up n f vi ve -> cast_value_up m f vi ve.
Proof.
  induction n as [|n IH]; intros m A B f vi ve Hmn Hrel.
  - assert (m = 0) by lia. subst m. exact Hrel.
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct m as [|m].
    + exact (IH 0 A B (normalize_focus f) vi ve (le_0_n n) Hprev).
    + destruct (Nat.eq_dec m n) as [->|Hneq].
      * split; assumption.
      * apply (proj1 (cast_value_up_normalize (S m) f vi ve)).
        eapply IH; [lia|exact Hprev].
Qed.

Lemma endpoint_value_left_mono :
  forall n m A B (f : Focus A B) vi ve,
    m <= n ->
    endpoint_value_left n f vi ve ->
    endpoint_value_left m f vi ve.
Proof.
  induction n as [|n IH]; intros m A B f vi ve Hmn Hrel.
  - assert (m = 0) by lia. subst m. exact Hrel.
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct m as [|m].
    + exact (IH 0 A B (normalize_focus f) vi ve (le_0_n n) Hprev).
    + destruct (Nat.eq_dec m n) as [->|Hneq].
      * split; assumption.
      * apply (proj1 (endpoint_value_left_normalize (S m) f vi ve)).
        eapply IH; [lia|exact Hprev].
Qed.

Lemma endpoint_value_right_mono :
  forall n m A B (f : Focus A B) vi ve,
    m <= n ->
    endpoint_value_right n f vi ve ->
    endpoint_value_right m f vi ve.
Proof.
  induction n as [|n IH]; intros m A B f vi ve Hmn Hrel.
  - assert (m = 0) by lia. subst m. exact Hrel.
  - cbn in Hrel. destruct Hrel as [Hprev Hlayer].
    destruct m as [|m].
    + exact (IH 0 A B (normalize_focus f) vi ve (le_0_n n) Hprev).
    + destruct (Nat.eq_dec m n) as [->|Hneq].
      * split; assumption.
      * apply (proj1 (endpoint_value_right_normalize (S m) f vi ve)).
        eapply IH; [lia|exact Hprev].
Qed.

Lemma cast_value_iso_typing n {A B} (f : Focus A B) vi ve :
  cast_value n f vi ve -> ⟪ empty i⊢ vi : A ⟫.
Proof.
  intros Hrel.
  exact (proj1 (cast_value_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma cast_value_equi_typing n {A B} (f : Focus A B) vi ve :
  cast_value n f vi ve -> ⟪ empty e⊢ ve : B ⟫.
Proof.
  intros Hrel.
  exact (proj2 (cast_value_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma cast_value_up_iso_typing n {A B} (f : Focus A B) vi ve :
  cast_value_up n f vi ve -> ⟪ empty i⊢ vi : B ⟫.
Proof.
  intros Hrel.
  exact (proj1 (cast_value_up_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma cast_value_up_equi_typing n {A B} (f : Focus A B) vi ve :
  cast_value_up n f vi ve -> ⟪ empty e⊢ ve : A ⟫.
Proof.
  intros Hrel.
  exact (proj2 (cast_value_up_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma endpoint_value_left_iso_typing n {A B} (f : Focus A B) vi ve :
  endpoint_value_left n f vi ve -> ⟪ empty i⊢ vi : A ⟫.
Proof.
  intros Hrel.
  exact (proj1
    (endpoint_value_left_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma endpoint_value_left_equi_typing n {A B} (f : Focus A B) vi ve :
  endpoint_value_left n f vi ve -> ⟪ empty e⊢ ve : A ⟫.
Proof.
  intros Hrel.
  exact (proj2
    (endpoint_value_left_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma endpoint_value_right_iso_typing n {A B} (f : Focus A B) vi ve :
  endpoint_value_right n f vi ve -> ⟪ empty i⊢ vi : B ⟫.
Proof.
  intros Hrel.
  exact (proj1
    (endpoint_value_right_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma endpoint_value_right_equi_typing n {A B} (f : Focus A B) vi ve :
  endpoint_value_right n f vi ve -> ⟪ empty e⊢ ve : B ⟫.
Proof.
  intros Hrel.
  exact (proj2
    (endpoint_value_right_mono n 0 A B f vi ve (le_0_n n) Hrel)).
Qed.

Lemma cast_term_mono {n m A B} (f : Focus A B) ti te :
  m <= n -> cast_term n f ti te -> cast_term m f ti te.
Proof.
  intros Hmn Hterm. eapply term_lift_mono; [|exact Hterm].
  intros vi ve. now apply cast_value_mono with (n := n).
Qed.

Lemma cast_term_up_mono {n m A B} (f : Focus A B) ti te :
  m <= n -> cast_term_up n f ti te -> cast_term_up m f ti te.
Proof.
  intros Hmn Hterm. eapply term_lift_mono; [|exact Hterm].
  intros vi ve. now apply cast_value_up_mono with (n := n).
Qed.

Lemma endpoint_term_left_mono {n m A B} (f : Focus A B) ti te :
  m <= n ->
  endpoint_term_left n f ti te ->
  endpoint_term_left m f ti te.
Proof.
  intros Hmn Hterm. eapply term_lift_mono; [|exact Hterm].
  intros vi ve. now apply endpoint_value_left_mono with (n := n).
Qed.

Lemma endpoint_term_right_mono {n m A B} (f : Focus A B) ti te :
  m <= n ->
  endpoint_term_right n f ti te ->
  endpoint_term_right m f ti te.
Proof.
  intros Hmn Hterm. eapply term_lift_mono; [|exact Hterm].
  intros vi ve. now apply endpoint_value_right_mono with (n := n).
Qed.

Lemma term_lift_termination_iff {R : HI.Tm -> HE.Tm -> Prop} {ti te} :
  term_lift R ti te ->
  (HIE.Terminating ti <-> HEE.Terminating te).
Proof.
  intros [HL HR]. split.
  - intros (vi & Hvi & Hei).
    destruct (HL vi Hvi Hei) as (ve & Hve & Hee & Hrel).
    now exists ve.
  - intros (ve & Hve & Hee).
    destruct (HR ve Hve Hee) as (vi & Hvi & Hei & Hrel).
    now exists vi.
Qed.

Lemma term_lift_antired {R : HI.Tm -> HE.Tm -> Prop}
  {ti ti' te te'} :
  HIE.evalStar ti ti' -> HEE.evalStar te te' ->
  term_lift R ti' te' -> term_lift R ti te.
Proof.
  intros Hii Hee [HL HR]. split.
  - intros vi Hvi Hiv.
    assert (Hi'v : HIE.evalStar ti' vi).
    { eapply StlcIso.LemmasEvaluation.determinacyStar; eauto.
      now apply StlcIso.LemmasEvaluation.values_are_normal. }
    destruct (HL vi Hvi Hi'v) as (ve & Hve & He'v & Hrel).
    exists ve. repeat split; try assumption.
    exact (@evalStepTrans HE.Tm HEE.eval te te' ve Hee He'v).
  - intros ve Hve Hev.
    assert (He'v : HEE.evalStar te' ve).
    { eapply StlcEqui.LemmasEvaluation.determinacyStar; eauto.
      now apply StlcEqui.LemmasEvaluation.values_are_normal. }
    destruct (HR ve Hve He'v) as (vi & Hvi & Hi'v & Hrel).
    exists vi. repeat split; try assumption.
    exact (@evalStepTrans HI.Tm HIE.eval ti ti' vi Hii Hi'v).
Qed.

Lemma cast_value_zero {A B} (f : Focus A B) vi ve :
  ⟪ empty i⊢ vi : A ⟫ -> ⟪ empty e⊢ ve : B ⟫ ->
  cast_value 0 f vi ve.
Proof. now split. Qed.

Lemma cast_value_up_zero {A B} (f : Focus A B) vi ve :
  ⟪ empty i⊢ vi : B ⟫ -> ⟪ empty e⊢ ve : A ⟫ ->
  cast_value_up 0 f vi ve.
Proof. now split. Qed.

Lemma cast_term_zero_values {A B} (f : Focus A B) vi ve :
  HIE.Value vi -> HEE.Value ve ->
  cast_value 0 f vi ve ->
  cast_term 0 f vi ve.
Proof.
  intros Hvi Hve Hrel. split.
  - intros vi' Hvi' Hei.
    assert (vi' = vi).
    { symmetry. eapply StlcIso.LemmasEvaluation.value_evalStar; eauto. }
    subst vi'. exists ve. split; [exact Hve|].
    split; [constructor|exact Hrel].
  - intros ve' Hve' Hee.
    assert (ve' = ve).
    { symmetry. eapply StlcEqui.LemmasEvaluation.value_evalStar; eauto. }
    subst ve'. exists vi. split; [exact Hvi|].
    split; [constructor|exact Hrel].
Qed.

Lemma cast_term_up_zero_values {A B} (f : Focus A B) vi ve :
  HIE.Value vi -> HEE.Value ve ->
  cast_value_up 0 f vi ve ->
  cast_term_up 0 f vi ve.
Proof.
  intros Hvi Hve Hrel. split.
  - intros vi' Hvi' Hei.
    assert (vi' = vi) by
      (symmetry; eapply StlcIso.LemmasEvaluation.value_evalStar; eauto).
    subst vi'. exists ve. split; [exact Hve|].
    split; [constructor|exact Hrel].
  - intros ve' Hve' Hee.
    assert (ve' = ve) by
      (symmetry; eapply StlcEqui.LemmasEvaluation.value_evalStar; eauto).
    subst ve'. exists vi. split; [exact Hvi|].
    split; [constructor|exact Hrel].
Qed.
