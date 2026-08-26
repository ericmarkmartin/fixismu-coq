Require Import ExactBacktranslation.BundleInvariant.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.GlobalEvaluation.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import ExactBacktranslation.CastCommon.
Require Import RecTypes.ValidTy.
Require Import RecTypes.LemmasTypes.
Require Import Common.Relations.
Require Import StlcIso.Inst.
Require Import StlcEqui.Inst.
Require Import LogRelIE.LR.
Require Import LogRelIE.LemmasPseudoType.
Require Import LogRelIE.LemmasLR.
Require Import LogRelIE.LemmasIntro.
Require Import LogRelIE.LemmasInversion.
From Stdlib Require Import Lia Lists.List.
Import ListNotations.

Module NBI := StlcIso.SpecSyntax.
Module NBIE := StlcIso.SpecEvaluation.

(** Every proper bundle cell evaluates to a pair of lambda abstractions.  This
    operational shape fact is independent of the recursive behavior hidden in
    the lambda bodies, and is what permits native-logical-relation bind
    arguments under call by value. *)
Definition cast_pair_function_shape (A B : Ty) (p : NBI.Tm) : Prop :=
  exists up_body down_body,
    NBIE.evalStar p
      (NBI.pair (NBI.abs A up_body) (NBI.abs B down_body)).

Fixpoint certificate_bundle_function_shape {H A B}
  (d : CastEq H A B) (self : NBI.Tm) : Prop :=
  match d in CastEq H0 A0 B0 return NBI.Tm -> Prop with
  | ce_back _ => fun _ => True
  | @ce_step H0 A0 B0 node => fun self0 =>
      cast_pair_function_shape A0 B0 (NBI.proj₁ self0)
      /\ node_bundle_function_shape node (NBI.proj₂ self0)
  end self
with node_bundle_function_shape {H A B}
  (node : CastNode H A B) (payload : NBI.Tm) : Prop :=
  match node in CastNode H0 A0 B0 return NBI.Tm -> Prop with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ => True
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => fun payload0 =>
      certificate_bundle_function_shape l (NBI.proj₁ payload0)
      /\ certificate_bundle_function_shape r (NBI.proj₂ payload0)
  | cn_mu_l _ _ _ child => fun payload0 =>
      certificate_bundle_function_shape child payload0
  | cn_mu_r _ _ _ _ child => fun payload0 =>
      certificate_bundle_function_shape child payload0
  end payload.

Fixpoint cast_terms_function_shape {H} : CastTerms H -> Prop :=
  match H return CastTerms H -> Prop with
  | nil => fun _ => True
  | (A, B) :: tail => fun rho =>
      cast_pair_function_shape A B (fst rho) /\
      cast_terms_function_shape (snd rho)
  end.

Lemma cast_terms_function_shape_nil :
  cast_terms_function_shape cast_terms_nil.
Proof. exact I. Qed.

Lemma cast_terms_function_shape_cons {H A B} p (rho : CastTerms H) :
  cast_pair_function_shape A B p ->
  cast_terms_function_shape rho ->
  cast_terms_function_shape (@cast_terms_cons H A B p rho).
Proof.
  intros Hp Hrho. now split.
Qed.

Lemma cast_terms_function_shape_lookup {H A B}
    (m : Assumed H A B) rho :
  cast_terms_function_shape rho ->
  cast_pair_function_shape A B (lookup_cast m rho).
Proof.
  revert rho. induction m; intros rho Hrho; cbn in *.
  - exact (proj1 Hrho).
  - now apply IHm, Hrho.
Qed.

Lemma global_node_cast_function_shape {H A B}
  (node : CastNode H A B) payload rho :
  cast_pair_function_shape A B (global_node_cast node payload rho).
Proof.
  destruct node; cbn [global_node_cast cast_pair_function_shape id_cast];
    eexists; eexists; constructor.
Qed.

Lemma cast_pair_function_shape_antired A B p p' :
  NBIE.evalStar p p' ->
  cast_pair_function_shape A B p' ->
  cast_pair_function_shape A B p.
Proof.
  intros Heval (up & down & Hshape).
  exists up, down. eapply evalStepTrans; eauto.
Qed.

Lemma bundle_function_shape_antired_mut :
  and
  (forall H A B (d : CastEq H A B), forall self self',
    NBIE.evalStar self self' ->
    certificate_bundle_function_shape d self' ->
    certificate_bundle_function_shape d self)
  (forall H A B (node : CastNode H A B), forall payload payload',
    NBIE.evalStar payload payload' ->
    node_bundle_function_shape node payload' ->
    node_bundle_function_shape node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH self self' Heval [Hroot Hpayload]. cbn. split.
    + eapply cast_pair_function_shape_antired; [|exact Hroot].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IH; [|exact Hpayload].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr payload payload' Heval
      [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr payload payload' Heval
      [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr payload payload' Heval
      [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H body B child IH payload payload' Heval Hshape.
    cbn. eapply IH; eauto.
  - intros H A body nm child IH payload payload' Heval Hshape.
    cbn. eapply IH; eauto.
Qed.

Lemma certificate_bundle_function_shape_antired {H A B}
  (d : CastEq H A B) self self' :
  NBIE.evalStar self self' ->
  certificate_bundle_function_shape d self' ->
  certificate_bundle_function_shape d self.
Proof.
  exact ((proj1 bundle_function_shape_antired_mut) H A B d self self').
Qed.

Lemma node_bundle_function_shape_antired {H A B}
  (node : CastNode H A B) payload payload' :
  NBIE.evalStar payload payload' ->
  node_bundle_function_shape node payload' ->
  node_bundle_function_shape node payload.
Proof.
  exact ((proj2 bundle_function_shape_antired_mut)
    H A B node payload payload').
Qed.

Lemma build_bundle_function_shape_mut :
  and
  (forall H A B (d : CastEq H A B), forall self rho,
    certificate_bundle_function_shape d
      (build_certificate_bundle d self rho))
  (forall H A B (node : CastNode H A B), forall payload rho,
    node_bundle_function_shape node (build_node_bundle node payload rho)).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH self rho.
    pose proof (IH (NBI.proj₂ self)
      (@cast_terms_cons H A B (NBI.proj₁ self) rho)) as Hbuilt.
    cbn. split.
    + eapply cast_pair_function_shape_antired.
      * apply evalToStar, NBIE.eval_eval₀.
        apply NBIE.eval_proj₁;
          [apply global_node_cast_value|apply build_node_bundle_value].
      * apply global_node_cast_function_shape.
    + eapply node_bundle_function_shape_antired; [|exact Hbuilt].
      apply evalToStar, NBIE.eval_eval₀.
      apply NBIE.eval_proj₂;
        [apply global_node_cast_value|apply build_node_bundle_value].
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr payload rho.
    pose proof (IHl (NBI.proj₁ payload) rho) as Hleft.
    pose proof (IHr (NBI.proj₂ payload) rho) as Hright.
    cbn. split.
    + eapply certificate_bundle_function_shape_antired; [|exact Hleft].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_function_shape_antired; [|exact Hright].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr payload rho.
    pose proof (IHl (NBI.proj₁ payload) rho) as Hleft.
    pose proof (IHr (NBI.proj₂ payload) rho) as Hright.
    cbn. split.
    + eapply certificate_bundle_function_shape_antired; [|exact Hleft].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_function_shape_antired; [|exact Hright].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr payload rho.
    pose proof (IHl (NBI.proj₁ payload) rho) as Hleft.
    pose proof (IHr (NBI.proj₂ payload) rho) as Hright.
    cbn. split.
    + eapply certificate_bundle_function_shape_antired; [|exact Hleft].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_function_shape_antired; [|exact Hright].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H body B child IH payload rho. cbn. apply IH.
  - intros H A body nm child IH payload rho. cbn. apply IH.
Qed.

Lemma build_certificate_bundle_function_shape {H A B}
  (d : CastEq H A B) self rho :
  certificate_bundle_function_shape d (build_certificate_bundle d self rho).
Proof.
  exact ((proj1 build_bundle_function_shape_mut) H A B d self rho).
Qed.

Theorem recursive_certificate_bundle_function_shape {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  certificate_bundle_function_shape d (recursive_certificate_bundle d).
Proof.
  intros HA HB.
  eapply certificate_bundle_function_shape_antired.
  - now apply recursive_certificate_bundle_unfolds.
  - apply build_certificate_bundle_function_shape.
Qed.

Theorem tied_certificate_bundle_function_shape {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  certificate_bundle_function_shape d (tied_certificate_bundle d).
Proof.
  intros HA HB.
  eapply certificate_bundle_function_shape_antired.
  - apply evalToStar, tied_certificate_bundle_step.
  - now apply recursive_certificate_bundle_function_shape.
Qed.

Lemma certificate_root_function_shape {H A B}
  (d : CastEq H A B) self rho :
  certificate_bundle_function_shape d self ->
  cast_terms_function_shape rho ->
  cast_pair_function_shape A B (certificate_root d self rho).
Proof.
  destruct d; cbn.
  - intros _ Hrho. now apply cast_terms_function_shape_lookup.
  - intros [Hroot _] _. exact Hroot.
Qed.

Theorem compile_global_pair_function_shape {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  cast_pair_function_shape A B (compile_global_pair d).
Proof.
  intros HA HB. unfold compile_global_pair.
  eapply certificate_root_function_shape.
  - now apply tied_certificate_bundle_function_shape.
  - apply cast_terms_function_shape_nil.
Qed.

Definition cast_function_shape (A : Ty) (f : NBI.Tm) : Prop :=
  exists body, NBIE.evalStar f (NBI.abs A body).

Lemma cast_pair_up_function_shape A B p :
  cast_pair_function_shape A B p ->
  cast_function_shape A (pair_up p).
Proof.
  intros (up_body & down_body & Hpair).
  exists up_body. unfold pair_up.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (NBI.pproj₁ NBI.phole) I Hpair).
  - apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁; exact I.
Qed.

Lemma cast_pair_down_function_shape A B p :
  cast_pair_function_shape A B p ->
  cast_function_shape B (pair_down p).
Proof.
  intros (up_body & down_body & Hpair).
  exists down_body. unfold pair_down.
  eapply evalStepTrans.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (NBI.pproj₂ NBI.phole) I Hpair).
  - apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂; exact I.
Qed.

Corollary compile_global_up_function_shape {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  cast_function_shape A (compile_global_up d).
Proof.
  intros HA HB. unfold compile_global_up.
  apply (cast_pair_up_function_shape A B).
  now apply compile_global_pair_function_shape.
Qed.

Corollary compile_global_down_function_shape {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  cast_function_shape B (compile_global_down d).
Proof.
  intros HA HB. unfold compile_global_down.
  apply (cast_pair_down_function_shape A B).
  now apply compile_global_pair_function_shape.
Qed.

(** The logical world and the number of leading recursive constructors form a
    single well-founded potential.  Structural rules spend one logical world;
    unfold/fold rules spend one leading-[mu] unit.  The radix is chosen larger
    than every endpoint leading-[mu] sum in the finite certificate. *)
Definition native_semantic_measure
  (radix : nat) (A B : Ty) (w : World) : nat :=
  w * radix + LMC A + LMC B.

Definition native_pair_action_below
  (radix budget : nat) (A B : Ty) (p : NBI.Tm) : Prop :=
  (forall dir w vi ve,
    native_semantic_measure radix A B w < budget ->
    valrel dir w (embed A) vi ve ->
    exists vo,
      NBIE.Value vo /\
      NBIE.evalStar (NBI.app (pair_up p) vi) vo /\
      valrel dir w (embed B) vo ve) /\
  (forall dir w vi ve,
    native_semantic_measure radix A B w < budget ->
    valrel dir w (embed B) vi ve ->
    exists vo,
      NBIE.Value vo /\
      NBIE.evalStar (NBI.app (pair_down p) vi) vo /\
      valrel dir w (embed A) vo ve).

Fixpoint certificate_bundle_native_action {H A B}
  (radix budget : nat) (d : CastEq H A B) (self : NBI.Tm) : Prop :=
  match d in CastEq H0 A0 B0 return NBI.Tm -> Prop with
  | ce_back _ => fun _ => True
  | @ce_step H0 A0 B0 node => fun self0 =>
      native_pair_action_below radix budget A0 B0 (NBI.proj₁ self0)
      /\ node_bundle_native_action radix budget node (NBI.proj₂ self0)
  end self
with node_bundle_native_action {H A B}
  (radix budget : nat) (node : CastNode H A B) (payload : NBI.Tm) : Prop :=
  match node in CastNode H0 A0 B0 return NBI.Tm -> Prop with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ => True
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => fun payload0 =>
      certificate_bundle_native_action radix budget l
        (NBI.proj₁ payload0)
      /\ certificate_bundle_native_action radix budget r
        (NBI.proj₂ payload0)
  | cn_mu_l _ _ _ child => fun payload0 =>
      certificate_bundle_native_action radix budget child payload0
  | cn_mu_r _ _ _ _ child => fun payload0 =>
      certificate_bundle_native_action radix budget child payload0
  end payload.

Fixpoint cast_terms_native_action {H}
  (radix budget : nat) : CastTerms H -> Prop :=
  match H return CastTerms H -> Prop with
  | nil => fun _ => True
  | (A, B) :: tail => fun rho =>
      native_pair_action_below radix budget A B (fst rho) /\
      cast_terms_native_action radix budget (snd rho)
  end.

Lemma cast_terms_native_action_nil radix budget :
  cast_terms_native_action radix budget cast_terms_nil.
Proof. exact I. Qed.

Lemma cast_terms_native_action_lookup radix budget {H A B}
  (m : Assumed H A B) rho :
  cast_terms_native_action radix budget rho ->
  native_pair_action_below radix budget A B (lookup_cast m rho).
Proof.
  revert rho. induction m; intros rho Hrho; cbn in *.
  - exact (proj1 Hrho).
  - now apply IHm, Hrho.
Qed.

Lemma cast_terms_native_action_cons radix budget {H A B}
  p (rho : CastTerms H) :
  native_pair_action_below radix budget A B p ->
  cast_terms_native_action radix budget rho ->
  cast_terms_native_action radix budget
    (@cast_terms_cons H A B p rho).
Proof.
  intros Hp Hrho. now split.
Qed.

Lemma certificate_root_native_action radix budget {H A B}
  (d : CastEq H A B) self rho :
  certificate_bundle_native_action radix budget d self ->
  cast_terms_native_action radix budget rho ->
  native_pair_action_below radix budget A B
    (certificate_root d self rho).
Proof.
  destruct d; cbn; intros Hself Hrho.
  - now apply cast_terms_native_action_lookup.
  - exact (proj1 Hself).
Qed.

Lemma native_pair_action_below_zero radix A B p :
  native_pair_action_below radix 0 A B p.
Proof. split; intros dir w vi ve Hmeasure Hrel; lia. Qed.

Lemma bundle_native_action_below_zero_mut :
  and
  (forall H A B (d : CastEq H A B), forall radix self,
    certificate_bundle_native_action radix 0 d self)
  (forall H A B (node : CastNode H A B), forall radix payload,
    node_bundle_native_action radix 0 node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut; cbn; intros; try exact I;
    try split; eauto using native_pair_action_below_zero.
Qed.

Lemma certificate_bundle_native_action_below_zero {H A B}
  (d : CastEq H A B) radix self :
  certificate_bundle_native_action radix 0 d self.
Proof.
  exact ((proj1 bundle_native_action_below_zero_mut) H A B d radix self).
Qed.

Lemma native_pair_action_below_antired radix budget A B p p' :
  NBIE.evalStar p p' ->
  native_pair_action_below radix budget A B p' ->
  native_pair_action_below radix budget A B p.
Proof.
  intros Heval [Hup Hdown]. split; intros dir w vi ve Hmeasure Hrel.
  - destruct (Hup dir w vi ve Hmeasure Hrel)
      as (vo & Hvo & Happ & Hout).
    exists vo. split; [exact Hvo|]. split.
    + eapply evalStepTrans.
      * exact (StlcIso.LemmasEvaluation.evalstar_ctx
          (NBI.papp₁ NBI.phole vi) I
          (StlcIso.LemmasEvaluation.evalstar_ctx
            (NBI.pproj₁ NBI.phole) I Heval)).
      * exact Happ.
    + exact Hout.
  - destruct (Hdown dir w vi ve Hmeasure Hrel)
      as (vo & Hvo & Happ & Hout).
    exists vo. split; [exact Hvo|]. split.
    + eapply evalStepTrans.
      * exact (StlcIso.LemmasEvaluation.evalstar_ctx
          (NBI.papp₁ NBI.phole vi) I
          (StlcIso.LemmasEvaluation.evalstar_ctx
            (NBI.pproj₂ NBI.phole) I Heval)).
      * exact Happ.
    + exact Hout.
Qed.

Lemma bundle_native_action_antired_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall radix budget self self',
      NBIE.evalStar self self' ->
      certificate_bundle_native_action radix budget d self' ->
      certificate_bundle_native_action radix budget d self)
  (forall H A B (node : CastNode H A B),
    forall radix budget payload payload',
      NBIE.evalStar payload payload' ->
      node_bundle_native_action radix budget node payload' ->
      node_bundle_native_action radix budget node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH radix budget self self' Heval
      [Hroot Hpayload]. cbn. split.
    + eapply native_pair_action_below_antired; [|exact Hroot].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IH; [|exact Hpayload].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr
      radix budget payload payload' Heval [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr
      radix budget payload payload' Heval [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr
      radix budget payload payload' Heval [Hl Hr]. cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H body B child IH radix budget payload payload' Heval Haction.
    cbn. eapply IH; [exact Heval|exact Haction].
  - intros H A body nm child IH radix budget payload payload' Heval Haction.
    cbn. eapply IH; [exact Heval|exact Haction].
Qed.

Lemma certificate_bundle_native_action_antired radix budget {H A B}
  (d : CastEq H A B) self self' :
  NBIE.evalStar self self' ->
  certificate_bundle_native_action radix budget d self' ->
  certificate_bundle_native_action radix budget d self.
Proof.
  exact ((proj1 bundle_native_action_antired_mut)
    H A B d radix budget self self').
Qed.

Lemma node_bundle_native_action_antired radix budget {H A B}
  (node : CastNode H A B) payload payload' :
  NBIE.evalStar payload payload' ->
  node_bundle_native_action radix budget node payload' ->
  node_bundle_native_action radix budget node payload.
Proof.
  exact ((proj2 bundle_native_action_antired_mut)
    H A B node radix budget payload payload').
Qed.

Fixpoint cast_terms_application_terminates {H} : CastTerms H -> Prop :=
  match H return CastTerms H -> Prop with
  | nil => fun _ => True
  | (A, B) :: tail => fun rho =>
      cast_pair_application_terminates A B (fst rho) /\
      cast_terms_application_terminates (snd rho)
  end.

Lemma cast_terms_application_terminates_nil :
  cast_terms_application_terminates cast_terms_nil.
Proof. exact I. Qed.

Lemma cast_terms_application_terminates_lookup {H A B}
  (m : Assumed H A B) rho :
  cast_terms_application_terminates rho ->
  cast_pair_application_terminates A B (lookup_cast m rho).
Proof.
  revert rho. induction m; intros rho Hrho; cbn in *.
  - exact (proj1 Hrho).
  - now apply IHm, Hrho.
Qed.

Lemma cast_terms_application_terminates_cons {H A B}
  p (rho : CastTerms H) :
  cast_pair_application_terminates A B p ->
  cast_terms_application_terminates rho ->
  cast_terms_application_terminates (@cast_terms_cons H A B p rho).
Proof.
  intros Hp Hrho. now split.
Qed.

Lemma certificate_root_application_terminates {H A B}
  (d : CastEq H A B) self rho :
  certificate_bundle_application_terminates d self ->
  cast_terms_application_terminates rho ->
  cast_pair_application_terminates A B (certificate_root d self rho).
Proof.
  destruct d; cbn; intros Hself Hrho.
  - now apply cast_terms_application_terminates_lookup.
  - exact (proj1 Hself).
Qed.

Lemma native_forward_output_oftype_from {A B p vi ve vo} :
  ValidTy A -> ValidTy B ->
  Tyeq A B ->
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  OfType (embed A) vi ve ->
  NBIE.Value vo ->
  NBIE.evalStar (NBI.app (pair_up p) vi) vo ->
  OfType (embed B) vo ve.
Proof.
  intros VA VB Heq Hp [[Hvi Htyvi] [Hve Htyve]] Hvo Heval.
  split.
  - split; [exact Hvo|]. rewrite repEmul_embed_leftinv.
    eapply StlcIso.TypeSafety.preservation_star; eauto using ValidEnv_nil.
    eapply StlcIso.SpecTyping.WtApp.
    + exact (pair_up_typing Hp).
    + now rewrite <- repEmul_embed_leftinv.
  - split; [exact Hve|]. rewrite isToEq_embed_leftinv.
    eapply StlcEqui.SpecTyping.WtEq.
    + exact Heq.
    + exact VA.
    + exact VB.
    + now rewrite <- isToEq_embed_leftinv.
Qed.

Lemma native_reverse_output_oftype_from {A B p vi ve vo} :
  ValidTy A -> ValidTy B ->
  Tyeq A B ->
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  OfType (embed B) vi ve ->
  NBIE.Value vo ->
  NBIE.evalStar (NBI.app (pair_down p) vi) vo ->
  OfType (embed A) vo ve.
Proof.
  intros VA VB Heq Hp [[Hvi Htyvi] [Hve Htyve]] Hvo Heval.
  split.
  - split; [exact Hvo|]. rewrite repEmul_embed_leftinv.
    eapply StlcIso.TypeSafety.preservation_star; eauto using ValidEnv_nil.
    eapply StlcIso.SpecTyping.WtApp.
    + exact (pair_down_typing Hp).
    + now rewrite <- repEmul_embed_leftinv.
  - split; [exact Hve|]. rewrite isToEq_embed_leftinv.
    eapply StlcEqui.SpecTyping.WtEq.
    + exact (tyeq_symm Heq).
    + exact VB.
    + exact VA.
    + now rewrite <- isToEq_embed_leftinv.
Qed.

Lemma native_forward_output_oftype {dir w A B p vi ve vo} :
  ValidTy A -> ValidTy B ->
  Tyeq A B ->
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  valrel dir w (embed A) vi ve ->
  NBIE.Value vo ->
  NBIE.evalStar (NBI.app (pair_up p) vi) vo ->
  OfType (embed B) vo ve.
Proof.
  intros VA VB Heq Hp Hrel Hvo Heval.
  exact (native_forward_output_oftype_from VA VB Heq Hp
    (valrel_implies_OfType Hrel) Hvo Heval).
Qed.

Lemma native_reverse_output_oftype {dir w A B p vi ve vo} :
  ValidTy A -> ValidTy B ->
  Tyeq A B ->
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  valrel dir w (embed B) vi ve ->
  NBIE.Value vo ->
  NBIE.evalStar (NBI.app (pair_down p) vi) vo ->
  OfType (embed A) vo ve.
Proof.
  intros VA VB Heq Hp Hrel Hvo Heval.
  exact (native_reverse_output_oftype_from VA VB Heq Hp
    (valrel_implies_OfType Hrel) Hvo Heval).
Qed.

(** Unlike products, sums, and arrows, exposing an iso-recursive value does
    not consume a logical world in the repository's native relation. *)
Lemma valrel_ptrec_inversion {dir w tau vi ve} :
  ValidPTy (ptrec tau) ->
  valrel dir w (ptrec tau) vi ve ->
  exists vi',
    vi = NBI.fold_ vi' /\
    valrel dir w (tau[beta1 (ptrec tau)]) vi' ve.
Proof.
  intros Vmu Hrel.
  rewrite valrel_fixp in Hrel.
  destruct Hrel as
    (Htyped & deep & (vi' & -> & Hfolds) & Hvalue & Hlayer).
  exists vi'. split; [reflexivity|].
  rewrite valrel_fixp. split.
  - destruct (OfType_inversion_ptrec Vmu Htyped)
      as (inner & Heq & Hinner).
    inversion Heq. subst inner. exact Hinner.
  - exists deep.
    replace (LMC_pty tau[beta1 (ptrec tau)]) with (LMC_pty tau) in *.
    + split; [exact Hfolds|]. split.
      * now cbn in Hvalue.
      * exact Hlayer.
    + symmetry.
      refine (LMC_pUnfoldOnce (ptrec tau) _ _).
      * exact (proj2 Vmu).
      * cbn. lia.
Qed.

Lemma valrel_embed_trec_inversion {dir w body vi ve} :
  ValidTy (trec body) ->
  valrel dir w (embed (trec body)) vi ve ->
  exists vi',
    vi = NBI.fold_ vi' /\
    valrel dir w (embed body[beta1 (trec body)]) vi' ve.
Proof.
  intros Vmu Hrel. cbn in Hrel.
  destruct (valrel_ptrec_inversion
    (ValidTy_implies_ValidPTy_embed Vmu) Hrel)
    as (vi' & -> & Hinner).
  exists vi'. split; [reflexivity|].
  rewrite embed_sub.
  replace (beta1 (trec body) >-> embed)
    with (beta1 (ptrec (embed body))).
  2:{ extensionality i. destruct i; reflexivity. }
  exact Hinner.
Qed.

Lemma native_valrel_lambda_from_oftype
  {dir w dom cod iso_body equi_ann equi_body} :
  OfType (ptarr dom cod)
    (I.abs (repEmul dom) iso_body)
    (E.abs equi_ann equi_body) ->
  (forall w' (vi : I.Tm) (ve : E.Tm),
    w' < w ->
    (dir = dir_gt -> StlcEqui.Size.size ve <= w') ->
    valrel dir w' dom vi ve ->
    termrel dir w' cod
      (iso_body[beta1 vi]) (equi_body[beta1 ve])) ->
  valrel dir w (ptarr dom cod)
    (I.abs (repEmul dom) iso_body)
    (E.abs equi_ann equi_body).
Proof.
  intros Htyped Hbody. rewrite valrel_fixp. split; [exact Htyped|].
  cbn. exists (I.abs (repEmul dom) iso_body). split; [reflexivity|].
  split; [exact I|].
  exists iso_body, equi_body, (repEmul dom), equi_ann.
  repeat split; try reflexivity.
  intros w' Hw' vi ve Hsize Hrel.
  exact (Hbody w' vi ve Hw' Hsize Hrel).
Qed.

Lemma native_generated_arrow_body_subst
  (domcast codcast vf va : I.Tm) :
  (I.app codcast[wkm]
      (I.app vf[wk]
        (I.app domcast[wkm] (I.var 0))))[beta1 va] =
  I.app codcast (I.app vf (I.app domcast va)).
Proof.
  cbn. repeat crushDbLemmasRewriteH.
  replace (I.apTm (beta1 va) codcast[wkm]) with codcast.
  2:{ symmetry. exact (@apply_wkm_beta1_cancel I.Tm I.Tm
        _ _ _ _ _ _ codcast va). }
  replace (I.apTm (beta1 va) domcast[wkm]) with domcast.
  2:{ symmetry. exact (@apply_wkm_beta1_cancel I.Tm I.Tm
        _ _ _ _ _ _ domcast va). }
  replace (I.apTm (beta1 va) vf[wk]) with vf.
  2:{ assert (Hwk : vf[wk] = vf[wkm]).
      { rewrite <- ap_liftSub, liftSub_wkm. reflexivity. }
      rewrite Hwk.
      symmetry. exact (@apply_wkm_beta1_cancel I.Tm I.Tm
        _ _ _ _ _ _ vf va). }
  reflexivity.
Qed.

Lemma native_forward_action_map_term radix budget A B p dir w ti te :
  cast_pair_function_shape A B p ->
  native_pair_action_below radix budget A B p ->
  (forall w', w' <= w ->
    native_semantic_measure radix A B w' < budget) ->
  termrel dir w (embed A) ti te ->
  termrel dir w (embed B) (NBI.app (pair_up p) ti) te.
Proof.
  intros Hshape [Haction _] Hmeasure Hterm.
  destruct (cast_pair_up_function_shape A B p Hshape)
    as (body & Hfun).
  eapply termrel_antired_star_left.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (NBI.papp₁ NBI.phole ti) I Hfun).
  - change (NBI.app (NBI.abs A body) ti) with
      (I.pctx_app ti (I.papp₂ (I.abs A body) I.phole)).
    change te with (E.pctx_app te E.phole).
    refine (@termrel_ectx dir w (embed A) (embed B) ti
      (I.papp₂ (I.abs A body) I.phole) te E.phole (conj I I) I Hterm _).
    intros w' Hw' vi ve Hrel.
    destruct (Haction dir w' vi ve (Hmeasure w' Hw') Hrel)
      as (vo & Hvo & Happ & Hout).
    assert (Hprefix : NBIE.evalStar
      (NBI.app (pair_up p) vi) (NBI.app (NBI.abs A body) vi)).
    { exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.papp₁ NBI.phole vi) I Hfun). }
    assert (Hsuffix : NBIE.evalStar (NBI.app (NBI.abs A body) vi) vo).
    { eapply StlcIso.LemmasEvaluation.determinacyStar;
        eauto using StlcIso.LemmasEvaluation.values_are_normal. }
    eapply termrel_antired_star_left; [exact Hsuffix|].
    now apply valrel_in_termrel.
Qed.

Lemma native_reverse_action_map_term radix budget A B p dir w ti te :
  cast_pair_function_shape A B p ->
  native_pair_action_below radix budget A B p ->
  (forall w', w' <= w ->
    native_semantic_measure radix A B w' < budget) ->
  termrel dir w (embed B) ti te ->
  termrel dir w (embed A) (NBI.app (pair_down p) ti) te.
Proof.
  intros Hshape [_ Haction] Hmeasure Hterm.
  destruct (cast_pair_down_function_shape A B p Hshape)
    as (body & Hfun).
  eapply termrel_antired_star_left.
  - exact (StlcIso.LemmasEvaluation.evalstar_ctx
      (NBI.papp₁ NBI.phole ti) I Hfun).
  - change (NBI.app (NBI.abs B body) ti) with
      (I.pctx_app ti (I.papp₂ (I.abs B body) I.phole)).
    change te with (E.pctx_app te E.phole).
    refine (@termrel_ectx dir w (embed B) (embed A) ti
      (I.papp₂ (I.abs B body) I.phole) te E.phole (conj I I) I Hterm _).
    intros w' Hw' vi ve Hrel.
    destruct (Haction dir w' vi ve (Hmeasure w' Hw') Hrel)
      as (vo & Hvo & Happ & Hout).
    assert (Hprefix : NBIE.evalStar
      (NBI.app (pair_down p) vi) (NBI.app (NBI.abs B body) vi)).
    { exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.papp₁ NBI.phole vi) I Hfun). }
    assert (Hsuffix : NBIE.evalStar (NBI.app (NBI.abs B body) vi) vo).
    { eapply StlcIso.LemmasEvaluation.determinacyStar;
        eauto using StlcIso.LemmasEvaluation.values_are_normal. }
    eapply termrel_antired_star_left; [exact Hsuffix|].
    now apply valrel_in_termrel.
Qed.

Lemma native_measure_smaller_world radix budget A B A' B' w' w :
  LMC A' + LMC B' < radix ->
  w' < w ->
  native_semantic_measure radix A B w < S budget ->
  native_semantic_measure radix A' B' w' < budget.
Proof. unfold native_semantic_measure. nia. Qed.

Lemma native_measure_smaller_lmc radix budget A B A' B' w :
  LMC A' + LMC B' < LMC A + LMC B ->
  native_semantic_measure radix A B w < S budget ->
  native_semantic_measure radix A' B' w < budget.
Proof. unfold native_semantic_measure. lia. Qed.

Lemma native_forward_outputs_below radix budget A B p dir w vi ve :
  ValidTy A -> ValidTy B ->
  Tyeq A B ->
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  cast_pair_application_terminates A B p ->
  native_pair_action_below radix budget A B p ->
  OfType (embed A) vi ve ->
  (forall w', w' < w ->
    native_semantic_measure radix A B w' < budget) ->
  (forall w', w' < w -> valrel dir w' (embed A) vi ve) ->
  exists vo,
    NBIE.Value vo /\
    NBIE.evalStar (NBI.app (pair_up p) vi) vo /\
    OfType (embed B) vo ve /\
    (forall w', w' < w -> valrel dir w' (embed B) vo ve).
Proof.
  intros VA VB Heq Hp [Hterm _] [Haction _] Hin Hmeasure Hinput.
  destruct Hin as [[Hvi Htyvi] Hve].
  assert (Htyvi' : StlcIso.SpecTyping.Typing empty vi A).
  { now rewrite <- repEmul_embed_leftinv. }
  destruct (Hterm vi Hvi Htyvi') as (vo & Hvo & Heval).
  exists vo. split; [exact Hvo|]. split; [exact Heval|]. split.
  - exact (native_forward_output_oftype_from VA VB Heq Hp
      (conj (conj Hvi Htyvi) Hve) Hvo Heval).
  - intros w' Hw'.
    destruct (Haction dir w' vi ve (Hmeasure w' Hw')
      (Hinput w' Hw')) as (vo' & Hvo' & Heval' & Hout').
    assert (Hvoeval : NBIE.evalStar vo vo').
    { eapply StlcIso.LemmasEvaluation.determinacyStar;
        eauto using StlcIso.LemmasEvaluation.values_are_normal. }
    assert (vo = vo') by
      (eapply StlcIso.LemmasEvaluation.value_evalStar; eauto).
    now subst vo'.
Qed.

Lemma native_reverse_outputs_below radix budget A B p dir w vi ve :
  ValidTy A -> ValidTy B ->
  Tyeq A B ->
  StlcIso.SpecTyping.Typing empty p (cast_pair_ty A B) ->
  cast_pair_application_terminates A B p ->
  native_pair_action_below radix budget A B p ->
  OfType (embed B) vi ve ->
  (forall w', w' < w ->
    native_semantic_measure radix A B w' < budget) ->
  (forall w', w' < w -> valrel dir w' (embed B) vi ve) ->
  exists vo,
    NBIE.Value vo /\
    NBIE.evalStar (NBI.app (pair_down p) vi) vo /\
    OfType (embed A) vo ve /\
    (forall w', w' < w -> valrel dir w' (embed A) vo ve).
Proof.
  intros VA VB Heq Hp [_ Hterm] [_ Haction] Hin Hmeasure Hinput.
  destruct Hin as [[Hvi Htyvi] Hve].
  assert (Htyvi' : StlcIso.SpecTyping.Typing empty vi B).
  { now rewrite <- repEmul_embed_leftinv. }
  destruct (Hterm vi Hvi Htyvi') as (vo & Hvo & Heval).
  exists vo. split; [exact Hvo|]. split; [exact Heval|]. split.
  - exact (native_reverse_output_oftype_from VA VB Heq Hp
      (conj (conj Hvi Htyvi) Hve) Hvo Heval).
  - intros w' Hw'.
    destruct (Haction dir w' vi ve (Hmeasure w' Hw')
      (Hinput w' Hw')) as (vo' & Hvo' & Heval' & Hout').
    assert (Hvoeval : NBIE.evalStar vo vo').
    { eapply StlcIso.LemmasEvaluation.determinacyStar;
        eauto using StlcIso.LemmasEvaluation.values_are_normal. }
    assert (vo = vo') by
      (eapply StlcIso.LemmasEvaluation.value_evalStar; eauto).
    now subst vo'.
Qed.

Lemma native_identity_pair_action_below radix budget T :
  native_pair_action_below radix budget T T
    (NBI.pair (id_cast T) (id_cast T)).
Proof.
  split; intros dir w vi ve Hmeasure Hrel.
  - exists vi. split; [exact (proj1 (valrel_implies_Value Hrel))|]. split.
    + pose proof (@pair_first_abs_app_eval T (BI.var 0)
        (BI.abs T (BI.var 0)) vi I
        (proj1 (valrel_implies_Value Hrel))) as Heval.
      cbn in Heval. exact Heval.
    + exact Hrel.
  - exists vi. split; [exact (proj1 (valrel_implies_Value Hrel))|]. split.
    + pose proof (@pair_second_abs_app_eval T (BI.var 0)
        (BI.abs T (BI.var 0)) vi I
        (proj1 (valrel_implies_Value Hrel))) as Heval.
      cbn in Heval. exact Heval.
    + exact Hrel.
Qed.

Lemma arrow_node_native_action_below radix budget H A1 A2 B1 B2
  (dom : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A1 B1)
  (cod : CastEq ((tarr A1 A2, tarr B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  PairEnvValid H ->
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_arr H A1 A2 B1 B2 dom cod)) ->
  CastTermsTyping empty ((tarr A1 A2, tarr B1 B2) :: H) rho ->
  certificate_lmc_bound dom < radix ->
  certificate_lmc_bound cod < radix ->
  node_bundle_native_action radix budget
    (cn_arr H A1 A2 B1 B2 dom cod) payload ->
  cast_terms_native_action radix budget rho ->
  node_bundle_function_shape (cn_arr H A1 A2 B1 B2 dom cod) payload ->
  cast_terms_function_shape rho ->
  native_pair_action_below radix (S budget)
    (tarr A1 A2) (tarr B1 B2)
    (global_node_cast (cn_arr H A1 A2 B1 B2 dom cod) payload rho).
Proof.
  intros VH VA1 VA2 VB1 VB2 Hpayload Htyrho Hdombound Hcodbound
    [Hdombundle Hcodbundle] Hrho [Hdomshape Hcodshape] Hrhoshape.
  pose proof (certificate_root_native_action radix budget dom
    (NBI.proj₁ payload) rho Hdombundle Hrho) as Hdomaction.
  pose proof (certificate_root_native_action radix budget cod
    (NBI.proj₂ payload) rho Hcodbundle Hrho) as Hcodaction.
  pose proof (certificate_root_function_shape dom
    (NBI.proj₁ payload) rho Hdomshape Hrhoshape) as Hdomrootshape.
  pose proof (certificate_root_function_shape cod
    (NBI.proj₂ payload) rho Hcodshape Hrhoshape) as Hcodrootshape.
  assert (Hdomselfty : StlcIso.SpecTyping.Typing empty
    (NBI.proj₁ payload) (certificate_bundle_ty dom))
    by (eapply StlcIso.SpecTyping.WtProj1; exact Hpayload).
  assert (Hcodselfty : StlcIso.SpecTyping.Typing empty
    (NBI.proj₂ payload) (certificate_bundle_ty cod))
    by (eapply StlcIso.SpecTyping.WtProj2; exact Hpayload).
  pose proof (certificate_root_typing dom _ _ Hdomselfty Htyrho) as Hdomty.
  pose proof (certificate_root_typing cod _ _ Hcodselfty Htyrho) as Hcodty.
  assert (Hdomlmc : LMC A1 + LMC B1 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate dom). lia. }
  assert (Hcodlmc : LMC A2 + LMC B2 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate cod). lia. }
  set (whole := cn_arr H A1 A2 B1 B2 dom cod).
  assert (Hwholeeq : Tyeq (tarr A1 A2) (tarr B1 B2)).
  { exact (focus_sound (focus (ce_step whole) fs)). }
  assert (Hglobalty : StlcIso.SpecTyping.Typing empty
    (global_node_cast whole payload rho)
    (cast_pair_ty (tarr A1 A2) (tarr B1 B2))).
  { subst whole. eapply global_node_cast_typing; eauto;
      now apply ValidTy_arr. }
  split; intros dir w vi ve Hmeasure Hrel.
  - destruct (valrel_ptarr_inversion
      (ValidTy_implies_ValidPTy_embed VA1)
      (ValidTy_implies_ValidPTy_embed VA2) Hrel)
      as (ti & te & ann & -> & -> & Vann & Hanneq & Hti & Hte & Hfun).
    rewrite (repEmul_embed_leftinv A1) in *.
    set (outbody :=
      NBI.app
        (pair_up (certificate_root cod (NBI.proj₂ payload) rho))[wkm]
        (NBI.app (NBI.abs A1 ti)[wk]
          (NBI.app
            (pair_down (certificate_root dom (NBI.proj₁ payload) rho))[wkm]
            (NBI.var 0)))).
    assert (Heval : NBIE.evalStar
      (NBI.app (pair_up (global_node_cast whole payload rho))
        (NBI.abs A1 ti))
      (NBI.abs B1 outbody)).
    { subst whole outbody.
      eapply global_arrow_forward_application_eval; exact I. }
    assert (Hrelclean : valrel dir w (embed (tarr A1 A2))
      (NBI.abs A1 ti) (E.abs ann te)).
    { exact Hrel. }
    assert (Houtoft : OfType (embed (tarr B1 B2))
      (NBI.abs B1 outbody) (E.abs ann te)).
    { exact (@native_forward_output_oftype dir w
        (tarr A1 A2) (tarr B1 B2)
        (global_node_cast whole payload rho)
        (NBI.abs A1 ti) (E.abs ann te) (NBI.abs B1 outbody)
        (ValidTy_arr VA1 VA2) (ValidTy_arr VB1 VB2)
        Hwholeeq Hglobalty Hrelclean I Heval). }
    exists (NBI.abs B1 outbody). split; [exact I|]. split; [exact Heval|].
    change (valrel dir w (ptarr (embed B1) (embed B2))
      (NBI.abs B1 outbody) (E.abs ann te)).
    assert (Houtoft' : OfType (ptarr (embed B1) (embed B2))
      (NBI.abs (repEmul (embed B1)) outbody) (E.abs ann te)).
    { rewrite repEmul_embed_leftinv. exact Houtoft. }
    assert (Hlambda : valrel dir w (ptarr (embed B1) (embed B2))
      (NBI.abs (repEmul (embed B1)) outbody) (E.abs ann te)).
    { eapply native_valrel_lambda_from_oftype; [exact Houtoft'|].
      intros w' vai vae Hw' Hsize Harg.
      destruct (proj2 Hdomaction dir w' vai vae
        ltac:(eapply native_measure_smaller_world; eauto) Harg)
        as (vad & Hvad & Hdomeval & Hdomout).
      assert (Hsource : termrel dir w' (embed A2)
        (ti[beta1 vad]) (te[beta1 vae])).
      { eapply Hfun; eauto. }
      assert (Hsource' : termrel dir w' (embed A2)
        (NBI.app (NBI.abs A1 ti)
          (NBI.app
            (pair_down (certificate_root dom (NBI.proj₁ payload) rho)) vai))
        (te[beta1 vae])).
      { eapply termrel_antired_star_left; [|exact Hsource].
        eapply evalStepTrans.
        - exact (StlcIso.LemmasEvaluation.evalstar_ctx
            (NBI.papp₂ (NBI.abs A1 ti) NBI.phole) (conj I I) Hdomeval).
        - apply evalToStar, NBIE.eval_eval₀.
          now apply NBIE.eval_beta.
      }
      assert (Hmapped : termrel dir w' (embed B2)
        (NBI.app
          (pair_up (certificate_root cod (NBI.proj₂ payload) rho))
          (NBI.app (NBI.abs A1 ti)
            (NBI.app
              (pair_down (certificate_root dom (NBI.proj₁ payload) rho)) vai)))
        (te[beta1 vae])).
      { eapply native_forward_action_map_term; eauto.
        intros w'' Hw''.
        eapply (native_measure_smaller_world radix budget
          (tarr A1 A2) (tarr B1 B2) A2 B2 w'' w).
        - exact Hcodlmc.
        - lia.
        - exact Hmeasure. }
      subst outbody.
      rewrite (@native_generated_arrow_body_subst
        (pair_down (certificate_root dom (NBI.proj₁ payload) rho))
        (pair_up (certificate_root cod (NBI.proj₂ payload) rho))
        (NBI.abs A1 ti) vai).
      exact Hmapped. }
    rewrite repEmul_embed_leftinv in Hlambda. exact Hlambda.
  - destruct (valrel_ptarr_inversion
      (ValidTy_implies_ValidPTy_embed VB1)
      (ValidTy_implies_ValidPTy_embed VB2) Hrel)
      as (ti & te & ann & -> & -> & Vann & Hanneq & Hti & Hte & Hfun).
    rewrite (repEmul_embed_leftinv B1) in *.
    set (outbody :=
      NBI.app
        (pair_down (certificate_root cod (NBI.proj₂ payload) rho))[wkm]
        (NBI.app (NBI.abs B1 ti)[wk]
          (NBI.app
            (pair_up (certificate_root dom (NBI.proj₁ payload) rho))[wkm]
            (NBI.var 0)))).
    assert (Heval : NBIE.evalStar
      (NBI.app (pair_down (global_node_cast whole payload rho))
        (NBI.abs B1 ti))
      (NBI.abs A1 outbody)).
    { subst whole outbody.
      eapply global_arrow_reverse_application_eval; exact I. }
    assert (Hrelclean : valrel dir w (embed (tarr B1 B2))
      (NBI.abs B1 ti) (E.abs ann te)).
    { exact Hrel. }
    assert (Houtoft : OfType (embed (tarr A1 A2))
      (NBI.abs A1 outbody) (E.abs ann te)).
    { exact (@native_reverse_output_oftype dir w
        (tarr A1 A2) (tarr B1 B2)
        (global_node_cast whole payload rho)
        (NBI.abs B1 ti) (E.abs ann te) (NBI.abs A1 outbody)
        (ValidTy_arr VA1 VA2) (ValidTy_arr VB1 VB2)
        Hwholeeq Hglobalty Hrelclean I Heval). }
    exists (NBI.abs A1 outbody). split; [exact I|]. split; [exact Heval|].
    change (valrel dir w (ptarr (embed A1) (embed A2))
      (NBI.abs A1 outbody) (E.abs ann te)).
    assert (Houtoft' : OfType (ptarr (embed A1) (embed A2))
      (NBI.abs (repEmul (embed A1)) outbody) (E.abs ann te)).
    { rewrite repEmul_embed_leftinv. exact Houtoft. }
    assert (Hlambda : valrel dir w (ptarr (embed A1) (embed A2))
      (NBI.abs (repEmul (embed A1)) outbody) (E.abs ann te)).
    { eapply native_valrel_lambda_from_oftype; [exact Houtoft'|].
      intros w' vai vae Hw' Hsize Harg.
      destruct (proj1 Hdomaction dir w' vai vae
        ltac:(eapply native_measure_smaller_world; eauto) Harg)
        as (vad & Hvad & Hdomeval & Hdomout).
      assert (Hsource : termrel dir w' (embed B2)
        (ti[beta1 vad]) (te[beta1 vae])).
      { eapply Hfun; eauto. }
      assert (Hsource' : termrel dir w' (embed B2)
        (NBI.app (NBI.abs B1 ti)
          (NBI.app
            (pair_up (certificate_root dom (NBI.proj₁ payload) rho)) vai))
        (te[beta1 vae])).
      { eapply termrel_antired_star_left; [|exact Hsource].
        eapply evalStepTrans.
        - exact (StlcIso.LemmasEvaluation.evalstar_ctx
            (NBI.papp₂ (NBI.abs B1 ti) NBI.phole) (conj I I) Hdomeval).
        - apply evalToStar, NBIE.eval_eval₀.
          now apply NBIE.eval_beta.
      }
      assert (Hmapped : termrel dir w' (embed A2)
        (NBI.app
          (pair_down (certificate_root cod (NBI.proj₂ payload) rho))
          (NBI.app (NBI.abs B1 ti)
            (NBI.app
              (pair_up (certificate_root dom (NBI.proj₁ payload) rho)) vai)))
        (te[beta1 vae])).
      { eapply native_reverse_action_map_term; eauto.
        intros w'' Hw''.
        eapply (native_measure_smaller_world radix budget
          (tarr A1 A2) (tarr B1 B2) A2 B2 w'' w).
        - exact Hcodlmc.
        - lia.
        - exact Hmeasure. }
      subst outbody.
      rewrite (@native_generated_arrow_body_subst
        (pair_up (certificate_root dom (NBI.proj₁ payload) rho))
        (pair_down (certificate_root cod (NBI.proj₂ payload) rho))
        (NBI.abs B1 ti) vai).
      exact Hmapped. }
    rewrite repEmul_embed_leftinv in Hlambda. exact Hlambda.
Qed.

Lemma product_node_native_action_below radix budget H A1 A2 B1 B2
  (fstc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A1 B1)
  (sndc : CastEq ((tprod A1 A2, tprod B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_prod H A1 A2 B1 B2 fstc sndc)) ->
  CastTermsTyping empty ((tprod A1 A2, tprod B1 B2) :: H) rho ->
  certificate_lmc_bound fstc < radix ->
  certificate_lmc_bound sndc < radix ->
  node_bundle_native_action radix budget
    (cn_prod H A1 A2 B1 B2 fstc sndc) payload ->
  cast_terms_native_action radix budget rho ->
  node_bundle_application_terminates
    (cn_prod H A1 A2 B1 B2 fstc sndc) payload ->
  cast_terms_application_terminates rho ->
  native_pair_action_below radix (S budget)
    (tprod A1 A2) (tprod B1 B2)
    (global_node_cast (cn_prod H A1 A2 B1 B2 fstc sndc) payload rho).
Proof.
  intros VA1 VA2 VB1 VB2 Hpayload Htyrho Hfstbound Hsndbound
    [Hfstbundle Hsndbundle] Hrho [Hfstterm Hsndterm] Hrhterm.
  pose proof (certificate_root_native_action radix budget fstc
    (NBI.proj₁ payload) rho Hfstbundle Hrho) as Hfstaction.
  pose proof (certificate_root_native_action radix budget sndc
    (NBI.proj₂ payload) rho Hsndbundle Hrho) as Hsndaction.
  pose proof (certificate_root_application_terminates fstc
    (NBI.proj₁ payload) rho Hfstterm Hrhterm) as Hfstappterm.
  pose proof (certificate_root_application_terminates sndc
    (NBI.proj₂ payload) rho Hsndterm Hrhterm) as Hsndappterm.
  assert (Hfstselfty : StlcIso.SpecTyping.Typing empty
    (NBI.proj₁ payload) (certificate_bundle_ty fstc))
    by (eapply StlcIso.SpecTyping.WtProj1; exact Hpayload).
  assert (Hsndselfty : StlcIso.SpecTyping.Typing empty
    (NBI.proj₂ payload) (certificate_bundle_ty sndc))
    by (eapply StlcIso.SpecTyping.WtProj2; exact Hpayload).
  pose proof (certificate_root_typing fstc _ _ Hfstselfty Htyrho)
    as Hfstty.
  pose proof (certificate_root_typing sndc _ _ Hsndselfty Htyrho)
    as Hsndty.
  assert (Hfstlmc : LMC A1 + LMC B1 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate fstc). lia. }
  assert (Hsndlmc : LMC A2 + LMC B2 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate sndc). lia. }
  set (whole := cn_prod H A1 A2 B1 B2 fstc sndc).
  assert (Hfsteq : Tyeq A1 B1).
  { exact (focus_sound (focus fstc (frames_cons whole fs))). }
  assert (Hsndeq : Tyeq A2 B2).
  { exact (focus_sound (focus sndc (frames_cons whole fs))). }
  split; intros dir w vi ve Hmeasure Hrel.
  - destruct (valrel_ptprod_inversion
      (ValidTy_implies_ValidPTy_embed VA1)
      (ValidTy_implies_ValidPTy_embed VA2) Hrel)
      as (vi1 & vi2 & ve1 & ve2 & -> & -> & Hof1 & Hof2 & Hchildren).
    pose proof (proj1 (OfType_implies_Value Hof1)) as Hvi1.
    pose proof (proj1 (OfType_implies_Value Hof2)) as Hvi2.
    destruct (native_forward_outputs_below radix budget A1 B1
      (certificate_root fstc (NBI.proj₁ payload) rho) dir w vi1 ve1
      VA1 VB1 Hfsteq Hfstty Hfstappterm Hfstaction Hof1
      ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
      ltac:(intros w' Hw'; exact (proj1 (Hchildren w' Hw'))))
      as (vo1 & Hvo1 & Heval1 & Hofout1 & Hrelout1).
    destruct (native_forward_outputs_below radix budget A2 B2
      (certificate_root sndc (NBI.proj₂ payload) rho) dir w vi2 ve2
      VA2 VB2 Hsndeq Hsndty Hsndappterm Hsndaction Hof2
      ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
      ltac:(intros w' Hw'; exact (proj2 (Hchildren w' Hw'))))
      as (vo2 & Hvo2 & Heval2 & Hofout2 & Hrelout2).
    exists (NBI.pair vo1 vo2). split; [now split|]. split.
    + eapply global_product_forward_application_eval; eauto.
    + eapply valrel_pair''; eauto using ValidTy_implies_ValidPTy_embed.
  - destruct (valrel_ptprod_inversion
      (ValidTy_implies_ValidPTy_embed VB1)
      (ValidTy_implies_ValidPTy_embed VB2) Hrel)
      as (vi1 & vi2 & ve1 & ve2 & -> & -> & Hof1 & Hof2 & Hchildren).
    pose proof (proj1 (OfType_implies_Value Hof1)) as Hvi1.
    pose proof (proj1 (OfType_implies_Value Hof2)) as Hvi2.
    destruct (native_reverse_outputs_below radix budget A1 B1
      (certificate_root fstc (NBI.proj₁ payload) rho) dir w vi1 ve1
      VA1 VB1 Hfsteq Hfstty Hfstappterm Hfstaction Hof1
      ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
      ltac:(intros w' Hw'; exact (proj1 (Hchildren w' Hw'))))
      as (vo1 & Hvo1 & Heval1 & Hofout1 & Hrelout1).
    destruct (native_reverse_outputs_below radix budget A2 B2
      (certificate_root sndc (NBI.proj₂ payload) rho) dir w vi2 ve2
      VA2 VB2 Hsndeq Hsndty Hsndappterm Hsndaction Hof2
      ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
      ltac:(intros w' Hw'; exact (proj2 (Hchildren w' Hw'))))
      as (vo2 & Hvo2 & Heval2 & Hofout2 & Hrelout2).
    exists (NBI.pair vo1 vo2). split; [now split|]. split.
    + eapply global_product_reverse_application_eval; eauto.
    + eapply valrel_pair''; eauto using ValidTy_implies_ValidPTy_embed.
Qed.

Lemma sum_node_native_action_below radix budget H A1 A2 B1 B2
  (lc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A1 B1)
  (rc : CastEq ((tsum A1 A2, tsum B1 B2) :: H) A2 B2)
  (fs : Frames H) payload rho :
  ValidTy A1 -> ValidTy A2 -> ValidTy B1 -> ValidTy B2 ->
  StlcIso.SpecTyping.Typing empty payload
    (node_bundle_ty (cn_sum H A1 A2 B1 B2 lc rc)) ->
  CastTermsTyping empty ((tsum A1 A2, tsum B1 B2) :: H) rho ->
  certificate_lmc_bound lc < radix ->
  certificate_lmc_bound rc < radix ->
  node_bundle_native_action radix budget
    (cn_sum H A1 A2 B1 B2 lc rc) payload ->
  cast_terms_native_action radix budget rho ->
  node_bundle_application_terminates
    (cn_sum H A1 A2 B1 B2 lc rc) payload ->
  cast_terms_application_terminates rho ->
  native_pair_action_below radix (S budget)
    (tsum A1 A2) (tsum B1 B2)
    (global_node_cast (cn_sum H A1 A2 B1 B2 lc rc) payload rho).
Proof.
  intros VA1 VA2 VB1 VB2 Hpayload Htyrho Hlbound Hrbound
    [Hlbundle Hrbundle] Hrho [Hlterm Hrterm] Hrhterm.
  pose proof (certificate_root_native_action radix budget lc
    (NBI.proj₁ payload) rho Hlbundle Hrho) as Hlaction.
  pose proof (certificate_root_native_action radix budget rc
    (NBI.proj₂ payload) rho Hrbundle Hrho) as Hraction.
  pose proof (certificate_root_application_terminates lc
    (NBI.proj₁ payload) rho Hlterm Hrhterm) as Hlappterm.
  pose proof (certificate_root_application_terminates rc
    (NBI.proj₂ payload) rho Hrterm Hrhterm) as Hrappterm.
  assert (Hlselfty : StlcIso.SpecTyping.Typing empty
    (NBI.proj₁ payload) (certificate_bundle_ty lc))
    by (eapply StlcIso.SpecTyping.WtProj1; exact Hpayload).
  assert (Hrselfty : StlcIso.SpecTyping.Typing empty
    (NBI.proj₂ payload) (certificate_bundle_ty rc))
    by (eapply StlcIso.SpecTyping.WtProj2; exact Hpayload).
  pose proof (certificate_root_typing lc _ _ Hlselfty Htyrho) as Hlty.
  pose proof (certificate_root_typing rc _ _ Hrselfty Htyrho) as Hrty.
  assert (Hllmc : LMC A1 + LMC B1 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate lc). lia. }
  assert (Hrlmc : LMC A2 + LMC B2 < radix).
  { pose proof (endpoint_lmc_bounded_by_certificate rc). lia. }
  set (whole := cn_sum H A1 A2 B1 B2 lc rc).
  assert (Hleq : Tyeq A1 B1).
  { exact (focus_sound (focus lc (frames_cons whole fs))). }
  assert (Hreq : Tyeq A2 B2).
  { exact (focus_sound (focus rc (frames_cons whole fs))). }
  split; intros dir w vi ve Hmeasure Hrel.
  - destruct (valrel_ptsum_inversion
      (ValidTy_implies_ValidPTy_embed VA1)
      (ValidTy_implies_ValidPTy_embed VA2) Hrel)
      as (vi' & ve' & [Hinl | Hinr]).
    + destruct Hinl as [-> [-> [Hof Hchildren]]].
      pose proof (proj1 (OfType_implies_Value Hof)) as Hvi.
      destruct (native_forward_outputs_below radix budget A1 B1
        (certificate_root lc (NBI.proj₁ payload) rho) dir w vi' ve'
        VA1 VB1 Hleq Hlty Hlappterm Hlaction Hof
        ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
        Hchildren)
        as (vo & Hvo & Heval & Hofout & Hrelout).
      exists (NBI.inl vo). split; [exact Hvo|]. split.
      * cbn [global_node_cast].
        eapply pair_first_sum_inl_app_eval; eauto; exact I.
      * eapply valrel_inl''; eauto using ValidTy_implies_ValidPTy_embed.
    + destruct Hinr as [-> [-> [Hof Hchildren]]].
      pose proof (proj1 (OfType_implies_Value Hof)) as Hvi.
      destruct (native_forward_outputs_below radix budget A2 B2
        (certificate_root rc (NBI.proj₂ payload) rho) dir w vi' ve'
        VA2 VB2 Hreq Hrty Hrappterm Hraction Hof
        ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
        Hchildren)
        as (vo & Hvo & Heval & Hofout & Hrelout).
      exists (NBI.inr vo). split; [exact Hvo|]. split.
      * cbn [global_node_cast].
        eapply pair_first_sum_inr_app_eval; eauto; exact I.
      * eapply valrel_inr''; eauto using ValidTy_implies_ValidPTy_embed.
  - destruct (valrel_ptsum_inversion
      (ValidTy_implies_ValidPTy_embed VB1)
      (ValidTy_implies_ValidPTy_embed VB2) Hrel)
      as (vi' & ve' & [Hinl | Hinr]).
    + destruct Hinl as [-> [-> [Hof Hchildren]]].
      pose proof (proj1 (OfType_implies_Value Hof)) as Hvi.
      destruct (native_reverse_outputs_below radix budget A1 B1
        (certificate_root lc (NBI.proj₁ payload) rho) dir w vi' ve'
        VA1 VB1 Hleq Hlty Hlappterm Hlaction Hof
        ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
        Hchildren)
        as (vo & Hvo & Heval & Hofout & Hrelout).
      exists (NBI.inl vo). split; [exact Hvo|]. split.
      * cbn [global_node_cast].
        eapply pair_second_sum_inl_app_eval; eauto; exact I.
      * eapply valrel_inl''; eauto using ValidTy_implies_ValidPTy_embed.
    + destruct Hinr as [-> [-> [Hof Hchildren]]].
      pose proof (proj1 (OfType_implies_Value Hof)) as Hvi.
      destruct (native_reverse_outputs_below radix budget A2 B2
        (certificate_root rc (NBI.proj₂ payload) rho) dir w vi' ve'
        VA2 VB2 Hreq Hrty Hrappterm Hraction Hof
        ltac:(intros w' Hw'; eapply native_measure_smaller_world; eauto)
        Hchildren)
        as (vo & Hvo & Heval & Hofout & Hrelout).
      exists (NBI.inr vo). split; [exact Hvo|]. split.
      * cbn [global_node_cast].
        eapply pair_second_sum_inr_app_eval; eauto; exact I.
      * eapply valrel_inr''; eauto using ValidTy_implies_ValidPTy_embed.
Qed.

Lemma mu_l_node_native_action_below radix budget H body B
  (child : CastEq ((trec body, B) :: H)
    body[beta1 (trec body)] B)
  (fs : Frames H) payload rho :
  ValidTy (trec body) -> ValidTy B ->
  certificate_bundle_native_action radix budget child payload ->
  cast_terms_native_action radix budget rho ->
  native_pair_action_below radix (S budget) (trec body) B
    (global_node_cast (cn_mu_l H body B child) payload rho).
Proof.
  intros VA VB Hbundle Hrho.
  pose proof (certificate_root_native_action radix budget child
    payload rho Hbundle Hrho) as Haction.
  assert (Hlmc :
    LMC body[beta1 (trec body)] + LMC B < LMC (trec body) + LMC B).
  { pose proof (LMC_unfold_trec_lt body (proj2 VA)). lia. }
  split; intros dir w vi ve Hmeasure Hrel.
  - destruct (valrel_embed_trec_inversion VA Hrel)
      as (inner & -> & Hinner).
    destruct (proj1 Haction dir w inner ve
      ltac:(eapply native_measure_smaller_lmc; eauto) Hinner)
      as (vo & Hvo & Heval & Hout).
    exists vo. split; [exact Hvo|]. split.
    + cbn [global_node_cast]. eapply pair_first_mu_l_app_eval; eauto.
      exact (proj1 (valrel_implies_Value Hinner)).
    + exact Hout.
  - destruct (proj2 Haction dir w vi ve
      ltac:(eapply native_measure_smaller_lmc; eauto) Hrel)
      as (vo & Hvo & Heval & Hout).
    exists (NBI.fold_ vo). split; [exact Hvo|]. split.
    + cbn [global_node_cast]. eapply pair_second_mu_l_app_eval; eauto.
      exact (proj1 (valrel_implies_Value Hrel)).
    + change (valrel dir w (ptrec (embed body)) (NBI.fold_ vo) ve).
      eapply valrel_fold_.
      * exact (ValidTy_implies_ValidPTy_embed VA).
      * rewrite embed_sub in Hout.
        replace (beta1 (trec body) >-> embed)
          with (beta1 (ptrec (embed body))) in Hout.
        2:{ extensionality i. destruct i; reflexivity. }
        exact Hout.
Qed.

Lemma mu_r_node_native_action_below radix budget H A body nm
  (child : CastEq ((A, trec body) :: H)
    A body[beta1 (trec body)])
  (fs : Frames H) payload rho :
  ValidTy A -> ValidTy (trec body) ->
  certificate_bundle_native_action radix budget child payload ->
  cast_terms_native_action radix budget rho ->
  native_pair_action_below radix (S budget) A (trec body)
    (global_node_cast (cn_mu_r H A body nm child) payload rho).
Proof.
  intros VA VB Hbundle Hrho.
  pose proof (certificate_root_native_action radix budget child
    payload rho Hbundle Hrho) as Haction.
  assert (Hlmc :
    LMC A + LMC body[beta1 (trec body)] < LMC A + LMC (trec body)).
  { pose proof (LMC_unfold_trec_lt body (proj2 VB)). lia. }
  split; intros dir w vi ve Hmeasure Hrel.
  - destruct (proj1 Haction dir w vi ve
      ltac:(eapply native_measure_smaller_lmc; eauto) Hrel)
      as (vo & Hvo & Heval & Hout).
    exists (NBI.fold_ vo). split; [exact Hvo|]. split.
    + cbn [global_node_cast]. eapply pair_first_mu_r_app_eval; eauto.
      exact (proj1 (valrel_implies_Value Hrel)).
    + change (valrel dir w (ptrec (embed body)) (NBI.fold_ vo) ve).
      eapply valrel_fold_.
      * exact (ValidTy_implies_ValidPTy_embed VB).
      * rewrite embed_sub in Hout.
        replace (beta1 (trec body) >-> embed)
          with (beta1 (ptrec (embed body))) in Hout.
        2:{ extensionality i. destruct i; reflexivity. }
        exact Hout.
  - destruct (valrel_embed_trec_inversion VB Hrel)
      as (inner & -> & Hinner).
    destruct (proj2 Haction dir w inner ve
      ltac:(eapply native_measure_smaller_lmc; eauto) Hinner)
      as (vo & Hvo & Heval & Hout).
    exists vo. split; [exact Hvo|]. split.
    + cbn [global_node_cast]. eapply pair_second_mu_r_app_eval; eauto.
      exact (proj1 (valrel_implies_Value Hinner)).
    + exact Hout.
Qed.

Lemma generated_node_native_action_below radix budget H A B
  (node : CastNode H A B) (fs : Frames H) payload rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
  CastTermsTyping empty ((A, B) :: H) rho ->
  node_lmc_bound node < radix ->
  node_bundle_native_action radix budget node payload ->
  cast_terms_native_action radix budget rho ->
  node_bundle_function_shape node payload ->
  cast_terms_function_shape rho ->
  node_bundle_application_terminates node payload ->
  cast_terms_application_terminates rho ->
  native_pair_action_below radix (S budget) A B
    (global_node_cast node payload rho).
Proof.
  destruct node as
    [H|H|H x
    |H A1 A2 B1 B2 dom cod
    |H A1 A2 B1 B2 fstc sndc
    |H A1 A2 B1 B2 lc rc
    |H body B child
    |H A body nm child];
    intros VH VA VB Hpayload Htyrho Hbound Hbundle Hrho
      Hshape Hrhoshape Hterm Hrhterm; cbn in Hbound, Hbundle, Hshape, Hterm.
  - apply native_identity_pair_action_below.
  - apply native_identity_pair_action_below.
  - apply native_identity_pair_action_below.
  - apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    eapply arrow_node_native_action_below; eauto; lia.
  - apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    eapply product_node_native_action_below; eauto; lia.
  - apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    eapply sum_node_native_action_below; eauto; lia.
  - eapply mu_l_node_native_action_below; eauto.
  - eapply mu_r_node_native_action_below; eauto.
Qed.

Lemma build_bundle_native_action_mut :
  and
  (forall H A B (d : CastEq H A B),
    forall radix budget (fs : Frames H) self rho,
      PairEnvValid H -> ValidTy A -> ValidTy B ->
      certificate_lmc_bound d < radix ->
      StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
      CastTermsTyping empty H rho ->
      certificate_bundle_native_action radix budget d self ->
      cast_terms_native_action radix budget rho ->
      certificate_bundle_function_shape d self ->
      cast_terms_function_shape rho ->
      certificate_bundle_application_terminates d self ->
      cast_terms_application_terminates rho ->
      certificate_bundle_native_action radix (S budget) d
        (build_certificate_bundle d self rho))
  (forall H A B (node : CastNode H A B),
    forall radix budget (fs : Frames H) payload rho,
      PairEnvValid H -> ValidTy A -> ValidTy B ->
      node_lmc_bound node < radix ->
      StlcIso.SpecTyping.Typing empty payload (node_bundle_ty node) ->
      CastTermsTyping empty ((A, B) :: H) rho ->
      node_bundle_native_action radix budget node payload ->
      cast_terms_native_action radix budget rho ->
      node_bundle_function_shape node payload ->
      cast_terms_function_shape rho ->
      node_bundle_application_terminates node payload ->
      cast_terms_application_terminates rho ->
      node_bundle_native_action radix (S budget) node
        (build_node_bundle node payload rho)).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH radix budget fs self rho VH VA VB Hbound
      Hself Htyrho [Hroot Hpayload] Hrho [Hrootshape Hpayloadshape]
      Hrhoshape [Hrootterm Hpayloadterm] Hrhterm.
    assert (Hnodebound : node_lmc_bound node < radix).
    { cbn [certificate_lmc_bound] in Hbound. lia. }
    assert (Hrootty : StlcIso.SpecTyping.Typing empty
      (NBI.proj₁ self) (cast_pair_ty A B))
      by (eapply StlcIso.SpecTyping.WtProj1; exact Hself).
    assert (Hpayloadty : StlcIso.SpecTyping.Typing empty
      (NBI.proj₂ self) (node_bundle_ty node))
      by (eapply StlcIso.SpecTyping.WtProj2; exact Hself).
    assert (Htyrho' : CastTermsTyping empty ((A, B) :: H)
      (@cast_terms_cons H A B (NBI.proj₁ self) rho))
      by now apply cast_terms_typing_cons.
    assert (Hrho' : cast_terms_native_action radix budget
      (@cast_terms_cons H A B (NBI.proj₁ self) rho))
      by now apply cast_terms_native_action_cons.
    assert (Hrhoshape' : cast_terms_function_shape
      (@cast_terms_cons H A B (NBI.proj₁ self) rho))
      by now apply cast_terms_function_shape_cons.
    assert (Hrhterm' : cast_terms_application_terminates
      (@cast_terms_cons H A B (NBI.proj₁ self) rho))
      by now apply cast_terms_application_terminates_cons.
    pose proof (generated_node_native_action_below radix budget H A B node fs
      (NBI.proj₂ self)
      (@cast_terms_cons H A B (NBI.proj₁ self) rho)
      VH VA VB Hpayloadty Htyrho' Hnodebound Hpayload Hrho'
      Hpayloadshape Hrhoshape' Hpayloadterm Hrhterm') as Hglobal.
    pose proof (IH radix budget fs (NBI.proj₂ self)
      (@cast_terms_cons H A B (NBI.proj₁ self) rho)
      VH VA VB Hnodebound Hpayloadty Htyrho' Hpayload Hrho'
      Hpayloadshape Hrhoshape' Hpayloadterm Hrhterm') as Hbuilt.
    cbn. split.
    + eapply native_pair_action_below_antired; [|exact Hglobal].
      apply evalToStar, NBIE.eval_eval₀.
      apply NBIE.eval_proj₁;
        [apply global_node_cast_value|apply build_node_bundle_value].
    + eapply node_bundle_native_action_antired; [|exact Hbuilt].
      apply evalToStar, NBIE.eval_eval₀.
      apply NBIE.eval_proj₂;
        [apply global_node_cast_value|apply build_node_bundle_value].
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget fs payload rho
      VH VA VB Hbound Hpayload Htyrho [Hl Hr] Hrho [Hsl Hsr]
      Hrhoshape [Htl Htr] Hrhterm.
    apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H))
      by (apply pair_env_valid_cons; [now apply ValidTy_arr|
          now apply ValidTy_arr|exact VH]).
    assert (Hlbound : certificate_lmc_bound l < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    assert (Hrbound : certificate_lmc_bound r < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    pose proof (IHl radix budget
      (frames_cons (cn_arr H A1 A2 B1 B2 l r) fs)
      (NBI.proj₁ payload) rho VH' VA1 VB1 Hlbound
      ltac:(eapply StlcIso.SpecTyping.WtProj1; exact Hpayload)
      Htyrho Hl Hrho Hsl Hrhoshape Htl Hrhterm) as Hleft.
    pose proof (IHr radix budget
      (frames_cons (cn_arr H A1 A2 B1 B2 l r) fs)
      (NBI.proj₂ payload) rho VH' VA2 VB2 Hrbound
      ltac:(eapply StlcIso.SpecTyping.WtProj2; exact Hpayload)
      Htyrho Hr Hrho Hsr Hrhoshape Htr Hrhterm) as Hright.
    cbn. split.
    + eapply certificate_bundle_native_action_antired; [|exact Hleft].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_native_action_antired; [|exact Hright].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget fs payload rho
      VH VA VB Hbound Hpayload Htyrho [Hl Hr] Hrho [Hsl Hsr]
      Hrhoshape [Htl Htr] Hrhterm.
    apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H))
      by (apply pair_env_valid_cons; [now apply ValidTy_prod|
          now apply ValidTy_prod|exact VH]).
    assert (Hlbound : certificate_lmc_bound l < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    assert (Hrbound : certificate_lmc_bound r < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    pose proof (IHl radix budget
      (frames_cons (cn_prod H A1 A2 B1 B2 l r) fs)
      (NBI.proj₁ payload) rho VH' VA1 VB1 Hlbound
      ltac:(eapply StlcIso.SpecTyping.WtProj1; exact Hpayload)
      Htyrho Hl Hrho Hsl Hrhoshape Htl Hrhterm) as Hleft.
    pose proof (IHr radix budget
      (frames_cons (cn_prod H A1 A2 B1 B2 l r) fs)
      (NBI.proj₂ payload) rho VH' VA2 VB2 Hrbound
      ltac:(eapply StlcIso.SpecTyping.WtProj2; exact Hpayload)
      Htyrho Hr Hrho Hsr Hrhoshape Htr Hrhterm) as Hright.
    cbn. split.
    + eapply certificate_bundle_native_action_antired; [|exact Hleft].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_native_action_antired; [|exact Hright].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H A1 A2 B1 B2 l IHl r IHr radix budget fs payload rho
      VH VA VB Hbound Hpayload Htyrho [Hl Hr] Hrho [Hsl Hsr]
      Hrhoshape [Htl Htr] Hrhterm.
    apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H))
      by (apply pair_env_valid_cons; [now apply ValidTy_sum|
          now apply ValidTy_sum|exact VH]).
    assert (Hlbound : certificate_lmc_bound l < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    assert (Hrbound : certificate_lmc_bound r < radix)
      by (cbn [node_lmc_bound] in Hbound; lia).
    pose proof (IHl radix budget
      (frames_cons (cn_sum H A1 A2 B1 B2 l r) fs)
      (NBI.proj₁ payload) rho VH' VA1 VB1 Hlbound
      ltac:(eapply StlcIso.SpecTyping.WtProj1; exact Hpayload)
      Htyrho Hl Hrho Hsl Hrhoshape Htl Hrhterm) as Hleft.
    pose proof (IHr radix budget
      (frames_cons (cn_sum H A1 A2 B1 B2 l r) fs)
      (NBI.proj₂ payload) rho VH' VA2 VB2 Hrbound
      ltac:(eapply StlcIso.SpecTyping.WtProj2; exact Hpayload)
      Htyrho Hr Hrho Hsr Hrhoshape Htr Hrhterm) as Hright.
    cbn. split.
    + eapply certificate_bundle_native_action_antired; [|exact Hleft].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₁;
        apply build_certificate_bundle_value.
    + eapply certificate_bundle_native_action_antired; [|exact Hright].
      apply evalToStar, NBIE.eval_eval₀, NBIE.eval_proj₂;
        apply build_certificate_bundle_value.
  - intros H body B child IH radix budget fs payload rho VH VA VB Hbound
      Hpayload Htyrho Hchild Hrho Hshape Hrhoshape Hterm Hrhterm.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((trec body, B) :: H))
      by now apply pair_env_valid_cons.
    cbn in Hbound, Hpayload, Hshape, Hterm |- *.
    exact (IH radix budget (frames_cons (cn_mu_l H body B child) fs)
      payload rho VH' VU VB Hbound Hpayload Htyrho Hchild Hrho
      Hshape Hrhoshape Hterm Hrhterm).
  - intros H A body nm child IH radix budget fs payload rho VH VA VB Hbound
      Hpayload Htyrho Hchild Hrho Hshape Hrhoshape Hterm Hrhterm.
    assert (VU : ValidTy body[beta1 (trec body)])
      by now apply ValidTy_unfold_trec.
    assert (VH' : PairEnvValid ((A, trec body) :: H))
      by now apply pair_env_valid_cons.
    cbn in Hbound, Hpayload, Hshape, Hterm |- *.
    exact (IH radix budget (frames_cons (cn_mu_r H A body nm child) fs)
      payload rho VH' VA VU Hbound Hpayload Htyrho Hchild Hrho
      Hshape Hrhoshape Hterm Hrhterm).
Qed.

Lemma build_certificate_bundle_native_action radix budget
  {H A B} (d : CastEq H A B) (fs : Frames H) self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  certificate_lmc_bound d < radix ->
  StlcIso.SpecTyping.Typing empty self (certificate_bundle_ty d) ->
  CastTermsTyping empty H rho ->
  certificate_bundle_native_action radix budget d self ->
  cast_terms_native_action radix budget rho ->
  certificate_bundle_function_shape d self ->
  cast_terms_function_shape rho ->
  certificate_bundle_application_terminates d self ->
  cast_terms_application_terminates rho ->
  certificate_bundle_native_action radix (S budget) d
    (build_certificate_bundle d self rho).
Proof.
  exact ((proj1 build_bundle_native_action_mut)
    H A B d radix budget fs self rho).
Qed.

Lemma cast_pair_application_terminates_antired A B p p' :
  NBIE.evalStar p p' ->
  cast_pair_application_terminates A B p' ->
  cast_pair_application_terminates A B p.
Proof.
  intros Heval [Hup Hdown]. split; intros vi Hvi Hty.
  - eapply StlcIso.LemmasEvaluation.termination_closed_under_antireductionStar.
    + exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.papp₁ NBI.phole vi) I
        (StlcIso.LemmasEvaluation.evalstar_ctx
          (NBI.pproj₁ NBI.phole) I Heval)).
    + exact (Hup vi Hvi Hty).
  - eapply StlcIso.LemmasEvaluation.termination_closed_under_antireductionStar.
    + exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.papp₁ NBI.phole vi) I
        (StlcIso.LemmasEvaluation.evalstar_ctx
          (NBI.pproj₂ NBI.phole) I Heval)).
    + exact (Hdown vi Hvi Hty).
Qed.

Lemma bundle_application_terminates_antired_mut :
  and
  (forall H A B (d : CastEq H A B), forall self self',
    NBIE.evalStar self self' ->
    certificate_bundle_application_terminates d self' ->
    certificate_bundle_application_terminates d self)
  (forall H A B (node : CastNode H A B), forall payload payload',
    NBIE.evalStar payload payload' ->
    node_bundle_application_terminates node payload' ->
    node_bundle_application_terminates node payload).
Proof.
  apply BundleCastEq_CastNode_ind_mut.
  - intros. exact I.
  - intros H A B node IH self self' Heval [Hroot Hpayload]. cbn. split.
    + eapply cast_pair_application_terminates_antired; [|exact Hroot].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IH; [|exact Hpayload].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
  - intros H A1 A2 B1 B2 l IHl r IHr payload payload' Heval [Hl Hr].
    cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr payload payload' Heval [Hl Hr].
    cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H A1 A2 B1 B2 l IHl r IHr payload payload' Heval [Hl Hr].
    cbn. split.
    + eapply IHl; [|exact Hl].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₁ NBI.phole) I Heval).
    + eapply IHr; [|exact Hr].
      exact (StlcIso.LemmasEvaluation.evalstar_ctx
        (NBI.pproj₂ NBI.phole) I Heval).
  - intros H body B child IH payload payload' Heval Hterm.
    cbn. eapply IH; [exact Heval|exact Hterm].
  - intros H A body nm child IH payload payload' Heval Hterm.
    cbn. eapply IH; [exact Heval|exact Hterm].
Qed.

Lemma certificate_bundle_application_terminates_antired {H A B}
  (d : CastEq H A B) self self' :
  NBIE.evalStar self self' ->
  certificate_bundle_application_terminates d self' ->
  certificate_bundle_application_terminates d self.
Proof.
  exact ((proj1 bundle_application_terminates_antired_mut)
    H A B d self self').
Qed.

Theorem recursive_certificate_bundle_native_action_all_budgets
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall budget,
    certificate_bundle_native_action
      (S (certificate_lmc_bound d)) budget d
      (recursive_certificate_bundle d).
Proof.
  intros VA VB budget. induction budget as [|budget IH].
  - apply certificate_bundle_native_action_below_zero.
  - assert (Hdelayedaction : certificate_bundle_native_action
      (S (certificate_lmc_bound d)) budget d
      (delayed_recursive_certificate_bundle d)).
    { eapply certificate_bundle_native_action_antired; [|exact IH].
      apply evalToStar. now apply delayed_recursive_certificate_bundle_step. }
    assert (Hrecshape : certificate_bundle_function_shape d
      (recursive_certificate_bundle d))
      by now apply recursive_certificate_bundle_function_shape.
    assert (Hdelayedshape : certificate_bundle_function_shape d
      (delayed_recursive_certificate_bundle d)).
    { eapply certificate_bundle_function_shape_antired; [|exact Hrecshape].
      apply evalToStar. now apply delayed_recursive_certificate_bundle_step. }
    assert (Hrecterm : certificate_bundle_application_terminates d
      (recursive_certificate_bundle d))
      by now apply recursive_certificate_bundle_application_terminates.
    assert (Hdelayedterm : certificate_bundle_application_terminates d
      (delayed_recursive_certificate_bundle d)).
    { eapply certificate_bundle_application_terminates_antired;
        [|exact Hrecterm].
      apply evalToStar. now apply delayed_recursive_certificate_bundle_step. }
    assert (Hbuild : certificate_bundle_native_action
      (S (certificate_lmc_bound d)) (S budget) d
      (build_certificate_bundle d
        (delayed_recursive_certificate_bundle d) cast_terms_nil)).
    { eapply (build_certificate_bundle_native_action
        (S (certificate_lmc_bound d)) budget d frames_nil
        (delayed_recursive_certificate_bundle d) cast_terms_nil).
      - apply pair_env_valid_nil.
      - exact VA.
      - exact VB.
      - lia.
      - now apply delayed_recursive_certificate_bundle_typing.
      - apply cast_terms_typing_nil.
      - exact Hdelayedaction.
      - apply cast_terms_native_action_nil.
      - exact Hdelayedshape.
      - apply cast_terms_function_shape_nil.
      - exact Hdelayedterm.
      - apply cast_terms_application_terminates_nil. }
    eapply certificate_bundle_native_action_antired; [|exact Hbuild].
    now apply recursive_certificate_bundle_unfolds.
Qed.

Theorem tied_certificate_bundle_native_action_all_budgets
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall budget,
    certificate_bundle_native_action
      (S (certificate_lmc_bound d)) budget d
      (tied_certificate_bundle d).
Proof.
  intros VA VB budget.
  eapply certificate_bundle_native_action_antired.
  - apply evalToStar, tied_certificate_bundle_step.
  - now apply recursive_certificate_bundle_native_action_all_budgets.
Qed.

Corollary compile_global_pair_native_action_all_budgets
  {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall budget,
    native_pair_action_below
      (S (certificate_lmc_bound d)) budget A B
      (compile_global_pair d).
Proof.
  intros VA VB budget. unfold compile_global_pair.
  eapply certificate_root_native_action.
  - now apply tied_certificate_bundle_native_action_all_budgets.
  - apply cast_terms_native_action_nil.
Qed.

Corollary compile_global_pair_native_action {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir w vi ve,
    valrel dir w (embed A) vi ve ->
    exists vo,
      NBIE.Value vo /\
      NBIE.evalStar (NBI.app (compile_global_up d) vi) vo /\
      valrel dir w (embed B) vo ve.
Proof.
  intros VA VB dir w vi ve Hrel.
  pose (radix := S (certificate_lmc_bound d)).
  pose (budget := S (native_semantic_measure radix A B w)).
  pose proof (compile_global_pair_native_action_all_budgets d VA VB budget)
    as Haction.
  assert (Hmeasure : native_semantic_measure
    (S (certificate_lmc_bound d)) A B w < budget).
  { unfold budget, radix. lia. }
  exact (proj1 Haction dir w vi ve Hmeasure Hrel).
Qed.

Corollary compile_global_pair_native_reverse_action {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir w vi ve,
    valrel dir w (embed B) vi ve ->
    exists vo,
      NBIE.Value vo /\
      NBIE.evalStar (NBI.app (compile_global_down d) vi) vo /\
      valrel dir w (embed A) vo ve.
Proof.
  intros VA VB dir w vi ve Hrel.
  pose (radix := S (certificate_lmc_bound d)).
  pose (budget := S (native_semantic_measure radix A B w)).
  pose proof (compile_global_pair_native_action_all_budgets d VA VB budget)
    as Haction.
  assert (Hmeasure : native_semantic_measure
    (S (certificate_lmc_bound d)) A B w < budget).
  { unfold budget, radix. lia. }
  exact (proj2 Haction dir w vi ve Hmeasure Hrel).
Qed.

(** The generated coercions also act directly on computations, not just on
    values.  This is the strict-CBV form needed at a source conversion: the
    source computation remains the application argument and is not delayed
    by an eta expansion. *)
Corollary compile_global_up_native_termrel {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir w ti te,
    termrel dir w (embed A) ti te ->
    termrel dir w (embed B) (NBI.app (compile_global_up d) ti) te.
Proof.
  intros VA VB dir w ti te Hrel.
  pose (radix := S (certificate_lmc_bound d)).
  pose (budget := S (native_semantic_measure radix A B w)).
  eapply native_forward_action_map_term.
  - now apply compile_global_pair_function_shape.
  - exact (compile_global_pair_native_action_all_budgets d VA VB budget).
  - intros w' Hw'. unfold budget, radix, native_semantic_measure. nia.
  - exact Hrel.
Qed.

Corollary compile_global_down_native_termrel {A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  forall dir w ti te,
    termrel dir w (embed B) ti te ->
    termrel dir w (embed A) (NBI.app (compile_global_down d) ti) te.
Proof.
  intros VA VB dir w ti te Hrel.
  pose (radix := S (certificate_lmc_bound d)).
  pose (budget := S (native_semantic_measure radix A B w)).
  eapply native_reverse_action_map_term.
  - now apply compile_global_pair_function_shape.
  - exact (compile_global_pair_native_action_all_budgets d VA VB budget).
  - intros w' Hw'. unfold budget, radix, native_semantic_measure. nia.
  - exact Hrel.
Qed.
