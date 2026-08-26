Require Import ExactBacktranslation.CertificateIndexed.
From Stdlib Require Import Arith.PeanoNat Lia Lists.List Logic.Eqdep_dec.
Import ListNotations.

(** Height is a proof property, not execution fuel in a generated cast.  It is
    useful for proving that the deterministic search can replay every finite
    cyclic certificate. *)
Fixpoint casteq_height {H A B} (d : CastEq H A B) : nat :=
  match d with
  | ce_back _ => 0
  | ce_step node => S (castnode_height node)
  end
with castnode_height {H A B} (node : CastNode H A B) : nat :=
  match node with
  | cn_unit _ | cn_bool _ | cn_var _ _ => 0
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => Nat.max (casteq_height l) (casteq_height r)
  | cn_mu_l _ _ _ child => casteq_height child
  | cn_mu_r _ _ _ _ child => casteq_height child
  end.

Lemma assumed_find_complete {H A B} (m : Assumed H A B) :
  exists m', assumed_find H A B = Some m'.
Proof.
  induction m as [H A B|H A B C D m IH]; cbn.
  - destruct (ty_eq_dec A A) as [HAA|Hneq]; [|contradiction].
    destruct (ty_eq_dec B B) as [HBB|Hneq]; [|contradiction].
    replace HAA with (eq_refl A) by (apply UIP_dec; exact ty_eq_dec).
    replace HBB with (eq_refl B) by (apply UIP_dec; exact ty_eq_dec).
    eexists; reflexivity.
  - destruct (ty_eq_dec A C) as [HAC|HAC].
    + destruct HAC. destruct (ty_eq_dec B D) as [HBD|HBD].
      * destruct HBD. eexists; reflexivity.
      * destruct IH as [m' Hm']. rewrite Hm'.
        eexists; reflexivity.
    + destruct IH as [m' Hm']. rewrite Hm'.
      eexists; reflexivity.
Qed.

Definition SearchComplete {H A B} (d : CastEq H A B) : Prop :=
  forall fuel, casteq_height d <= fuel ->
    exists d', search_casteq_bounded fuel H A B = Some d'.

Definition NodeSearchComplete {H A B} (node : CastNode H A B) : Prop :=
  forall fuel, castnode_height node <= fuel ->
    exists d', search_casteq_bounded (S fuel) H A B = Some d'.

Scheme CastEq_ind_mut := Induction for CastEq Sort Prop
with CastNode_ind_mut := Induction for CastNode Sort Prop.
Combined Scheme CastEq_CastNode_ind_mut
  from CastEq_ind_mut, CastNode_ind_mut.

Lemma search_casteq_bounded_complete_mut :
  (forall H A B (d : CastEq H A B), SearchComplete d) /\
  (forall H A B (node : CastNode H A B), NodeSearchComplete node).
Proof.
  apply CastEq_CastNode_ind_mut with
    (P := fun H A B d => SearchComplete d)
    (P0 := fun H A B node => NodeSearchComplete node).
  - intros H A B m fuel Hfuel.
    destruct (assumed_find_complete m) as [m' Hm'].
    destruct fuel; cbn; rewrite Hm'; eauto.
  - intros H A B node IH fuel Hfuel.
    destruct fuel as [|fuel]; [cbn in Hfuel; lia|].
    apply IH. cbn in Hfuel. lia.
  - intros H fuel Hfuel. cbn.
    destruct (assumed_find H tunit tunit); eauto.
  - intros H fuel Hfuel. cbn.
    destruct (assumed_find H tbool tbool); eauto.
  - intros H x fuel Hfuel. cbn.
    destruct (assumed_find H (tvar x) (tvar x)); eauto.
    destruct (PeanoNat.Nat.eq_dec x x) as [Hxx|Hneq]; [|contradiction].
    replace Hxx with (eq_refl x)
      by (apply UIP_dec; exact PeanoNat.Nat.eq_dec).
    eexists; reflexivity.
  - intros H A1 A2 B1 B2 l IHl r IHr fuel Hfuel. cbn in *.
    destruct (assumed_find H (tarr A1 A2) (tarr B1 B2)); eauto.
    destruct (IHl fuel) as [l' Hl]; [lia|].
    destruct (IHr fuel) as [r' Hr]; [lia|].
    rewrite Hl, Hr. eexists; reflexivity.
  - intros H A1 A2 B1 B2 l IHl r IHr fuel Hfuel. cbn in *.
    destruct (assumed_find H (tprod A1 A2) (tprod B1 B2)); eauto.
    destruct (IHl fuel) as [l' Hl]; [lia|].
    destruct (IHr fuel) as [r' Hr]; [lia|].
    rewrite Hl, Hr. eexists; reflexivity.
  - intros H A1 A2 B1 B2 l IHl r IHr fuel Hfuel. cbn in *.
    destruct (assumed_find H (tsum A1 A2) (tsum B1 B2)); eauto.
    destruct (IHl fuel) as [l' Hl]; [lia|].
    destruct (IHr fuel) as [r' Hr]; [lia|].
    rewrite Hl, Hr. eexists; reflexivity.
  - intros H body B child IH fuel Hfuel. cbn in *.
    destruct (assumed_find H (trec body) B); eauto.
    destruct (IH fuel) as [child' Hchild]; [lia|].
    rewrite Hchild. eexists; reflexivity.
  - intros H A body nm child IH fuel Hfuel.
    destruct nm; cbn in *.
    all: match goal with
         | |- context [assumed_find ?H0 ?A0 ?B0] =>
             destruct (assumed_find H0 A0 B0);
             [eexists; reflexivity|]
         end.
    all: destruct (IH fuel) as [child' Hchild]; [lia|].
    all: rewrite Hchild; eexists; reflexivity.
Qed.

Theorem search_casteq_bounded_complete {H A B} (d : CastEq H A B) fuel :
  casteq_height d <= fuel ->
  exists d', search_casteq_bounded fuel H A B = Some d'.
Proof.
  exact ((proj1 search_casteq_bounded_complete_mut) H A B d fuel).
Qed.

Corollary search_closed_bounded_certificate_complete {A B}
  (d : ClosedCastEq A B) :
  exists found,
    search_closed_bounded (casteq_height d) A B = Some found.
Proof.
  apply search_casteq_bounded_complete with (d := d). lia.
Qed.
