Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.SearchCompleteness.
Require Import RecTypes.ValidTy.
Require Import RecTypes.LemmasTypes.
Require Import Db.Lemmas.
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Wf_nat Lia.
Import ListNotations.

(** A finite closure presentation of a recursive type.  [env] contains the
    closed recursive types denoted by the de Bruijn variables whose binders
    have been crossed. *)
Fixpoint closure_lookup (env : list Ty) (i : nat) : Ty :=
  match env, i with
  | [], i0 => tvar i0
  | A :: _, 0 => A
  | _ :: env0, S i0 => closure_lookup env0 i0
  end.

Lemma closure_lookup_nth_error env i A :
  nth_error env i = Some A -> closure_lookup env i = A.
Proof.
  revert i. induction env as [|B env IH]; intros [|i] H; cbn in *;
    try discriminate; eauto.
  now inversion H.
Qed.

Definition instantiate_ty (env : list Ty) (A : Ty) : Ty :=
  A[closure_lookup env].

Fixpoint ty_closures (env : list Ty) (A : Ty) : list Ty :=
  instantiate_ty env A ::
  match A with
  | tarr A1 A2 | tprod A1 A2 | tsum A1 A2 =>
      ty_closures env A1 ++ ty_closures env A2
  | trec body =>
      ty_closures (instantiate_ty env (trec body) :: env) body
  | _ => []
  end.

Definition closed_ty_closures (A : Ty) : list Ty :=
  nodup ty_eq_dec (ty_closures nil A).

Lemma instantiate_ty_nil A : instantiate_ty nil A = A.
Proof.
  unfold instantiate_ty.
  replace (closure_lookup nil) with (idm Ty).
  - now apply ap_id.
  - extensionality i. reflexivity.
Qed.

Lemma closure_lookup_cons_comp env self :
  (up (closure_lookup env) >=> beta1 self) =
  closure_lookup (self :: env).
Proof.
  extensionality i. destruct i; cbn.
  - reflexivity.
  - rewrite <- ap_liftSub, liftSub_wkm.
    now apply apply_wkm_beta1_cancel.
Qed.

Lemma instantiate_ty_unfold env body :
  instantiate_ty env (trec body) = trec (body[up (closure_lookup env)]) /\
  (body[up (closure_lookup env)])[beta1 (instantiate_ty env (trec body))] =
    instantiate_ty (instantiate_ty env (trec body) :: env) body.
Proof.
  split; [reflexivity|].
  unfold instantiate_ty. rewrite ap_comp.
  now rewrite closure_lookup_cons_comp.
Qed.

Inductive TyChild : Ty -> Ty -> Prop :=
| child_arr_l A B : TyChild (tarr A B) A
| child_arr_r A B : TyChild (tarr A B) B
| child_prod_l A B : TyChild (tprod A B) A
| child_prod_r A B : TyChild (tprod A B) B
| child_sum_l A B : TyChild (tsum A B) A
| child_sum_r A B : TyChild (tsum A B) B
| child_rec body : TyChild (trec body) body[beta1 (trec body)].

Definition ChildrenIn (ambient : list Ty) (A : Ty) : Prop :=
  forall B, TyChild A B -> In B ambient.

Lemma ty_closures_instantiate_here env A :
  In (instantiate_ty env A) (ty_closures env A).
Proof. destruct A; cbn; now left. Qed.

(** Every state exposed by one structural/unfolding step is another member
    of the same finite closure.  The environment hypothesis accounts for a
    variable that jumps back to an enclosing recursive state. *)
Lemma ty_closures_children_aux env A ambient :
  incl (ty_closures env A) ambient ->
  Forall (ChildrenIn ambient) env ->
  forall X, In X (ty_closures env A) -> ChildrenIn ambient X.
Proof.
  revert env ambient.
  induction A; intros env ambient Hsub Henv X HX; cbn in HX.
  all: destruct HX as [<-|HX].
  - cbn [instantiate_ty]. intros Y HY. inversion HY; subst.
    + apply Hsub. cbn. apply in_cons. apply in_or_app. left.
      apply ty_closures_instantiate_here.
    + apply Hsub. cbn. apply in_cons. apply in_or_app. right.
      apply ty_closures_instantiate_here.
  - apply in_app_iff in HX as [HX|HX].
    + eapply IHA1; [|exact Henv|exact HX].
      intros Z HZ. apply Hsub. cbn. apply in_cons, in_or_app. now left.
    + eapply IHA2; [|exact Henv|exact HX].
      intros Z HZ. apply Hsub. cbn. apply in_cons, in_or_app. now right.
  - cbn [instantiate_ty]. intros Y HY. inversion HY.
  - contradiction.
  - cbn [instantiate_ty]. intros Y HY. inversion HY.
  - contradiction.
  - cbn [instantiate_ty]. intros Y HY. inversion HY; subst.
    + apply Hsub. cbn. apply in_cons. apply in_or_app. left.
      apply ty_closures_instantiate_here.
    + apply Hsub. cbn. apply in_cons. apply in_or_app. right.
      apply ty_closures_instantiate_here.
  - apply in_app_iff in HX as [HX|HX].
    + eapply IHA1; [|exact Henv|exact HX].
      intros Z HZ. apply Hsub. cbn. apply in_cons, in_or_app. now left.
    + eapply IHA2; [|exact Henv|exact HX].
      intros Z HZ. apply Hsub. cbn. apply in_cons, in_or_app. now right.
  - cbn [instantiate_ty]. intros Y HY. inversion HY; subst.
    + apply Hsub. cbn. apply in_cons. apply in_or_app. left.
      apply ty_closures_instantiate_here.
    + apply Hsub. cbn. apply in_cons. apply in_or_app. right.
      apply ty_closures_instantiate_here.
  - apply in_app_iff in HX as [HX|HX].
    + eapply IHA1; [|exact Henv|exact HX].
      intros Z HZ. apply Hsub. cbn. apply in_cons, in_or_app. now left.
    + eapply IHA2; [|exact Henv|exact HX].
      intros Z HZ. apply Hsub. cbn. apply in_cons, in_or_app. now right.
  - intros Y HY. inversion HY; subst.
    destruct (instantiate_ty_unfold env A) as [Hrec Hunfold].
    change (In
      ((A[up (closure_lookup env)])[beta1 (instantiate_ty env (trec A))])
      ambient).
    rewrite Hunfold.
    apply Hsub. cbn. apply in_cons. apply ty_closures_instantiate_here.
  - eapply IHA; [| |exact HX].
    + intros Z HZ. apply Hsub. cbn. now apply in_cons.
    + constructor; [|exact Henv].
      intros Y HY. inversion HY; subst.
      destruct (instantiate_ty_unfold env A) as [Hrec Hunfold].
      change (In
        ((A[up (closure_lookup env)])[beta1 (instantiate_ty env (trec A))])
        ambient).
      rewrite Hunfold.
      apply Hsub. cbn. apply in_cons. apply ty_closures_instantiate_here.
  - cbn [instantiate_ty].
    destruct (nth_error env i) eqn:Hnth.
    + assert (Hin : In t env) by now apply nth_error_In in Hnth.
      rewrite Forall_forall in Henv.
      rewrite (closure_lookup_nth_error env i t Hnth). exact (Henv t Hin).
    + intros Y HY.
      assert (closure_lookup env i = tvar (i - length env)).
      { clear Hsub Henv Y HY.
        revert i Hnth. induction env as [|Z env IH]; intros i Hnth; cbn.
        - now rewrite Nat.sub_0_r.
        - destruct i; [discriminate|].
          cbn in Hnth. now rewrite (IH i Hnth). }
      rewrite H in HY. inversion HY.
  - contradiction.
Qed.

Theorem closed_ty_closures_children A X :
  In X (closed_ty_closures A) -> ChildrenIn (closed_ty_closures A) X.
Proof.
  unfold closed_ty_closures.
  rewrite nodup_In. intros HX.
  eapply ty_closures_children_aux.
  - intros Z HZ. apply nodup_In. exact HZ.
  - constructor.
  - exact HX.
Qed.

Definition pair_ty_eq_dec (p q : Ty * Ty) : {p = q} + {p <> q}.
Proof. decide equality; apply ty_eq_dec. Defined.

Definition closure_pairs (A B : Ty) : list (Ty * Ty) :=
  flat_map (fun X => map (fun Y => (X, Y)) (closed_ty_closures B))
    (closed_ty_closures A).

Definition closure_pair_set (A B : Ty) : list (Ty * Ty) :=
  nodup pair_ty_eq_dec (closure_pairs A B).

Lemma closure_pairs_intro A B X Y :
  In X (closed_ty_closures A) ->
  In Y (closed_ty_closures B) ->
  In (X, Y) (closure_pair_set A B).
Proof.
  intros HX HY. unfold closure_pair_set. rewrite nodup_In.
  unfold closure_pairs. apply in_flat_map.
  exists X. split; [exact HX|].
  now apply in_map.
Qed.

Definition casteq_decision_fuel (A B : Ty) : nat :=
  S (length (closure_pair_set A B)).

Definition decide_casteq (A B : Ty) : option (ClosedCastEq A B) :=
  search_closed_bounded (casteq_decision_fuel A B) A B.

Theorem decide_casteq_sound A B d :
  decide_casteq A B = Some d -> Tyeq A B.
Proof. intros _. now apply casteq_sound. Qed.

(** Deterministic head view of coinductive equality.  When the left endpoint
    is recursive we unfold it first, exactly as [search_casteq_bounded] does. *)
Inductive TyeqNode : Ty -> Ty -> Prop :=
| ten_unit : TyeqNode tunit tunit
| ten_bool : TyeqNode tbool tbool
| ten_var x : TyeqNode (tvar x) (tvar x)
| ten_arr A1 A2 B1 B2 :
    Tyeq A1 B1 -> Tyeq A2 B2 ->
    TyeqNode (tarr A1 A2) (tarr B1 B2)
| ten_prod A1 A2 B1 B2 :
    Tyeq A1 B1 -> Tyeq A2 B2 ->
    TyeqNode (tprod A1 A2) (tprod B1 B2)
| ten_sum A1 A2 B1 B2 :
    Tyeq A1 B1 -> Tyeq A2 B2 ->
    TyeqNode (tsum A1 A2) (tsum B1 B2)
| ten_mu_l body B :
    Tyeq body[beta1 (trec body)] B ->
    TyeqNode (trec body) B
| ten_mu_r A body :
    NotMu A -> Tyeq A body[beta1 (trec body)] ->
    TyeqNode A (trec body).

Lemma valid_trec_body_contr body :
  ValidTy (trec body) -> SimpleContr body.
Proof.
  intros V. destruct V as [_ VC]. inversion VC. assumption.
Qed.

Lemma tyeq_unfold_left body B :
  ValidTy (trec body) ->
  Tyeq (trec body) B ->
  Tyeq body[beta1 (trec body)] B.
Proof.
  intros VA HE.
  refine (@eq_trans_contr body[beta1 (trec body)]
    (trec body) B _ _ _).
  - exact (ValidTy_SimpleContr VA).
  - apply ty_eq_unfoldrec. now apply valid_trec_body_contr.
  - exact HE.
Qed.

Lemma tyeq_node_of_valid {A B} :
  ValidTy A -> ValidTy B -> Tyeq A B -> TyeqNode A B.
Proof.
  intros VA VB HE.
  destruct A as [A1 A2| | |A1 A2|A1 A2|body|i].
  - destruct B; inversion HE; subst.
    + now apply ten_arr.
    + apply ten_mu_r; [constructor|assumption].
  - destruct B; inversion HE; subst.
    + constructor.
    + apply ten_mu_r; [constructor|assumption].
  - destruct B; inversion HE; subst.
    + constructor.
    + apply ten_mu_r; [constructor|assumption].
  - destruct B; inversion HE; subst.
    + now apply ten_prod.
    + apply ten_mu_r; [constructor|assumption].
  - destruct B; inversion HE; subst.
    + now apply ten_sum.
    + apply ten_mu_r; [constructor|assumption].
  - apply ten_mu_l. now apply tyeq_unfold_left.
  - destruct B; inversion HE; subst.
    + apply ten_mu_r; [constructor|assumption].
    + apply ten_var.
Qed.

Lemma valid_ty_child {A B} : ValidTy A -> TyChild A B -> ValidTy B.
Proof.
  intros VA HC. inversion HC; subst;
    eauto using ValidTy_unfold_trec.
  - exact (proj1 (ValidTy_invert_arr VA)).
  - exact (proj2 (ValidTy_invert_arr VA)).
  - exact (proj1 (ValidTy_invert_prod VA)).
  - exact (proj2 (ValidTy_invert_prod VA)).
  - exact (proj1 (ValidTy_invert_sum VA)).
  - exact (proj2 (ValidTy_invert_sum VA)).
Qed.

Lemma assumed_find_in_complete {H A B} :
  In (A, B) H -> exists m, assumed_find H A B = Some m.
Proof.
  induction H as [|[C D] H IH]; cbn; intros Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst.
      destruct (ty_eq_dec A A) as [HAA|HAA]; [|contradiction].
      destruct (ty_eq_dec B B) as [HBB|HBB]; [|contradiction].
      replace HAA with (eq_refl A)
        by (apply Eqdep_dec.UIP_dec; exact ty_eq_dec).
      replace HBB with (eq_refl B)
        by (apply Eqdep_dec.UIP_dec; exact ty_eq_dec).
      eexists; reflexivity.
    + destruct (ty_eq_dec A C) as [HAC|HAC].
      * subst C. destruct (ty_eq_dec B D) as [HBD|HBD].
        -- destruct HBD. eexists; reflexivity.
        -- destruct (IH Hin) as [m Hm]. rewrite Hm.
           eexists; reflexivity.
      * destruct (IH Hin) as [m Hm]. rewrite Hm.
        eexists; reflexivity.
Qed.

Lemma assumed_find_none_not_in {H A B} :
  assumed_find H A B = None -> ~ In (A, B) H.
Proof.
  intros Hnone Hin.
  destruct (assumed_find_in_complete Hin) as [m Hsome].
  congruence.
Qed.

Lemma closure_pair_set_nodup A B : NoDup (closure_pair_set A B).
Proof. unfold closure_pair_set. apply NoDup_nodup. Qed.

Section FiniteSearchCompleteness.

Variables RootA RootB : Ty.

Let LA := closed_ty_closures RootA.
Let LB := closed_ty_closures RootB.
Let U := closure_pair_set RootA RootB.

(** The induction measure is the number of as-yet unseen pairs in the finite
    product closure.  It is proof fuel only: generated casts contain no fuel
    and execute through the fixed-point bundle. *)
Lemma search_casteq_finite_complete :
  forall remaining H A B fuel,
    NoDup H ->
    incl H U ->
    In A LA ->
    In B LB ->
    ValidTy A ->
    ValidTy B ->
    Tyeq A B ->
    remaining = length U - length H ->
    S remaining <= fuel ->
    exists d, search_casteq_bounded fuel H A B = Some d.
Proof.
  induction remaining as [remaining IH] using lt_wf_ind.
  intros H A B fuel Hnodup Hsub HA HB VA VB HE Hremaining Hfuel.
  destruct (assumed_find H A B) as [back|] eqn:Hfind.
  - exists (ce_back back).
    destruct fuel; cbn [search_casteq_bounded]; now rewrite Hfind.
  - assert (Hnotin : ~ In (A, B) H).
    { now apply assumed_find_none_not_in. }
    assert (Hpair : In (A, B) U).
    { apply closure_pairs_intro; assumption. }
    assert (Hlength : length H < length U).
    { pose proof (NoDup_incl_length Hnodup Hsub) as Hle.
      destruct (Nat.lt_ge_cases (length H) (length U)) as [Hlt|Hge];
        [exact Hlt|].
      exfalso. apply Hnotin.
      eapply NoDup_length_incl; eauto. }
    assert (Hnext_nodup : NoDup ((A, B) :: H)).
    { now constructor. }
    assert (Hnext_sub : incl ((A, B) :: H) U).
    { intros p Hp. destruct Hp as [Hp|Hp].
      - now subst p.
      - now apply Hsub. }
    assert (HAchildren : ChildrenIn LA A).
    { now apply closed_ty_closures_children. }
    assert (HBchildren : ChildrenIn LB B).
    { now apply closed_ty_closures_children. }
    destruct fuel as [|fuel]; [lia|].
    assert (Hrecur :
      forall A' B',
        In A' LA -> In B' LB ->
        ValidTy A' -> ValidTy B' -> Tyeq A' B' ->
        exists d,
          search_casteq_bounded fuel ((A, B) :: H) A' B' = Some d).
    { intros A' B' HA' HB' VA' VB' HE'.
      eapply (IH (length U - length ((A, B) :: H))).
      - cbn. lia.
      - exact Hnext_nodup.
      - exact Hnext_sub.
      - exact HA'.
      - exact HB'.
      - exact VA'.
      - exact VB'.
      - exact HE'.
      - reflexivity.
      - cbn in *. lia. }
    pose proof (tyeq_node_of_valid VA VB HE) as Hnode.
    destruct Hnode.
    + cbn [search_casteq_bounded]. rewrite Hfind.
      eexists; reflexivity.
    + cbn [search_casteq_bounded]. rewrite Hfind.
      eexists; reflexivity.
    + cbn [search_casteq_bounded]. rewrite Hfind.
      destruct (PeanoNat.Nat.eq_dec x x) as [Hxx|Hxx];
        [|contradiction].
      replace Hxx with (eq_refl x)
        by (apply Eqdep_dec.UIP_dec; exact PeanoNat.Nat.eq_dec).
      eexists; reflexivity.
    + destruct (Hrecur A1 B1
        (HAchildren A1 (child_arr_l A1 A2))
        (HBchildren B1 (child_arr_l B1 B2))
        (valid_ty_child VA (child_arr_l A1 A2))
        (valid_ty_child VB (child_arr_l B1 B2)) H0) as [l Hl].
      destruct (Hrecur A2 B2
        (HAchildren A2 (child_arr_r A1 A2))
        (HBchildren B2 (child_arr_r B1 B2))
        (valid_ty_child VA (child_arr_r A1 A2))
        (valid_ty_child VB (child_arr_r B1 B2)) H1) as [r Hr].
      cbn [search_casteq_bounded]. rewrite Hfind, Hl, Hr.
      eexists; reflexivity.
    + destruct (Hrecur A1 B1
        (HAchildren A1 (child_prod_l A1 A2))
        (HBchildren B1 (child_prod_l B1 B2))
        (valid_ty_child VA (child_prod_l A1 A2))
        (valid_ty_child VB (child_prod_l B1 B2)) H0) as [l Hl].
      destruct (Hrecur A2 B2
        (HAchildren A2 (child_prod_r A1 A2))
        (HBchildren B2 (child_prod_r B1 B2))
        (valid_ty_child VA (child_prod_r A1 A2))
        (valid_ty_child VB (child_prod_r B1 B2)) H1) as [r Hr].
      cbn [search_casteq_bounded]. rewrite Hfind, Hl, Hr.
      eexists; reflexivity.
    + destruct (Hrecur A1 B1
        (HAchildren A1 (child_sum_l A1 A2))
        (HBchildren B1 (child_sum_l B1 B2))
        (valid_ty_child VA (child_sum_l A1 A2))
        (valid_ty_child VB (child_sum_l B1 B2)) H0) as [l Hl].
      destruct (Hrecur A2 B2
        (HAchildren A2 (child_sum_r A1 A2))
        (HBchildren B2 (child_sum_r B1 B2))
        (valid_ty_child VA (child_sum_r A1 A2))
        (valid_ty_child VB (child_sum_r B1 B2)) H1) as [r Hr].
      cbn [search_casteq_bounded]. rewrite Hfind, Hl, Hr.
      eexists; reflexivity.
    + destruct (Hrecur body[beta1 (trec body)] B
        (HAchildren _ (child_rec body)) HB
        (valid_ty_child VA (child_rec body)) VB H0) as [child Hchild].
      cbn [search_casteq_bounded]. rewrite Hfind, Hchild.
      eexists; reflexivity.
    + destruct (Hrecur A body[beta1 (trec body)]
        HA (HBchildren _ (child_rec body))
        VA (valid_ty_child VB (child_rec body)) H1) as [child Hchild].
      destruct H0; cbn [search_casteq_bounded] in *;
        rewrite Hfind, Hchild; eexists; reflexivity.
Qed.

End FiniteSearchCompleteness.

Theorem decide_casteq_complete A B :
  ValidTy A -> ValidTy B -> Tyeq A B ->
  exists d, decide_casteq A B = Some d.
Proof.
  intros VA VB HE.
  unfold decide_casteq, search_closed_bounded, casteq_decision_fuel.
  eapply (search_casteq_finite_complete A B
    (length (closure_pair_set A B)) nil A B).
  - constructor.
  - intros p Hp. contradiction.
  - unfold closed_ty_closures. rewrite nodup_In.
    pose proof (ty_closures_instantiate_here nil A) as HA.
    now rewrite instantiate_ty_nil in HA.
  - unfold closed_ty_closures. rewrite nodup_In.
    pose proof (ty_closures_instantiate_here nil B) as HB.
    now rewrite instantiate_ty_nil in HB.
  - exact VA.
  - exact VB.
  - exact HE.
  - cbn. lia.
  - lia.
Qed.

Corollary decide_casteq_iff A B (VA : ValidTy A) (VB : ValidTy B) :
  Tyeq A B <-> exists d, decide_casteq A B = Some d.
Proof.
  split; [now apply decide_casteq_complete|].
  intros [d Hd]. now apply (decide_casteq_sound A B d).
Qed.

Corollary decide_casteq_none_iff A B (VA : ValidTy A) (VB : ValidTy B) :
  decide_casteq A B = None <-> ~ Tyeq A B.
Proof.
  split.
  - intros Hnone HE.
    destruct (decide_casteq_complete A B VA VB HE) as [d Hd].
    congruence.
  - intros Hneq. destruct (decide_casteq A B) as [d|] eqn:Hdec;
      [exfalso; apply Hneq; now apply (decide_casteq_sound A B d)|reflexivity].
Qed.

(** A proof-producing equality decision API for valid endpoints.  The left
    branch contains the executable cyclic certificate; the right branch is
    justified by completeness of finite closure search. *)
Definition casteq_decide_valid A B (VA : ValidTy A) (VB : ValidTy B) :
  {d : ClosedCastEq A B | decide_casteq A B = Some d} + {~ Tyeq A B}.
Proof.
  destruct (decide_casteq A B) as [d|] eqn:Hdec.
  - left. now exists d.
  - right. now apply (proj1 (decide_casteq_none_iff A B VA VB)).
Defined.
