Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.CastCommon.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.InstAnnot.
Require Import StlcIso.Fix.
Require Import StlcIso.LemmasTyping.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Module IA := StlcIso.SpecAnnot.

(** A computationally annotated counterpart of the heterogeneous environment
    used by the raw global coercion interpreter. *)
Fixpoint CastTermsA (H : PairEnv) : Type :=
  match H with
  | nil => Datatypes.unit
  | _ :: H' => (IA.TmA * CastTermsA H')%type
  end.

Definition cast_terms_annot_nil : CastTermsA nil := tt.

Definition cast_terms_annot_cons {H A B}
  (t : IA.TmA) (rho : CastTermsA H) : CastTermsA ((A, B) :: H) :=
  (t, rho).

Fixpoint erase_cast_terms_annot {H} : CastTermsA H -> CastTerms H :=
  match H return CastTermsA H -> CastTerms H with
  | nil => fun _ => tt
  | _ :: H' => fun rho =>
      (IA.eraseAnnot (fst rho), erase_cast_terms_annot (snd rho))
  end.

Fixpoint lookup_cast_annot {H A B}
  (m : Assumed H A B) : CastTermsA H -> IA.TmA :=
  match m with
  | assumed_here => fun rho => fst rho
  | assumed_there m' => fun rho => lookup_cast_annot m' (snd rho)
  end.

Lemma erase_lookup_cast_annot {H A B} (m : Assumed H A B)
    (rho : CastTermsA H) :
  IA.eraseAnnot (lookup_cast_annot m rho) =
  lookup_cast m (erase_cast_terms_annot rho).
Proof. induction m; cbn; auto. Qed.

Definition pair_up_annot (A B : Ty) (p : IA.TmA) : IA.TmA :=
  IA.ia_proj₁ (tarr A B) (tarr B A) p.

Definition pair_down_annot (A B : Ty) (p : IA.TmA) : IA.TmA :=
  IA.ia_proj₂ (tarr A B) (tarr B A) p.

Definition certificate_root_annot {H A B} (d : CastEq H A B)
    (self : IA.TmA) (rho : CastTermsA H) : IA.TmA :=
  match d in CastEq H0 A0 B0
        return IA.TmA -> CastTermsA H0 -> IA.TmA with
  | @ce_back H0 A0 B0 m => fun _ rho0 => lookup_cast_annot m rho0
  | @ce_step H0 A0 B0 node => fun self0 _ =>
      IA.ia_proj₁ (cast_pair_ty A0 B0) (node_bundle_ty node) self0
  end self rho.

Definition certificate_up_annot {H A B} (d : CastEq H A B)
    (self : IA.TmA) (rho : CastTermsA H) : IA.TmA :=
  pair_up_annot A B (certificate_root_annot d self rho).

Definition certificate_down_annot {H A B} (d : CastEq H A B)
    (self : IA.TmA) (rho : CastTermsA H) : IA.TmA :=
  pair_down_annot A B (certificate_root_annot d self rho).

(** Every ordinary fold/unfold introduced by the raw interpreter is annotated
    here with the recursive body supplied by the corresponding certificate
    node. *)
Definition global_node_cast_annot {H A B} (node : CastNode H A B)
    (payload_self : IA.TmA)
    (rho : CastTermsA ((A, B) :: H)) : IA.TmA :=
  match node in CastNode H0 A0 B0
        return IA.TmA -> CastTermsA ((A0, B0) :: H0) -> IA.TmA with
  | cn_unit _ => fun _ _ =>
      IA.ia_pair (tarr tunit tunit) (tarr tunit tunit)
        (IA.ia_abs tunit tunit (IA.ia_var 0))
        (IA.ia_abs tunit tunit (IA.ia_var 0))
  | cn_bool _ => fun _ _ =>
      IA.ia_pair (tarr tbool tbool) (tarr tbool tbool)
        (IA.ia_abs tbool tbool (IA.ia_var 0))
        (IA.ia_abs tbool tbool (IA.ia_var 0))
  | cn_var _ x => fun _ _ =>
      IA.ia_pair (tarr (tvar x) (tvar x)) (tarr (tvar x) (tvar x))
        (IA.ia_abs (tvar x) (tvar x) (IA.ia_var 0))
        (IA.ia_abs (tvar x) (tvar x) (IA.ia_var 0))
  | cn_arr _ A1 A2 B1 B2 dom cod => fun ps rho0 =>
      let dp := certificate_root_annot dom
        (IA.ia_proj₁ (certificate_bundle_ty dom)
          (certificate_bundle_ty cod) ps) rho0 in
      let cp := certificate_root_annot cod
        (IA.ia_proj₂ (certificate_bundle_ty dom)
          (certificate_bundle_ty cod) ps) rho0 in
      IA.ia_pair
        (tarr (tarr A1 A2) (tarr B1 B2))
        (tarr (tarr B1 B2) (tarr A1 A2))
        (IA.ia_abs (tarr A1 A2) (tarr B1 B2)
          (IA.ia_abs B1 B2
            (IA.ia_app A2 B2 (pair_up_annot A2 B2 cp)[wkm][wkm]
              (IA.ia_app A1 A2 (IA.ia_var 1)
                (IA.ia_app B1 A1
                  (pair_down_annot A1 B1 dp)[wkm][wkm]
                  (IA.ia_var 0))))))
        (IA.ia_abs (tarr B1 B2) (tarr A1 A2)
          (IA.ia_abs A1 A2
            (IA.ia_app B2 A2 (pair_down_annot A2 B2 cp)[wkm][wkm]
              (IA.ia_app B1 B2 (IA.ia_var 1)
                (IA.ia_app A1 B1
                  (pair_up_annot A1 B1 dp)[wkm][wkm]
                  (IA.ia_var 0))))))
  | cn_prod _ A1 A2 B1 B2 fstc sndc => fun ps rho0 =>
      let fp := certificate_root_annot fstc
        (IA.ia_proj₁ (certificate_bundle_ty fstc)
          (certificate_bundle_ty sndc) ps) rho0 in
      let sp := certificate_root_annot sndc
        (IA.ia_proj₂ (certificate_bundle_ty fstc)
          (certificate_bundle_ty sndc) ps) rho0 in
      IA.ia_pair
        (tarr (tprod A1 A2) (tprod B1 B2))
        (tarr (tprod B1 B2) (tprod A1 A2))
        (IA.ia_abs (tprod A1 A2) (tprod B1 B2)
          (IA.ia_pair B1 B2
            (IA.ia_app A1 B1 (pair_up_annot A1 B1 fp)[wkm]
              (IA.ia_proj₁ A1 A2 (IA.ia_var 0)))
            (IA.ia_app A2 B2 (pair_up_annot A2 B2 sp)[wkm]
              (IA.ia_proj₂ A1 A2 (IA.ia_var 0)))))
        (IA.ia_abs (tprod B1 B2) (tprod A1 A2)
          (IA.ia_pair A1 A2
            (IA.ia_app B1 A1 (pair_down_annot A1 B1 fp)[wkm]
              (IA.ia_proj₁ B1 B2 (IA.ia_var 0)))
            (IA.ia_app B2 A2 (pair_down_annot A2 B2 sp)[wkm]
              (IA.ia_proj₂ B1 B2 (IA.ia_var 0)))))
  | cn_sum _ A1 A2 B1 B2 lc rc => fun ps rho0 =>
      let lp := certificate_root_annot lc
        (IA.ia_proj₁ (certificate_bundle_ty lc)
          (certificate_bundle_ty rc) ps) rho0 in
      let rp := certificate_root_annot rc
        (IA.ia_proj₂ (certificate_bundle_ty lc)
          (certificate_bundle_ty rc) ps) rho0 in
      IA.ia_pair
        (tarr (tsum A1 A2) (tsum B1 B2))
        (tarr (tsum B1 B2) (tsum A1 A2))
        (IA.ia_abs (tsum A1 A2) (tsum B1 B2)
          (IA.ia_caseof A1 A2 (tsum B1 B2) (IA.ia_var 0)
            (IA.ia_inl B1 B2
              (IA.ia_app A1 B1 (pair_up_annot A1 B1 lp)[wkm][wkm]
                (IA.ia_var 0)))
            (IA.ia_inr B1 B2
              (IA.ia_app A2 B2 (pair_up_annot A2 B2 rp)[wkm][wkm]
                (IA.ia_var 0)))))
        (IA.ia_abs (tsum B1 B2) (tsum A1 A2)
          (IA.ia_caseof B1 B2 (tsum A1 A2) (IA.ia_var 0)
            (IA.ia_inl A1 A2
              (IA.ia_app B1 A1 (pair_down_annot A1 B1 lp)[wkm][wkm]
                (IA.ia_var 0)))
            (IA.ia_inr A1 A2
              (IA.ia_app B2 A2 (pair_down_annot A2 B2 rp)[wkm][wkm]
                (IA.ia_var 0)))))
  | cn_mu_l _ body B child => fun ps rho0 =>
      let cp := certificate_root_annot child ps rho0 in
      IA.ia_pair
        (tarr (trec body) B) (tarr B (trec body))
        (IA.ia_abs (trec body) B
          (IA.ia_app body[beta1 (trec body)] B
            (pair_up_annot body[beta1 (trec body)] B cp)[wkm]
            (IA.ia_unfold_ body (IA.ia_var 0))))
        (IA.ia_abs B (trec body)
          (IA.ia_fold_ body
            (IA.ia_app B body[beta1 (trec body)]
              (pair_down_annot body[beta1 (trec body)] B cp)[wkm]
              (IA.ia_var 0))))
  | cn_mu_r _ A body _ child => fun ps rho0 =>
      let cp := certificate_root_annot child ps rho0 in
      IA.ia_pair
        (tarr A (trec body)) (tarr (trec body) A)
        (IA.ia_abs A (trec body)
          (IA.ia_fold_ body
            (IA.ia_app A body[beta1 (trec body)]
              (pair_up_annot A body[beta1 (trec body)] cp)[wkm]
              (IA.ia_var 0))))
        (IA.ia_abs (trec body) A
          (IA.ia_app body[beta1 (trec body)] A
            (pair_down_annot A body[beta1 (trec body)] cp)[wkm]
            (IA.ia_unfold_ body (IA.ia_var 0))))
  end payload_self rho.

Fixpoint build_certificate_bundle_annot {H A B} (d : CastEq H A B)
    (self : IA.TmA) (rho : CastTermsA H) {struct d} : IA.TmA :=
  match d in CastEq H0 A0 B0
        return IA.TmA -> CastTermsA H0 -> IA.TmA with
  | @ce_back H0 A0 B0 _ => fun _ _ => IA.ia_unit
  | @ce_step H0 A0 B0 node => fun self0 rho0 =>
      let root_self := IA.ia_proj₁ (cast_pair_ty A0 B0)
        (node_bundle_ty node) self0 in
      let payload_self := IA.ia_proj₂ (cast_pair_ty A0 B0)
        (node_bundle_ty node) self0 in
      let rho' := cast_terms_annot_cons root_self rho0 in
      IA.ia_pair (cast_pair_ty A0 B0) (node_bundle_ty node)
        (global_node_cast_annot node payload_self rho')
        (build_node_bundle_annot node payload_self rho')
  end self rho
with build_node_bundle_annot {H A B} (node : CastNode H A B)
    (payload_self : IA.TmA)
    (rho : CastTermsA ((A, B) :: H)) {struct node} : IA.TmA :=
  match node in CastNode H0 A0 B0
        return IA.TmA -> CastTermsA ((A0, B0) :: H0) -> IA.TmA with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ _ => IA.ia_unit
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => fun ps rho0 =>
      IA.ia_pair (certificate_bundle_ty l) (certificate_bundle_ty r)
        (build_certificate_bundle_annot l
          (IA.ia_proj₁ (certificate_bundle_ty l)
            (certificate_bundle_ty r) ps) rho0)
        (build_certificate_bundle_annot r
          (IA.ia_proj₂ (certificate_bundle_ty l)
            (certificate_bundle_ty r) ps) rho0)
  | cn_mu_l _ _ _ child => fun ps rho0 =>
      build_certificate_bundle_annot child ps rho0
  | cn_mu_r _ _ _ _ child => fun ps rho0 =>
      build_certificate_bundle_annot child ps rho0
  end payload_self rho.

Definition global_bundle_functional_annot {A B}
    (d : ClosedCastEq A B) : IA.TmA :=
  let BT := certificate_bundle_ty d in
  let self := IA.ia_app tunit BT (IA.ia_var 1) IA.ia_unit in
  IA.ia_abs (tarr tunit BT) (tarr tunit BT)
    (IA.ia_abs tunit BT
      (build_certificate_bundle_annot d self cast_terms_annot_nil)).

Definition tied_certificate_bundle_annot {A B}
    (d : ClosedCastEq A B) : IA.TmA :=
  let BT := certificate_bundle_ty d in
  IA.ia_app tunit BT
    (IA.ia_app
      (tarr (tarr tunit BT) (tarr tunit BT))
      (tarr tunit BT)
      (ufix_annot tunit BT) (global_bundle_functional_annot d))
    IA.ia_unit.

Definition compile_global_pair_annot {A B}
    (d : ClosedCastEq A B) : IA.TmA :=
  certificate_root_annot d (tied_certificate_bundle_annot d)
    cast_terms_annot_nil.

Definition compile_global_up_annot {A B}
    (d : ClosedCastEq A B) : IA.TmA :=
  pair_up_annot A B (compile_global_pair_annot d).

Definition compile_global_down_annot {A B}
    (d : ClosedCastEq A B) : IA.TmA :=
  pair_down_annot A B (compile_global_pair_annot d).

(** Erasure commutes with the renamings used inside generated casts. *)
Lemma erase_annot_ren (t : IA.TmA) (xi : Sub Ix) :
  IA.eraseAnnot (IA.apTmA xi t) =
  StlcIso.SpecSyntax.apTm xi (IA.eraseAnnot t).
Proof. revert xi. induction t; intros xi; cbn; f_equal; eauto. Qed.

Lemma erase_annot_var_sub (t : IA.TmA) (xi : Sub Ix) :
  IA.eraseAnnot (IA.apTmA (fun x => IA.ia_var (xi x)) t) =
  StlcIso.SpecSyntax.apTm
    (fun x => StlcIso.SpecSyntax.var (xi x)) (IA.eraseAnnot t).
Proof.
  assert (HA : forall zeta : Sub Ix,
    (fun x => IA.ia_var (zeta x))↑ =
    (fun x => IA.ia_var ((zeta↑) x))).
  { intros zeta. apply functional_extensionality.
    intros [|x]; reflexivity. }
  assert (HI : forall zeta : Sub Ix,
    (fun x => StlcIso.SpecSyntax.var (zeta x))↑ =
    (fun x => StlcIso.SpecSyntax.var ((zeta↑) x))).
  { intros zeta. apply functional_extensionality.
    intros [|x]; reflexivity. }
  revert xi. induction t; intros xi; cbn;
    repeat rewrite HA; repeat rewrite HI; f_equal; eauto.
Qed.

Lemma erase_annot_wkm (t : IA.TmA) :
  IA.eraseAnnot (IA.apTmA wkm t) =
  StlcIso.SpecSyntax.apTm wkm (IA.eraseAnnot t).
Proof.
  change (IA.eraseAnnot
    (IA.apTmA (fun x => IA.ia_var (S x)) t) =
    StlcIso.SpecSyntax.apTm
      (fun x => StlcIso.SpecSyntax.var (S x)) (IA.eraseAnnot t)).
  exact (erase_annot_var_sub t (fun x => S x)).
Qed.

Lemma erase_certificate_root_annot {H A B} (d : CastEq H A B)
    self (rho : CastTermsA H) :
  IA.eraseAnnot (certificate_root_annot d self rho) =
  certificate_root d (IA.eraseAnnot self) (erase_cast_terms_annot rho).
Proof.
  destruct d; cbn; auto using erase_lookup_cast_annot.
Qed.

Lemma erase_global_node_cast_annot {H A B} (node : CastNode H A B)
    payload (rho : CastTermsA ((A, B) :: H)) :
  IA.eraseAnnot (global_node_cast_annot node payload rho) =
  global_node_cast node (IA.eraseAnnot payload)
    (erase_cast_terms_annot rho).
Proof.
  destruct node; cbn;
    repeat rewrite erase_annot_wkm;
    repeat setoid_rewrite erase_certificate_root_annot;
    reflexivity.
Qed.

Lemma erase_build_certificate_bundle_annot {H A B}
    (d : CastEq H A B) self (rho : CastTermsA H) :
  IA.eraseAnnot (build_certificate_bundle_annot d self rho) =
  build_certificate_bundle d (IA.eraseAnnot self)
    (erase_cast_terms_annot rho)
with erase_build_node_bundle_annot {H A B}
    (node : CastNode H A B) payload
    (rho : CastTermsA ((A, B) :: H)) :
  IA.eraseAnnot (build_node_bundle_annot node payload rho) =
  build_node_bundle node (IA.eraseAnnot payload)
    (erase_cast_terms_annot rho).
Proof.
  - destruct d; cbn -[global_node_cast_annot global_node_cast
      build_node_bundle_annot build_node_bundle].
    + reflexivity.
    + rewrite erase_global_node_cast_annot.
      rewrite erase_build_node_bundle_annot.
      reflexivity.
  - destruct node; cbn -[build_certificate_bundle_annot
      build_certificate_bundle]; try reflexivity;
      repeat rewrite erase_build_certificate_bundle_annot; reflexivity.
Qed.

Theorem erase_global_bundle_functional_annot {A B}
    (d : ClosedCastEq A B) :
  IA.eraseAnnot (global_bundle_functional_annot d) =
  global_bundle_functional d.
Proof.
  unfold global_bundle_functional_annot, global_bundle_functional.
  cbn. now rewrite erase_build_certificate_bundle_annot.
Qed.

Theorem erase_tied_certificate_bundle_annot {A B}
    (d : ClosedCastEq A B) :
  IA.eraseAnnot (tied_certificate_bundle_annot d) =
  tied_certificate_bundle d.
Proof.
  unfold tied_certificate_bundle_annot, tied_certificate_bundle.
  cbn -[ufix_annot global_bundle_functional_annot].
  rewrite eraseAnnot_ufix, erase_global_bundle_functional_annot.
  reflexivity.
Qed.

Theorem erase_compile_global_pair_annot {A B}
    (d : ClosedCastEq A B) :
  IA.eraseAnnot (compile_global_pair_annot d) = compile_global_pair d.
Proof.
  unfold compile_global_pair_annot, compile_global_pair.
  rewrite erase_certificate_root_annot.
  now rewrite erase_tied_certificate_bundle_annot.
Qed.

Theorem erase_compile_global_up_annot {A B}
    (d : ClosedCastEq A B) :
  IA.eraseAnnot (compile_global_up_annot d) = compile_global_up d.
Proof.
  unfold compile_global_up_annot, compile_global_up, pair_up_annot, pair_up.
  cbn. now rewrite erase_compile_global_pair_annot.
Qed.

Theorem erase_compile_global_down_annot {A B}
    (d : ClosedCastEq A B) :
  IA.eraseAnnot (compile_global_down_annot d) = compile_global_down d.
Proof.
  unfold compile_global_down_annot, compile_global_down,
    pair_down_annot, pair_down.
  cbn. now rewrite erase_compile_global_pair_annot.
Qed.

(** Direct annotated typing: this does not reify a raw typing derivation in
    [Prop]. *)
Lemma annot_typing_var_ren {Gamma1 t T} :
  IA.AnnotTyping Gamma1 t T ->
  forall Gamma2 (xi : Sub Ix), WtRen Gamma1 Gamma2 xi ->
  IA.AnnotTyping Gamma2
    (IA.apTmA (fun x => IA.ia_var (xi x)) t) T.
Proof.
  intros Ht.
  assert (HA : forall zeta : Sub Ix,
    (fun x => IA.ia_var (zeta x))↑ =
    (fun x => IA.ia_var ((zeta↑) x))).
  { intros zeta. apply functional_extensionality.
    intros [|x]; reflexivity. }
  induction Ht; intros Gamma2 xi Hxi; cbn;
    repeat rewrite HA; eauto using IA.AnnotTyping, wtRen_up.
  econstructor; eauto using wtRen_up.
Qed.

Lemma annot_typing_weaken {Gamma t T U} :
  IA.AnnotTyping Gamma t T ->
  IA.AnnotTyping (Gamma r▻ U) t[wkm] T.
Proof.
  intros Ht.
  change (IA.AnnotTyping (Gamma r▻ U)
    (IA.apTmA (fun x => IA.ia_var (S x)) t) T).
  eapply annot_typing_var_ren; [exact Ht|apply wtRen_wkm].
Qed.

Fixpoint CastTermsATyping (Gamma : Env) (H : PairEnv) :
    CastTermsA H -> Prop :=
  match H return CastTermsA H -> Prop with
  | nil => fun _ => True
  | (A, B) :: H' => fun rho =>
      IA.AnnotTyping Gamma (fst rho) (cast_pair_ty A B) /\
      CastTermsATyping Gamma H' (snd rho)
  end.

Lemma cast_terms_annot_typing_nil Gamma :
  CastTermsATyping Gamma nil cast_terms_annot_nil.
Proof. exact I. Qed.

Lemma cast_terms_annot_typing_cons {H A B Gamma t rho} :
  IA.AnnotTyping Gamma t (cast_pair_ty A B) ->
  CastTermsATyping Gamma H rho ->
  CastTermsATyping Gamma ((A, B) :: H)
    (cast_terms_annot_cons t rho).
Proof. split; assumption. Qed.

Lemma lookup_cast_annot_typing {Gamma H A B}
    (m : Assumed H A B) rho :
  CastTermsATyping Gamma H rho ->
  IA.AnnotTyping Gamma (lookup_cast_annot m rho) (cast_pair_ty A B).
Proof.
  revert rho. induction m; intros rho Hrho; cbn in *.
  - exact (proj1 Hrho).
  - apply IHm. exact (proj2 Hrho).
Qed.

Lemma pair_up_annot_typing {Gamma p A B} :
  IA.AnnotTyping Gamma p (cast_pair_ty A B) ->
  IA.AnnotTyping Gamma (pair_up_annot A B p) (tarr A B).
Proof.
  intros Hp. unfold pair_up_annot, cast_pair_ty in *.
  now apply IA.ia_WtProj1.
Qed.

Lemma pair_down_annot_typing {Gamma p A B} :
  IA.AnnotTyping Gamma p (cast_pair_ty A B) ->
  IA.AnnotTyping Gamma (pair_down_annot A B p) (tarr B A).
Proof.
  intros Hp. unfold pair_down_annot, cast_pair_ty in *.
  now apply IA.ia_WtProj2.
Qed.

Lemma certificate_root_annot_typing {Gamma H A B}
    (d : CastEq H A B) self rho :
  IA.AnnotTyping Gamma self (certificate_bundle_ty d) ->
  CastTermsATyping Gamma H rho ->
  IA.AnnotTyping Gamma (certificate_root_annot d self rho)
    (cast_pair_ty A B).
Proof.
  destruct d; cbn; intros Hself Hrho.
  - now apply lookup_cast_annot_typing.
  - apply IA.ia_WtProj1. exact Hself.
Qed.

Lemma certificate_up_annot_typing {Gamma H A B}
    (d : CastEq H A B) self rho :
  IA.AnnotTyping Gamma self (certificate_bundle_ty d) ->
  CastTermsATyping Gamma H rho ->
  IA.AnnotTyping Gamma (certificate_up_annot d self rho) (tarr A B).
Proof.
  intros Hself Hrho. apply pair_up_annot_typing.
  now apply certificate_root_annot_typing.
Qed.

Lemma certificate_down_annot_typing {Gamma H A B}
    (d : CastEq H A B) self rho :
  IA.AnnotTyping Gamma self (certificate_bundle_ty d) ->
  CastTermsATyping Gamma H rho ->
  IA.AnnotTyping Gamma (certificate_down_annot d self rho) (tarr B A).
Proof.
  intros Hself Hrho. apply pair_down_annot_typing.
  now apply certificate_root_annot_typing.
Qed.

Lemma id_cast_annot_typing {Gamma A} :
  ValidTy A ->
  IA.AnnotTyping Gamma (IA.ia_abs A A (IA.ia_var 0)) (tarr A A).
Proof.
  intros VA. apply IA.ia_WtAbs; [exact VA|].
  apply IA.ia_WtVar. constructor.
Qed.

Lemma global_node_cast_annot_typing {Gamma H A B}
    (node : CastNode H A B) payload_self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma payload_self (node_bundle_ty node) ->
  CastTermsATyping Gamma ((A, B) :: H) rho ->
  IA.AnnotTyping Gamma (global_node_cast_annot node payload_self rho)
    (cast_pair_ty A B).
Proof.
  destruct node as
      [H|H|H x
      |H A1 A2 B1 B2 dom cod
      |H A1 A2 B1 B2 fstc sndc
      |H A1 A2 B1 B2 lc rc
      |H body B child
      |H A body nmu child]; intros VH VA VB Hself Hrho; cbn in *.
  - apply IA.ia_WtPair; apply id_cast_annot_typing; assumption.
  - apply IA.ia_WtPair; apply id_cast_annot_typing; assumption.
  - apply IA.ia_WtPair; apply id_cast_annot_typing; assumption.
  - apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    assert (Hdomself : IA.AnnotTyping Gamma
      (IA.ia_proj₁ (certificate_bundle_ty dom)
        (certificate_bundle_ty cod) payload_self)
      (certificate_bundle_ty dom))
      by (apply IA.ia_WtProj1; exact Hself).
    assert (Hcodself : IA.AnnotTyping Gamma
      (IA.ia_proj₂ (certificate_bundle_ty dom)
        (certificate_bundle_ty cod) payload_self)
      (certificate_bundle_ty cod))
      by (apply IA.ia_WtProj2; exact Hself).
    assert (Hdom := certificate_root_annot_typing dom _ _ Hdomself Hrho).
    assert (Hcod := certificate_root_annot_typing cod _ _ Hcodself Hrho).
    assert (HUdom := pair_up_annot_typing Hdom).
    assert (HDdom := pair_down_annot_typing Hdom).
    assert (HUcod := pair_up_annot_typing Hcod).
    assert (HDcod := pair_down_annot_typing Hcod).
    apply IA.ia_WtPair.
    + apply IA.ia_WtAbs; [now apply ValidTy_arr|].
      apply IA.ia_WtAbs; [exact VB1|].
      eapply IA.ia_WtApp.
      * exact (annot_typing_weaken
          (annot_typing_weaken HUcod)).
      * eapply IA.ia_WtApp.
        -- apply IA.ia_WtVar. constructor. constructor.
        -- eapply IA.ia_WtApp.
           ++ exact (annot_typing_weaken
                (annot_typing_weaken HDdom)).
           ++ apply IA.ia_WtVar. constructor.
    + apply IA.ia_WtAbs; [now apply ValidTy_arr|].
      apply IA.ia_WtAbs; [exact VA1|].
      eapply IA.ia_WtApp.
      * exact (annot_typing_weaken
          (annot_typing_weaken HDcod)).
      * eapply IA.ia_WtApp.
        -- apply IA.ia_WtVar. constructor. constructor.
        -- eapply IA.ia_WtApp.
           ++ exact (annot_typing_weaken
                (annot_typing_weaken HUdom)).
           ++ apply IA.ia_WtVar. constructor.
  - apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    assert (Hfstself : IA.AnnotTyping Gamma
      (IA.ia_proj₁ (certificate_bundle_ty fstc)
        (certificate_bundle_ty sndc) payload_self)
      (certificate_bundle_ty fstc))
      by (apply IA.ia_WtProj1; exact Hself).
    assert (Hsndself : IA.AnnotTyping Gamma
      (IA.ia_proj₂ (certificate_bundle_ty fstc)
        (certificate_bundle_ty sndc) payload_self)
      (certificate_bundle_ty sndc))
      by (apply IA.ia_WtProj2; exact Hself).
    assert (Hfst := certificate_root_annot_typing fstc _ _ Hfstself Hrho).
    assert (Hsnd := certificate_root_annot_typing sndc _ _ Hsndself Hrho).
    assert (HUfst := pair_up_annot_typing Hfst).
    assert (HDfst := pair_down_annot_typing Hfst).
    assert (HUsnd := pair_up_annot_typing Hsnd).
    assert (HDsnd := pair_down_annot_typing Hsnd).
    apply IA.ia_WtPair.
    + apply IA.ia_WtAbs; [now apply ValidTy_prod|].
      apply IA.ia_WtPair.
      * eapply IA.ia_WtApp; [exact (annot_typing_weaken HUfst)|].
        apply IA.ia_WtProj1. apply IA.ia_WtVar. constructor.
      * eapply IA.ia_WtApp; [exact (annot_typing_weaken HUsnd)|].
        apply IA.ia_WtProj2. apply IA.ia_WtVar. constructor.
    + apply IA.ia_WtAbs; [now apply ValidTy_prod|].
      apply IA.ia_WtPair.
      * eapply IA.ia_WtApp; [exact (annot_typing_weaken HDfst)|].
        apply IA.ia_WtProj1. apply IA.ia_WtVar. constructor.
      * eapply IA.ia_WtApp; [exact (annot_typing_weaken HDsnd)|].
        apply IA.ia_WtProj2. apply IA.ia_WtVar. constructor.
  - apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    assert (Hlself : IA.AnnotTyping Gamma
      (IA.ia_proj₁ (certificate_bundle_ty lc)
        (certificate_bundle_ty rc) payload_self)
      (certificate_bundle_ty lc))
      by (apply IA.ia_WtProj1; exact Hself).
    assert (Hrself : IA.AnnotTyping Gamma
      (IA.ia_proj₂ (certificate_bundle_ty lc)
        (certificate_bundle_ty rc) payload_self)
      (certificate_bundle_ty rc))
      by (apply IA.ia_WtProj2; exact Hself).
    assert (Hl := certificate_root_annot_typing lc _ _ Hlself Hrho).
    assert (Hr := certificate_root_annot_typing rc _ _ Hrself Hrho).
    assert (HUl := pair_up_annot_typing Hl).
    assert (HDl := pair_down_annot_typing Hl).
    assert (HUr := pair_up_annot_typing Hr).
    assert (HDr := pair_down_annot_typing Hr).
    apply IA.ia_WtPair.
    + apply IA.ia_WtAbs; [now apply ValidTy_sum|].
      eapply IA.ia_WtCaseof; eauto.
      * apply IA.ia_WtVar. constructor.
      * apply IA.ia_WtInl; [exact VB2|].
        eapply IA.ia_WtApp.
        -- exact (annot_typing_weaken (annot_typing_weaken HUl)).
        -- apply IA.ia_WtVar. constructor.
      * apply IA.ia_WtInr; [exact VB1|].
        eapply IA.ia_WtApp.
        -- exact (annot_typing_weaken (annot_typing_weaken HUr)).
        -- apply IA.ia_WtVar. constructor.
    + apply IA.ia_WtAbs; [now apply ValidTy_sum|].
      eapply IA.ia_WtCaseof; eauto.
      * apply IA.ia_WtVar. constructor.
      * apply IA.ia_WtInl; [exact VA2|].
        eapply IA.ia_WtApp.
        -- exact (annot_typing_weaken (annot_typing_weaken HDl)).
        -- apply IA.ia_WtVar. constructor.
      * apply IA.ia_WtInr; [exact VA1|].
        eapply IA.ia_WtApp.
        -- exact (annot_typing_weaken (annot_typing_weaken HDr)).
        -- apply IA.ia_WtVar. constructor.
  - assert (Hchild := certificate_root_annot_typing
      child payload_self rho Hself Hrho).
    assert (HU := pair_up_annot_typing Hchild).
    assert (HD := pair_down_annot_typing Hchild).
    apply IA.ia_WtPair.
    + apply IA.ia_WtAbs; [exact VA|].
      eapply IA.ia_WtApp.
      * exact (annot_typing_weaken HU).
      * apply IA.ia_WtUnfold; [apply IA.ia_WtVar; constructor|exact VA].
    + apply IA.ia_WtAbs; [exact VB|].
      apply IA.ia_WtFold; [|exact VA].
      eapply IA.ia_WtApp; [exact (annot_typing_weaken HD)|].
      apply IA.ia_WtVar. constructor.
  - assert (Hchild := certificate_root_annot_typing
      child payload_self rho Hself Hrho).
    assert (HU := pair_up_annot_typing Hchild).
    assert (HD := pair_down_annot_typing Hchild).
    apply IA.ia_WtPair.
    + apply IA.ia_WtAbs; [exact VA|].
      apply IA.ia_WtFold; [|exact VB].
      eapply IA.ia_WtApp; [exact (annot_typing_weaken HU)|].
      apply IA.ia_WtVar. constructor.
    + apply IA.ia_WtAbs; [exact VB|].
      eapply IA.ia_WtApp.
      * exact (annot_typing_weaken HD).
      * apply IA.ia_WtUnfold; [apply IA.ia_WtVar; constructor|exact VB].
Qed.

Lemma build_certificate_bundle_annot_typing {Gamma H A B}
    (d : CastEq H A B) self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma self (certificate_bundle_ty d) ->
  CastTermsATyping Gamma H rho ->
  IA.AnnotTyping Gamma (build_certificate_bundle_annot d self rho)
    (certificate_bundle_ty d)
with build_node_bundle_annot_typing {Gamma H A B}
    (node : CastNode H A B) payload_self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma payload_self (node_bundle_ty node) ->
  CastTermsATyping Gamma ((A, B) :: H) rho ->
  IA.AnnotTyping Gamma
    (build_node_bundle_annot node payload_self rho)
    (node_bundle_ty node).
Proof.
  - destruct d as [H A B m|H A B node];
      intros VH VA VB Hself Hrho; cbn.
    + apply IA.ia_WtUnit.
    + assert (Hroot : IA.AnnotTyping Gamma
        (IA.ia_proj₁ (cast_pair_ty A B) (node_bundle_ty node) self)
        (cast_pair_ty A B))
        by (apply IA.ia_WtProj1; exact Hself).
      assert (Hpayload : IA.AnnotTyping Gamma
        (IA.ia_proj₂ (cast_pair_ty A B) (node_bundle_ty node) self)
        (node_bundle_ty node))
        by (apply IA.ia_WtProj2; exact Hself).
      assert (Hrho' : CastTermsATyping Gamma ((A, B) :: H)
        (cast_terms_annot_cons
          (IA.ia_proj₁ (cast_pair_ty A B) (node_bundle_ty node) self)
          rho)).
      { now apply cast_terms_annot_typing_cons. }
      apply IA.ia_WtPair.
      * eapply global_node_cast_annot_typing; eauto.
      * eapply build_node_bundle_annot_typing; eauto.
  - destruct node as
      [H|H|H x
      |H A1 A2 B1 B2 l r
      |H A1 A2 B1 B2 l r
      |H A1 A2 B1 B2 l r
      |H body B child
      |H A body nmu child]; intros VH VA VB Hself Hrho; cbn in *.
    + apply IA.ia_WtUnit.
    + apply IA.ia_WtUnit.
    + apply IA.ia_WtUnit.
    + apply ValidTy_invert_arr in VA as [VA1 VA2].
      apply ValidTy_invert_arr in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H)).
      { apply pair_env_valid_cons;
          [now apply ValidTy_arr|now apply ValidTy_arr|exact VH]. }
      apply IA.ia_WtPair.
      * eapply build_certificate_bundle_annot_typing; eauto.
        apply IA.ia_WtProj1. exact Hself.
      * eapply build_certificate_bundle_annot_typing; eauto.
        apply IA.ia_WtProj2. exact Hself.
    + apply ValidTy_invert_prod in VA as [VA1 VA2].
      apply ValidTy_invert_prod in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H)).
      { apply pair_env_valid_cons;
          [now apply ValidTy_prod|now apply ValidTy_prod|exact VH]. }
      apply IA.ia_WtPair.
      * eapply build_certificate_bundle_annot_typing; eauto.
        apply IA.ia_WtProj1. exact Hself.
      * eapply build_certificate_bundle_annot_typing; eauto.
        apply IA.ia_WtProj2. exact Hself.
    + apply ValidTy_invert_sum in VA as [VA1 VA2].
      apply ValidTy_invert_sum in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H)).
      { apply pair_env_valid_cons;
          [now apply ValidTy_sum|now apply ValidTy_sum|exact VH]. }
      apply IA.ia_WtPair.
      * eapply build_certificate_bundle_annot_typing; eauto.
        apply IA.ia_WtProj1. exact Hself.
      * eapply build_certificate_bundle_annot_typing; eauto.
        apply IA.ia_WtProj2. exact Hself.
    + assert (VU : ValidTy body[beta1 (trec body)])
        by now apply ValidTy_unfold_trec.
      assert (VH' : PairEnvValid ((trec body, B) :: H))
        by now apply pair_env_valid_cons.
      eapply build_certificate_bundle_annot_typing; eauto.
    + assert (VU : ValidTy body[beta1 (trec body)])
        by now apply ValidTy_unfold_trec.
      assert (VH' : PairEnvValid ((A, trec body) :: H))
        by now apply pair_env_valid_cons.
      eapply build_certificate_bundle_annot_typing; eauto.
Qed.

Lemma global_bundle_functional_annot_typing {Gamma A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma (global_bundle_functional_annot d)
    (tarr (tarr tunit (certificate_bundle_ty d))
      (tarr tunit (certificate_bundle_ty d))).
Proof.
  intros VA VB. unfold global_bundle_functional_annot.
  assert (VBT : ValidTy (certificate_bundle_ty d)).
  { eapply certificate_bundle_ty_valid; eauto using pair_env_valid_nil. }
  apply IA.ia_WtAbs.
  - apply ValidTy_arr;
      [eauto with tyvalid cty simple_contr_rec|exact VBT].
  - apply IA.ia_WtAbs.
    + eauto with tyvalid cty simple_contr_rec.
    + eapply build_certificate_bundle_annot_typing.
      * apply pair_env_valid_nil.
      * exact VA.
      * exact VB.
      * eapply IA.ia_WtApp.
        -- apply IA.ia_WtVar. constructor. constructor.
        -- apply IA.ia_WtUnit.
      * apply cast_terms_annot_typing_nil.
Qed.

Theorem tied_certificate_bundle_annot_typing {Gamma A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma (tied_certificate_bundle_annot d)
    (certificate_bundle_ty d).
Proof.
  intros VA VB. unfold tied_certificate_bundle_annot.
  assert (VBT : ValidTy (certificate_bundle_ty d)).
  { eapply certificate_bundle_ty_valid; eauto using pair_env_valid_nil. }
  eapply IA.ia_WtApp.
  - eapply IA.ia_WtApp.
    + apply ufix_annot_typing.
      * eauto with tyvalid cty simple_contr_rec.
      * exact VBT.
    + now apply global_bundle_functional_annot_typing.
  - apply IA.ia_WtUnit.
Qed.

Theorem compile_global_pair_annot_typing {Gamma A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma (compile_global_pair_annot d) (cast_pair_ty A B).
Proof.
  intros VA VB. unfold compile_global_pair_annot.
  apply certificate_root_annot_typing.
  - now apply tied_certificate_bundle_annot_typing.
  - apply cast_terms_annot_typing_nil.
Qed.

Theorem compile_global_up_annot_typing {Gamma A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma (compile_global_up_annot d) (tarr A B).
Proof.
  intros VA VB. apply pair_up_annot_typing.
  now apply compile_global_pair_annot_typing.
Qed.

Theorem compile_global_down_annot_typing {Gamma A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  IA.AnnotTyping Gamma (compile_global_down_annot d) (tarr B A).
Proof.
  intros VA VB. apply pair_down_annot_typing.
  now apply compile_global_pair_annot_typing.
Qed.
