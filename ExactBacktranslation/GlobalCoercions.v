Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.CastCommon.
Require Import ExactBacktranslation.StructuralCoercions.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.Inst.
Require Import StlcIso.Fix.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
Require Import Db.Lemmas.
From Coq Require Import Lists.List.
Import ListNotations.

(** One bundle cell for every proper certificate node. Backreferences add no
    cell: they select an ancestor cell through [CastTerms]. *)
Fixpoint certificate_bundle_ty {H A B} (d : CastEq H A B) : Ty :=
  match d with
  | ce_back _ => tunit
  | ce_step node => tprod (cast_pair_ty A B) (node_bundle_ty node)
  end
with node_bundle_ty {H A B} (node : CastNode H A B) : Ty :=
  match node with
  | cn_unit _ | cn_bool _ | cn_var _ _ => tunit
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r =>
      tprod (certificate_bundle_ty l) (certificate_bundle_ty r)
  | cn_mu_l _ _ _ child => certificate_bundle_ty child
  | cn_mu_r _ _ _ _ child => certificate_bundle_ty child
  end.

(** Select the cast pair denoted by a certificate. For a backreference this
    comes from the ancestor environment; for a proper node it is the head of
    that node's bundle cell. *)
Definition certificate_root {H A B} (d : CastEq H A B)
  (self : Tm) (rho : CastTerms H) : Tm :=
  match d in CastEq H0 _ _ return CastTerms H0 -> Tm with
  | ce_back m => fun rho0 => lookup_cast m rho0
  | ce_step _ => fun _ => proj₁ self
  end rho.

Definition certificate_up {H A B} (d : CastEq H A B)
  (self : Tm) (rho : CastTerms H) : Tm :=
  pair_up (certificate_root d self rho).

Definition certificate_down {H A B} (d : CastEq H A B)
  (self : Tm) (rho : CastTerms H) : Tm :=
  pair_down (certificate_root d self rho).

Lemma certificate_root_subst {H A B} (d : CastEq H A B)
  self (rho : CastTerms H) zeta :
  (certificate_root d self rho)[zeta] =
  certificate_root d self[zeta] (subst_cast_terms zeta rho).
Proof.
  destruct d; cbn; auto using lookup_cast_subst.
Qed.

Lemma subst_after_weaken t zeta :
  t[wkm][zeta↑] = t[zeta][wkm].
Proof. symmetry. apply apply_wkm_comm. Qed.

Lemma subst_after_weaken2 t zeta :
  t[wkm][wkm][zeta↑↑] = t[zeta][wkm][wkm].
Proof.
  rewrite (subst_after_weaken (t[wkm]) zeta↑).
  now rewrite subst_after_weaken.
Qed.

(** Structural casts read child cast pairs from the corresponding child
    sub-bundles of [payload_self]. *)
Definition global_node_cast {H A B} (node : CastNode H A B)
  (payload_self : Tm) (rho : CastTerms ((A, B) :: H)) : Tm :=
  match node in CastNode H0 A0 B0
        return Tm -> CastTerms ((A0, B0) :: H0) -> Tm with
  | cn_unit _ => fun _ _ => pair (id_cast tunit) (id_cast tunit)
  | cn_bool _ => fun _ _ => pair (id_cast tbool) (id_cast tbool)
  | cn_var _ x => fun _ _ => pair (id_cast (tvar x)) (id_cast (tvar x))
  | cn_arr _ A1 A2 B1 B2 dom cod => fun ps rho0 =>
      let dp := certificate_root dom (proj₁ ps) rho0 in
      let cp := certificate_root cod (proj₂ ps) rho0 in
      pair
        (abs (tarr A1 A2)
          (abs B1
            (tm_app (pair_up cp)[wkm][wkm]
              (tm_app (var 1)
                (tm_app (pair_down dp)[wkm][wkm] (var 0))))))
        (abs (tarr B1 B2)
          (abs A1
            (tm_app (pair_down cp)[wkm][wkm]
              (tm_app (var 1)
                (tm_app (pair_up dp)[wkm][wkm] (var 0))))))
  | cn_prod _ A1 A2 B1 B2 fstc sndc => fun ps rho0 =>
      let fp := certificate_root fstc (proj₁ ps) rho0 in
      let sp := certificate_root sndc (proj₂ ps) rho0 in
      pair
        (abs (tprod A1 A2)
          (pair
            (tm_app (pair_up fp)[wkm] (proj₁ (var 0)))
            (tm_app (pair_up sp)[wkm] (proj₂ (var 0)))))
        (abs (tprod B1 B2)
          (pair
            (tm_app (pair_down fp)[wkm] (proj₁ (var 0)))
            (tm_app (pair_down sp)[wkm] (proj₂ (var 0)))))
  | cn_sum _ A1 A2 B1 B2 lc rc => fun ps rho0 =>
      let lp := certificate_root lc (proj₁ ps) rho0 in
      let rp := certificate_root rc (proj₂ ps) rho0 in
      pair
        (abs (tsum A1 A2)
          (caseof (var 0)
            (inl (tm_app (pair_up lp)[wkm][wkm] (var 0)))
            (inr (tm_app (pair_up rp)[wkm][wkm] (var 0)))))
        (abs (tsum B1 B2)
          (caseof (var 0)
            (inl (tm_app (pair_down lp)[wkm][wkm] (var 0)))
            (inr (tm_app (pair_down rp)[wkm][wkm] (var 0)))))
  | cn_mu_l _ body B child => fun ps rho0 =>
      let cp := certificate_root child ps rho0 in
      pair
        (abs (trec body)
          (tm_app (pair_up cp)[wkm] (unfold_ (var 0))))
        (abs B (fold_ (tm_app (pair_down cp)[wkm] (var 0))))
  | cn_mu_r _ A body _ child => fun ps rho0 =>
      let cp := certificate_root child ps rho0 in
      pair
        (abs A (fold_ (tm_app (pair_up cp)[wkm] (var 0))))
        (abs (trec body)
          (tm_app (pair_down cp)[wkm] (unfold_ (var 0))))
  end payload_self rho.

Lemma global_node_cast_subst {H A B} (node : CastNode H A B)
  payload (rho : CastTerms ((A, B) :: H)) zeta :
  (global_node_cast node payload rho)[zeta] =
  global_node_cast node payload[zeta] (subst_cast_terms zeta rho).
Proof.
  destruct node; cbn;
    try setoid_rewrite subst_after_weaken2;
    try setoid_rewrite subst_after_weaken;
    try setoid_rewrite (certificate_root_subst _ _ _ zeta);
    cbn; reflexivity.
Qed.

(** Build all proper-node cells. Recursive calls only construct child
    sub-bundles; no fixed point occurs here. *)
Fixpoint build_certificate_bundle {H A B} (d : CastEq H A B)
  (self : Tm) (rho : CastTerms H) {struct d} : Tm :=
  match d in CastEq H0 A0 B0 return Tm -> CastTerms H0 -> Tm with
  | ce_back _ => fun _ _ => unit
  | ce_step node => fun self0 rho0 =>
      let root_self := proj₁ self0 in
      let payload_self := proj₂ self0 in
      let rho' := cast_terms_cons root_self rho0 in
      pair (global_node_cast node payload_self rho')
           (build_node_bundle node payload_self rho')
  end self rho
with build_node_bundle {H A B} (node : CastNode H A B)
  (payload_self : Tm) (rho : CastTerms ((A, B) :: H))
  {struct node} : Tm :=
  match node in CastNode H0 A0 B0
        return Tm -> CastTerms ((A0, B0) :: H0) -> Tm with
  | cn_unit _ | cn_bool _ | cn_var _ _ => fun _ _ => unit
  | cn_arr _ _ _ _ _ l r
  | cn_prod _ _ _ _ _ l r
  | cn_sum _ _ _ _ _ l r => fun ps rho0 =>
      pair (build_certificate_bundle l (proj₁ ps) rho0)
           (build_certificate_bundle r (proj₂ ps) rho0)
  | cn_mu_l _ _ _ child => fun ps rho0 =>
      build_certificate_bundle child ps rho0
  | cn_mu_r _ _ _ _ child => fun ps rho0 =>
      build_certificate_bundle child ps rho0
  end payload_self rho.

Lemma build_certificate_bundle_subst {H A B} (d : CastEq H A B)
  self (rho : CastTerms H) zeta :
  (build_certificate_bundle d self rho)[zeta] =
  build_certificate_bundle d self[zeta] (subst_cast_terms zeta rho)
with build_node_bundle_subst {H A B} (node : CastNode H A B)
  payload (rho : CastTerms ((A, B) :: H)) zeta :
  (build_node_bundle node payload rho)[zeta] =
  build_node_bundle node payload[zeta] (subst_cast_terms zeta rho).
Proof.
  - destruct d; cbn -[global_node_cast build_node_bundle].
    + reflexivity.
    + setoid_rewrite global_node_cast_subst.
      setoid_rewrite build_node_bundle_subst.
      reflexivity.
  - destruct node; cbn -[build_certificate_bundle]; try reflexivity;
      setoid_rewrite build_certificate_bundle_subst; reflexivity.
Qed.

Definition global_bundle_functional {A B} (d : ClosedCastEq A B) : Tm :=
  let BT := certificate_bundle_ty d in
  let self := tm_app (var 1) unit in
  abs (tarr tunit BT)
      (abs tunit (build_certificate_bundle d self cast_terms_nil)).

(** The only fixed point in the global interpreter. *)
Definition tied_certificate_bundle {A B} (d : ClosedCastEq A B) : Tm :=
  let BT := certificate_bundle_ty d in
  tm_app (tm_app (ufix tunit BT) (global_bundle_functional d)) unit.

(** The recursive thunk exposed after the outer [ufix] beta step.  Naming it
    makes the operational fixed-point equation usable without identifying
    intensional syntax modulo a reduction step. *)
Definition recursive_certificate_bundle {A B} (d : ClosedCastEq A B) : Tm :=
  let BT := certificate_bundle_ty d in
  tm_app (ufix₁ (global_bundle_functional d) tunit BT) unit.

(** The beta-delayed self reference that is captured underneath the bundle's
    cast lambdas by one operational unfolding of [ufix]. *)
Definition delayed_recursive_certificate_bundle {A B}
  (d : ClosedCastEq A B) : Tm :=
  let BT := certificate_bundle_ty d in
  let loop := ufix₁ (global_bundle_functional d) tunit BT in
  tm_app (abs tunit (tm_app loop (var 0))) unit.

Definition compile_global_pair {A B} (d : ClosedCastEq A B) : Tm :=
  certificate_root d (tied_certificate_bundle d) cast_terms_nil.

Definition compile_global_up {A B} (d : ClosedCastEq A B) : Tm :=
  pair_up (compile_global_pair d).

Definition compile_global_down {A B} (d : ClosedCastEq A B) : Tm :=
  pair_down (compile_global_pair d).

Lemma compile_global_up_unfold {A B} (d : ClosedCastEq A B) :
  compile_global_up d =
  pair_up (certificate_root d (tied_certificate_bundle d) cast_terms_nil).
Proof. reflexivity. Qed.

Lemma certificate_bundle_ty_valid {H A B} (d : CastEq H A B) :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  ValidTy (certificate_bundle_ty d)
with node_bundle_ty_valid {H A B} (node : CastNode H A B) :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  ValidTy (node_bundle_ty node).
Proof.
  - destruct d as [H A B m|H A B node]; intros VH VA VB; cbn.
    + eauto with tyvalid cty simple_contr_rec.
    + apply ValidTy_prod.
      * now apply cast_pair_ty_valid.
      * now apply node_bundle_ty_valid.
  - destruct node as
      [H|H|H x
      |H A1 A2 B1 B2 l r
      |H A1 A2 B1 B2 l r
      |H A1 A2 B1 B2 l r
      |H body B child
      |H A body nmu child]; intros VH VA VB; cbn.
    + eauto with tyvalid cty simple_contr_rec.
    + eauto with tyvalid cty simple_contr_rec.
    + eauto with tyvalid cty simple_contr_rec.
    + apply ValidTy_invert_arr in VA as [VA1 VA2].
      apply ValidTy_invert_arr in VB as [VB1 VB2].
      apply ValidTy_prod.
      * eapply certificate_bundle_ty_valid; eauto.
        apply pair_env_valid_cons; [now apply ValidTy_arr|now apply ValidTy_arr|exact VH].
      * eapply certificate_bundle_ty_valid; eauto.
        apply pair_env_valid_cons; [now apply ValidTy_arr|now apply ValidTy_arr|exact VH].
    + apply ValidTy_invert_prod in VA as [VA1 VA2].
      apply ValidTy_invert_prod in VB as [VB1 VB2].
      apply ValidTy_prod.
      * eapply certificate_bundle_ty_valid; eauto.
        apply pair_env_valid_cons; [now apply ValidTy_prod|now apply ValidTy_prod|exact VH].
      * eapply certificate_bundle_ty_valid; eauto.
        apply pair_env_valid_cons; [now apply ValidTy_prod|now apply ValidTy_prod|exact VH].
    + apply ValidTy_invert_sum in VA as [VA1 VA2].
      apply ValidTy_invert_sum in VB as [VB1 VB2].
      apply ValidTy_prod.
      * eapply certificate_bundle_ty_valid; eauto.
        apply pair_env_valid_cons; [now apply ValidTy_sum|now apply ValidTy_sum|exact VH].
      * eapply certificate_bundle_ty_valid; eauto.
        apply pair_env_valid_cons; [now apply ValidTy_sum|now apply ValidTy_sum|exact VH].
    + eapply certificate_bundle_ty_valid; eauto.
      * now apply pair_env_valid_cons.
      * now apply ValidTy_unfold_trec.
    + eapply certificate_bundle_ty_valid; eauto.
      * now apply pair_env_valid_cons.
      * now apply ValidTy_unfold_trec.
Qed.

Lemma certificate_root_typing {Γ H A B} (d : CastEq H A B) self rho :
  ⟪ Γ i⊢ self : certificate_bundle_ty d ⟫ ->
  CastTermsTyping Γ H rho ->
  ⟪ Γ i⊢ certificate_root d self rho : cast_pair_ty A B ⟫.
Proof.
  destruct d; cbn; intros Hself Hρ.
  - now apply lookup_cast_typing.
  - exact (@StlcIso.SpecTyping.WtProj1 Γ self (cast_pair_ty A B)
             (node_bundle_ty c) Hself).
Qed.

Lemma certificate_up_typing {Γ H A B} (d : CastEq H A B) self rho :
  ⟪ Γ i⊢ self : certificate_bundle_ty d ⟫ ->
  CastTermsTyping Γ H rho ->
  ⟪ Γ i⊢ certificate_up d self rho : tarr A B ⟫.
Proof. intros Hs Hr. apply pair_up_typing. now apply certificate_root_typing. Qed.

Lemma certificate_down_typing {Γ H A B} (d : CastEq H A B) self rho :
  ⟪ Γ i⊢ self : certificate_bundle_ty d ⟫ ->
  CastTermsTyping Γ H rho ->
  ⟪ Γ i⊢ certificate_down d self rho : tarr B A ⟫.
Proof. intros Hs Hr. apply pair_down_typing. now apply certificate_root_typing. Qed.

Lemma global_node_cast_typing {Γ H A B} (node : CastNode H A B)
  payload_self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ payload_self : node_bundle_ty node ⟫ ->
  CastTermsTyping Γ ((A, B) :: H) rho ->
  ⟪ Γ i⊢ global_node_cast node payload_self rho : cast_pair_ty A B ⟫.
Proof.
  destruct node as
      [H|H|H x
      |H A1 A2 B1 B2 dom cod
      |H A1 A2 B1 B2 fstc sndc
      |H A1 A2 B1 B2 lc rc
      |H body B child
      |H A body nmu child]; intros VH VA VB Hself Hρ; cbn in *.
  - apply WtPair; apply id_cast_typing; assumption.
  - apply WtPair; apply id_cast_typing; assumption.
  - apply WtPair; apply id_cast_typing; assumption.
  - apply ValidTy_invert_arr in VA as [VA1 VA2].
    apply ValidTy_invert_arr in VB as [VB1 VB2].
    assert (Hdomself : ⟪ Γ i⊢ proj₁ payload_self : certificate_bundle_ty dom ⟫)
      by (eapply WtProj1; exact Hself).
    assert (Hcodself : ⟪ Γ i⊢ proj₂ payload_self : certificate_bundle_ty cod ⟫)
      by (eapply WtProj2; exact Hself).
    assert (Hdom := certificate_root_typing dom _ _ Hdomself Hρ).
    assert (Hcod := certificate_root_typing cod _ _ Hcodself Hρ).
    assert (HUdom := pair_up_typing Hdom).
    assert (HDdom := pair_down_typing Hdom).
    assert (HUcod := pair_up_typing Hcod).
    assert (HDcod := pair_down_typing Hcod).
    apply WtPair.
    + apply WtAbs; [|now apply ValidTy_arr].
      apply WtAbs; [|exact VB1].
      eapply WtApp.
      * exact (typing_weaken (typing_weaken HUcod)).
      * eapply WtApp.
        -- apply WtVar. constructor. constructor.
        -- eapply WtApp.
           ++ exact (typing_weaken (typing_weaken HDdom)).
           ++ apply WtVar. constructor.
    + apply WtAbs; [|now apply ValidTy_arr].
      apply WtAbs; [|exact VA1].
      eapply WtApp.
      * exact (typing_weaken (typing_weaken HDcod)).
      * eapply WtApp.
        -- apply WtVar. constructor. constructor.
        -- eapply WtApp.
           ++ exact (typing_weaken (typing_weaken HUdom)).
           ++ apply WtVar. constructor.
  - apply ValidTy_invert_prod in VA as [VA1 VA2].
    apply ValidTy_invert_prod in VB as [VB1 VB2].
    assert (Hfstself : ⟪ Γ i⊢ proj₁ payload_self : certificate_bundle_ty fstc ⟫)
      by (eapply WtProj1; exact Hself).
    assert (Hsndself : ⟪ Γ i⊢ proj₂ payload_self : certificate_bundle_ty sndc ⟫)
      by (eapply WtProj2; exact Hself).
    assert (Hfst := certificate_root_typing fstc _ _ Hfstself Hρ).
    assert (Hsnd := certificate_root_typing sndc _ _ Hsndself Hρ).
    assert (HUfst := pair_up_typing Hfst).
    assert (HDfst := pair_down_typing Hfst).
    assert (HUsnd := pair_up_typing Hsnd).
    assert (HDsnd := pair_down_typing Hsnd).
    apply WtPair.
    + apply WtAbs; [|now apply ValidTy_prod]. apply WtPair.
      * eapply WtApp; [exact (typing_weaken HUfst)|].
        eapply WtProj1. apply WtVar. constructor.
      * eapply WtApp; [exact (typing_weaken HUsnd)|].
        eapply WtProj2. apply WtVar. constructor.
    + apply WtAbs; [|now apply ValidTy_prod]. apply WtPair.
      * eapply WtApp; [exact (typing_weaken HDfst)|].
        eapply WtProj1. apply WtVar. constructor.
      * eapply WtApp; [exact (typing_weaken HDsnd)|].
        eapply WtProj2. apply WtVar. constructor.
  - apply ValidTy_invert_sum in VA as [VA1 VA2].
    apply ValidTy_invert_sum in VB as [VB1 VB2].
    assert (Hlself : ⟪ Γ i⊢ proj₁ payload_self : certificate_bundle_ty lc ⟫)
      by (eapply WtProj1; exact Hself).
    assert (Hrself : ⟪ Γ i⊢ proj₂ payload_self : certificate_bundle_ty rc ⟫)
      by (eapply WtProj2; exact Hself).
    assert (Hl := certificate_root_typing lc _ _ Hlself Hρ).
    assert (Hr := certificate_root_typing rc _ _ Hrself Hρ).
    assert (HUl := pair_up_typing Hl).
    assert (HDl := pair_down_typing Hl).
    assert (HUr := pair_up_typing Hr).
    assert (HDr := pair_down_typing Hr).
    apply WtPair.
    + apply WtAbs; [|now apply ValidTy_sum].
      eapply WtCaseof with (τ₁ := A1) (τ₂ := A2) (T := tsum B1 B2);
        eauto with tyvalid.
      * apply WtVar. constructor.
      * eapply WtInl with (τ₂ := B2); [|exact VB2]. eapply WtApp.
        -- exact (typing_weaken (typing_weaken HUl)).
        -- apply WtVar. constructor.
      * eapply WtInr with (τ₁ := B1); [|exact VB1]. eapply WtApp.
        -- exact (typing_weaken (typing_weaken HUr)).
        -- apply WtVar. constructor.
    + apply WtAbs; [|now apply ValidTy_sum].
      eapply WtCaseof with (τ₁ := B1) (τ₂ := B2) (T := tsum A1 A2);
        eauto with tyvalid.
      * apply WtVar. constructor.
      * eapply WtInl with (τ₂ := A2); [|exact VA2]. eapply WtApp.
        -- exact (typing_weaken (typing_weaken HDl)).
        -- apply WtVar. constructor.
      * eapply WtInr with (τ₁ := A1); [|exact VA1]. eapply WtApp.
        -- exact (typing_weaken (typing_weaken HDr)).
        -- apply WtVar. constructor.
  - assert (Hchild := certificate_root_typing child payload_self rho Hself Hρ).
    assert (HU := pair_up_typing Hchild).
    assert (HD := pair_down_typing Hchild).
    apply WtPair.
    + apply WtAbs; [|exact VA]. eapply WtApp.
      * exact (typing_weaken HU).
      * eapply WtUnfold; [apply WtVar; constructor|exact VA].
    + apply WtAbs; [|exact VB]. eapply WtFold; [|exact VA].
      eapply WtApp; [exact (typing_weaken HD)|]. apply WtVar. constructor.
  - assert (Hchild := certificate_root_typing child payload_self rho Hself Hρ).
    assert (HU := pair_up_typing Hchild).
    assert (HD := pair_down_typing Hchild).
    apply WtPair.
    + apply WtAbs; [|exact VA]. eapply WtFold; [|exact VB].
      eapply WtApp; [exact (typing_weaken HU)|]. apply WtVar. constructor.
    + apply WtAbs; [|exact VB]. eapply WtApp.
      * exact (typing_weaken HD).
      * eapply WtUnfold; [apply WtVar; constructor|exact VB].
Qed.

Lemma build_certificate_bundle_typing {Γ H A B} (d : CastEq H A B)
  self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ self : certificate_bundle_ty d ⟫ ->
  CastTermsTyping Γ H rho ->
  ⟪ Γ i⊢ build_certificate_bundle d self rho : certificate_bundle_ty d ⟫
with build_node_bundle_typing {Γ H A B} (node : CastNode H A B)
  payload_self rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ payload_self : node_bundle_ty node ⟫ ->
  CastTermsTyping Γ ((A, B) :: H) rho ->
  ⟪ Γ i⊢ build_node_bundle node payload_self rho : node_bundle_ty node ⟫.
Proof.
  - destruct d as [H A B m|H A B node]; intros VH VA VB Hself Hρ; cbn.
    + apply WtUnit.
    + assert (Hroot : ⟪ Γ i⊢ proj₁ self : cast_pair_ty A B ⟫)
        by (eapply WtProj1; exact Hself).
      assert (Hpayload : ⟪ Γ i⊢ proj₂ self : node_bundle_ty node ⟫)
        by (eapply WtProj2; exact Hself).
      assert (Hρ' : CastTermsTyping Γ ((A, B) :: H)
                       (cast_terms_cons (proj₁ self) rho)).
      { now apply cast_terms_typing_cons. }
      apply WtPair.
      * eapply global_node_cast_typing; eauto.
      * eapply build_node_bundle_typing; eauto.
  - destruct node as
      [H|H|H x
      |H A1 A2 B1 B2 l r
      |H A1 A2 B1 B2 l r
      |H A1 A2 B1 B2 l r
      |H body B child
      |H A body nmu child]; intros VH VA VB Hself Hρ; cbn in *.
    + apply WtUnit.
    + apply WtUnit.
    + apply WtUnit.
    + apply ValidTy_invert_arr in VA as [VA1 VA2].
      apply ValidTy_invert_arr in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H)).
      { apply pair_env_valid_cons; [now apply ValidTy_arr|now apply ValidTy_arr|exact VH]. }
      apply WtPair.
      * eapply build_certificate_bundle_typing; eauto.
        eapply WtProj1; exact Hself.
      * eapply build_certificate_bundle_typing; eauto.
        eapply WtProj2; exact Hself.
    + apply ValidTy_invert_prod in VA as [VA1 VA2].
      apply ValidTy_invert_prod in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H)).
      { apply pair_env_valid_cons; [now apply ValidTy_prod|now apply ValidTy_prod|exact VH]. }
      apply WtPair.
      * eapply build_certificate_bundle_typing; eauto.
        eapply WtProj1; exact Hself.
      * eapply build_certificate_bundle_typing; eauto.
        eapply WtProj2; exact Hself.
    + apply ValidTy_invert_sum in VA as [VA1 VA2].
      apply ValidTy_invert_sum in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H)).
      { apply pair_env_valid_cons; [now apply ValidTy_sum|now apply ValidTy_sum|exact VH]. }
      apply WtPair.
      * eapply build_certificate_bundle_typing; eauto.
        eapply WtProj1; exact Hself.
      * eapply build_certificate_bundle_typing; eauto.
        eapply WtProj2; exact Hself.
    + assert (VU : ValidTy body[beta1 (trec body)])
        by now apply ValidTy_unfold_trec.
      assert (VH' : PairEnvValid ((trec body, B) :: H))
        by now apply pair_env_valid_cons.
      eapply build_certificate_bundle_typing; eauto.
    + assert (VU : ValidTy body[beta1 (trec body)])
        by now apply ValidTy_unfold_trec.
      assert (VH' : PairEnvValid ((A, trec body) :: H))
        by now apply pair_env_valid_cons.
      eapply build_certificate_bundle_typing; eauto.
Qed.

Lemma global_bundle_functional_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ global_bundle_functional d :
      tarr (tarr tunit (certificate_bundle_ty d))
           (tarr tunit (certificate_bundle_ty d)) ⟫.
Proof.
  intros VA VB. unfold global_bundle_functional.
  apply WtAbs.
  - apply WtAbs.
    + eapply build_certificate_bundle_typing.
      * apply pair_env_valid_nil.
      * exact VA.
      * exact VB.
      * eapply WtApp.
        -- apply WtVar. constructor. constructor.
        -- apply WtUnit.
      * apply cast_terms_typing_nil.
    + eauto with tyvalid cty simple_contr_rec.
  - apply ValidTy_arr.
    + eauto with tyvalid cty simple_contr_rec.
    + eapply certificate_bundle_ty_valid; eauto using pair_env_valid_nil.
Qed.

Theorem tied_certificate_bundle_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ tied_certificate_bundle d : certificate_bundle_ty d ⟫.
Proof.
  intros VA VB. unfold tied_certificate_bundle.
  eapply WtApp.
  - eapply WtApp.
    + apply ufix_typing.
      * eauto with tyvalid cty simple_contr_rec.
      * eapply certificate_bundle_ty_valid; eauto using pair_env_valid_nil.
    + now apply global_bundle_functional_typing.
  - apply WtUnit.
Qed.

Lemma recursive_certificate_bundle_typing {Γ A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ recursive_certificate_bundle d : certificate_bundle_ty d ⟫.
Proof.
  intros VA VB. unfold recursive_certificate_bundle.
  eapply WtApp.
  - eapply ufix₁_typing.
    + eauto with tyvalid cty simple_contr_rec.
    + eapply certificate_bundle_ty_valid;
        eauto using pair_env_valid_nil.
    + now apply global_bundle_functional_typing.
  - apply WtUnit.
Qed.

Lemma delayed_recursive_certificate_bundle_typing {Γ A B}
  (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ delayed_recursive_certificate_bundle d :
      certificate_bundle_ty d ⟫.
Proof.
  intros VA VB. unfold delayed_recursive_certificate_bundle.
  eapply WtApp.
  - apply WtAbs.
    + eapply WtApp.
      * eapply ufix₁_typing.
        -- eauto with tyvalid cty simple_contr_rec.
        -- eapply certificate_bundle_ty_valid;
             eauto using pair_env_valid_nil.
        -- now apply global_bundle_functional_typing.
      * apply WtVar. constructor.
    + eauto with tyvalid cty simple_contr_rec.
  - apply WtUnit.
Qed.

Theorem compile_global_pair_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ compile_global_pair d : cast_pair_ty A B ⟫.
Proof.
  intros VA VB. unfold compile_global_pair.
  apply certificate_root_typing.
  - now apply tied_certificate_bundle_typing.
  - apply cast_terms_typing_nil.
Qed.

Theorem compile_global_up_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ compile_global_up d : tarr A B ⟫.
Proof.
  intros VA VB. apply pair_up_typing. now apply compile_global_pair_typing.
Qed.

Theorem compile_global_down_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ compile_global_down d : tarr B A ⟫.
Proof.
  intros VA VB. apply pair_down_typing. now apply compile_global_pair_typing.
Qed.
