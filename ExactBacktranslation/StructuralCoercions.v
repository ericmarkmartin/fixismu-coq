Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.CastCommon.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.Inst.
Require Import StlcIso.Fix.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
From Stdlib Require Import Lists.List.
Import ListNotations.

(** Terms realizing the assumed cast pairs. The head corresponds to the most
    recently introduced equality assumption. *)
(** The environment shape is computed from the type-pair environment.  Unlike
    an indexed inductive list, this nested product has definitionally simple
    head and tail projections. *)
Fixpoint CastTerms (H : PairEnv) : Type :=
  match H with
  | nil => Datatypes.unit
  | _ :: H' => (Tm * CastTerms H')%type
  end.

Definition cast_terms_nil : CastTerms nil := tt.

Definition cast_terms_cons {H A B}
  (t : Tm) (rho : CastTerms H) : CastTerms ((A, B) :: H) := (t, rho).

(** Pointwise term substitution on a heterogeneous cast environment. *)
Fixpoint subst_cast_terms {H} (zeta : Sub Tm) :
  CastTerms H -> CastTerms H :=
  match H return CastTerms H -> CastTerms H with
  | nil => fun _ => tt
  | _ :: H' => fun rho =>
      ((fst rho)[zeta], subst_cast_terms zeta (snd rho))
  end.

Fixpoint lookup_cast {H A B}
  (m : Assumed H A B) : CastTerms H -> Tm :=
  match m with
  | assumed_here => fun rho => fst rho
  | assumed_there m' => fun rho => lookup_cast m' (snd rho)
  end.

Lemma lookup_cast_subst {H A B} (m : Assumed H A B)
  (rho : CastTerms H) zeta :
  (lookup_cast m rho)[zeta] =
  lookup_cast m (subst_cast_terms zeta rho).
Proof.
  induction m; cbn; auto.
Qed.

Fixpoint weaken_cast_terms {H} : CastTerms H -> CastTerms H :=
  match H return CastTerms H -> CastTerms H with
  | nil => fun _ => tt
  | _ :: H' => fun rho => ((fst rho)[wkm], weaken_cast_terms (snd rho))
  end.

Definition weaken_cast_terms2 {H} (rho : CastTerms H) : CastTerms H :=
  weaken_cast_terms (weaken_cast_terms rho).

Definition pair_up (p : Tm) : Tm := proj₁ p.
Definition pair_down (p : Tm) : Tm := proj₂ p.

(** Compilation is structurally recursive over the finite certificate. A step
    ties its own forward/reverse pair with the repository's ordinary [ufix].
    The recursive pair [self unit] is added to the environment used for child
    certificates. *)
Fixpoint compile_casteq {H A B} (d : CastEq H A B)
  (rho : CastTerms H) {struct d} : Tm :=
  match d in CastEq H0 A0 B0 return CastTerms H0 -> Tm with
  | @ce_back H0 A0 B0 m => fun rho0 => lookup_cast m rho0
  | @ce_step H0 A0 B0 node => fun rho0 =>
      let P := cast_pair_ty A0 B0 in
      let selfP := tm_app (var 1) unit in
      let rho' := cast_terms_cons selfP (weaken_cast_terms2 rho0) in
      let body := compile_castnode node rho' in
      let functional := abs (tarr tunit P) (abs tunit body) in
      tm_app (tm_app (ufix tunit P) functional) unit
  end rho
with compile_castnode {H A B} (node : CastNode H A B)
  (rho : CastTerms ((A, B) :: H)) {struct node} : Tm :=
  match node in CastNode H0 A0 B0
        return CastTerms ((A0, B0) :: H0) -> Tm with
  | cn_unit _ => fun _ => pair (id_cast tunit) (id_cast tunit)
  | cn_bool _ => fun _ => pair (id_cast tbool) (id_cast tbool)
  | cn_var _ x => fun _ => pair (id_cast (tvar x)) (id_cast (tvar x))
  | cn_arr _ A1 A2 B1 B2 dom cod => fun rho0 =>
      let dp := compile_casteq dom rho0 in
      let cp := compile_casteq cod rho0 in
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
  | cn_prod _ A1 A2 B1 B2 fstc sndc => fun rho0 =>
      let fp := compile_casteq fstc rho0 in
      let sp := compile_casteq sndc rho0 in
      pair
        (abs (tprod A1 A2)
          (pair
            (tm_app (pair_up fp)[wkm] (proj₁ (var 0)))
            (tm_app (pair_up sp)[wkm] (proj₂ (var 0)))))
        (abs (tprod B1 B2)
          (pair
            (tm_app (pair_down fp)[wkm] (proj₁ (var 0)))
            (tm_app (pair_down sp)[wkm] (proj₂ (var 0)))))
  | cn_sum _ A1 A2 B1 B2 lc rc => fun rho0 =>
      let lp := compile_casteq lc rho0 in
      let rp := compile_casteq rc rho0 in
      pair
        (abs (tsum A1 A2)
          (caseof (var 0)
            (inl (tm_app (pair_up lp)[wkm][wkm] (var 0)))
            (inr (tm_app (pair_up rp)[wkm][wkm] (var 0)))))
        (abs (tsum B1 B2)
          (caseof (var 0)
            (inl (tm_app (pair_down lp)[wkm][wkm] (var 0)))
            (inr (tm_app (pair_down rp)[wkm][wkm] (var 0)))))
  | cn_mu_l _ body B child => fun rho0 =>
      let cp := compile_casteq child rho0 in
      pair
        (abs (trec body)
          (tm_app (pair_up cp)[wkm] (unfold_ (var 0))))
        (abs B
          (fold_ (tm_app (pair_down cp)[wkm] (var 0))))
  | cn_mu_r _ A body _ child => fun rho0 =>
      let cp := compile_casteq child rho0 in
      pair
        (abs A
          (fold_ (tm_app (pair_up cp)[wkm] (var 0))))
        (abs (trec body)
          (tm_app (pair_down cp)[wkm] (unfold_ (var 0))))
  end rho.

Definition compile_closed_pair {A B} (d : ClosedCastEq A B) : Tm :=
  compile_casteq d cast_terms_nil.

Definition compile_closed_up {A B} (d : ClosedCastEq A B) : Tm :=
  pair_up (compile_closed_pair d).

Definition compile_closed_down {A B} (d : ClosedCastEq A B) : Tm :=
  pair_down (compile_closed_pair d).

Lemma compile_closed_up_unfold {A B} (d : ClosedCastEq A B) :
  compile_closed_up d = proj₁ (compile_casteq d cast_terms_nil).
Proof. reflexivity. Qed.

Lemma compile_closed_down_unfold {A B} (d : ClosedCastEq A B) :
  compile_closed_down d = proj₂ (compile_casteq d cast_terms_nil).
Proof. reflexivity. Qed.

Fixpoint CastTermsTyping (Γ : Env) (H : PairEnv) : CastTerms H -> Prop :=
  match H return CastTerms H -> Prop with
  | nil => fun _ => True
  | (A, B) :: H' => fun rho =>
      ⟪ Γ i⊢ fst rho : cast_pair_ty A B ⟫ /\
      CastTermsTyping Γ H' (snd rho)
  end.

Lemma cast_terms_typing_nil Γ : CastTermsTyping Γ nil cast_terms_nil.
Proof. exact I. Qed.

Lemma cast_terms_typing_cons {H A B Γ t rho} :
  ⟪ Γ i⊢ t : cast_pair_ty A B ⟫ ->
  CastTermsTyping Γ H rho ->
  CastTermsTyping Γ ((A, B) :: H) (cast_terms_cons t rho).
Proof. split; assumption. Qed.

Definition PairEnvValid (H : PairEnv) : Prop :=
  forall A B, Assumed H A B -> ValidTy A /\ ValidTy B.

Lemma pair_env_valid_nil : PairEnvValid nil.
Proof. intros A B m. inversion m. Qed.

Lemma pair_env_valid_cons {H A B} :
  ValidTy A -> ValidTy B -> PairEnvValid H ->
  PairEnvValid ((A, B) :: H).
Proof.
  intros VA VB VH X Y m. inversion m; subst.
  - split; assumption.
  - eauto.
Qed.

Lemma cast_pair_ty_valid {A B} :
  ValidTy A -> ValidTy B -> ValidTy (cast_pair_ty A B).
Proof.
  intros VA VB. unfold cast_pair_ty.
  eauto with tyvalid.
Qed.

Lemma lookup_cast_typing {Γ H A B} (m : Assumed H A B) rho :
  CastTermsTyping Γ H rho ->
  ⟪ Γ i⊢ lookup_cast m rho : cast_pair_ty A B ⟫.
Proof.
  revert rho. induction m; intros rho Hρ; cbn in *.
  - exact (proj1 Hρ).
  - apply IHm. exact (proj2 Hρ).
Qed.

Lemma cast_terms_typing_weaken {Γ H rho U} :
  CastTermsTyping Γ H rho ->
  CastTermsTyping (Γ r▻ U) H (weaken_cast_terms rho).
Proof.
  revert rho. induction H as [|[A B] H IH]; intros rho Hρ; cbn in *.
  - exact I.
  - split.
    + now apply typing_weaken, Hρ.
    + apply IH, Hρ.
Qed.

Lemma cast_terms_typing_weaken2 {Γ H rho U V} :
  CastTermsTyping Γ H rho ->
  CastTermsTyping (Γ r▻ U r▻ V) H (weaken_cast_terms2 rho).
Proof.
  intros Hρ. unfold weaken_cast_terms2.
  apply cast_terms_typing_weaken, cast_terms_typing_weaken. exact Hρ.
Qed.

Lemma pair_up_typing {Γ p A B} :
  ⟪ Γ i⊢ p : cast_pair_ty A B ⟫ ->
  ⟪ Γ i⊢ pair_up p : tarr A B ⟫.
Proof. intros Hp. unfold pair_up, cast_pair_ty in *. eapply WtProj1; exact Hp. Qed.

Lemma pair_down_typing {Γ p A B} :
  ⟪ Γ i⊢ p : cast_pair_ty A B ⟫ ->
  ⟪ Γ i⊢ pair_down p : tarr B A ⟫.
Proof. intros Hp. unfold pair_down, cast_pair_ty in *. eapply WtProj2; exact Hp. Qed.

Lemma compile_casteq_typing {Γ H A B} (d : CastEq H A B) rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  CastTermsTyping Γ H rho ->
  ⟪ Γ i⊢ compile_casteq d rho : cast_pair_ty A B ⟫
with compile_castnode_typing {Γ H A B} (node : CastNode H A B) rho :
  PairEnvValid H -> ValidTy A -> ValidTy B ->
  CastTermsTyping Γ ((A, B) :: H) rho ->
  ⟪ Γ i⊢ compile_castnode node rho : cast_pair_ty A B ⟫.
Proof.
  - destruct d as [H A B m|H A B node]; intros VH VA VB Hρ; cbn.
    + now apply lookup_cast_typing.
    + set (P := cast_pair_ty A B).
      assert (VP : ValidTy P) by (subst P; now apply cast_pair_ty_valid).
      eapply WtApp.
      * eapply WtApp.
        -- apply ufix_typing; [eauto with tyvalid|exact VP].
        -- apply WtAbs.
           ++ apply WtAbs.
              ** apply compile_castnode_typing.
                 --- exact VH.
                 --- exact VA.
                 --- exact VB.
                 --- apply cast_terms_typing_cons.
                     +++ unfold P. eapply WtApp.
                         *** apply WtVar. constructor. constructor.
                         *** apply WtUnit.
                     +++ exact (cast_terms_typing_weaken2 Hρ).
              ** eauto with tyvalid.
           ++ apply ValidTy_arr; [eauto with tyvalid|exact VP].
      * apply WtUnit.
  - destruct node as
      [H|H|H x
      |H A1 A2 B1 B2 dom cod
      |H A1 A2 B1 B2 fstc sndc
      |H A1 A2 B1 B2 lc rc
      |H body B child
      |H A body nmu child]; intros VH VA VB Hρ; cbn.
    + apply WtPair; apply id_cast_typing; assumption.
    + apply WtPair; apply id_cast_typing; assumption.
    + apply WtPair; apply id_cast_typing; assumption.
    + apply ValidTy_invert_arr in VA as [VA1 VA2].
      apply ValidTy_invert_arr in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tarr A1 A2, tarr B1 B2) :: H)).
      { apply pair_env_valid_cons; [now apply ValidTy_arr|now apply ValidTy_arr|exact VH]. }
      assert (Hdom := @compile_casteq_typing Γ _ _ _ dom rho VH' VA1 VB1 Hρ).
      assert (Hcod := @compile_casteq_typing Γ _ _ _ cod rho VH' VA2 VB2 Hρ).
      assert (HUdom := pair_up_typing Hdom).
      assert (HDdom := pair_down_typing Hdom).
      assert (HUcod := pair_up_typing Hcod).
      assert (HDcod := pair_down_typing Hcod).
      apply WtPair.
      * apply WtAbs; [|now apply ValidTy_arr].
        apply WtAbs; [|exact VB1].
        eapply WtApp.
        -- exact (typing_weaken (typing_weaken HUcod)).
        -- eapply WtApp.
           ++ apply WtVar. constructor. constructor.
           ++ eapply WtApp.
              ** exact (typing_weaken (typing_weaken HDdom)).
              ** apply WtVar. constructor.
      * apply WtAbs; [|now apply ValidTy_arr].
        apply WtAbs; [|exact VA1].
        eapply WtApp.
        -- exact (typing_weaken (typing_weaken HDcod)).
        -- eapply WtApp.
           ++ apply WtVar. constructor. constructor.
           ++ eapply WtApp.
              ** exact (typing_weaken (typing_weaken HUdom)).
              ** apply WtVar. constructor.
    + apply ValidTy_invert_prod in VA as [VA1 VA2].
      apply ValidTy_invert_prod in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tprod A1 A2, tprod B1 B2) :: H)).
      { apply pair_env_valid_cons; [now apply ValidTy_prod|now apply ValidTy_prod|exact VH]. }
      assert (Hfst := @compile_casteq_typing Γ _ _ _ fstc rho VH' VA1 VB1 Hρ).
      assert (Hsnd := @compile_casteq_typing Γ _ _ _ sndc rho VH' VA2 VB2 Hρ).
      assert (HUfst := pair_up_typing Hfst).
      assert (HDfst := pair_down_typing Hfst).
      assert (HUsnd := pair_up_typing Hsnd).
      assert (HDsnd := pair_down_typing Hsnd).
      apply WtPair.
      * apply WtAbs; [|now apply ValidTy_prod]. apply WtPair.
        -- eapply WtApp; [exact (typing_weaken HUfst)|].
           eapply WtProj1. apply WtVar. constructor.
        -- eapply WtApp; [exact (typing_weaken HUsnd)|].
           eapply WtProj2. apply WtVar. constructor.
      * apply WtAbs; [|now apply ValidTy_prod]. apply WtPair.
        -- eapply WtApp; [exact (typing_weaken HDfst)|].
           eapply WtProj1. apply WtVar. constructor.
        -- eapply WtApp; [exact (typing_weaken HDsnd)|].
           eapply WtProj2. apply WtVar. constructor.
    + apply ValidTy_invert_sum in VA as [VA1 VA2].
      apply ValidTy_invert_sum in VB as [VB1 VB2].
      assert (VH' : PairEnvValid ((tsum A1 A2, tsum B1 B2) :: H)).
      { apply pair_env_valid_cons; [now apply ValidTy_sum|now apply ValidTy_sum|exact VH]. }
      assert (Hl := @compile_casteq_typing Γ _ _ _ lc rho VH' VA1 VB1 Hρ).
      assert (Hr := @compile_casteq_typing Γ _ _ _ rc rho VH' VA2 VB2 Hρ).
      assert (HUl := pair_up_typing Hl).
      assert (HDl := pair_down_typing Hl).
      assert (HUr := pair_up_typing Hr).
      assert (HDr := pair_down_typing Hr).
      apply WtPair.
      * apply WtAbs; [|now apply ValidTy_sum].
        eapply WtCaseof with (τ₁ := A1) (τ₂ := A2) (T := tsum B1 B2);
          eauto with tyvalid.
        -- apply WtVar. constructor.
        -- eapply WtInl with (τ₂ := B2); [|exact VB2]. eapply WtApp.
           ++ exact (typing_weaken (typing_weaken HUl)).
           ++ apply WtVar. constructor.
        -- eapply WtInr with (τ₁ := B1); [|exact VB1]. eapply WtApp.
           ++ exact (typing_weaken (typing_weaken HUr)).
           ++ apply WtVar. constructor.
      * apply WtAbs; [|now apply ValidTy_sum].
        eapply WtCaseof with (τ₁ := B1) (τ₂ := B2) (T := tsum A1 A2);
          eauto with tyvalid.
        -- apply WtVar. constructor.
        -- eapply WtInl with (τ₂ := A2); [|exact VA2]. eapply WtApp.
           ++ exact (typing_weaken (typing_weaken HDl)).
           ++ apply WtVar. constructor.
        -- eapply WtInr with (τ₁ := A1); [|exact VA1]. eapply WtApp.
           ++ exact (typing_weaken (typing_weaken HDr)).
           ++ apply WtVar. constructor.
    + assert (VU : ValidTy body[beta1 (trec body)]).
      { now apply ValidTy_unfold_trec. }
      assert (VH' : PairEnvValid ((trec body, B) :: H)).
      { now apply pair_env_valid_cons. }
      assert (Hchild := @compile_casteq_typing Γ _ _ _ child rho VH' VU VB Hρ).
      assert (HU := pair_up_typing Hchild).
      assert (HD := pair_down_typing Hchild).
      apply WtPair.
      * apply WtAbs; [|exact VA]. eapply WtApp.
        -- exact (typing_weaken HU).
        -- eapply WtUnfold; [apply WtVar; constructor|exact VA].
      * apply WtAbs; [|exact VB]. eapply WtFold; [|exact VA].
        eapply WtApp; [exact (typing_weaken HD)|].
        apply WtVar. constructor.
    + assert (VU : ValidTy body[beta1 (trec body)]).
      { now apply ValidTy_unfold_trec. }
      assert (VH' : PairEnvValid ((A, trec body) :: H)).
      { now apply pair_env_valid_cons. }
      assert (Hchild := @compile_casteq_typing Γ _ _ _ child rho VH' VA VU Hρ).
      assert (HU := pair_up_typing Hchild).
      assert (HD := pair_down_typing Hchild).
      apply WtPair.
      * apply WtAbs; [|exact VA]. eapply WtFold; [|exact VB].
        eapply WtApp; [exact (typing_weaken HU)|].
        apply WtVar. constructor.
      * apply WtAbs; [|exact VB]. eapply WtApp.
        -- exact (typing_weaken HD).
        -- eapply WtUnfold; [apply WtVar; constructor|exact VB].
Qed.

Theorem compile_closed_pair_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ compile_closed_pair d : cast_pair_ty A B ⟫.
Proof.
  intros VA VB. unfold compile_closed_pair.
  eapply compile_casteq_typing; eauto using pair_env_valid_nil,
    cast_terms_typing_nil.
Qed.

Theorem compile_closed_up_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ compile_closed_up d : tarr A B ⟫.
Proof.
  intros VA VB. apply pair_up_typing.
  now apply compile_closed_pair_typing.
Qed.

Theorem compile_closed_down_typing {Γ A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ Γ i⊢ compile_closed_down d : tarr B A ⟫.
Proof.
  intros VA VB. apply pair_down_typing.
  now apply compile_closed_pair_typing.
Qed.
