Require Export Db.Inst.
Require Export Db.Lemmas.
Require Export Db.WellScoping.

Require Export RecTypes.SpecTypes.

#[export]
#[refine] Instance vrTy : Vr Ty := {| vr := tvar |}.
Proof. inversion 1; auto. Defined.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushRecTypesMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     rewrite ?comp_up, ?up_liftSub, ?up_comp_lift
    );
  auto.

Module TyKit <: Kit.

  Definition TM := Ty.
  Definition inst_vr := vrTy.

  Section Application.

    Context {Y : Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Ty}.

    #[refine] Global Instance inst_ap : Ap Ty Y := {| ap := apTy |}.
    Proof.
      induction x; crush.
    Defined.

    #[refine] Global Instance inst_ap_vr : LemApVr Ty Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  #[export]
  #[refine] Instance inst_ap_inj: LemApInj Ty Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  #[export]
  #[refine] Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Ty}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z Ty}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYTmZ: LemApLift Y Z Ty} :
    LemApComp Ty Y Z := {}.
  Proof. induction x; crush. Qed.

  #[export]
  #[refine] Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Ty} :
    LemApLiftSub Ty Y := {}.
  Proof. induction t; crush. Qed.

  Lemma inst_ap_ixComp (τ: Ty) :
    ∀ (ξ: Sub Ix) (ζ: Sub Ty), τ[ξ][ζ] = τ[⌈ξ⌉ >=> ζ].
  Proof. pose proof up_comp_lift. induction τ; crush. Qed.

End TyKit.


Module InstTy := Inst TyKit.
Export InstTy. (* Export for shorter names. *)

#[export]
Instance wsVrTy: WsVr Ty.
Proof.
  constructor.
  - now constructor.
  - now inversion 1.
Qed.

Section ApplicationTy.

  Context {Y: Type}.
  Context {vrY : Vr Y}.
  Context {wkY: Wk Y}.
  Context {liftY: Lift Y Ty}.
  Context {wsY: Ws Y}.
  Context {wsVrY: WsVr Y}.
  Context {wsWkY: WsWk Y}.
  Context {wsLiftY: WsLift Y Ty}.

  Hint Resolve wsLift : ws.
  Hint Resolve wsSub_up : ws.


  Global Instance wsApTy : WsAp Ty Y.
  Proof.
    constructor.
    - intros ξ γ δ t wξ wt; revert ξ δ wξ.
      induction wt; intros ξ δ wξ; crush;
      try econstructor;
      try match goal with
            | |- wsTy ?δ ?t =>
              change (wsTy δ t) with ⟨ δ ⊢ t ⟩
          end; eauto with ws.
    - intros γ t wt.
      induction wt; crush.
      + apply IHwt; inversion 1; crush.
  Qed.
End ApplicationTy.

#[export]
Instance wsWkTy : WsWk Ty.
Proof.
  constructor; crush.
  - refine (wsAp _ H); eauto.
    constructor; eauto.
Qed.
