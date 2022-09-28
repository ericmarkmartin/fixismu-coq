Require Export Db.Inst.
Require Export Db.Lemmas.
Require Export Db.WellScoping.

Require Export LogRelIE.PseudoTypeIE.

#[refine] Instance vrPTy : Vr PTy := {| vr := ptvar |}.
Proof. inversion 1; auto. Defined.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushPTypesMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     rewrite ?comp_up, ?up_liftSub, ?up_comp_lift
    );
  auto.

Module PTyKit <: Kit.

  Definition TM := PTy.
  Definition inst_vr := vrPTy.

  Section Application.

    Context {Y : Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y PTy}.

    #[refine] Global Instance inst_ap : Ap PTy Y := {| ap := apPTy |}.
    Proof.
      induction x; crush.
    Defined.

    #[refine] Global Instance inst_ap_vr : LemApVr PTy Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  #[refine] Instance inst_ap_inj: LemApInj PTy Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  #[refine] Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y PTy}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z PTy}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYTmZ: LemApLift Y Z PTy} :
    LemApComp PTy Y Z := {}.
  Proof. induction x; crush. Qed.

  #[refine] Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y PTy} :
    LemApLiftSub PTy Y := {}.
  Proof. induction t; crush. Qed.

  Lemma inst_ap_ixComp (τ: PTy) :
    ∀ (ξ: Sub Ix) (ζ: Sub PTy), τ[ξ][ζ] = τ[⌈ξ⌉ >=> ζ].
  Proof. pose proof up_comp_lift. induction τ; crush. Qed.

End PTyKit.

Module InstPTy := Inst.Inst PTyKit.
Export InstPTy. (* Export for shorter names. *)

Instance wsVrPTy: WsVr PTy.
Proof.
  constructor.
  - now constructor.
  - now inversion 1.
Qed.

Section ApplicationPTy.

  Context {Y: Type}.
  Context {vrY : Vr Y}.
  Context {wkY: Wk Y}.
  Context {liftY: Lift Y PTy}.
  Context {wsY: Ws Y}.
  Context {wsVrY: WsVr Y}.
  Context {wsWkY: WsWk Y}.
  Context {wsLiftY: WsLift Y PTy}.

  Hint Resolve wsLift : ws.
  Hint Resolve wsSub_up : ws.

  Global Instance wsApPTy : WsAp PTy Y.
  Proof.
    constructor.
    - intros ξ γ δ t wξ wt; revert ξ δ wξ;
      induction wt; intros ξ δ wξ; crush;
      try econstructor;
      try match goal with
            | |- wsPTy ?δ ?t =>
              change (wsPTy δ t) with ⟨ δ ⊢ t ⟩
          end; eauto with ws.
    - intros γ t wt.
      induction wt; crush.
      + apply IHwt; inversion 1; crush.
  Qed.
End ApplicationPTy.

Instance wsWkPTy : WsWk PTy.
Proof.
  constructor; crush.
  - refine (wsAp _ H); eauto.
    constructor; eauto.
Qed.
