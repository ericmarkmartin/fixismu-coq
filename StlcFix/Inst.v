Require Export Db.Inst.
Require Export Db.Lemmas.
Require Export Db.WellScoping.
Require Export StlcFix.SpecSyntax.

#[refine] Instance vrTm : Vr Tm := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     rewrite ?comp_up, ?up_liftSub, ?up_comp_lift
    );
  auto.

Module TmKit <: Kit.

  Definition TM := Tm.
  Definition inst_vr := vrTm.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Tm}.

    #[refine] Global Instance inst_ap : Ap Tm Y := {| ap := apTm |}.
    Proof. induction x; crush. Defined.

    #[refine] Global Instance inst_ap_vr : LemApVr Tm Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  #[refine] Instance inst_ap_inj: LemApInj Tm Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  #[refine] Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Tm}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z Tm}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYTmZ: LemApLift Y Z Tm} :
    LemApComp Tm Y Z := {}.
  Proof. induction x; crush. Qed.

  #[refine] Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Tm} :
    LemApLiftSub Tm Y := {}.
  Proof. induction t; crush. Qed.

  Lemma inst_ap_ixComp (t: Tm) :
    ∀ (ξ: Sub Ix) (ζ: Sub Tm), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
  Proof. pose proof up_comp_lift. induction t; crush. Qed.

End TmKit.

Module InstTm := Inst TmKit.
Export InstTm. (* Export for shorter names. *)

Instance wsVrTm: WsVr Tm.
Proof.
  constructor.
  - now constructor.
  - now inversion 1.
Qed.

Section Application.

  Context {Y: Type}.
  Context {vrY : Vr Y}.
  Context {wkY: Wk Y}.
  Context {liftY: Lift Y Tm}.
  Context {wsY: Ws Y}.
  Context {wsVrY: WsVr Y}.
  Context {wsWkY: WsWk Y}.
  Context {wsLiftY: WsLift Y Tm}.

  Hint Resolve wsLift : ws.
  Hint Resolve wsSub_up : ws.


  Global Instance wsApTm : WsAp Tm Y.
  Proof.
    constructor.
    - intros ξ γ δ t wξ wt; revert ξ δ wξ.
      induction wt; intros ξ δ wξ; crush;
      try econstructor;
      try match goal with
            | |- wsTm ?δ ?t =>
              change (wsTm δ t) with ⟨ δ ⊢ t ⟩
          end; eauto with ws.
    - intros γ t wt.
      induction wt; crush.
      + apply IHwt; inversion 1; crush.
      + apply IHwt2; inversion 1; crush.
      + apply IHwt3; inversion 1; crush.
  Qed.
End Application.

Instance wsWkTm: WsWk Tm.
Proof.
  constructor; crush.
  - refine (wsAp _ H); eauto.
    constructor; eauto.
Qed.
(*   - admit. *)
(*     (* induction x; cbn in H; inversion H. *) *)
(*     (* + change (wk i) with (S i) in *. *) *)
(*     (*   inversion H1; subst. eapply WsVar; eassumption. *) *)
(*     (* +  *) *)
(* Admitted. *)
