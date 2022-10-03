Require Export Db.Inst.
Require Export Db.Lemmas.
Require Export Db.WellScoping.
Require Export StlcEqui.SpecSyntax.
Require Export StlcEqui.SpecAnnot.
Require Export StlcEqui.Inst.

#[export]
#[refine] Instance vrTmA : Vr TmA := {| vr := ea_var |}.
Proof. inversion 1; auto. Defined.

(* #[export] *)
(* #[refine] Instance vrTy : Vr Ty := {| vr := tvar |}. *)
(* Proof. inversion 1; auto. Defined. *)

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

Module TmAKit <: Kit.

  Definition TM := TmA.
  Definition inst_vr := vrTmA.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y TmA}.

    #[refine] Global Instance inst_ap : Ap TmA Y := {| ap := apTmA |}.
    Proof.
      induction x; crush; now f_equal.
    Defined.

    #[refine] Global Instance inst_ap_vr : LemApVr TmA Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  #[export]
  #[refine] Instance inst_ap_inj: LemApInj TmA Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  #[export]
  #[refine] Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TmA}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z TmA}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYTmAZ: LemApLift Y Z TmA} :
    LemApComp TmA Y Z := {}.
  Proof. induction x; crush; f_equal; eauto. Qed.

  #[export]
  #[refine] Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TmA} :
    LemApLiftSub TmA Y := {}.
  Proof. induction t; crush; f_equal; eauto. Qed.

  Lemma inst_ap_ixComp (t: TmA) :
    ∀ (ξ: Sub Ix) (ζ: Sub TmA), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
  Proof. pose proof up_comp_lift. induction t; crush; f_equal; eauto. Qed.

End TmAKit.

Module InstTmA := Inst TmAKit.
Export InstTmA. (* Export for shorter names. *)

Module InstTy := Inst TyKit.
Export InstTy. (* Export for shorter names. *)

(* Instance wsVrTmA: WsVr TmA. *)
(* Proof. *)
(*   constructor. *)
(*   - now constructor. *)
(*   - now inversion 1. *)
(* Qed. *)

(* Section Application. *)

(*   Context {Y: Type}. *)
(*   Context {vrY : Vr Y}. *)
(*   Context {wkY: Wk Y}. *)
(*   Context {liftY: Lift Y TmA}. *)
(*   Context {wsY: Ws Y}. *)
(*   Context {wsVrY: WsVr Y}. *)
(*   Context {wsWkY: WsWk Y}. *)
(*   Context {wsLiftY: WsLift Y TmA}. *)

(*   Hint Resolve wsLift : ws. *)
(*   Hint Resolve wsSub_up : ws. *)


(*   Global Instance wsApTmA : WsAp TmA Y. *)
(*   Proof. *)
(*     constructor. *)
(*     - intros ξ γ δ t wξ wt; revert ξ δ wξ. *)
(*       induction wt; intros ξ δ wξ; crush; *)
(*       try econstructor; *)
(*       try match goal with *)
(*             | |- wsTmA ?δ ?t => *)
(*               change (wsTmA δ t) with ⟨ δ ⊢ t ⟩ *)
(*           end; eauto with ws. *)
(*     - intros γ t wt. *)
(*       induction wt; crush. *)
(*       + apply IHwt; inversion 1; crush. *)
(*       + apply IHwt2; inversion 1; crush. *)
(*       + apply IHwt3; inversion 1; crush. *)
(*   Qed. *)
(* End Application. *)

(* Instance wsWkTmA: WsWk TmA. *)
(* Proof. *)
(*   constructor; crush. *)
(*   - refine (wsAp _ H); eauto. *)
(*     constructor; eauto. *)
(* Qed. *)
(* (*   - admit. *) *)
(* (*     (* induction x; cbn in H; inversion H. *) *) *)
(* (*     (* + change (wk i) with (S i) in *. *) *) *)
(* (*     (*   inversion H1; subst. eapply WsVar; eassumption. *) *) *)
(* (*     (* +  *) *) *)
(* (* Admitted. *) *)
