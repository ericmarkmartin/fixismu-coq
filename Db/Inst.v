Require Export Db.Spec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Module Type Kit.

  Parameter TM: Type.
  #[export]
  Declare Instance inst_vr: Vr TM.
  #[export]
  Declare Instance inst_ap: ∀ Y {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM}, Ap TM Y.

  #[export]
  Declare Instance inst_ap_inj: LemApInj (apXY := inst_ap Ix) TM Ix.
  #[export]
  Declare Instance inst_ap_vr:
    ∀ Y {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM}, LemApVr TM Y.
  Parameter inst_ap_comp:
    ∀ Y Z {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM} {vrZ: Vr Z} {wkZ: Wk Z}
      {liftZ: Lift Z TM} {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
      {apLiftYZTM: LemApLift Y Z TM}, LemApComp TM Y Z.
  Parameter inst_ap_liftSub:
    ∀ Y {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM}, LemApLiftSub TM Y.
  Parameter inst_ap_ixComp:
    ∀ (t: TM) (ξ: Sub Ix) (ζ: Sub TM), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].

End Kit.

Module Inst (kit: Kit).

  Local Ltac crush :=
    intros; cbn in * |-;
    repeat
      (cbn;
       repeat crushDbSyntaxMatchH;
       rewrite ?ap_vr, ?ap_comp);
    auto.

  Import kit.
  #[export]
  Existing Instance inst_ap.
  #[export]
  Existing Instance inst_ap_vr.
  #[export]
  Existing Instance inst_ap_inj.
  #[export]
  Existing Instance inst_ap_comp.
  #[export]
  Existing Instance inst_ap_liftSub.


  #[export]
  Instance inst_apTMZTM {Z} {vrZ: Vr Z} {apTMZ: Ap TM Z} :
    LemApLift TM Z TM := λ _ _, eq_refl.
  #[export]
  Instance inst_apLiftIxIx: LemApLift Ix Ix TM := ap_vr.

  #[export]
  #[refine] Instance compUpTMIx: LemCompUp TM Ix := {}.
  Proof. intros; extensionality i; destruct i; crush. Qed.

  #[export]
  Instance inst_wkApIx: LemApWk TM Ix := λ _, eq_refl.

  #[export]
  #[refine] Instance compUpTM: LemCompUp TM TM := {}.
  Proof.
    intros; extensionality i; destruct i; crush.
    rewrite inst_ap_ixComp; f_equal.
    extensionality j; destruct j; crush.
  Qed.

  #[export]
  #[refine] Instance wkApTM: LemApWk TM TM := {}.
  Proof.
    crush.
    rewrite  <- ap_liftSub.
    f_equal.
    extensionality i; crush.
  Qed.

  (* Instance sbTM: Subst TM := {}. *)

  (* Automatically populate the infrastructure database for type TM with lemmas
     for which the rewrite direction is certain. *)
  (* Hint Rewrite (apply_wkm_comm TM Ix) : infrastructure. *)
  (* Hint Rewrite (apply_wkm_beta1_cancel TM TM) : infrastructure. *)
  (* Hint Rewrite (apply_beta1_comm TM TM) : infrastructure. *)

  (* Hint Rewrite (apply_wkm_up_comm TM Ix) : infrastructure. *)
  (* Hint Rewrite (apply_wkm_beta1_up_cancel TM TM) : infrastructure. *)
  (* Hint Rewrite (apply_beta1_up_comm TM TM) : infrastructure. *)

  (* Hint Rewrite (apply_wkm_up2_comm TM Ix) : infrastructure. *)
  (* Hint Rewrite (apply_wkm_beta1_up2_cancel TM TM) : infrastructure. *)
  (* Hint Rewrite (apply_beta1_up2_comm TM TM) : infrastructure. *)

  (* Hint Rewrite (apply_wkm_ups_comm TM Ix) : infrastructure. *)
  (* Hint Rewrite (apply_wkm_beta1_ups_cancel TM TM) : infrastructure. *)
  (* Hint Rewrite (apply_beta1_ups_comm TM TM) : infrastructure. *)

  (* Hint Rewrite (ap_liftSub' TM TM) : infrastructure. *)
  (* Hint Rewrite (up_liftSub TM) : infrastructure. *)
  (* Hint Rewrite (liftSub_wkm TM) : infrastructure. *)
  (* Hint Rewrite (liftSub_wkms TM) : infrastructure. *)

  (* Hint Rewrite (up_wk TM) : infrastructure. *)
  (* Hint Rewrite (wk_ap TM) : infrastructure. *)

  (* Set Printing  Implicit. *)
  (* Unset Printing Notations. *)
  (* Print Rewrite HintDb infrastructure. *)


End Inst.
