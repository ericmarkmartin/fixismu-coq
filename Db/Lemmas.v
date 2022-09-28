Require Export Db.Spec.
Require Export Db.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Create HintDb ws.
Hint Constructors wsIx : ws.

Local Tactic Notation "crush'" tactic(T) :=
  cbn; intros;
  repeat
    (cbn;
     repeat crushDbSyntaxMatchH;
     crushRewriter;
     T);
  auto.

Lemma ap_wks {X Y} {vrX: Vr X} {wkX: Wk X} {vrY: Vr Y} {wkY: Wk Y}
  {apXY: Ap X Y} {apWkXY: LemApWk X Y} {apYY: Ap Y Y}
  {apCompXY: LemApComp X Y Y} {apWkYY: LemApWk Y Y} :
  ∀ (δ: Dom) (x: X), @wks X _ _ δ x = x[@wkms Y _ _ δ].
Proof.
  induction δ; crush' rewrite ?ap_wk, ?ap_comp.
  f_equal; extensionality i;
    cbn; now rewrite ap_wk.
Qed.

Definition ap_id'      := @ap_id.
Definition ap_comp'    := @ap_comp.
Definition ap_vr'      := @ap_vr.
Definition ap_lift'    := @ap_lift.
Definition ap_wk'      := @ap_wk.
Definition ap_wks'     := @ap_wks.
Definition comp_up'    := @comp_up.
Definition lift_vr'    := @lift_vr.
Definition ap_liftSub' := @ap_liftSub.

Arguments ap_id _ _ {_ _} x.
Arguments ap_comp' _ _ _ {_ _ _ _ _ _} x ξ ζ.
Arguments ap_vr' _ _ {_ _ _ _ _} ξ i.
Arguments ap_lift' _ _ _ {_ _ _ _ _ _ _} ζ x.
Arguments ap_wk' _ _ {_ _ _ _ _ _} x.
Arguments ap_wks' _ _ {_ _ _ _ _ _ _ _ _} δ x.
Arguments comp_up' _ _ {_ _ _ _ _ _} ξ ζ.
Arguments lift_vr' _ _ {_ _ _} i.
Arguments ap_liftSub' _ _ {_ _ _ _} t ξ.

(** *** Domains *)

Lemma dunion_assoc (δ₁ δ₂ δ₃: Dom) :
  δ₁ ∪ (δ₂ ∪ δ₃) = (δ₁ ∪ δ₂) ∪ δ₃.
Proof. induction δ₃; cbn; congruence. Qed.

Section Lemmas.

  Local Ltac crush :=
    crush' rewrite ?ap_vr, ?comp_up.

  (* Injectivity is closed under up. *)
  Lemma InjSubIxUp (ξ: Sub Ix) :
    Inj ξ → Inj (ξ ↑).
  Proof.
    intros ? [|?] [|?] ?; cbn in *;
      auto; discriminate.
  Qed.

  (* The following lemmas have more generic versions, but we stick to the
     specialized Ix versions to make proof search easier. *)
  Section Indices.

    Context {X: Type}.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.

    (* Up commutes with lift. *)
    Lemma up_liftSub (ξ: Sub Ix) : ⌈ξ⌉↑ = ⌈ξ↑⌉.
    Proof.
      extensionality i; destruct i;
        cbn; now rewrite ?wk_vr.
    Qed.

    Lemma ups_liftSub (δ: Dom) :
      ∀ (ξ: Sub Ix), ⌈ξ⌉ ↑⋆ δ = ⌈ξ ↑⋆ δ⌉.
    Proof.
      induction δ; cbn; intros.
      - reflexivity.
      - now rewrite ?IHδ, ?up_liftSub.
    Qed.
    (* (* Lifting the identity yields the identity. *) *)
    (* Lemma liftSub_id : ⌈idm Ix⌉ = idm X. *)
    (* Proof. reflexivity. Qed. *)

    (* The weakening substitution is just the lifted
         weakening renaming. *)
    Lemma liftSub_wkm : ⌈@wkm Ix _ _⌉ = @wkm X _ _.
    Proof. extensionality i; crush. Qed.

    Lemma liftSub_wkms (δ: Dom) : ⌈@wkms Ix _ _ δ⌉ = @wkms X _ _ δ.
    Proof.
      extensionality i; induction δ; cbn in *.
      - reflexivity.
      - rewrite <- IHδ; cbn.
        rewrite wk_vr; reflexivity.
    Qed.

    Context {apX : Ap X X}.
    Context {apVrX: LemApVr X X}.

    Lemma liftSub_comp (ξ ζ: Sub Ix) :
      @liftSub Ix _ X _  _ (ξ >=> ζ) = ⌈ξ⌉ >=> ⌈ζ⌉.
    Proof. extensionality i; crush. Qed.

    (* Up commutes with the composition with a lifting
       on the left-hand side .*)
    Lemma up_comp_lift (ξ: Sub Ix) (ζ: Sub X):
      (⌈ξ⌉ >=> ζ)↑ = ⌈ξ↑⌉ >=> ζ↑.
    Proof. extensionality i; destruct i; crush. Qed.

  End Indices.

  Section Weakening.

    Context {X: Type}.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.

    Lemma up_idm : up (idm X) = idm X.
    Proof.
      extensionality i; destruct i; cbn;
        now rewrite ?wk_vr.
    Qed.

    Lemma ups_idm (δ: Dom) : ups (idm X) δ = idm X.
    Proof.
      induction δ; cbn;
        now rewrite ?IHδ, ?up_idm.
    Qed.

    Lemma ups_dunion (ξ: Sub X) δ₁ δ₂ :
       ξ ↑⋆ (δ₁ ∪ δ₂) = (ξ ↑⋆ δ₁) ↑⋆ δ₂.
    Proof. induction δ₂; crush. Qed.

    Lemma ups_up (ξ : Sub X) δ : (ξ ↑⋆ δ) ↑ = ξ ↑⋆ (S δ).
    Proof. reflexivity. Qed.

    Lemma wkm_snoc0 : wkm · vr 0 = idm X.
    Proof. extensionality i; destruct i; crush. Qed.

    Lemma wkms_zero : wkms 0 = idm X.
    Proof. reflexivity. Qed.

    Lemma apply_ups_wks (ξ: Sub X) (δ: Dom) (i: Ix) :
      (ξ ↑⋆ δ) (wks δ i) = wks δ (ξ i).
    Proof. induction δ; crush. Qed.

    Lemma wks_comm δ (ξ: Sub X) :
      ∀ i, wks δ (ξ i) = (ξ ↑⋆ δ) (wks δ i).
    Proof. induction δ; crush. Qed.

    (* Point-wise the weakening substitution is the
       variable injection of the weakening action on
       indices. *)
    Lemma apply_wkms (δ: Dom) (i: Ix) :
      @wkms X _ _ δ i = vr (wks δ i).
    Proof. induction δ; crush. Qed.

    Context {apX : Ap X X}.
    Context {apWkX: LemApWk X X}.

    Lemma apply_up_def_O (ζ: Sub X) :
      (ζ ↑) 0 = vr 0.
    Proof. crush. Qed.

    Lemma apply_up_def_S (ζ: Sub X) :
      ∀ (i: Ix), (ζ ↑) (S i) = (ζ i)[wkm].
    Proof. crush. Qed.

    Lemma up_def (ζ: Sub X) :
      ζ ↑ = (ζ >=> wkm) · vr 0.
    Proof. extensionality i; destruct i; crush. Qed.

    Lemma wkms_succ (δ: Dom) : wkms (S δ) = wkms δ >=> @wkm X _ _.
    Proof. extensionality i; crush. Qed.

  End Weakening.

  Section Application.

    Context {X: Type}.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
    Context {apX : Ap X X}.

    Section Het.
      Context {S: Type}.
      Context {vrS : Vr S}.
      Context {wkS : Wk S}.
      Context {apXS: Ap X S}.

      Lemma comp_id_right (ζ: Sub X) :
        ζ >=> idm S = ζ.
      Proof. extensionality i; crush. Qed.

    End Het.

    Context {apVrX: LemApVr X X}.

    Lemma comp_id_left (ζ: Sub X) :
      @idm X _ >=> ζ = ζ.
    Proof. extensionality i; crush. Qed.

    Lemma comp_snoc (ζ₁ ζ₂: Sub X) t :
      (ζ₁ · t) >=> ζ₂ = (ζ₁ >=> ζ₂) · t[ζ₂].
    Proof. extensionality i; destruct i; reflexivity. Qed.

    Context {apWkX: LemApWk X X}.
    Context {apCompX: LemApComp X X X}.

    Lemma apply_wk_ap (x: X) (ζ: Sub X) :
      (wk x)[ζ] = x[wkm >=> ζ].
    Proof. now rewrite ap_wk. Qed.

    Lemma apply_wks_ap δ (x: X) (ζ: Sub X) :
      (wks δ x)[ζ] = x[wkms δ >=> ζ].
    Proof. now rewrite ap_wks, ap_comp. Qed.

    (* Always try to associate to the left in rewriting. *)
    Lemma comp_assoc (ζ₁ ζ₂ ζ₃: Sub X) :
      ζ₁ >=> (ζ₂ >=> ζ₃) = (ζ₁ >=> ζ₂) >=> ζ₃.
    Proof. extensionality i; crush. Qed.

    Lemma wkms_comm δ (ξ: Sub X) :
      ξ      >=> wkms δ =
      wkms δ >=> (ξ ↑⋆ δ).
    Proof.
      pose proof apply_wkms.
      pose proof apply_ups_wks.
      pose proof ap_wks.
      extensionality i; crush.
    Qed.

    Lemma wkm_comm (ξ: Sub X) :
      ξ   >=> wkm =
      wkm >=> ξ↑.
    Proof. apply (wkms_comm 1). Qed.

    Context {Y: Type}.
    Context {vrY: Vr Y}.
    Context {wkY: Wk Y}.
    Context {apXY: Ap X Y}.
    Context {compUpX : LemCompUp X Y}.

    Lemma comp_ups (ξ: Sub X) (ζ: Sub Y) (δ: Dom) :
      (ξ >=> ζ) ↑⋆ δ  = (ξ ↑⋆ δ) >=> (ζ ↑⋆ δ).
    Proof. induction δ; crush. Qed.

  End Application.

  Section BetaInteraction.

    Context {X : Type}.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
    Context {apX : Ap X X}.
    Context {apWkX: LemApWk X X}.
    Context {apVrX: LemApVr X X}.
    Context {apCompX: LemApComp X X X}.

    Lemma beta_comm δ (ζ₁ ζ₂: Sub X) :
      beta δ ζ₁  >=> ζ₂  =
      (ζ₂ ↑⋆ δ)  >=> beta δ (ζ₁ >=> ζ₂).
    Proof.
      extensionality i. crush. revert ζ₁ ζ₂ i.
      induction δ; crush.
      destruct i; crush.
      rewrite ap_wk, ap_comp; crush.
      f_equal; extensionality j; crush.
    Qed.

    Lemma apply_beta_wks (δ: Dom) :
      ∀ (ξ: Sub X) i, beta δ ξ (wks δ i) = vr i.
    Proof. induction δ; crush. Qed.

    Lemma wkms_beta_cancel δ (ξ: Sub X) :
      wkms δ >=> beta δ ξ = idm X.
    Proof.
      pose proof apply_wkms.
      pose proof apply_beta_wks.
      extensionality i; crush.
    Qed.

    Lemma beta1_comm (x : X) (ζ: Sub X) :
      beta1 x >=> ζ  =
      (ζ ↑)   >=> beta1 x[ζ].
    Proof. apply (beta_comm 1). Qed.

    Lemma wkm_beta1_cancel (x: X) :
      wkm >=> beta1 x = idm X.
    Proof. apply (wkms_beta_cancel 1). Qed.

  End BetaInteraction.

  Section Misc.

    Context {X: Type}.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
    Context {apX: Ap X X}.
    Context {apVrX: LemApVr X X}.

    Lemma wkm_snoc_cancel (ζ: Sub X) t : wkm >=> (ζ · t) = ζ.
    Proof. extensionality i; destruct i; crush. Qed.

    Lemma snoc_eta_red (ζ: Sub X) : (wkm >=> ζ) · ζ 0 = ζ.
    Proof. extensionality i; destruct i; crush. Qed.

  End Misc.

  (* This subsection contains pointful variables of the pointfree lemmas of the
     previous subsection. These are intended to be user-facing. The Db.Inst
     module populates the infrastructure database with these lemmas and some
     others such that it results in a terminating rewrite system (hopefully). *)
  Section Pointful.

    Context {T X: Type}.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
    Context {apTX: Ap T X}.
    Context {apXX: Ap X X}.
    Context {apCompTX: LemApComp T X X}.
    Context {apVrX: LemApVr X X}.
    Context {apWkX: LemApWk X X}.
    Context {apCompX: LemApComp X X X}.
    Context {compUpX: LemCompUp X X}.

    Local Ltac crushPointful :=
      (* (* Convert renamings into substitutions *) *)
      (* rewrite <- ?ap_liftSub; *)
      (* Go point-free *)
      rewrite ?ap_comp; f_equal;
      (* Flow ups outside *)
      rewrite <- ?comp_up, <- ?comp_ups;
      (* (* Convert lifted weakening renaming into weakening substitution *) *)
      (* rewrite <- ?liftSub_wkm; *)
      (* Apply the point-free lemmas *)
      rewrite ?wkm_comm,
              ?wkm_beta1_cancel,
              ?beta1_comm;
      (* Get rid of identities *)
      rewrite ?up_idm, ?ups_idm, ?ap_id;
      reflexivity.

    Lemma apply_wkm_comm (t: T) (ξ: Sub X) :
      t[ξ][wkm] = t[wkm][ξ↑].
    Proof. crushPointful. Qed.

    Lemma apply_wkm_beta1_cancel (t: T) (x: X) :
      t[wkm][beta1 x] = t.
    Proof. crushPointful. Qed.

    Lemma apply_beta1_comm (t: T) (x: X) (ζ: Sub X) :
      t[beta1 x][ζ] = t[ζ↑][beta1 x[ζ]].
    Proof. crushPointful. Qed.

    (* 1 up variant *)
    Lemma apply_wkm_up_comm (t: T) (ξ: Sub X) :
      t[ξ↑][wkm↑] = t[wkm↑][ξ↑↑].
    Proof. crushPointful. Qed.

    Lemma apply_wkm_beta1_up_cancel (t: T) (x: X) :
      t[wkm↑][(beta1 x)↑] = t.
    Proof. crushPointful. Qed.

    Lemma apply_beta1_up_comm (t: T) (x: X) (ζ: Sub X) :
      t[(beta1 x)↑][ζ↑] = t[ζ↑↑][(beta1 x[ζ])↑].
    Proof. crushPointful. Qed.

    (* 2 ups variant *)
    Lemma apply_wkm_up2_comm (t: T) (ξ: Sub X) :
      t[ξ↑↑][wkm↑↑] = t[wkm↑↑][ξ↑↑↑].
    Proof. crushPointful. Qed.

    Lemma apply_wkm_beta1_up2_cancel (t: T) (x: X) :
      t[wkm↑↑][(beta1 x)↑↑] = t.
    Proof. crushPointful. Qed.

    Lemma apply_beta1_up2_comm (t: T) (x: X) (ζ: Sub X) :
      t[(beta1 x)↑↑][ζ↑↑] = t[ζ↑↑↑][(beta1 x[ζ])↑↑].
    Proof. crushPointful. Qed.

    (* δ ups variant *)
    Lemma apply_wkm_ups_comm (δ: Dom) (t: T) (ξ: Sub X) :
      t[ξ ↑⋆ δ][wkm ↑⋆ δ] = t[wkm ↑⋆ δ][ξ↑ ↑⋆ δ].
    Proof. crushPointful. Qed.

    Lemma apply_wkm_beta1_ups_cancel (δ: Dom) (t: T) (x: X) :
      t[wkm ↑⋆ δ][beta1 x ↑⋆ δ] = t.
    Proof. crushPointful. Qed.

    Lemma apply_beta1_ups_comm (δ: Dom) (t: T) (x: X) (ζ: Sub X) :
      t[beta1 x ↑⋆ δ][ζ ↑⋆ δ] = t[ζ↑ ↑⋆ δ][beta1 x[ζ] ↑⋆ δ].
    Proof. crushPointful. Qed.

  End Pointful.

End Lemmas.

Ltac crushDbLemmasMatchH :=
  match goal with
    | H: context[@ap ?X ?X ?vrX _ ?ξ (@vr ?X ?vrX ?i)] |- _ =>
      replace (@ap X X vrX _ ξ (@vr X vrX i)) with (ξ i) in H by
          refine (eq_sym (ap_vr ξ i))

    | |- context[@up ?X ?vrX ?wkX ?ζ O        ] =>
      change (@up X vrX wkX ζ O) with (@vr X vrX O)
    | |- context[@up _ _ ?wkX (idm _)         ] => rewrite (@up_idm _ _ wkX)
    | |- context[@ups _ _ ?wkX (idm _) ?δ     ] => rewrite (@ups_idm _ _ wkX δ)
    | |- context[@ap ?X ?X ?vrX _ ?ξ (@vr ?X ?vrX ?i)] =>
      replace (@ap X X vrX _ ξ (@vr X vrX i)) with (ξ i) by
          refine (eq_sym (ap_vr ξ i))
  end.

Ltac crushDbLemmasRewriteH :=
  rewrite
    ?dunion_assoc, ?ups_dunion, ?comp_up, ?comp_ups,
    (* ?up_liftSub, ?ups_liftSub, *)
    (* ?ap_liftSub, ?liftSub_wkm, ?liftSub_wkms, ?ap_lift, *)
    <- ?ap_comp,
    ?apply_wkm_comm,     ?apply_wkm_beta1_cancel,     ?apply_beta1_comm,
    ?apply_wkm_up_comm,  ?apply_wkm_beta1_up_cancel,  ?apply_beta1_up_comm,
    ?apply_wkm_up2_comm, ?apply_wkm_beta1_up2_cancel, ?apply_beta1_up2_comm,
    ?apply_wkm_ups_comm, ?apply_wkm_beta1_ups_cancel, ?apply_beta1_ups_comm.



    (* Print liftSub_wkm. *)

    (* Unset Printing Notations. *)
    (* Set Printing Implicit. *)
    (* Print ups_idm. *)

    (* | [|- context[(@liftSub Ix _ ?X _ _ ?ξ)↑]] => replace (@liftSub Ix _ X _ _ ξ)↑ *)
    (*                                                 with (@liftSub Ix _ X _ _ ξ↑) by *)
    (*                                                   exact (eq_sym (up_liftSub ξ)) *)
    (* | [|- context[@liftSub Ix _ ?X _ _ ?ξ ↑⋆ ?δ]] => replace (@liftSub Ix _ X _ _ ξ ↑⋆ δ) *)
    (*                                                 with (@liftSub Ix _ X _ _ (ξ ↑⋆ δ)) by *)
    (*                                                   exact (eq_sym (ups_liftSub δ ξ)) *)


  (* liftSub_id : ⌈idm Ix⌉ = idm X. *)
  (* liftSub_wkm  ⌈@wkm Ix _ _⌉ = @wkm X _ _. *)
  (* liftSub_wkms  ⌈@wkms Ix _ _ δ⌉ = @wkms X _ _ δ. *)
