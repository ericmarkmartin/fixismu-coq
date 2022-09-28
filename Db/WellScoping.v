Require Export Db.Spec.
Require Export Db.Lemmas.
Require Coq.Setoids.Setoid.

Section WsSnoc.

  Context {X: Type}.
  Context {wsX: Ws X}.

  Lemma ws_snoc (γ₁ γ₂: Dom) (ζ: Sub X) (x: X) :
    ⟨ ζ : γ₁ => γ₂ ⟩ → ⟨ γ₂ ⊢ x ⟩ → ⟨ (ζ · x) : S γ₁ => γ₂ ⟩.
  Proof.
    intros wζ wx i wi.
    inversion wi; eauto.
  Qed.

  Lemma wsi_snoc_sub (γ₁ γ₂: Dom) (ζ: Sub X) (x: X) :
    ⟨ ζ · x : S γ₁ => γ₂ ⟩ → ⟨ ζ : γ₁ => γ₂ ⟩.
  Proof.
    intros wζ i.
    specialize (wζ (S i)).
    eauto using wsIx.
  Qed.

  Lemma wsi_snoc_tm (γ₁ γ₂: Dom) (ζ: Sub X) (x: X) :
    ⟨ ζ · x : S γ₁ => γ₂ ⟩ → ⟨ γ₂ ⊢ x ⟩.
  Proof.
    intros wζ.
    specialize (wζ 0).
    eauto using wsIx.
  Qed.

End WsSnoc.

Lemma wsiS (γ: Dom) (i: Ix) : S γ ∋ S i → γ ∋ i.
Proof. inversion 1; auto. Qed.

Hint Constructors wsIx : ws.
Hint Resolve wsiS : wsi.
Hint Resolve ws_snoc : ws.
Hint Resolve wsi_snoc_sub : wsi.
Hint Resolve wsi_snoc_tm : wsi.

Ltac crushScopingMatchH :=
  match goal with
    | [ H: 0 ∋ _                 |- _ ] => inversion H
    | [ H: S _    ∋ O            |- _ ] => clear H
    | [ H: S _ ∋ S _             |- _ ] => apply wsiS in H
    | [ H: S _ ∋ wk _             |- _ ] => apply wsiS in H
    (* | [ H: @ws ?X ?wsX (S ?δ) (@wk ?X ?vrX ?wkX ?x) |- _ *)
    (*   ] => apply (@wsiWk X wsX vrX wkX _ δ x) in H *)
    | [H: ∀ i, S _ ∋ i → _ |- _] =>
      let HS := fresh in
      let HO := fresh in
      pose proof (fun i wi => H (S i) (wsS _ i wi)) as HS;
      pose proof (H 0 (ws0 _)) as HO;
      clear H; cbn in HS; cbn in HO
    | [ H: ⟨ _ ⊢ vr _ ⟩ |- _ ] => eapply wsiVr in H

    | [ wi : S _ ∋ ?i
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : S _ ∋ ?i
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- S _ ∋ 0               ] => apply ws0
    | [ |- S _ ∋ S _             ] => apply wsS
    | [ |- S _ ∋ wk _             ] => apply wsS
    | [ |- WsSub _ _ (_ · _)     ] => eapply ws_snoc

    | [ |- ⟨ S _ ⊢ wk _ ⟩ ] => eapply wsWk
    | [ |- ⟨ _ ⊢ vr _ ⟩ ] => eapply wsVr
    (* | [ |- ⟨ _ ⊢ _[_] ⟩ ] => eapply wsAp *)
  end.

Local Ltac crush :=
  cbn; intros;
  repeat
    (cbn;
     repeat crushScopingMatchH;
     repeat crushDbSyntaxMatchH;
     rewrite ?ap_vr in *);
  eauto with typeclass_instances ws;
  eauto with typeclass_instances wsi.

(* Lemma wsIx_plus_dec {γ δ i} (wi: γ ∪ δ ∋ i) : *)
(*   ∀ (P: Prop), *)
(*     (∀ j, γ ∋ j → wkl δ j = i → P) → *)
(*     (∀ j, δ ∋ j → wkr γ j = i → P) → P. *)
(* Proof with cbn in *; subst; eauto using wsIx. *)
(*   depind wi; destruct δ... *)
(*   eapply IHwi; intros... *)
(* Qed. *)

(* Lemma wsIx_plus_dec' {γ δ i} (wi: γ ∪ δ ∋ i) : *)
(*   (∃ j, γ ∋ j ∧ wkl δ j = i) ∨ *)
(*   (∃ j, δ ∋ j ∧ wkr γ j = i). *)
(* Proof. apply (wsIx_plus_dec wi); eauto. Qed. *)


(* Lemma wsIx_wks (δ: Dom) : *)
(*   ∀ (γ: Dom) (i: Ix), γ ∋ i → (γ ∪ δ) ∋ (wks δ i). *)
(* Proof. induction δ; eauto using wsIx. Qed. *)
(* Hint Resolve wsIx_wks : ws. *)

(* Lemma wsiIx_wks (δ: Dom) : *)
(*   ∀ (γ: Dom) (i: Ix), (γ ∪ δ) ∋ (wks δ i) → γ ∋ i. *)
(* Proof. induction δ; eauto using wsIx, wsiS. Qed. *)
(* Hint Resolve wsiIx_wks : wsi. *)

(* Lemma wsiIx_wks1 : *)
(*   ∀ (γ: Dom) (i: Ix), (S γ) ∋ (wks 1 i) → γ ∋ i. *)
(* Proof. apply (wsiIx_wks 1). Qed. *)
(* Hint Resolve wsiIx_wks : wsi. *)

Section Stuff.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.
  Context {wsX: Ws X}.
  Context {wsVrX: WsVr X}.
  Context {wsWkX: WsWk X}.

  Lemma ws_wks (δ: Dom) :
    ∀ γ (x: X), ⟨ γ ⊢ x ⟩ → ⟨ γ ∪ δ ⊢ wks δ x ⟩.
  Proof. induction δ; crush. Qed.

  (* Lemma wsi_wks (δ: Dom) : *)
  (*   ∀ γ (x: X), ⟨ γ ∪ δ ⊢ wks δ x ⟩ → ⟨ γ ⊢ x ⟩. *)
  (* Proof. induction δ; crush. Qed. *)

  Lemma wsSub_idm (γ: Dom) : ⟨ idm X : γ => γ ⟩.
  Proof. unfold WsSub, idm; crush. Qed.

  Lemma wsSub_wkm (γ: Dom) : ⟨ wkm : γ => S γ ⟩.
  Proof. unfold WsSub; crush. Qed.

  Lemma wsSub_wkms (γ: Dom) d : ⟨ wkms d : γ => d + γ ⟩.
  Proof. unfold WsSub, wkms; induction d; crush. Qed.


  Definition WsSubNatural (γ₁ γ₂: Dom) (ξ₁ ξ₂ : Sub X) : Prop :=
    ∀ (i: Ix), ⟨ γ₁ ⊢ ξ₁ i ⟩ → ⟨ γ₂ ⊢ ξ₂ i ⟩.

  Lemma wsSubNat_comp
    {f₁ f₂ f₃: Dom → Dom} {ξ₁ ξ₂ ξ₃: Sub X}
    (H₁₂: ∀ γ, WsSubNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂)
    (H₂₃: ∀ γ, WsSubNatural (f₂ γ) (f₃ γ) ξ₂ ξ₃) :
    ∀ γ, WsSubNatural (f₁ γ) (f₃ γ) ξ₁ ξ₃.
  Proof. unfold WsSubNatural in *; eauto. Qed.

  Lemma wsSub_natural'
    {f₁ f₂: Dom → Dom} {ξ₁ ξ₂: Sub X}
    (hyp: ∀ γ, WsSubNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂) :
    ∀ γ₁ γ₂,
      WsSub γ₁ (f₁ γ₂) ξ₁ →
      WsSub γ₁ (f₂ γ₂) ξ₂.
  Proof. unfold WsSubNatural, WsSub in *; eauto. Qed.

  Lemma wsSub_up (γ₁ γ₂: Dom) (ξ: Sub X) :
    ⟨ ξ : γ₁ => γ₂ ⟩ → ⟨ ξ↑ : S γ₁ => S γ₂ ⟩.
  Proof. unfold up, WsSub; crush. Qed.
  Hint Resolve wsSub_up : ws.

  (* Lemma wsiSub_up (γ₁ γ₂: Dom) (ξ: Sub X) : *)
  (*   ⟨ ξ↑ : S γ₁ => S γ₂ ⟩ → ⟨ ξ : γ₁ => γ₂ ⟩. *)
  (* Proof. *)
  (*   unfold WsSub; crush. *)
  (*   eauto using wsiWk. *)
  (* Qed. *)
  (* Hint Resolve wsiSub_up : wsi. *)

  Lemma wsSub_ups (γ₁ γ₂ δ: Dom) (ξ: Sub X) :
    WsSub γ₁ γ₂ ξ → WsSub (γ₁ ∪ δ) (γ₂ ∪ δ) (ξ ↑⋆ δ).
  Proof. induction δ; crush. Qed.
  Hint Resolve wsSub_ups : ws.

  (* Lemma wsiSub_ups (γ₁ γ₂ δ: Dom) (ξ: Sub X) : *)
  (*   WsSub (γ₁ ∪ δ) (γ₂ ∪ δ) (ξ ↑⋆ δ) → WsSub γ₁ γ₂ ξ. *)
  (* Proof. induction δ; crush. Qed. *)
  (* Hint Resolve wsiSub_ups : wsi. *)

  Lemma wsSub_closed (ξ: Sub X) (δ: Dom) : ⟨ ξ : 0 => δ ⟩.
  Proof. unfold WsSub; crush. Qed.
  Hint Resolve wsSub_closed : ws.

  Context {apX: Ap X X}.
  Context {apVrX: LemApVr X X}.
  Context {apWkX: LemApWk X X}.
  Context {apCompXXX: LemApComp X X X}.
  Context {wsApX: WsAp X X}.

  Lemma weakening {γ: Dom} {x: X} (wx: ⟨ γ ⊢ x ⟩) :
    ⟨ S γ ⊢ x[wkm] ⟩.
  Proof.
    rewrite <- ap_wk.
    now apply wsWk.
  Qed.

  Lemma weakenings δ {γ: Dom} {x: X} (wx: ⟨ γ ⊢ x ⟩) :
    ⟨ γ ∪ δ ⊢ x[wkms δ] ⟩.
  Proof.
    induction δ.
    - cbn; now rewrite ap_id.
    - rewrite wkms_succ, <- ap_comp.
      now apply weakening.
  Qed.

  Lemma substitution {γ δ: Dom} {ξ: Sub X} (wξ: ⟨ ξ : γ => δ ⟩) :
    ∀ {x: X}, ⟨ γ ⊢ x ⟩ → ⟨ δ ⊢ x[ξ] ⟩.
  Proof. intros; now apply (wsAp wξ). Qed.

  (* Lemma wsSubClosed_beta {δ} {ξ: Sub X} (wξ: ⟨ ξ : δ => 0 ⟩) : *)
  (*   ∀ i, δ ∋ i → ξ i = beta δ ξ i. *)
  (* Proof. *)
  (*   revert ξ wξ. *)
  (*   induction δ; intros ξ wξ i wi. *)
  (*   - crush. *)
  (*   - crush. *)
  (*     apply (IHδ (S >-> ξ)). *)
  (*     + intros j wj. *)
  (*       apply wξ. *)
  (*       now constructor. *)
  (*     + easy. *)
  (* Qed. *)

  Lemma wsClosed_invariant {Y} {vrY : Vr Y} {apXY : Ap X Y} {wsY : Ws Y} {wsApY : WsAp X Y} {x: X} (wx: ⟨ 0 ⊢ x ⟩) :
    ∀ (ξ: Sub Y), x[ξ] = x.
  Proof.
    intros.
    replace x with x[idm Y] at 2 by crush.
    eapply (wsApExt wx). 
    inversion 1.
  Qed.

  Lemma closed_invar_sub {d1 d2 t0} (wt0: ⟨ 0 ⊢ t0 ⟩) :
    ∀ t1 ζ,
      t1 = t0[wkms d1] →
      ⟨ ζ : d1 => d2 ⟩ →
      t1[ζ] = t0[wkms d2].
  Proof.
    intros; subst. rewrite ap_comp.
    eapply (wsApExt wt0); inversion 1.
  Qed.

  Lemma wsSub_natural
    {f₁ f₂: Dom → Dom} {ξ₁ ξ₂: Sub X}
    (hyp: ∀ γ, WsSubNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂) (ξ: Sub Ix) :
    ∀ (γ₁ γ₂ : Dom),
      ⟨ ⌈ξ⌉ >=> ξ₁ : γ₁ => f₁ γ₂ ⟩ →
      ⟨ ⌈ξ⌉ >=> ξ₂ : γ₁ => f₂ γ₂ ⟩.
  Proof.
    eapply wsSub_natural'.
    unfold WsSubNatural in *; crush.
    (* rewrite ap_vr in H; crush. *)
  Qed.

  Lemma wsSub_comp {γ₁ γ₂ γ₃: Dom} {ξ₁ ξ₂: Sub X} :
    WsSub γ₁ γ₂ ξ₁ → WsSub γ₂ γ₃ ξ₂ → WsSub γ₁ γ₃ (ξ₁ >=> ξ₂).
  Proof.
    unfold WsSub, comp; crush.
    eapply wsAp; eauto.
  Qed.
  Hint Resolve wsSub_comp : ws.

  Lemma wsSub_beta (γ δ: Dom) :
    ∀ (ξ: Sub X),
      ⟨ ξ : δ => γ ⟩ →
      ⟨ beta δ ξ : γ ∪ δ => γ ⟩.
  Proof. unfold WsSub; induction δ; crush. Qed.
  Hint Resolve wsSub_beta : ws.

  (* Lemma wsSubNatural_up (γ₁ γ₂: Dom) (ξ₁ ξ₂: Sub X) : *)
  (*   WsSubNatural γ₁ γ₂ ξ₁ ξ₂ → *)
  (*   WsSubNatural (S γ₁) (S γ₂) (ξ₁ ↑) (ξ₂ ↑). *)
  (* Proof. intros H i; destruct i; crush. Qed. *)
  (* Hint Resolve wsSubNatural_up : ws. *)

  (* Lemma wsSubNatural_ups (δ: Dom) : *)
  (*   ∀ (γ₁ γ₂: Dom) (f g: Sub X) (wfg: WsSubNatural γ₁ γ₂ f g), *)
  (*     WsSubNatural (γ₁ ∪ δ) (γ₂ ∪ δ) (f ↑⋆ δ) (g ↑⋆ δ). *)
  (* Proof. induction δ; crush. Qed. *)
  (* Hint Resolve wsSubNatural_ups : ws. *)

  Lemma wsSub_sub_beta1 γ t (wt: ⟨ γ ⊢ t ⟩) :
    ⟨ beta1 t : S γ => γ ⟩.
  Proof. apply (wsSub_beta γ 1); crush. Qed.
  Hint Resolve wsSub_sub_beta1 : ws.

  (* Lemma wsSubNatural_wks_id δ : *)
  (*   ∀ γ, WsSubNatural (γ ∪ δ) γ (wkms δ) (idm X). *)
  (* Proof. *)
  (*   unfold WsSubNatural; intros. *)
  (*   (* eapply wsi_wks. *) *)
  (*   rewrite ap_wks, ap_vr; simpl; eauto. *)
  (* Qed. *)
  (* Hint Resolve wsSubNatural_wks_id : wsi. *)

  (* Lemma wsiSub_comp_wkms δ ξ : *)
  (*   ∀ γ₁ γ₂, *)
  (*     WsSub γ₁ (γ₂ ∪ δ) (ξ >=> wkms δ) → *)
  (*     WsSub γ₁ γ₂        ξ. *)
  (* Proof. apply (wsSub_natural (wsSubNatural_wkl_id δ)). Qed. *)
  (* Hint Resolve wsiSub_comp_wkl : wsi. *)

  (* Lemma wsSub_natural *)
  (*   {f₁ f₂: Dom → Dom} {ξ₁ ξ₂: Ren} *)
  (*   (hyp: ∀ γ, WsSubNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂) : *)
  (*   ∀ γ₁ γ₂ ζ, *)
  (*     WsSub γ₁ (f₁ γ₂) (sub_comp_ren ζ ξ₁) → *)
  (*     WsSub γ₁ (f₂ γ₂) (sub_comp_ren ζ ξ₂). *)
  (* Proof. unfold WsSub, sub_comp_ren in *; eauto using wsTm_natural. Qed. *)

  (* Lemma wsiSub_comp_wks' ζ δ γ₁ γ₂ : *)
  (*   WsSub γ₁ (γ₂ ∪ δ) (sub_comp_ren ζ (wks δ)) → *)
  (*   WsSub γ₁ γ₂       (sub_comp_ren ζ ren_id). *)
  (* Proof. apply (wsSub_natural (wsSubNatural_wks_id δ)). Qed. *)

  (* Lemma wsiSub_comp_wks ζ δ γ₁ γ₂ : *)
  (*   WsSub γ₁ (γ₂ ∪ δ) (sub_comp_ren ζ (wks δ)) → *)
  (*   WsSub γ₁ γ₂       ζ. *)
  (* Proof. *)
  (*   pose proof (wsiSub_comp_wks' ζ). *)
  (*   specialize (H δ γ₁ γ₂). crush. *)
  (* Qed. *)
  (* Hint Resolve wsiSub_comp_wks : wsi. *)

  (* Lemma wsiSub_comp_wks1 ζ γ₁ γ₂ : *)
  (*   WsSub γ₁ (S γ₂) (sub_comp_ren ζ (wks 1)) → *)
  (*   WsSub γ₁ γ₂     ζ. *)
  (* Proof. apply (wsiSub_comp_wks ζ 1). Qed. *)
  (* Hint Resolve wsiSub_comp_wks1 : wsi. *)

  (* Lemma wsTm_natural t : *)
  (*   ∀ γ δ ξ₁ ξ₂ (wξ: WsSubNatural γ δ ξ₁ ξ₂), *)
  (*     wsTm γ t[ξ₁] → wsTm δ t[ξ₂]. *)
  (* Proof. *)
  (*   induction t; cbn; intros γ δ ξ₁ ξ₂ wξ wt; *)
  (*     inversion wt; subst; cbn; constructor; crush. *)
  (* Qed. *)

  (* Lemma wsiTm_wks δ γ t : *)
  (*   wsTm (γ ∪ δ) (t[wks δ]) → wsTm γ t. *)
  (* Proof. *)
  (*   replace (wsTm γ t) with (wsTm γ (t[ren_id])). *)
  (*   apply wsTm_natural; auto with wsi. *)
  (*   crush. *)
  (* Qed. *)
  (* Hint Resolve wsiTm_wks : wsi. *)

  (* Lemma wsiTm_wks1 γ t : *)
  (*   wsTm (S γ) (t[wks 1]) → wsTm γ t. *)
  (* Proof. apply (wsiTm_wks 1). Qed. *)
  (* Hint Resolve wsiTm_wks1 : wsi. *)

End Stuff.
