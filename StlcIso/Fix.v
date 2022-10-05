Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasTyping.
Require Import StlcIso.Inst.
Require Import StlcIso.InstAnnot.
Require Import Db.Lemmas.
Require Import Db.WellScoping.

Require Import Coq.Bool.Bool.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushRecTypesMatchH;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     rewrite <- ?ap_liftSub, <- ?up_liftSub
     (* repeat crushStlcIsoScopingMatchH; *)
     (* repeat crushScopingMatchH *)
    );
  auto.

(* Definition ufix₂_annot (f : TmA) (τ1 τ2 : Ty) : TmA := *)
(*   let t : TmA := ia_abs (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) *)
(*                        (tarr τ1 τ2) *)
(*                        (ia_app (tarr τ1 τ2) (tarr τ1 τ2) f[wkm] *)
(*                                (ia_abs τ1 τ2 (ia_app τ1 τ2 (ia_app (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (tarr τ1 τ2) (ia_unfold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) (ia_var 1)) (ia_var 1)) (ia_var 0)))) *)
(*   in ia_app (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (tarr τ1 τ2) (ia_unfold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) (ia_fold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) t)) (ia_fold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) t). *)

Definition ufix₁_annot (f : TmA) (τ1 τ2 : Ty) : TmA :=
  let t : TmA := ia_abs (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm]))
                       (tarr τ1 τ2)
                       (ia_app (tarr τ1 τ2) (tarr τ1 τ2) f[wkm]
                               (ia_abs τ1 τ2 (ia_app τ1 τ2 (ia_app (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (tarr τ1 τ2) (ia_unfold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) (ia_var 1)) (ia_var 1)) (ia_var 0))))
  in ia_app (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (tarr τ1 τ2)
            (ia_unfold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) (ia_fold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) t))
            (ia_fold_ (tarr (tvar 0) (tarr τ1 τ2)[wkm]) t).

Definition ufix_annot (τ1 τ2 : Ty) : TmA :=
  ia_abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (tarr τ1 τ2) (ufix₁_annot (ia_var 0) τ1 τ2).


(* Definition ufix₂ (f : Tm) (τ1 τ2 : Ty) : Tm := *)
(*   let t : Tm := abs (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (app f[wkm] (abs τ1 (app (app (unfold_ (var 1)) (var 1)) (var 0)))) *)
(*   in app (unfold_ (fold_ t)) (fold_ t). *)

(* note that ufix₁ has a unfold-fold redex.
  this is of course unnecessary, but it will appear after evaluation, so it's easier to put it there from the start as well (to reduce the amount of different terms to keep track of).
*)
Definition ufix₁ (f : Tm) (τ1 τ2 : Ty) : Tm :=
  let t : Tm := abs (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (app f[wkm] (abs τ1 (app (app (unfold_ (var 1)) (var 1)) (var 0))))
  in app (unfold_ (fold_ t)) (fold_ t).

Definition ufix (τ1 τ2 : Ty) : Tm :=
  abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (ufix₁ (var 0) τ1 τ2).

Definition Om (τ : Ty) : Tm :=
  app (ufix₁ (abs (tunit r⇒ τ) (var 0)) tunit τ) unit.

Definition OmA (τ : Ty) : TmA :=
  ia_app tunit τ (ufix₁_annot (ia_abs (tunit r⇒ τ) (tunit r⇒ τ) (ia_var 0)) tunit τ) ia_unit.

Lemma eraseAnnot_ufix {τ₁ τ₂} : eraseAnnot (ufix_annot τ₁ τ₂) = ufix τ₁ τ₂.
Proof. reflexivity. Qed.

Lemma ufix_eval₁' f (valf: Value f) {τ1 τ2} : (app (ufix τ1 τ2) f) --> (ufix₁ f τ1 τ2).
Proof.
  unfold ufix, ufix₁.
  apply (eval_ctx₀ phole); crush; eapply eval_beta''; crush.
Qed.

Lemma ufix_eval₁ f (valf: Value f) {τ1 τ2} : app (ufix τ1 τ2) f  --> ufix₁ f τ1 τ2.
Proof.
  eauto using ufix_eval₁'.
Qed.

Lemma ufix₁_evaln' {t τ1 τ2} : evaln (ufix₁ (abs (tarr τ1 τ2) t) τ1 τ2) (t[beta1 (abs τ1 (app (ufix₁ (abs (tarr τ1 τ2) t[wkm↑]) τ1 τ2) (var 0)))]) 3.
Proof.
  unfold ufix₁.
  econstructor.
  {eapply (eval_ctx₀ (papp₁ phole _)); [|now cbn].
   eapply eval_fold_unfold; now cbn.
  }
  cbn.
  repeat change (apTm ?ξ ?t) with t[ξ].
  econstructor.
  { eapply eval_eval₀, eval_beta; now cbn. }
  cbn.
  repeat change (apTm ?ξ ?t) with t[ξ].
  rewrite <-?ap_liftSub, <-?up_liftSub, ?liftSub_wkm.
  rewrite apply_wkm_beta1_up_cancel.
  crushDbLemmasRewriteH.
  econstructor.
  { eapply eval_eval₀, eval_beta; now cbn. }
  econstructor.
Qed.

(* Lemma unfold_fold_id { Γ t τ } : *)
(*   ValidTy τ → *)
(*   ⟪ Γ i⊢ t : τ ⟫ → *)
(*   ⟪ Γ i⊢ unfold_ (fold_ t) : τ ⟫. *)
(* Proof. *)
(*   intros. *)
(*   Check WtUnfold. *)
(*   Check WtFold. *)
(*   apply WtUnfold. *)

Lemma fizz {τ₁ τ₂ }:
  (trec (tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]) r⇒ τ₁ r⇒ τ₂) = (tvar 0 r⇒ (τ₁ r⇒ τ₂) [wkm])[beta1 (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))].
Proof.
  crush.
Qed.

Lemma ufix₁_typing {t τ₁ τ₂ Γ} :
  ValidTy τ₁ → ValidTy τ₂ →
  ⟪ Γ i⊢ t : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ i⊢ ufix₁ t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros (cl1 & cr1) (cl2 & cr2) tyt.
  unfold ufix₁.
  apply (@WtApp Γ _ _ (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm])) (tarr τ₁ τ₂)).
  - (* rewrite <-(apply_wkm_beta1_cancel (τ₁ r⇒ τ₂) (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))) at 1. *)
    rewrite fizz.
    econstructor.
    econstructor.
    rewrite <-fizz.
    econstructor.
    econstructor.
    crush.
    eapply typing_sub.
    exact tyt.
    apply wtSub_wkm.
    econstructor.
    econstructor.
    econstructor.
    rewrite fizz.
    econstructor.
    econstructor.
    econstructor.
    econstructor.

    crushValidTy.
    crush.
    apply WsFn.
    change (wsTy _ _) with ⟨ 1 ⊢ τ₁[wkm] ⟩.
    crushValidTy.
    change (wsTy _ _) with ⟨ 1 ⊢ τ₂[wkm] ⟩.
    crushValidTy.
    crush.
    econstructor.
    econstructor.
    econstructor.
    pose proof (SimpleContrRec_ren) as (H & _).
    specialize (H τ₁ cr1 wkm).
    erewrite <-ap_liftSub in H.
    exact H.
    econstructor.
    pose proof (SimpleContrRec_ren) as (H & _).
    specialize (H τ₂ cr2 wkm).
    erewrite <-ap_liftSub in H.
    exact H.
    crushTyping.
    crushTyping.
    crushValidTy.
    crushValidTy.
    crush.
    crushValidTy.
    crushValidTy.
    crush.
    econstructor.
    econstructor;
    econstructor;
    pose proof (SimpleContrRec_ren) as (H & _).
    specialize (H τ₁ cr1 wkm).
    erewrite <-ap_liftSub in H.
    exact H.
    specialize (H τ₂ cr2 wkm).
    erewrite <-ap_liftSub in H.
    exact H.
    crushValidTyMatch.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    crush.
    crushValidTy.
    crushValidTy.
    crush.
    crushValidTy.
    crushValidTy.
    crush.
    crushValidTy.
    crush.
    crushValidTy.
  - crushTypingMatchH.
    rewrite <-fizz.
    crushTypingMatchH.
    crushTypingMatchH.
    crush.
    eapply typing_sub.
    exact tyt.
    apply wtSub_wkm.
    econstructor.
    econstructor.
    econstructor.
    rewrite fizz.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    repeat (crushValidTy; crush).
    repeat econstructor.
    repeat econstructor.
    crushValidTy.
    repeat (crushValidTy; crush).
    repeat (crushValidTy; crush).
Qed.

Lemma ufix_typing {τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ Γ i⊢ ufix τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  constructor.
  apply ufix₁_typing.
  all: repeat (crushTyping; crushValidTy).
Qed.

Lemma ufix₁_annot_typing {t τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ (Γ r▻ trec (tvar 0 r⇒ τ₁[wkm] r⇒ τ₂[wkm])) ia⊢ t [wkm] : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ ia⊢ ufix₁_annot t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros (cl1 & cr1) (cl2 & cr2) tyt.
  unfold ufix₁_annot.
  crushTypingIA.
  - repeat change (apTy ?ξ ?τ) with τ[ξ].
    repeat change (τ₁[wkm] r⇒ τ₂[wkm]) with (τ₁ r⇒ τ₂)[wkm].
    rewrite fizz.
    econstructor.
    econstructor.
    rewrite <-fizz.
    econstructor.
    econstructor.
    crush.
    crushValidTy.
    crushValidTy.
    crush.
    crushValidTy.
    econstructor.
    exact tyt.
    econstructor.
    crushValidTy.
    econstructor.
    econstructor.
    rewrite fizz.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    repeat (crush; crushValidTy).
    repeat (crush; crushValidTy).
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    repeat (crush; crushValidTy).
    repeat (crush; crushValidTy).
    repeat (crush; crushValidTy).
  - repeat change (apTy ?ξ ?τ) with τ[ξ].
    repeat change (τ₁[wkm] r⇒ τ₂[wkm]) with (τ₁ r⇒ τ₂)[wkm].
    crush.
    econstructor.
    repeat (crush; crushValidTy).
    econstructor.
    exact tyt.
    econstructor.
    repeat (crush; crushValidTy).
    econstructor.
    econstructor.
    repeat change (τ₁[wkm] r⇒ τ₂[wkm]) with (τ₁ r⇒ τ₂)[wkm].
    rewrite fizz.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    repeat (crush; crushValidTy).
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
  - repeat (crush; crushValidTy).
Qed.

Lemma ufix_annot_typing {τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ Γ ia⊢ ufix_annot τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  intros (cl1 & cr1) (cl2 & cr2).
  constructor; crushValidTy.
  eapply ufix₁_annot_typing; crushValidTy.
  constructor.
  crushTyping.
Qed.

(* Lemma ufix₁_evaln {t} : evaln (ufix₁ (abs t)) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) 2. *)
(* Proof. *)
(*   eauto using ufix₁_evaln', ctxevaln_evaln. *)
(* Qed. *)

(* Lemma ufix₁_eval {t} : ufix₁ (abs t) -->+ t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]. *)
(* Proof. *)
(*   refine (evaln_to_evalPlus _). *)
(*   apply ufix₁_evaln. *)
(* Qed. *)

(* Lemma ufix_ws (γ : Dom) : *)
(*   ⟨ γ ⊢ ufix ⟩. *)
(* Proof. *)
(*   unfold ufix, ufix₁. *)
(*   crush. *)
(* Qed. *)

(* (* TODO: simplify using result about scoping under subst... *) *)
(* Lemma ufix₁_ws {γ t} : *)
(*   ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ ufix₁ t ⟩. *)
(* Proof. *)
(*   unfold ufix₁. *)
(*   crush. *)
(* Qed. *)

Lemma wtOm_tau {Γ} τ : ValidTy τ → ⟪ Γ i⊢ Om τ : τ ⟫.
Proof.
  unfold Om.
  crushTyping;
  eapply ufix₁_typing;
    crushTyping.
Qed.

Lemma wtOmA_tau {Γ} τ : ValidTy τ → ⟪ Γ ia⊢ OmA τ : τ ⟫.
  unfold OmA.
  crushTypingIA;
  eapply ufix₁_annot_typing;
    (crushTypingIA; crushValidTy).
Qed.

#[export]
Hint Resolve wtOm_tau : typing.
#[export]
Hint Resolve wtOmA_tau : typing.
(* #[export]
Hint Resolve stlcOmegaAT : typing. *)

Definition OmHelp (τ : Ty) : Tm :=
  app (abs tunit (app (ufix₁ (abs (tunit r⇒ τ) (var 0)) tunit τ) (var 0))) unit.

Lemma evaln_to_evalPlus {t t' n} : evaln t t' (S n) → t -->+ t'.
Proof.
  intros.
  eapply evaln_split1 in H as (? & ? & ?).
  apply evaln_to_evalStar in H0.
  eapply evalStepStarToPlus.
  exact H.
  exact H0.
Qed.

Lemma stlcOmega_cycles {τ} : Om τ -->+ Om τ.
  cut (Om τ -->+ OmHelp τ ∧ OmHelp τ -->+ Om τ).
  - destruct 1. apply evalPlusToStar in H0. eapply evalPlusStarToPlus. exact H. exact H0.
  - unfold Om, OmHelp; split.
    + eapply (evalplus_ctx (papp₁ phole _)).
      constructor.
      eapply evaln_to_evalPlus.
      pose proof (@ufix₁_evaln' (var 0) tunit τ).
      remember (var 0)[beta1 (abs tunit (app (ufix₁ (abs (tunit r⇒ τ) (var 0)[wkm↑]) tunit τ) (var 0)))] as x.
      remember (abs tunit (app (ufix₁ (abs (tunit r⇒ τ) (var 0)) tunit τ) (var 0))) as y.
      enough (x = y).
      rewrite <-H0.
      exact H.
      subst.
      cbn.
      reflexivity.
    + unfold ufix₁.
      eapply evalStepStarToPlus.
      apply eval₀_to_eval.
      apply eval_beta; now cbn.
      cbn.
      change (wk 0) with 1.
      apply rt1n_refl.
Qed.

Lemma Om_div {τ} : (Om τ)⇑.
Proof.
  apply cycles_dont_terminate.
  apply stlcOmega_cycles.
Qed.
