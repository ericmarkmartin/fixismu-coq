Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.SpecAnnot.
Require Import StlcIso.LemmasTyping.
(* Require Import StlcIso.SpecScoping. *)
(* Require Import StlcIso.LemmasScoping. *)
Require Import StlcIso.Inst.
Require Import StlcIso.InstAnnot.
Require Import Db.Lemmas.
Require Import Db.WellScoping.

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

Lemma eraseAnnot_ufix {τ₁ τ₂} : eraseAnnot (ufix_annot τ₁ τ₂) = ufix τ₁ τ₂.
Proof.

  reflexivity.
Qed.

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

Lemma foo {Γ t τ τ'} :
  τ[beta1 (trec τ)] = τ' →
  ⟪ Γ i⊢ t : trec τ ⟫ →
  ⟪ Γ i⊢ unfold_ t : τ' ⟫.
Proof.
  intros. subst.
  constructor. assumption.
Qed.

Lemma ufix₁_typing {t τ₁ τ₂ Γ} :
  ⟪ Γ i⊢ t : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ i⊢ ufix₁ t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros.
  unfold ufix₁.

  apply (@WtApp Γ _ _ (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm])) (tarr τ₁ τ₂)).
  - rewrite <-(apply_wkm_beta1_cancel (τ₁ r⇒ τ₂) (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))) at 3.
    apply (WtUnfold _ (τ := tarr (tvar 0) (tarr τ₁ τ₂)[wkm])).
    econstructor.
    crushTyping.
    rewrite ?apply_wkm_beta1_cancel.
    eassumption.
    rewrite <-(apply_wkm_beta1_cancel (τ₁ r⇒ τ₂) (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))) at 1.
    change (trec _ r⇒ _) with (tvar 0 r⇒ (τ₁ r⇒ τ₂) [wkm])[beta1 (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))].
    repeat econstructor.
  - constructor.
    cbn.
    constructor.
    crushTyping.
    rewrite ?apply_wkm_beta1_cancel.
    eassumption.
    rewrite <-(apply_wkm_beta1_cancel (τ₁ r⇒ τ₂) (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))) at 1.
    change (trec _ r⇒ _) with (tvar 0 r⇒ (τ₁ r⇒ τ₂) [wkm])[beta1 (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm]))].
    repeat econstructor.
Qed.

Lemma ufix_typing {τ₁ τ₂ Γ} :
  ⟪ Γ i⊢ ufix τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  constructor.
  apply ufix₁_typing.
  crushTyping.
Qed.

Lemma ufix₁_annot_typing {t τ₁ τ₂ Γ} :
  ⟪ (Γ r▻ trec (tvar 0 r⇒ τ₁[wkm] r⇒ τ₂[wkm])) ia⊢ t [wkm] : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ ia⊢ ufix₁_annot t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros tytwk.
  unfold ufix₁_annot.
  repeat constructor.
  - replace (trec (tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]) r⇒ τ₁ r⇒ τ₂) with ((tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]) [ beta1 (trec (tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]))]).
    repeat econstructor.
    cbn.
    crushTyping.
    rewrite ?apply_wkm_beta1_cancel.
    repeat econstructor.
    eassumption.
    replace (trec (tvar 0 r⇒ (τ₁ [wkm] r⇒ τ₂[wkm])) r⇒ τ₁ r⇒ τ₂) with ((tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]) [ beta1 (trec (tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]))]).
    repeat econstructor.
    cbn.
    crushTyping; rewrite ?apply_wkm_beta1_cancel; try reflexivity.
    crushTyping; rewrite ?apply_wkm_beta1_cancel; try reflexivity.
  - cbn.
    crushTyping; rewrite ?apply_wkm_beta1_cancel.
    repeat econstructor.
    try eassumption.
    replace (trec (tvar 0 r⇒ (τ₁ [wkm] r⇒ τ₂[wkm])) r⇒ τ₁ r⇒ τ₂) with ((tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]) [ beta1 (trec (tvar 0 r⇒ (τ₁ r⇒ τ₂)[wkm]))]).
    repeat econstructor.
    cbn.
    crushTyping; rewrite ?apply_wkm_beta1_cancel; try reflexivity.
Qed.

Lemma ufix_annot_typing {τ₁ τ₂ Γ} :
  ⟪ Γ ia⊢ ufix_annot τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  constructor.
  apply ufix₁_annot_typing.
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

