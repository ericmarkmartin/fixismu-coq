Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.
Require Export RecTypes.ValidTy.
Require Export RecTypes.LemmasTypes.

Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.SpecAnnot.
Require Import StlcEqui.LemmasTyping.
Require Import StlcEqui.Inst.
Require Import StlcEqui.InstAnnot.
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
     (* repeat crushStlcEquiScopingMatchH; *)
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
  let t : TmA := ea_abs (trec (tarr (tvar 0) (tarr τ1 τ2)))
                       (tarr τ1 τ2)
                       (ea_app (tarr τ1 τ2) (tarr τ1 τ2) f[wkm]
                               (ea_abs τ1 τ2 (ea_app τ1 τ2 (ea_app (trec (tarr (tvar 0) (tarr τ1 τ2))) (tarr τ1 τ2) (ea_coerce (trec (tarr (tvar 0) (tarr τ1 τ2))) (ea_var 1)) (ea_var 1)) (ea_var 0))))
  in ea_app (trec (tarr (tvar 0) (tarr τ1 τ2))) (tarr τ1 τ2)
            t
            (ea_coerce (tarr (trec (tarr (tvar 0) (tarr τ1 τ2))) (tarr τ1 τ2)) t).

Definition ufix_annot (τ1 τ2 : Ty) : TmA :=
  ea_abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (tarr τ1 τ2) (ufix₁_annot (ea_var 0) τ1 τ2).


(* Definition ufix₂ (f : Tm) (τ1 τ2 : Ty) : Tm := *)
(*   let t : Tm := abs (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (app f[wkm] (abs τ1 (app (app (unfold_ (var 1)) (var 1)) (var 0)))) *)
(*   in app (unfold_ (fold_ t)) (fold_ t). *)

(* note that ufix₁ has a unfold-fold redex.
  this is of course unnecessary, but it will appear after evaluation, so it's easier to put it there from the start as well (to reduce the amount of different terms to keep track of).
*)
Definition ufix₁ (f : Tm) (τ1 τ2 : Ty) : Tm :=
  let t : Tm := abs (trec (tarr (tvar 0) (tarr τ1 τ2))) (app f[wkm] (abs τ1 (app (app (var 1) (var 1)) (var 0))))
  in app t t.

Definition ufix (τ1 τ2 : Ty) : Tm :=
  abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (ufix₁ (var 0) τ1 τ2).

Lemma eraseAnnot_ufix {τ₁ τ₂} : eraseAnnot (ufix_annot τ₁ τ₂) = ufix τ₁ τ₂.
Proof.
  reflexivity.
Qed.

(* Lemma eraseAnnot_ufix₁ {f τ₁ τ₂} : eraseAnnot (ufix₁_annot f τ₁ τ₂) = ufix₁ (eraseAnnot f) τ₁ τ₂. *)
(* Proof. *)
(*   cbn. *)
(*   unfold ufix₁. *)
(*   admit. *)
(* Admitted. *)


Lemma ufix_eval₁' f (valf: Value f) {τ1 τ2} : (app (ufix τ1 τ2) f) --> (ufix₁ f τ1 τ2).
Proof.
  unfold ufix, ufix₁.
  apply (eval_ctx₀ phole); crush; eapply eval_beta''; crush.
Qed.

Lemma ufix_eval₁ f (valf: Value f) {τ1 τ2} : app (ufix τ1 τ2) f  --> ufix₁ f τ1 τ2.
Proof.
  eauto using ufix_eval₁'.
Qed.

Lemma ufix₁_evaln' {t τ1 τ2 τ} :
  evaln (ufix₁ (abs τ t) τ1 τ2) (t[beta1 (abs τ1 (app (ufix₁ (abs τ t[wkm↑]) τ1 τ2) (var 0)))]) 2.
Proof.
  unfold ufix₁.
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

Lemma ufix₁_typing {t τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ Γ e⊢ t : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ e⊢ ufix₁ t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros (cl1 & cr1) (cl2 & cr2) tyt.
  unfold ufix₁.
  crushTypingMatchH.
  crushTypingMatchH.
  crushTypingMatchH.
  crushTyping.
  crushTypingMatchH.
  crushTypingMatchH.
  crushTypingMatchH.
  eapply WtEq with (T := trec (tvar 0 r⇒ τ₁ r⇒ τ₂)).
  eapply EqMuL.
  crush.
  rewrite ?wsClosed_invariant.
  eapply tyeq_refl.
  crush.
  crush.
  crushValidTy.
  crushValidTy.
  crushTyping.
  crushTyping.
  crushTyping.
  crushValidTy.
  crushValidTy.
  crushTypingMatchH.
  eapply EqMuR.
  crush.
  rewrite ?wsClosed_invariant.
  eapply tyeq_refl.
  crush.
  crush.
  crushValidTy.
  crushValidTy.
  crushTypingMatchH.
  crushTypingMatchH.
  crushTyping.
  crushTypingMatchH.
  crushTypingMatchH.
  crushTypingMatchH.
  eapply WtEq with (T := trec (tvar 0 r⇒ τ₁ r⇒ τ₂)).
  eapply EqMuL.
  crush.
  rewrite ?wsClosed_invariant.
  eapply tyeq_refl.
  crush.
  crush.
  crushValidTy.
  crushValidTy.
  crushTyping.
  crushTyping.
  crushTyping.
  crushValidTy.
  crushValidTy.
Qed.

Lemma ufix₁_annot_typing {t τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ (Γ r▻ trec (tvar 0 r⇒ τ₁ r⇒ τ₂)) ea⊢ t [wkm] : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ ea⊢ ufix₁_annot t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros (cl1 & cr1) (cl2 & cr2).
  unfold ufix₁_annot.
  crushTypingEA;
    crushValidTy.
  - eapply EqMuL.
    cbn. crush.
    rewrite ?wsClosed_invariant; try assumption.
    eapply tyeq_refl.
  - eapply EqMuR.
    cbn. crush.
    rewrite ?wsClosed_invariant; try assumption.
    eapply tyeq_refl.
  - eapply EqMuL.
    cbn. crush.
    rewrite ?wsClosed_invariant; try assumption.
    eapply tyeq_refl.
Qed.

Lemma ufix_annot_typing {τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ Γ ea⊢ ufix_annot τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  intros (cl1 & cr1) (cl2 & cr2).
  constructor; crushValidTy.
  eapply ufix₁_annot_typing; crushValidTy.
  constructor.
  crushTyping.
Qed.

Lemma ufix_typing {τ₁ τ₂ Γ} :
  ValidTy τ₁ -> ValidTy τ₂ ->
  ⟪ Γ e⊢ ufix τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  intros vτ₁ vτ₂.
  change (ufix τ₁ τ₂) with (eraseAnnot (ufix_annot τ₁ τ₂)).
  now eapply eraseAnnotT, ufix_annot_typing.
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

