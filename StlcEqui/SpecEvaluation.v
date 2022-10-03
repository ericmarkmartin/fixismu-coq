Require Export StlcEqui.Inst.
Require Export Coq.Relations.Relation_Operators.
Require Export Common.Relations.

(** ** Evaluation *)

Fixpoint Value (t: Tm) : Prop :=
  match t with
    | abs τ t      => True
    | unit         => True
    | true         => True
    | false        => True
    | pair t₁ t₂   => Value t₁ ∧ Value t₂
    | inl t        => Value t
    | inr t        => Value t
    | var _ | app _ _ | ite _ _ _
    | proj₁ _
    | proj₂ _
    | caseof _ _ _
    | seq _ _ => False
  end.

Fixpoint ECtx (C: PCtx) : Prop :=
  match C with
    | phole            => True
    | papp₁ C t        => ECtx C
    | papp₂ t C        => Value t ∧ ECtx C
    | pite₁ C t₂ t₃    => ECtx C
    | ppair₁ C t       => ECtx C
    | ppair₂ t C       => Value t ∧ ECtx C
    | pproj₁ C         => ECtx C
    | pproj₂ C         => ECtx C
    | pinl C           => ECtx C
    | pinr C           => ECtx C
    | pcaseof₁ C t₂ t₃ => ECtx C
    | pseq₁ C t        => ECtx C
    | pabs _ _
    | pite₂ _ _ _ | pite₃ _ _ _
    | pcaseof₂ _ _ _ | pcaseof₃ _ _ _
    | pseq₂ _ _ => False
  end.

Reserved Notation "t₁ -->₀ t₂" (at level 80).
Inductive eval₀ : Tm → Tm → Prop :=
  | eval_beta {τ₁ t₁ t₂} :
      Value t₂ →
      app (abs τ₁ t₁) t₂ -->₀ t₁[beta1 t₂]
  | eval_ite_true {t₁ t₂} :
      ite true t₁ t₂ -->₀ t₁
  | eval_ite_false {t₁ t₂} :
      ite false t₁ t₂ -->₀ t₂
  | eval_proj₁ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₁ (pair t₁ t₂) -->₀ t₁
  | eval_proj₂ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₂ (pair t₁ t₂) -->₀ t₂
  | eval_case_inl {t t₁ t₂} :
      Value t →
      caseof (inl t) t₁ t₂ -->₀ t₁[beta1 t]
  | eval_case_inr {t t₁ t₂} :
      Value t →
      caseof (inr t) t₁ t₂ -->₀ t₂[beta1 t]
  | eval_seq_next {t₁ t₂} :
      Value t₁ →
      seq t₁ t₂ -->₀ t₂
where "t₁ -->₀ t₂" := (eval₀ t₁ t₂).

Reserved Notation "t₁ --> t₂" (at level 80).
Inductive eval : Tm → Tm → Prop :=
| eval_ctx₀ C {t t'} :
    t -->₀ t' → ECtx C → pctx_app t C --> pctx_app t' C
where "t₁ --> t₂" := (eval t₁ t₂).

#[export]
Hint Constructors eval : eval.
#[export]
Hint Constructors eval₀ : eval.
#[export]
Hint Constructors clos_refl_trans_1n : eval.
#[export]
Hint Constructors clos_trans_1n : eval.

Definition normal (t : Tm) := forall t', not (t --> t').

(* Alternative induction principle without program contexts. *)
Lemma eval_ind' (P: Tm → Tm → Prop) :
  (∀ (τ₁ : Ty) (t₁ t₂ : Tm), Value t₂ → P (app (abs τ₁ t₁) t₂) t₁[beta1 t₂]) →
  (∀ t₁ t₂ : Tm, P (ite true t₁ t₂) t₁) →
  (∀ t₁ t₂ : Tm, P (ite false t₁ t₂) t₂) →
  (∀ t₁ t₂ : Tm, Value t₁ → Value t₂ → P (proj₁ (pair t₁ t₂)) t₁) →
  (∀ t₁ t₂ : Tm, Value t₁ → Value t₂ → P (proj₂ (pair t₁ t₂)) t₂) →
  (∀ t t₁ t₂ : Tm, Value t → P (caseof (inl t) t₁ t₂) t₁[beta1 t]) →
  (∀ t t₁ t₂ : Tm, Value t → P (caseof (inr t) t₁ t₂) t₂[beta1 t]) →
  (∀ t₁ t₂ : Tm, Value t₁ → P (seq t₁ t₂) t₂) →
  (∀ t₁ t₁' t₂ : Tm, t₁ --> t₁' → P t₁ t₁' → P (app t₁ t₂) (app t₁' t₂)) →
  (∀ t₁ t₂ t₂' : Tm, Value t₁ → t₂ --> t₂' → P t₂ t₂' → P (app t₁ t₂) (app t₁ t₂')) →
  (∀ t₁ t₁' t₂ t₃ : Tm, t₁ --> t₁' → P t₁ t₁' → P (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)) →
  (∀ t₁ t₁' t₂ : Tm, t₁ --> t₁' → P t₁ t₁' → P (pair t₁ t₂) (pair t₁' t₂)) →
  (∀ t₁ t₂ t₂' : Tm, Value t₁ → t₂ --> t₂' → P t₂ t₂' → P (pair t₁ t₂) (pair t₁ t₂')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (proj₁ t) (proj₁ t')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (proj₂ t) (proj₂ t')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (inl t) (inl t')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (inr t) (inr t')) →
  (∀ t₁ t₁' t₂ t₃ : Tm, t₁ --> t₁' → P t₁ t₁' → P (caseof t₁ t₂ t₃) (caseof t₁' t₂ t₃)) →
  (∀ t₁ t₁' t₂ : Tm, t₁ --> t₁' → P t₁ t₁' → P (seq t₁ t₂) (seq t₁' t₂)) →
  ∀ t t0 : Tm, t --> t0 → P t t0.
Proof.
  do 21 intro; induction 1 as [C ? ? r' ec].
  revert ec t t' r'.
  induction C; cbn in *; intuition.
  induction r'; cbn in *; intuition.
Qed.

(* The in-between induction principle *)
Lemma eval_ind'' (P: Tm → Tm → Prop) :
  (∀ t t' : Tm, t -->₀ t' → P t t') →
  (∀ t₁ t₁' t₂ : Tm, t₁ --> t₁' → P t₁ t₁' → P (app t₁ t₂) (app t₁' t₂)) →
  (∀ t₁ t₂ t₂' : Tm, Value t₁ → t₂ --> t₂' → P t₂ t₂' → P (app t₁ t₂) (app t₁ t₂')) →
  (∀ t₁ t₁' t₂ t₃ : Tm, t₁ --> t₁' → P t₁ t₁' → P (ite t₁ t₂ t₃) (ite t₁' t₂ t₃)) →
  (∀ t₁ t₁' t₂ : Tm, t₁ --> t₁' → P t₁ t₁' → P (pair t₁ t₂) (pair t₁' t₂)) →
  (∀ t₁ t₂ t₂' : Tm, Value t₁ → t₂ --> t₂' → P t₂ t₂' → P (pair t₁ t₂) (pair t₁ t₂')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (proj₁ t) (proj₁ t')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (proj₂ t) (proj₂ t')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (inl t) (inl t')) →
  (∀ t t' : Tm, t --> t' → P t t' → P (inr t) (inr t')) →
  (∀ t₁ t₁' t₂ t₃ : Tm, t₁ --> t₁' → P t₁ t₁' → P (caseof t₁ t₂ t₃) (caseof t₁' t₂ t₃)) →
  (∀ t₁ t₁' t₂ : Tm, t₁ --> t₁' → P t₁ t₁' → P (seq t₁ t₂) (seq t₁' t₂)) →
  ∀ t t0 : Tm, t --> t0 → P t t0.
Proof.
  do 14 intro; induction 1.
  induction C; cbn in *; intuition.
Qed.

Definition evaln := stepRel eval.
Definition evalStar := clos_refl_trans_1n Tm eval.

#[export]
Hint Constructors stepRel : eval.

(* (* domi: this definition is equivalent to the normal eval.  Not sure why it's there anymore *) *)
(* Inductive ctxeval : Tm → Tm → Prop := *)
(* | mkCtxEval : forall Cu t₀ t₀', ECtx Cu → t₀ -->₀ t₀' → ctxeval (pctx_app t₀ Cu) (pctx_app t₀' Cu). *)

(* Definition ctxevalStar := clos_refl_trans_1n Tm ctxeval. *)
(* Definition ctxevaln := stepRel ctxeval. *)

(* Arguments ctxevaln /. *)
(* Arguments ctxevalStar /. *)


Notation "t₁ -->* t₂" := (clos_refl_trans_1n Tm eval t₁ t₂) (at level 80).
Notation "t₁ -->+ t₂" := (clos_trans_1n Tm eval t₁ t₂) (at level 80).

Definition Terminating (t: Tm) : Prop :=
  ∃ v, Value v ∧ t -->* v.

Notation "t ⇓" := (Terminating t) (at level 8, format "t ⇓").
Notation "t ⇑" := (not (Terminating t)) (at level 8, format "t ⇑").

(* Terminates in maximum n steps *)
Definition TerminatingN (t: Tm) (n : nat) : Prop :=
  ∃ v m, Value v ∧ m ≤ n ∧ evaln t v m.
Notation "t ⇓_ n" := (TerminatingN t n) (at level 8, format "t ⇓_ n").

Section DerivedRules.

  Lemma eval_eval₀ {t t'} : t -->₀ t' -> t --> t'.
  Proof. intro r; now apply (eval_ctx₀ phole r). Qed.

  Lemma eval_beta'' {t₁ t₂ t' τ} :
    Value t₂ → t' = t₁[beta1 t₂] →
    app (abs τ t₁) t₂ -->₀ t'.
  Proof. intros; subst; auto using eval₀. Qed.

End DerivedRules.

(* Section CtxEval. *)
(*   Lemma eval₀_ctxeval {t t'} : t -->₀ t' → ctxeval t t'. *)
(*   Proof. *)
(*     apply (mkCtxEval phole _ _ I). *)
(*   Qed. *)

(*   Lemma ctxeval_eval {t t'} : ctxeval t t' → t --> t'. *)
(*   Proof. *)
(*     destruct 1. *)
(*     refine (eval_ctx₀ _ _ _); assumption. *)
(*   Qed. *)

(*   Lemma eval_ctxeval {t t'} : t --> t' -> ctxeval t t'. *)
(*   Proof. *)
(*     destruct 1. *)
(*     refine (mkCtxEval _ _ _ _ _); assumption. *)
(*   Qed. *)

(*   Lemma ctxevaln_evaln {t t' n} : ctxevaln t t' n → evaln t t' n. *)
(*   Proof. *)
(*     induction 1; econstructor; eauto using ctxeval_eval with eval. *)
(*   Qed. *)

(*   (* Lemma ctxevaln_evaln_ctx {t t' n} : ctxevaln t t' n → forall Cu, ECtx Cu → evaln (pctx_app t Cu) (pctx_app t' Cu) n. *) *)
(*   (* Proof. *) *)
(*   (*   induction 1; unfold evaln in *; *) *)
(*   (*   econstructor; eauto using ctxeval_eval_ctx with eval. *) *)
(*   (* Qed. *) *)
(* End CtxEval. *)
