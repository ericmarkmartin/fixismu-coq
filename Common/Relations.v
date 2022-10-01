Require Export Coq.Relations.Relations.
Require Coq.Relations.Operators_Properties.
Require Coq.Setoids.Setoid.
Require Export Coq.Unicode.Utf8.

Hint Constructors clos_refl_trans_1n : eval.
Hint Constructors clos_trans_1n : eval.

(* ** Transitive and transitive-reflexive closure *)
Section RtProperties.

  Context {A: Type}.
  Context {R: relation A}.

  Notation "t₁ --> t₂" := (R t₁ t₂) (at level 80).
  Notation "t₁ -->* t₂" := (clos_refl_trans_1n A R t₁ t₂) (at level 80).
  Notation "t₁ -->+ t₂" := (clos_trans_1n A R t₁ t₂) (at level 80).

  Lemma evalToPlus {t t'} : t --> t' -> t -->+ t'.
  Proof. eauto with eval. Qed.

  Lemma evalToStar {t t'} : t --> t' -> t -->* t'.
  Proof. eauto with eval. Qed.

  Lemma evalPlusToStar {t t'} : t -->+ t' -> t -->* t'.
  Proof. induction 1; eauto with eval. Qed.

  Lemma evalStarPlusToPlus {t t' t''} :
    t -->* t' → t' -->+ t'' → t -->+ t''.
  Proof. induction 1; eauto with eval. Qed.

  Lemma evalPlusStepToPlus {t t' t''} :
    t -->+ t' → t' --> t'' → t -->+ t''.
  Proof. induction 1; eauto with eval. Qed.

  Lemma evalPlusStarToPlus {t t' t''} :
    t -->+ t' → t' -->* t'' → t -->+ t''.
  Proof. induction 2; eauto using evalPlusStepToPlus with eval. Qed.

  Lemma evalStepStarToPlus {t} t' {t''} :
    t --> t' → t' -->* t'' → t -->+ t''.
  Proof. eauto using evalPlusStarToPlus with eval. Qed.

  Lemma evalStepStar {t} t' {t''} :
    t --> t' → t' -->* t'' → t -->* t''.
  Proof. eauto with eval. Qed.

  Lemma evalStepTrans {t} t' {t''} :
    t -->* t' → t' -->* t'' → t -->* t''.
  Proof. intros e1 e2. 
         rewrite <- clos_rt_rt1n_iff in *.
         refine (rt_trans _ _ _ _ _ e1 e2).
  Qed.

  Lemma inversion_evalStar {t t'} :
    t -->* t' → t = t' ∨ (t -->+ t').
  Proof. inversion 1; eauto using evalPlusStarToPlus with eval. Qed.

  Lemma inversion_evalPlus {t t'} :
    t -->+ t' → ∃ t'', t --> t'' ∧ t'' -->* t'.
  Proof. induction 1 as [t t' e|t t'' t' e ePlus];
         [exists t'|exists t''] ; eauto using evalPlusToStar with eval. 
  Qed.

End RtProperties.

Section StepRel.

  Inductive stepRel {A} (R : A → A → Prop) (t : A) : A → nat → Prop :=
  | stepRel_zero : stepRel R t t 0
  | stepRel_step : forall t' t'' n, R t t' → stepRel R t' t'' n → stepRel R t t'' (S n).

  Lemma evalTrans_to_stepRel {A R t t'} :
    clos_refl_trans_1n A R t t' → exists n, stepRel R t t' n.
  Proof.
    induction 1 as [|t t' t'' e es [n IHn]]; eauto using stepRel_zero, stepRel_step.
  Qed.

  Lemma stepRel_to_evalStar {A R t t' n} : stepRel R t t' n → clos_refl_trans_1n A R t t'.
  Proof.
    induction 1; eauto using clos_refl_trans_1n.
  Qed.
End StepRel.

Hint Constructors stepRel : eval.
