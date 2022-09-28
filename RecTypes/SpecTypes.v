Require Export Db.Spec.
Require Export Db.WellScoping.

Require Import Coq.micromega.Lia.

Inductive Ty : Set :=
  | tarr (τ₁ τ₂ : Ty)
  | tunit
  | tbool
  | tprod (τ₁ τ₂: Ty)
  | tsum (τ₁ τ₂: Ty)
  | trec (τ : Ty)
  | tvar (i : Ix).

Notation "A r⊎ B" := (tsum A B) (at level 85, right associativity).
Notation "A r× B" := (tprod A B) (at level 85, right associativity).
Notation "A r⇒ B" := (tarr A B) (at level 85, right associativity).

(** ** Typing environments. *)

Inductive Env : Set :=
  | empty
  | evar (Γ : Env) (τ : Ty).

Fixpoint dom (Γ: Env) : Dom :=
  match Γ with
    | empty    => O
    | evar Γ τ => S (dom Γ)
  end.
Notation "Γ r▻ T" := (evar Γ T) (at level 55, left associativity).

Reserved Notation "Γ₁ r▻▻ Γ₂" (at level 55, left associativity).
Fixpoint ecat (Γ₁ Γ₂ : Env) {struct Γ₂} : Env :=
  match Γ₂ with
    | empty  => Γ₁
    | Γ₂ r▻ τ => (Γ₁ r▻▻ Γ₂) r▻ τ
  end
where "Γ₁ r▻▻ Γ₂" := (ecat Γ₁ Γ₂).

(*  a type is closed with an (type variable) environment of size n *)
Inductive wsTy (γ : Dom) : Ty → Prop :=
    | WsTUnit : wsTy γ tunit
    | WsBool : wsTy γ tbool
    | WsFn {τ τ'} : wsTy γ τ → wsTy γ τ' → wsTy γ (tarr τ τ')
    | WsSum {τ τ'} : wsTy γ τ → wsTy γ τ' → wsTy γ (tsum τ τ')
    | WsProd {τ τ'} : wsTy γ τ → wsTy γ τ' → wsTy γ (tprod τ τ')
    | WsRec {τ} : wsTy (S γ) τ → wsTy γ (trec τ)
    | WsTVar {i} : γ ∋ i → wsTy γ (tvar i).

Section WellScoping.
  Lemma WsTy_mono {n m : nat} {τ} : n <= m -> wsTy n τ -> wsTy m τ.
  Proof.
    intros ineq cτn.
    revert m ineq.
    induction cτn; constructor; eauto.
    - eapply (IHcτn (S m)); lia.
    - revert m ineq.
      induction H.
      + intros.
        destruct m; [exfalso; lia|].
        constructor.
      + intros.
        destruct m; [exfalso; lia|].
        constructor.
        eapply IHwsIx; lia.
  Qed.

End WellScoping.

Instance WsTy : Ws Ty := wsTy.

Section Application.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {wkY: Wk Y}.

  Context {vrTy: Vr Ty}.
  Context {liftYTy: Lift Y Ty}.

  Fixpoint apTy (ζ: Sub Y) (τ: Ty) {struct τ} : Ty :=
    match τ with
      | tarr τ₁ τ₂ => tarr (apTy ζ τ₁) (apTy ζ τ₂)
      | tunit => tunit
      | tbool => tbool
      | tprod τ₁ τ₂ => tprod (apTy ζ τ₁) (apTy ζ τ₂)
      | tsum τ₁ τ₂ => tsum (apTy ζ τ₁) (apTy ζ τ₂)
      | trec τ => trec (apTy (ζ↑) τ)
      | tvar α => lift (ζ α)
    end.

  Global Arguments apTy ζ !τ.
End Application.

Ltac crushRecTypesMatchH :=
  match goal with
    | [ H: S _ = S _             |- _ ] => apply eq_add_S in H
    | [ H: tarr _ _  = tarr _ _  |- _ ] => inversion H; clear H
    | [ H: tprod _ _ = tprod _ _ |- _ ] => inversion H; clear H
    | [ H: tsum _ _  = tsum _ _  |- _ ] => inversion H; clear H
    | [ H: trec _ = trec _ |- _ ] => inversion H; clear H
    | [ H: tvar _ = tvar _ |- _ ] => inversion H; clear H

    | [ |- tarr _ _ = tarr _ _ ] => f_equal
    | [ |- tprod _ _ = tprod _ _ ] => f_equal
    | [ |- tsum _ _ = tsum _ _ ] => f_equal
    | [ |- trec _ = trec _ ] => f_equal
    | [ |- tvar _ = tvar _ ] => f_equal
    | [ |- tunit = tunit ] => reflexivity
    | [ |- tbool = tbool ] => reflexivity

    | [ |- _ r▻ _        = _ r▻ _        ] => f_equal
    | [ |- context[apTy ?ζ ?τ] ] =>
      change (apTy ζ τ) with τ[ζ]
  end.

Reserved Notation "⟪  i : T r∈ Γ  ⟫"
  (at level 0, i at level 98, Γ at level 98).
Inductive GetEvar : Env → Ix → Ty → Prop :=
  | GetEvarHere {Γ T} :
      ⟪   O : T r∈ Γ r▻ T  ⟫
  | GetEvarThere {Γ T T' i} :
      ⟪   i : T r∈ Γ      ⟫ →
      ⟪ S i : T r∈ Γ r▻ T' ⟫
where "⟪  i : T r∈ Γ  ⟫" := (GetEvar Γ i T).
Hint Constructors GetEvar : ws.

Definition WtRen (Γ₁ Γ₂: Env) (ξ: Sub Ix) : Prop :=
  ∀ i T, ⟪ i : T r∈ Γ₁ ⟫ → ⟪ (ξ i) : T r∈ Γ₂ ⟫.

Lemma getEvarInvHere { Γ T U } :
  ⟪ 0 : T r∈ (Γ r▻ U) ⟫ → T = U.
Proof. inversion 1; auto. Qed.

Lemma getEvarInvThere {Γ i T U} :
  ⟪ (S i) : T r∈ Γ r▻ U ⟫ → ⟪ i : T r∈ Γ ⟫.
Proof. inversion 1; auto. Qed.
Hint Resolve getEvarInvThere : wsi.
