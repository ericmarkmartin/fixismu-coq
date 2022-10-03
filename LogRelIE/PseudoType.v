Require Import StlcIsoValid.LemmasEvaluation.
Require Import StlcIsoValid.LemmasTyping.
Require Import StlcIsoValid.SpecEvaluation.
Require Import StlcIsoValid.SpecEquivalent.
Require Import StlcIsoValid.SpecSyntax.
Require Import StlcIsoValid.SpecTyping.
Require Import StlcIsoValid.SpecAnnot.
Require Import StlcEqui.LemmasEvaluation.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.SpecSyntax.
Require Import UValIE.UVal.
Require Import RecTypes.SpecTypes.

Require Import Coq.micromega.Lia.

Module I.
  Include StlcIsoValid.LemmasEvaluation.
  Include StlcIsoValid.LemmasTyping.
  Include StlcIsoValid.SpecEvaluation.
  Include StlcIsoValid.SpecEquivalent.
  Include StlcIsoValid.SpecSyntax.
  Include StlcIsoValid.SpecTyping.
  Include StlcIsoValid.SpecAnnot.
  Include StlcIsoValid.CanForm.
End I.

Module E.
  Include StlcEqui.LemmasEvaluation.
  Include StlcEqui.LemmasTyping.
  Include StlcEqui.SpecEvaluation.
  Include StlcEqui.SpecEquivalent.
  Include StlcEqui.SpecAnnot.
  Include StlcEqui.SpecTyping.
  Include StlcEqui.SpecSyntax.
  Include StlcEqui.CanForm.
End E.

Inductive Prec : Set :=
| precise
| imprecise.

Inductive PTy : Set :=
| ptarr (τ₁ τ₂ : PTy)
| ptunit
| ptbool
| ptprod (τ₁ τ₂ : PTy)
| ptsum (τ₁ τ₂ : PTy)
| ptrec (τ : PTy)
| ptvar (i : Ix)
| pEmulDV (n : nat) (p : Prec) (τ : Ty).

Notation "A p⊎ B" := (ptsum A B) (at level 85, right associativity).
Notation "A p× B" := (ptprod A B) (at level 85, right associativity).
Notation "A p⇒ B" := (ptarr A B) (at level 85, right associativity).

Fixpoint repEmul (τ : PTy) : Ty :=
  match τ with
    | ptarr τ₁ τ₂ => tarr (repEmul τ₁) (repEmul τ₂)
    | ptunit => tunit
    | ptbool => tbool
    | ptprod τ₁ τ₂ => tprod (repEmul τ₁) (repEmul τ₂)
    | ptsum τ₁ τ₂ => tsum (repEmul τ₁) (repEmul τ₂)
    | ptrec τ => trec (repEmul τ)
    | ptvar i => tvar i
    | pEmulDV n p T => UValIE n T
  end.

Fixpoint isToEq (τ : PTy) : Ty :=
  match τ with
    | ptunit => tunit
    | ptbool => tbool
    | ptprod τ₁ τ₂ => tprod (isToEq τ₁) (isToEq τ₂)
    | ptarr τ₁ τ₂ => tarr (isToEq τ₁) (isToEq τ₂)
    | ptsum τ₁ τ₂ => tsum (isToEq τ₁) (isToEq τ₂)
    | ptrec τ => trec (isToEq τ)
    | ptvar i => tvar i
    | pEmulDV n p T => T
  end.

Definition OfTypeStlcIso (τ : PTy) (t : I.Tm) : Prop :=
  I.Value t ∧ (I.Typing empty t (repEmul τ) ).

(* Fixpoint OfTypeStlcIso' (τ : PTy) (t : U.UTm) : Prop := *)
(*   match τ with *)
(*     | ptarr τ₁ τ₂ => *)
(*       match t with *)
(*         | U.abs _ => True *)
(*         | _       => False *)
(*       end *)
(*     | ptunit => t = U.unit *)
(*     (* | ptbool => t = U.true ∨ t = U.false *) *)
(*     (* | ptprod τ₁ τ₂ => *) *)
(*     (*   match t with *) *)
(*     (*     | U.pair t₁ t₂ => OfTypeStlcIso' τ₁ t₁ ∧ OfTypeStlcIso' τ₂ t₂ *) *)
(*     (*     | _            => False *) *)
(*     (*   end *) *)
(*     | ptsum τ₁ τ₂ => *)
(*       match t with *)
(*         | U.inl t₁ => OfTypeStlcIso' τ₁ t₁ *)
(*         | U.inr t₂ => OfTypeStlcIso' τ₂ t₂ *)
(*         | _        => False *)
(*       end *)
(*     | pEmulDV n p => U.Value t *)
(*   end. *)
(* Arguments OfTypeStlcIso' !τ !t /. *)

Definition OfTypeStlcEqui (τ : PTy) (t : E.Tm) : Prop :=
  E.Value t ∧ E.Typing empty t (isToEq τ).

Arguments OfTypeStlcIso !τ !t /.

Definition OfType (τ : PTy) (t₁ : I.Tm) (t₂ : E.Tm) : Prop :=
  OfTypeStlcIso τ t₁ ∧ OfTypeStlcEqui τ t₂.

Inductive PEnv : Set :=
| pempty
| pevar (Γ : PEnv) (τ : PTy).

Notation "Γ p▻ T" := (pevar Γ T) (at level 55, left associativity).

Fixpoint pdom (Γ : PEnv) : Dom :=
  match Γ with
    | pempty => 0
    | pevar Γ _ => S (pdom Γ)
  end.

Inductive wsPTy (γ : Dom) : PTy → Prop :=
| WsPTUnit : wsPTy γ ptunit
| WsPBool : wsPTy γ ptbool
| WsPFn {τ τ'} : wsPTy γ τ → wsPTy γ τ' → wsPTy γ (τ p⇒ τ')
| WsPSum {τ τ'} : wsPTy γ τ → wsPTy γ τ' → wsPTy γ (τ p⊎ τ')
| WsPProd {τ τ'} : wsPTy γ τ → wsPTy γ τ' → wsPTy γ (τ p× τ')
| WsPRec {τ} : wsPTy (S γ) τ → wsPTy γ (ptrec τ)
| WsPTVar {i} : γ ∋ i → wsPTy γ (ptvar i)
| WsPEmulDv {n p τ} : wsTy 0 τ → wsPTy γ (pEmulDV n p τ).

Section WellScoping.

  Inductive innerPClosed : PTy → Prop :=
    | innerPUnitClosed : innerPClosed ptunit
    | innerPBoolClosed : innerPClosed ptbool
    | innerPFnClosed {τ τ'} : innerPClosed τ → innerPClosed τ' → innerPClosed (τ p⇒ τ)
    | innerPSumClosed {τ τ'} : innerPClosed τ → innerPClosed τ' → innerPClosed (τ p⊎ τ)
    | innerPProdClosed {τ τ'} : innerPClosed τ → innerPClosed τ' → innerPClosed (τ p× τ)
    | innerPRecClosed {τ} : innerPClosed τ → innerPClosed (ptrec τ)
    | innerPVarClosed {i} : innerPClosed (ptvar i)
    | innerPEmulDvClosed {n p τ} : ⟨ 0 ⊢ τ ⟩ → innerPClosed (pEmulDV n p τ).

  Lemma WsPTy_mono {n m : nat} {τ} : n <= m → wsPTy n τ → wsPTy m τ.
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

#[export]
Instance WsPTy : Ws PTy := wsPTy.

(* #[refine] Instance vrPTy : Vr PTy := {| vr := ptvar |}. *)
(* Proof. inversion 1; auto. Defined. *)

(* Instance wsVrPTy: WsVr PTy. *)
(* Proof. *)
(*   constructor. *)
(*   - now constructor. *)
(*   - now inversion 1. *)
(* Qed. *)

Section Application.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {wkY: Wk Y}.

  Context {vrPTy: Vr PTy}.
  Context {liftYPTy: Lift Y PTy}.

  Fixpoint apPTy (ζ: Sub Y) (τ: PTy) {struct τ} : PTy :=
    match τ with
      | ptarr τ₁ τ₂ => ptarr (apPTy ζ τ₁) (apPTy ζ τ₂)
      | ptunit => ptunit
      | ptbool => ptbool
      | ptprod τ₁ τ₂ => ptprod (apPTy ζ τ₁) (apPTy ζ τ₂)
      | ptsum τ₁ τ₂ => ptsum (apPTy ζ τ₁) (apPTy ζ τ₂)
      | ptrec τ => ptrec (apPTy (ζ↑) τ)
      | ptvar α => lift (ζ α)
      | pEmulDV n p τ => pEmulDV n p τ
          (* let ζ := fun (i : Ix) => isToEq (ζ i) in *)
          (* pEmulDV n p (apTy ζ τ) *)
    end.

  Global Arguments apPTy ζ !τ.
End Application.

(* Fixpoint subt (T T' : Ty) (i : Ix) {struct T} : Ty := *)
(*   match T with *)
(*   | tarr τ τ' => *)
(*     let A := subt τ T' i in *)
(*     let B := subt τ' T' i in *)
(*     (tarr A B) *)
(*   | tunit => tunit *)
(*   | tsum τ τ' => *)
(*     let A := (⟪ τ : i -> T' ⟫) in *)
(*     let B := (⟪ τ' : i -> T' ⟫) in *)
(*     (tsum A B) *)
(*   end *)
(*  where "⟪ T : i -> S ⟫" := (subt T S i). *)








(* Lemma ValidTy_invert_arr  *)

(* Ltac crushValidTyMatch := *)
(*   try assumption; *)
(*   match goal with *)
(*   | H: ⟨ _ ⊢ ?τ ⟩ |- ⟨ _ ⊢ ?τ ⟩ => refine (WsTy_mono _ H) *)
(*   | H : ValidTy ?τ |- SimpleContr ?τ => exact (proj2 H) *)
(*   | H : ValidTy ?τ |- SimpleRec ?τ => eapply SimpleRecContr *)
(*   | H : ValidTy ?τ |- ⟨ 0 ⊢ ?τ ⟩ => exact (proj1 H) *)
(*   | H : ValidTy ?τ |- ⟨ _ ⊢ ?τ ⟩ => refine (WsTy_mono _ (proj1 H)) *)
(*   | H: ValidTy (_ r⇒ _) |- _ => eapply ValidTy_invert_arr in H; destruct H as (? & ?) *)
(*   | H: ValidTy (_ r× _) |- _ => eapply ValidTy_invert_prod in H; destruct H as (? & ?) *)
(*   | H: ValidTy (_ r⊎ _) |- _ => eapply ValidTy_invert_sum in H; destruct H as (? & ?) *)
(*   | |- SimpleContr (trec _) => constructor *)
(*   | |- SimpleContr (_ r× _) => constructor *)
(*   | |- SimpleContr (_ r⇒ _) => constructor *)
(*   | |- SimpleContr (_ r⊎ _) => constructor *)
(*   | |- SimpleContr tunit => constructor *)
(*   | |- SimpleContr tbool => constructor *)
(*   | |- SimpleContr (tvar _) => constructor *)
(*   | |- SimpleRec (trec _) => constructor *)
(*   | |- SimpleRec (_ r× _) => constructor *)
(*   | |- SimpleRec (_ r⇒ _) => constructor *)
(*   | |- SimpleRec (_ r⊎ _) => constructor *)
(*   | |- SimpleRec tunit => constructor *)
(*   | |- SimpleRec tbool => constructor *)
(*   | |- SimpleRec (tvar _) => constructor *)
(*   | |- ValidTy _ => split *)
(*   | |- ValidEnv empty => eapply ValidEnv_nil *)
(*   | |- ValidEnv (_ r▻ _) => eapply ValidEnv_cons *)
(*   | |- ⟨ _ ⊢ trec _ ⟩ => constructor *)
(*   | |- ⟨ _ ⊢ _ r× _ ⟩ => constructor *)
(*   | |- ⟨ _ ⊢ _ r⊎ _ ⟩ => constructor *)
(*   | |- ⟨ _ ⊢ _ r⇒ _ ⟩ => constructor *)
(*   | |- ⟨ _ ⊢ tunit ⟩ => constructor *)
(*   | |- ⟨ _ ⊢ tbool ⟩ => constructor *)
(*   | |- ⟨ _ ⊢ tvar _ ⟩ => constructor *)
(*   | |- wsTy ?n ?τ => change (⟨ n ⊢ τ ⟩) *)
(*   | H: ⟨ 0 ⊢ ?τ ⟩ |- context [ ?τ [ ?σ ] ] => rewrite (wsClosed_invariant (x := τ)) *)
(*   | H: SimpleContr ?τ |- SimpleRec ?τ => eapply SimpleRecContr *)
(* (* , H2: ⟨ 0 ⊢ ?τ ⟩  *) *)
(*   end. *)


(* Ltac crushValidTy := *)
(*   repeat (crushValidTyMatch; try lia; eauto with ws wsi). *)

(* Hint Extern 20 (ValidTy _) => *)
(*   crushValidTy : tyvalid2. *)

(* Hint Extern 20 (Closed_SimpleRec_SimpleContr _) => *)
(*   crushValidTy : tyvalid2. *)

Ltac crushPTypesMatchH :=
  match goal with
    | [ H: S _ = S _             |- _ ] => apply eq_add_S in H
    | [ H: ptarr _ _  = ptarr _ _  |- _ ] => inversion H; clear H
    | [ H: ptprod _ _ = ptprod _ _ |- _ ] => inversion H; clear H
    | [ H: ptsum _ _  = ptsum _ _  |- _ ] => inversion H; clear H
    | [ H: ptrec _ = ptrec _ |- _ ] => inversion H; clear H
    | [ H: ptvar _ = ptvar _ |- _ ] => inversion H; clear H

    | [ |- ptarr _ _ = ptarr _ _ ] => f_equal
    | [ |- ptprod _ _ = ptprod _ _ ] => f_equal
    | [ |- ptsum _ _ = ptsum _ _ ] => f_equal
    | [ |- ptrec _ = ptrec _ ] => f_equal
    | [ |- ptvar _ = ptvar _ ] => f_equal
    | [ |- ptunit = ptunit ] => reflexivity
    | [ |- ptbool = ptbool ] => reflexivity

    | [ |- _ p▻ _        = _ p▻ _        ] => f_equal
    | [ |- context[apPTy ?ζ ?τ] ] =>
      change (apPTy ζ τ) with τ[ζ]
  end.

Reserved Notation "⟪  i : T p∈ Γ  ⟫"
  (at level 0, i at level 98, Γ at level 98).
Inductive GetEvarP : PEnv → Ix → PTy → Prop :=
  | GetEvarHere {Γ T} :
      ⟪   O : T p∈ Γ p▻ T  ⟫
  | GetEvarThere {Γ T T' i} :
      ⟪   i : T p∈ Γ      ⟫ →
      ⟪ S i : T p∈ Γ p▻ T' ⟫
where "⟪  i : T p∈ Γ  ⟫" := (GetEvarP Γ i T).

Lemma pdom_works {i T Γ} :
  ⟪ i : T p∈ Γ ⟫ → pdom Γ ∋ i.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma pdom_works_inv {i Γ} :
  pdom Γ ∋ i → ∃ τ, ⟪ i : τ p∈ Γ ⟫.
Proof.
  revert i. induction Γ; intros i.
  - inversion 1.
  - inversion 1.
    + subst. exists τ. constructor.
    + subst. destruct (IHΓ i0 H1) as (τ0 & iinΓ).
      exists τ0. constructor. assumption.
Qed.

Fixpoint repEmulCtx (Γ : PEnv) : Env :=
  match Γ with
    | pempty => empty
    | pevar Γ τ => evar (repEmulCtx Γ) (repEmul τ)
  end.

Lemma repEmulCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  GetEvar (repEmulCtx Γ) i (repEmul τ).
Proof.
  induction 1; eauto using GetEvar.
Qed.

Fixpoint isToEqCtx (Γ : PEnv) : Env :=
  match Γ with
  | pempty => empty
  | pevar Γ τ => evar (isToEqCtx Γ) (isToEq τ)
  end.

Lemma isToEqCtx_works {Γ i τ} :
  ⟪ i : τ p∈ Γ ⟫ →
  E.GetEvar (isToEqCtx Γ) i (isToEq τ).
Proof.
  induction 1; eauto using E.GetEvar.
Qed.

Fixpoint embed (τ : Ty) : PTy :=
  match τ with
    | tunit => ptunit
    | tarr τ₁ τ₂ => ptarr (embed τ₁) (embed τ₂)
    | tbool => ptbool
    | tprod τ₁ τ₂ => ptprod (embed τ₁) (embed τ₂)
    | tsum τ₁ τ₂ => ptsum (embed τ₁) (embed τ₂)
    | trec τ => ptrec (embed τ)
    | tvar i => ptvar i
  end.

Fixpoint embedCtx (Γ : Env) : PEnv :=
  match Γ with
    | empty => pempty
    | evar Γ τ => pevar (embedCtx Γ) (embed τ)
  end.

Lemma embedCtx_works {Γ i τ} :
  GetEvar Γ i τ →
  ⟪ i : embed τ p∈ embedCtx Γ ⟫.
Proof.
  induction 1; eauto using GetEvarP.
Qed.

Lemma embedCtx_works_inv {Γ i τ} :
  ⟪ i : τ p∈ embedCtx Γ ⟫ →
  exists τ', τ = embed τ' ∧ (GetEvar Γ i τ').
Proof.
  revert i τ. induction Γ; intros i τ' iτ; simpl in *; inversion iτ; subst.
  - exists τ; intuition.
  - destruct (IHΓ _ _ H3) as [τ'' [eq ty]].
    exists τ''; intuition; eauto using GetEvarP.
Qed.

Lemma OfTypeStlcIso_isToEq {vu τ τ'}:
  isToEq τ = isToEq τ' ->
  OfTypeStlcEqui τ vu ->
  OfTypeStlcEqui τ' vu.
Proof.
  intros eq [vvu tyu].
  split; [assumption|].
  now rewrite <-eq.
Qed.
