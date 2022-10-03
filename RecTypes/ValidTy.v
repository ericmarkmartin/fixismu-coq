Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.


Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Max.
Require Import Coq.micromega.Lia.

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

Fixpoint numbFree (τ : Ty) : nat :=
  match τ with
  | tunit => 0
  | tbool => 0
  | τ1 r× τ2 => max (numbFree τ1) (numbFree τ2)
  | τ1 r⊎ τ2 => max (numbFree τ1) (numbFree τ2)
  | τ1 r⇒ τ2 => max (numbFree τ1) (numbFree τ2)
  | trec τ => pred (numbFree τ)
  | tvar i => S i
  end.
Arguments numbFree !τ.

Lemma numbFree_sound τ : ⟨ numbFree τ ⊢ τ ⟩.
Proof.
  induction τ; cbn; constructor.
  - refine (WsTy_mono _ IHτ1); lia.
  - refine (WsTy_mono _ IHτ2); lia.
  - refine (WsTy_mono _ IHτ1); lia.
  - refine (WsTy_mono _ IHτ2); lia.
  - refine (WsTy_mono _ IHτ1); lia.
  - refine (WsTy_mono _ IHτ2); lia.
  - refine (WsTy_mono _ IHτ); lia.
  - induction i; constructor; assumption.
Qed.

Definition decideClosed τ := match numbFree τ with
                             | 0 => B.true
                             | _ => B.false
                             end.

Arguments decideClosed /.
Lemma decideClosed_sound {τ} : Is_true (decideClosed τ) -> ⟨ 0 ⊢ τ ⟩.
Proof.
  unfold decideClosed, WsTy.
  remember (numbFree τ).
  destruct n; intuition.
  rewrite Heqn.
  now eapply numbFree_sound.
Qed.

Lemma numbFree_complete {τ n} : ⟨ n ⊢ τ ⟩ -> numbFree τ <= n.
Proof.
  induction 1; cbn; try lia.
  induction H; lia.
Qed.

Lemma numbFree_complete' {τ} : ⟨ 0 ⊢ τ ⟩ -> numbFree τ = 0.
Proof.
  intros cl.
  cut (numbFree τ <= 0).
  - lia.
  - now eapply numbFree_complete.
Qed.

Lemma decideClosed_complete {τ} : ⟨ 0 ⊢ τ ⟩ -> Is_true (decideClosed τ).
Proof.
  intros cτ.
  assert (nc := numbFree_complete cτ).
  assert (eq : numbFree τ = 0) by lia.
  unfold decideClosed.
  now rewrite eq.
Qed.


Inductive ClosedEnv : Env → Prop :=
  | EmptyClosed : ClosedEnv empty
  | VarClosed {Γ τ} :
      ⟨ 0 ⊢ τ ⟩ →
      ClosedEnv Γ →
      ClosedEnv (evar Γ τ).

#[export]
Hint Constructors wsTy : cty.
#[export]
Hint Constructors ClosedEnv : cenv.

Definition ValidTy : Ty -> Prop := fun τ => ⟨ 0 ⊢ τ ⟩ /\ SimpleContr τ.
Definition ValidEnv : Env -> Prop := fun Γ => ClosedEnv Γ /\ ContrEnv Γ.

Lemma ValidTy_SimpleContr {τ} : ValidTy τ -> SimpleContr τ.
Proof.
  now destruct 1.
Qed.
#[export]
Hint Resolve ValidTy_SimpleContr : simple_contr_rec.

Lemma ValidEnv_nil : ValidEnv empty.
Proof.
  split; constructor; eauto.
Qed.
#[export]
Hint Resolve ValidEnv_nil : tyvalid.

Lemma ValidEnv_cons {Γ τ} : ValidEnv Γ -> ValidTy τ -> ValidEnv (Γ r▻ τ).
Proof.
  intros [env_cl env_contr] [ty_cl ty_contr].
  split; constructor; eauto.
Qed.
#[export]
Hint Resolve ValidEnv_cons : tyvalid.
