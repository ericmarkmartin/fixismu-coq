Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.LemmasTypes.

Require Export StlcIso.Inst.
Require Export StlcIso.SpecSyntax.

(** * Typing *)

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

(*  a type is closed with an (type variable) environment of size n *)
Inductive ClosedNTy (n : nat) : Ty → Prop :=
    | UnitClosed :
        ClosedNTy n tunit
    | FnClosed {τ τ'} :
        ClosedNTy n τ →
        ClosedNTy n τ' →
        ClosedNTy n (tarr τ τ')
    | ClosedSum {τ τ'} :
        ClosedNTy n τ →
        ClosedNTy n τ' →
        ClosedNTy n (tsum τ τ')
    | ClosedRec {τ} :
        ClosedNTy (S n) τ →
        ClosedNTy n (trec τ)
    | ClosedVar {i} :
        i < n →
        ClosedNTy n (tvar i).

Definition ClosedTy : Ty → Prop := ClosedNTy 0.

Inductive ClosedEnv : Env → Prop :=
  | EmptyClosed : ClosedEnv empty
  | VarClosed {Γ τ} :
      ClosedTy τ →
      ClosedEnv Γ →
      ClosedEnv (evar Γ τ).

Reserved Notation "⟪  Γ i⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98 ).
Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | WtVar {i T} :
      ⟪ i : T r∈ Γ ⟫ →
      ⟪ Γ i⊢ var i : T ⟫
  | WtAbs {t τ₁ τ₂} :
      ⟪ Γ r▻ τ₁ i⊢ t : τ₂ ⟫ →
      ⟪ Γ i⊢ abs τ₁ t : tarr τ₁ τ₂ ⟫
  | WtApp {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ i⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ Γ i⊢ t₂ : τ₁ ⟫ →
      ⟪ Γ i⊢ app t₁ t₂ : τ₂ ⟫
  | WtUnit :
      ⟪ Γ i⊢ unit : tunit ⟫
  | WtTrue :
      ⟪ Γ i⊢ true : tbool ⟫
  | WtFalse :
      ⟪ Γ i⊢ false : tbool ⟫
  | WtIte {t₁ t₂ t₃ T} :
      ⟪ Γ i⊢ t₁ : tbool ⟫ →
      ⟪ Γ i⊢ t₂ : T ⟫ →
      ⟪ Γ i⊢ t₃ : T ⟫ →
      ⟪ Γ i⊢ ite t₁ t₂ t₃ : T ⟫
  | WtPair {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ i⊢ t₁ : τ₁ ⟫ →
      ⟪ Γ i⊢ t₂ : τ₂ ⟫ →
      ⟪ Γ i⊢ pair t₁ t₂ : tprod τ₁ τ₂ ⟫
  | WtProj1 {t τ₁ τ₂} :
      ⟪ Γ i⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ i⊢ proj₁ t : τ₁ ⟫
  | WtProj2 {t τ₁ τ₂} :
      ⟪ Γ i⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ i⊢ proj₂ t : τ₂ ⟫
  | WtInl {t τ₁ τ₂} :
      ⟪ Γ i⊢ t : τ₁ ⟫ →
      ⟪ Γ i⊢ inl t : tsum τ₁ τ₂ ⟫
  | WtInr {t τ₁ τ₂} :
      ⟪ Γ i⊢ t : τ₂ ⟫ →
      ⟪ Γ i⊢ inr t : tsum τ₁ τ₂ ⟫
  | WtCaseof {t₁ t₂ t₃ τ₁ τ₂ T} :
      ⟪ Γ i⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ i⊢ t₂ : T ⟫ →
      ⟪ Γ r▻ τ₂ i⊢ t₃ : T ⟫ →
      ⟪ Γ i⊢ caseof t₁ t₂ t₃ : T ⟫
  | WtFold {t τ} :
      ⟪ Γ i⊢ t : τ[beta1 (trec τ)] ⟫ →
      ⟪ Γ i⊢ fold_ t : trec τ ⟫
  | WtUnfold {t τ} :
      ⟪ Γ i⊢ t : trec τ ⟫ →
      ⟪ Γ i⊢ unfold_ t : τ[beta1 (trec τ)] ⟫
  | WtSeq {t₁ t₂ T} :
      ⟪ Γ i⊢ t₁ : tunit ⟫ →
      ⟪ Γ i⊢ t₂ : T ⟫ →
      ⟪ Γ i⊢ seq t₁ t₂ : T ⟫
where "⟪  Γ i⊢ t : T  ⟫" := (Typing Γ t T).


Reserved Notation "⟪ i⊢ C : Γ₀ , τ₀ → Γ , τ ⟫"
  (at level 0, C at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  i⊢  C  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
Inductive PCtxTyping (Γ₀: Env) (τ₀: Ty) : Env → PCtx → Ty → Prop :=
  | WtPHole :
      ⟪ i⊢ phole : Γ₀, τ₀ → Γ₀, τ₀ ⟫
  | WtPAbs {Γ C τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, τ₂ ⟫ →
      ⟪ i⊢ pabs τ₁ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
  | WtPAppl {Γ C t₂ τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ →
      ⟪ Γ i⊢ t₂ : τ₁ ⟫ →
      ⟪ i⊢ papp₁ C t₂ : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPAppr {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ i⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ i⊢ papp₂ t₁ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPIteI {Γ C t₂ t₃ T} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ , tbool ⟫ →
      ⟪ Γ i⊢ t₂ : T ⟫ →
      ⟪ Γ i⊢ t₃ : T ⟫ →
      ⟪ i⊢ pite₁ C t₂ t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | WtPIteT {Γ t₁ C t₃ T} :
      ⟪ Γ i⊢ t₁ : tbool ⟫ →
      ⟪ i⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ Γ i⊢ t₃ : T ⟫ →
      ⟪ i⊢ pite₂ t₁ C t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | WtPIteE {Γ t₁ t₂ C T} :
      ⟪ Γ i⊢ t₁ : tbool ⟫ →
      ⟪ Γ i⊢ t₂ : T ⟫ →
      ⟪ i⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ i⊢ pite₃ t₁ t₂ C : Γ₀ , τ₀ → Γ , T ⟫
  | WtPPair₁ {Γ C t₂ τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ Γ i⊢ t₂ : τ₂ ⟫ →
      ⟪ i⊢ ppair₁ C t₂ : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | WtPPair₂ {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ i⊢ t₁ : τ₁ ⟫ →
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ i⊢ ppair₂ t₁ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | WtPProj₁ {Γ C τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ i⊢ pproj₁ C : Γ₀, τ₀ → Γ, τ₁ ⟫
  | WtPProj₂ {Γ C τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ i⊢ pproj₂ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | WtPInl {Γ C τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ i⊢ pinl C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | WtPInr {Γ C τ₁ τ₂} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ i⊢ pinr C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | WtPCaseof₁ {Γ C t₂ t₃ τ₁ τ₂ T} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ i⊢ t₂ : T ⟫ →
      ⟪ Γ r▻ τ₂ i⊢ t₃ : T ⟫ →
      ⟪ i⊢ pcaseof₁ C t₂ t₃ : Γ₀, τ₀ → Γ, T ⟫
  | WtPCaseof₂ {Γ t₁ C t₃ τ₁ τ₂ T} :
      ⟪ Γ i⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ i⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, T ⟫ →
      ⟪ Γ r▻ τ₂ i⊢ t₃ : T ⟫ →
      ⟪ i⊢ pcaseof₂ t₁ C t₃ : Γ₀, τ₀ → Γ, T ⟫
  | WtPCaseof₃ {Γ t₁ t₂ C τ₁ τ₂ T} :
      ⟪ Γ i⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ i⊢ t₂ : T ⟫ →
      ⟪ i⊢ C : Γ₀, τ₀ → Γ r▻ τ₂, T ⟫ →
      ⟪ i⊢ pcaseof₃ t₁ t₂ C : Γ₀, τ₀ → Γ, T ⟫
  | WtPFold {Γ C τ} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, τ [beta1 (trec τ)] ⟫ →
      ⟪ i⊢ pfold C : Γ₀, τ₀ → Γ, trec τ ⟫
  | WtPUnfold {Γ C τ} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, trec τ ⟫ →
      ⟪ i⊢ punfold C : Γ₀, τ₀ → Γ, τ [beta1 (trec τ)] ⟫
  | WtPSeq₁ {Γ C t₂ T} :
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, tunit ⟫ →
      ⟪ Γ i⊢ t₂ : T ⟫ →
      ⟪ i⊢ pseq₁ C t₂ : Γ₀, τ₀ → Γ, T ⟫
  | WtPSeq₂ {Γ C t₁ T} :
      ⟪ Γ i⊢ t₁ : tunit ⟫ →
      ⟪ i⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ⟪ i⊢ pseq₂ t₁ C : Γ₀, τ₀ → Γ, T ⟫
where "⟪ i⊢ C : Γ₀ , τ₀ → Γ , τ ⟫" := (PCtxTyping Γ₀ τ₀ Γ C τ).

Lemma pctxtyping_app {Γ₀ t₀ τ₀ Γ C τ} :
  ⟪ Γ₀ i⊢ t₀ : τ₀ ⟫ → ⟪ i⊢ C : Γ₀, τ₀ → Γ , τ ⟫ → ⟪ Γ i⊢ pctx_app t₀ C : τ ⟫.
Proof.
  intros wt₀ wC;
  induction wC; cbn; subst; eauto using Typing.
Qed.

Lemma pctxtyping_cat {Γ₀ τ₀ C₁ Γ₁ τ₁ C₂ Γ₂ τ₂} :
  ⟪ i⊢ C₁ : Γ₀, τ₀ → Γ₁ , τ₁ ⟫ →
  ⟪ i⊢ C₂ : Γ₁, τ₁ → Γ₂ , τ₂ ⟫ →
  ⟪ i⊢ pctx_cat C₁ C₂ : Γ₀, τ₀ → Γ₂ , τ₂ ⟫.
Proof.
  intros wC₁ wC₂.
  induction wC₂; cbn; eauto using PCtxTyping.
Qed.

Definition WtSub (Γ₁ Γ₂: Env) (ζ: Sub Tm) : Prop :=
  ∀ i T, ⟪ i : T r∈ Γ₁ ⟫ → ⟪ Γ₂ i⊢ (ζ i) : T ⟫.
