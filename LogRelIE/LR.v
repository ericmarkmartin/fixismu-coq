Require Export LogRelIE.PseudoType.
Require Import LogRelIE.LemmasPseudoType.
Require Import StlcIsoValid.SpecSyntax.
Require Import StlcIsoValid.SpecEvaluation.
Require Import StlcIsoValid.SpecTyping.
Require Import StlcIsoValid.Size.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.Inst.
Require Import StlcEqui.Size.
Require Import UValIE.UVal.

Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.

Inductive Direction : Set :=
| dir_lt
| dir_gt.

Definition World := nat.
Definition lev : World → nat := fun w => w.
Definition later : World → World := pred.
Fixpoint lateri (i : nat) : World → World :=
  match i with
    | 0 => fun x => x
    | S i => fun w => pred (lateri i w)
  end.

Definition PTRel := PTy → I.Tm → E.Tm → Prop.
Definition PCRel := PTy → I.PCtx → E.PCtx → Prop.

(* Intuitively: observing termination takes a step in addition to the actual evaluation steps *)
Definition Observe (n : nat) (T : nat → Prop) : Prop :=
  match n with
    | 0 => False
    | S n' => T n'
  end.

Lemma lt_le {w w' w''} (fw : w' < w) (fw' : w'' ≤ w') : w'' < w.
Proof.
  lia.
Defined.

Definition prod_rel (R₁ R₂ : I.Tm → E.Tm → Prop) : I.Tm → E.Tm → Prop :=
  fun ts tu =>
    match ts , tu with
      | I.pair ts₁ ts₂ , E.pair tu₁ tu₂ => R₁ ts₁ tu₁ ∧ R₂ ts₂ tu₂
      | _              , _              => False
    end.
Definition sum_rel (R₁ R₂ : I.Tm → E.Tm → Prop) : I.Tm → E.Tm → Prop :=
  fun ts tu =>
    match ts , tu with
      | I.inl ts' , E.inl tu' => R₁ ts' tu'
      | I.inr ts' , E.inr tu' => R₂ ts' tu'
      | _         , _         => False
    end.
(* Definition arr_rel (R₁ R₂ : F.Tm → I.Tm → Prop) : F.Tm → I.Tm → Prop := *)
(*   fun tsb tub => *)
(*     ∀ ts' tu', *)
(*       R₁ ts' tu' → *)
(*       R₂ (tsb [beta1 ts']) (tub [beta1 tu']). *)

(* Arguments prod_rel R₁ R₂ !ts !tu. *)
Arguments sum_rel R₁ R₂ !ts !tu.
(* Arguments arr_rel R₁ R₂ !ts !tu. *)

Section LogicalRelation.

  Variable (d: Direction).

  Definition Obs (w : World) (ts : I.Tm) (tu : E.Tm) :=
    match d with
      | dir_lt => Observe (lev w) (I.TermHor ts) → E.Terminating tu
      | dir_gt => Observe (lev w) (TermHor tu) → I.Terminating ts
    end.

  Definition contrel' (w : World) (vr' : ∀ w' : World, w' ≤ w → PTRel) : PCRel :=
   fun τ Cs Cu => ∀ w' (fw : w' ≤ w) ts tu, vr' w' fw τ ts tu → Obs w' (I.pctx_app ts Cs) (E.pctx_app tu Cu).

  Definition termrel' (w : World) (vr' : ∀ w' : World, w' ≤ w → PTRel) : PTRel :=
    fun τ ts tu => ∀ Cs Cu,
        I.ECtx Cs → E.ECtx Cu → contrel' w vr' τ Cs Cu →
        Obs w (I.pctx_app ts Cs) (E.pctx_app tu Cu).

  Definition is_inl (t t': I.Tm) : Prop := t = I.inl t'.

  Fixpoint has_n_folds (n : nat) (t : I.Tm) (t' : I.Tm) :=
    match n with
    | 0 => t = t'
    | S n => exists t2, t = I.fold_ t2 /\ has_n_folds n t2 t'
    end.


  (* ERROR: in the case for ptrec, we need to allow fold_s for the StlcIso term! *)
  Definition valrel' (w : World) (ind : ∀ (w' : World), w' < w → PTRel) : PTRel :=
    fun τ ts tu =>
      OfType τ ts tu ∧
      let latervr : PTRel := fun τ ts tu => ∀ w' (fw : w' < w), ind w' fw τ ts tu in
      let laterlatervr : ∀ w' (fw : w' < w) w'' (fw' : w'' ≤ w'), PTRel := fun w' fw w'' fw' => ind w'' (lt_le fw fw') in
      let vrunit : I.Tm → E.Tm → Prop := fun ts tu => ts = I.unit ∧ tu = E.unit in
      let vrbool : I.Tm → E.Tm → Prop := fun ts tu => (ts = I.true ∧ tu = E.true) ∨ (ts = I.false ∧ tu = E.false) in
      let vrprod : PTy → PTy → I.Tm → E.Tm → Prop :=
          fun τ₁ τ₂ =>
            prod_rel (latervr τ₁) (latervr τ₂) in
      let vrsum : PTy → PTy → I.Tm → E.Tm → Prop :=
          fun τ₁ τ₂ =>
            sum_rel (latervr τ₁) (latervr τ₂) in
      let vrarr : PTy → PTy → I.Tm → E.Tm → Prop :=
          fun τ₁ τ₂ ts tu =>
            exists ts' tu' τ₁' τ₂',
              ts = I.abs τ₁' ts' /\
              tu = E.abs τ₂' tu' /\
            ∀ w' (fw : w' < w) vs vu,
              (d = dir_gt -> E.size vu <= w') ->
              ind w' fw τ₁ vs vu ->
              termrel' w' (laterlatervr w' fw) τ₂ (ts' [beta1 vs]) (tu' [beta1 vu])
      in
      exists ts2, has_n_folds (LMC_pty τ) ts ts2 /\ I.Value ts /\
      match pUnfoldn (LMC_pty τ) τ with
      | ptunit => vrunit ts2 tu
      | ptbool => vrbool ts2 tu
      | ptprod τ₁ τ₂ => vrprod τ₁ τ₂ ts2 tu
      | ptsum τ₁ τ₂ => vrsum τ₁ τ₂ ts2 tu
      | ptarr τ₁ τ₂ => vrarr τ₁ τ₂ ts2 tu
      | ptrec _ => False
      | ptvar _ => False
      | pEmulDV n p τ' => match n with
                         | 0 => ts2 = I.unit ∧ p = imprecise
                         | S n' => (ts2 = unkUVal n ∧ p = imprecise) ∨
                                  exists ts',
                                  match unfoldn (LMC τ') τ' with
                                   | tunit => is_inl ts2 ts' ∧ vrunit ts' tu
                                   | tbool => is_inl ts2 ts' ∧ vrbool ts' tu
                                   | tprod τ₁ τ₂ => is_inl ts2 ts' ∧ vrprod (pEmulDV n' p τ₁) (pEmulDV n' p τ₂) ts' tu
                                   | tarr τ₁ τ₂ => is_inl ts2 ts' ∧ vrarr (pEmulDV n' p τ₁) (pEmulDV n' p τ₂) ts' tu
                                   | tsum τ₁ τ₂ => is_inl ts2 ts' ∧ vrsum (pEmulDV n' p τ₁) (pEmulDV n' p τ₂) ts' tu
                                   | trec τ'' => False
                                   | tvar _ => False
                                   end
                       end
      end.

  Definition valrel (w : World) (τ : PTy)(t₁ : I.Tm) (t₂ : E.Tm) : Prop :=
    Fix lt_wf (fun w => PTRel) valrel' w τ t₁ t₂.

  Lemma valrel_def_funext w (ind₁ ind₂ : ∀ w', w' < w → PTRel) :
    (∀ w' (fw : w' < w), ind₁ w' fw = ind₂ w' fw) →
    valrel' w ind₁ = valrel' w ind₂.
  Proof.
    intros.
    enough (ind₁ = ind₂) as -> by auto.
    extensionality w'.
    extensionality fw.
    trivial.
  Qed.

  Lemma valrel_fixp : ∀ w, valrel w = valrel' w (fun w _ => valrel w).
  Proof.
    refine (Fix_eq lt_wf (fun w => PTRel) valrel' valrel_def_funext).
  Qed.

  Definition contrel (w : World) : PCRel :=
    contrel' w (fun w fw => valrel w).

  Definition termrel (w : World) : PTRel :=
    termrel' w (fun w fw => valrel w).

  Lemma termrel_fixp :
    ∀ w, termrel w = termrel' w (fun w _ => valrel' w (fun w _ => valrel w)).
  Proof.
    unfold termrel.
    intros w.
    f_equal.
    (* Should we avoid functional extensionality? *)
    extensionality w'.
    extensionality fw.
    apply valrel_fixp.
  Qed.

  Definition envrel (w : World) (Γ : PEnv) (γs : Sub I.Tm) (γu : Sub E.Tm) : Prop :=
    ∀ i τ, ⟪ i : τ p∈ Γ ⟫ → valrel w τ (γs i) (γu i).

  Definition OpenLRN (n : nat) (Γ : PEnv) (ts : I.Tm) (tu : E.Tm) (τ : PTy) : Prop :=
    ⟪ repEmulCtx Γ i⊢ ts : repEmul τ ⟫ ∧
    ⟪ isToEqCtx Γ e⊢ tu : isToEq τ ⟫ ∧
    (* ⟨ pdom Γ ⊢ tu ⟩ ∧ *)
    ∀ w, lev w ≤ n → ∀ γs γu, envrel w Γ γs γu → termrel w τ (ts [ γs ]) (tu [ γu ]).

  Definition OpenLR (Γ : PEnv) (ts : I.Tm) (tu : E.Tm) (τ : PTy) : Prop :=
    ∀ n, OpenLRN n Γ ts tu τ.

  Definition OpenLRCtxN (n : nat) (Cs : I.PCtx) (Cu : E.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
    ⟪ i⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ , repEmul τ ⟫ ∧
    ⟪ e⊢ Cu : isToEqCtx Γ' , isToEq τ' → isToEqCtx Γ , isToEq τ ⟫ ∧
    ∀ ts tu, OpenLRN n Γ' ts tu τ' -> OpenLRN n Γ (I.pctx_app ts Cs) (E.pctx_app tu Cu) τ.

  Definition OpenLRCtx (Cs : I.PCtx) (Cu : E.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
    ⟪ i⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ' , repEmul τ ⟫ ∧
    ⟪ e⊢ Cu : isToEqCtx Γ' , isToEq τ' → isToEqCtx Γ' , isToEq τ ⟫ ∧
    ∀ ts tu, OpenLR Γ' ts tu τ' → OpenLR Γ (I.pctx_app ts Cs) (E.pctx_app tu Cu) τ.

End LogicalRelation.

Arguments termrel d w τ t₁ t₂ : simpl never.
Arguments valrel d w τ t₁ t₂ : simpl never.
Arguments valrel' d w ind !τ !t₁ !t₂ /.

Notation "⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ ⟫" := (OpenLRN d n Γ ts tu τ)
  (at level 0, ts at level 98,
   d at level 98, n at level 98,
   tu at level 98,
   Γ at level 98, τ at level 98,
   format "⟪ Γ ⊩  ts ⟦ d , n ⟧ tu  :  τ  ⟫").

Notation "⟪ Γ ⊩ ts ⟦ d ⟧ tu : τ ⟫" := (OpenLR d Γ ts tu τ)
  (at level 0, ts at level 98,
   d at level 98, tu at level 98,
   Γ at level 98, τ at level 98,
   format "⟪ Γ ⊩  ts ⟦ d ⟧ tu  :  τ  ⟫").

Notation "⟪ ⊩ Cs ⟦ d , n ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫" := (OpenLRCtxN d n Cs Cu Γ₀ τ₀ Γ τ)
  (at level 0, Cs at level 98,
   d at level 98, n at level 98,
   Cu at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ⊩  Cs ⟦ d , n ⟧ Cu  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").

Notation "⟪ ⊩ Cs ⟦ d ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫" := (OpenLRCtx d Cs Cu Γ₀ τ₀ Γ τ)
  (at level 0, Cs at level 98,
   d at level 98, Cu at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ⊩  Cs ⟦ d ⟧ Cu  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").

Section TermRelZero.
  Definition termreli₀ d dfc w τ ts tu :=
    (∃ vs vu, clos_refl_trans_1n I.Tm I.eval ts vs ∧ tu -->* vu ∧
              valrel d w τ vs vu) ∨
    (forall Cs Cu, I.ECtx Cs → E.ECtx Cu → Obs d (lateri dfc w) (I.pctx_app ts Cs) (E.pctx_app tu Cu)).

  Arguments termreli₀ d dfc w τ ts tu : simpl never.

  Definition termrel₀ d w τ ts tu :=
    termreli₀ d 0 w τ ts tu.

  Arguments termrel₀ d w τ ts tu : simpl never.

End TermRelZero.

Section TermRelZeroNoDiv.
  Definition termrelnd₀ d w τ ts tu :=
    match d with
    | dir_lt => forall vs, I.Value vs -> clos_refl_trans_1n I.Tm I.eval ts vs ->
                     ∃ vu, E.Value vu /\ tu -->* vu ∧ valrel d w τ vs vu
    | dir_gt => forall vu, E.Value vu -> tu -->* vu ->
                     ∃ vs, I.Value vs /\ clos_refl_trans_1n I.Tm I.eval ts vs ∧ valrel d w τ vs vu
    end.

  Arguments termrelnd₀ d w τ ts tu : simpl never.
End TermRelZeroNoDiv.
