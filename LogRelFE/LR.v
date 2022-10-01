Require Export LogRelFE.PseudoType.
Require Import LogRelFE.LemmasPseudoType.
Require Import StlcFix.SpecSyntax.
Require Import StlcFix.SpecEvaluation.
Require Import StlcFix.SpecTyping.
Require Import StlcFix.Size.
Require Import StlcEqui.SpecSyntax.
Require Import StlcEqui.SpecTyping.
Require Import StlcEqui.SpecEvaluation.
Require Import StlcEqui.Inst.
Require Import StlcEqui.Size.
Require Import UValFE.UVal.

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
    | 0 => fun w => w
    | S i => fun w => pred (lateri i w)
  end.

Definition PTRel := PTy → F.Tm → E.Tm → Prop.
Definition PCRel := PTy → F.PCtx → E.PCtx → Prop.

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

Definition prod_rel (R₁ R₂ : F.Tm → E.Tm → Prop) : F.Tm → E.Tm → Prop :=
  fun ts tu =>
    match ts , tu with
      | F.pair ts₁ ts₂ , E.pair tu₁ tu₂ => R₁ ts₁ tu₁ ∧ R₂ ts₂ tu₂
      | _              , _              => False
    end.
Definition sum_rel (R₁ R₂ : F.Tm → E.Tm → Prop) : F.Tm → E.Tm → Prop :=
  fun ts tu =>
    match ts , tu with
      | F.inl ts' , E.inl tu' => R₁ ts' tu'
      | F.inr ts' , E.inr tu' => R₂ ts' tu'
      | _         , _         => False
    end.
(* Definition arr_rel (R₁ R₂ : F.Tm → E.Tm → Prop) : F.Tm → E.Tm → Prop := *)
(*   fun tsb tub => *)
(*     ∀ ts' tu', *)
(*       R₁ ts' tu' → *)
(*       R₂ (tsb [beta1 ts']) (tub [beta1 tu']). *)

(* Arguments prod_rel R₁ R₂ !ts !tu. *)
Arguments sum_rel R₁ R₂ !ts !tu.
(* Arguments arr_rel R₁ R₂ !ts !tu. *)

Section LogicalRelation.

  Variable (d: Direction).

  Definition Obs (w : World) (ts : F.Tm) (tu : E.Tm) :=
    match d with
      | dir_lt => Observe (lev w) (F.TermHor ts) → E.Terminating tu
      | dir_gt => Observe (lev w) (TermHor tu) → F.Terminating ts
    end.

  Definition contrel' (w : World) (vr' : ∀ w' : World, w' ≤ w → PTRel) : PCRel :=
   fun τ Cs Cu => ∀ w' (fw : w' ≤ w) ts tu, vr' w' fw τ ts tu → Obs w' (F.pctx_app ts Cs) (E.pctx_app tu Cu).

  Definition termrel' (w : World) (vr' : ∀ w' : World, w' ≤ w → PTRel) : PTRel :=
    fun τ ts tu => ∀ Cs Cu,
        F.ECtx Cs → E.ECtx Cu → contrel' w vr' τ Cs Cu →
        Obs w (F.pctx_app ts Cs) (E.pctx_app tu Cu).

  Definition is_inl (t t': F.Tm) : Prop := t = F.inl t'.

  Definition valrel' (w : World) (ind : ∀ w' : World, w' < w → PTRel) : PTRel :=
    fun τ ts tu =>
      OfType τ ts tu ∧
      let latervr : PTRel := fun τ ts tu => ∀ w' (fw : w' < w), ind w' fw τ ts tu in
      let laterlatervr : ∀ w' (fw : w' < w) w'' (fw' : w'' ≤ w'), PTRel := fun w' fw w'' fw' => ind w'' (lt_le fw fw') in
      let vrunit : F.Tm → E.Tm → Prop := fun ts tu => ts = F.unit ∧ tu = E.unit in
      let vrbool : F.Tm → E.Tm → Prop := fun ts tu => (ts = F.true ∧ tu = E.true) ∨ (ts = F.false ∧ tu = E.false) in
      let vrprod : PTy → PTy → F.Tm → E.Tm → Prop :=
          fun τ₁ τ₂ =>
            prod_rel (latervr τ₁) (latervr τ₂) in
      let vrsum : PTy → PTy → F.Tm → E.Tm → Prop :=
          fun τ₁ τ₂ =>
            sum_rel (latervr τ₁) (latervr τ₂) in
      let vrarr : PTy → PTy → F.Tm → E.Tm → Prop :=
          fun τ₁ τ₂ ts tu =>
            exists ts' tu' τ₁' τ₂',
              ts = F.abs τ₁' ts' /\
              tu = E.abs τ₂' tu' /\
            ∀ w' (fw : w' < w) vs vu,
              (d = dir_gt -> E.size vu <= w') ->
              ind w' fw τ₁ vs vu ->
              termrel' w' (laterlatervr w' fw) τ₂ (ts' [beta1 vs]) (tu' [beta1 vu])
      in
      match τ with
        | ptunit => vrunit ts tu
        | ptbool => vrbool ts tu
        | ptprod τ₁ τ₂ => vrprod τ₁ τ₂ ts tu
        | ptsum τ₁ τ₂ => vrsum τ₁ τ₂ ts tu
        | ptarr τ₁ τ₂ => vrarr τ₁ τ₂ ts tu
        | pEmulDV n p τ' => match n with
                           | 0 => ts = F.unit ∧ p = imprecise
                           | S n' => (ts = unkUVal n ∧ p = imprecise) ∨
                                    exists ts',
                                    match unfoldn (LMC τ') τ' with
                                     | E.tunit => is_inl ts ts' ∧ vrunit ts' tu
                                     | E.tbool => is_inl ts ts' ∧ vrbool ts' tu
                                     | E.tprod τ₁ τ₂ => is_inl ts ts' ∧ vrprod (pEmulDV n' p τ₁) (pEmulDV n' p τ₂) ts' tu
                                     | E.tarr τ₁ τ₂ => is_inl ts ts' ∧ vrarr (pEmulDV n' p τ₁) (pEmulDV n' p τ₂) ts' tu
                                     | E.tsum τ₁ τ₂ => is_inl ts ts' ∧ vrsum (pEmulDV n' p τ₁) (pEmulDV n' p τ₂) ts' tu
                                     | E.trec τ'' => False
                                     | E.tvar _ => False
                                     end
                         end
      end.

  Definition valrel (w : World) (τ : PTy)(t₁ : F.Tm) (t₂ : E.Tm) : Prop :=
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

  Definition envrel (w : World) (Γ : PEnv) (γs : Sub F.Tm) (γu : Sub E.Tm) : Prop :=
    ∀ i τ, ⟪ i : τ p∈ Γ ⟫ → valrel w τ (γs i) (γu i).

  Definition OpenLRN (n : nat) (Γ : PEnv) (ts : F.Tm) (tu : E.Tm) (τ : PTy) : Prop :=
    ⟪ repEmulCtx Γ ⊢ ts : repEmul τ ⟫ ∧
    ⟪ fxToIsCtx Γ e⊢ tu : fxToIs τ ⟫ ∧
    (* ⟨ pdom Γ ⊢ tu ⟩ ∧ *)
    ∀ w, lev w ≤ n → ∀ γs γu, envrel w Γ γs γu → termrel w τ (ts [ γs ]) (tu [ γu ]).

  Definition OpenLR (Γ : PEnv) (ts : F.Tm) (tu : E.Tm) (τ : PTy) : Prop :=
    ∀ n, OpenLRN n Γ ts tu τ.

  Definition OpenLRCtxN (n : nat) (Cs : F.PCtx) (Cu : E.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
    ⟪ ⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ , repEmul τ ⟫ ∧
    ⟪ e⊢ Cu : fxToIsCtx Γ' , fxToIs τ' → fxToIsCtx Γ , fxToIs τ ⟫ ∧
    ∀ ts tu, OpenLRN n Γ' ts tu τ' -> OpenLRN n Γ (F.pctx_app ts Cs) (E.pctx_app tu Cu) τ.

  Definition OpenLRCtx (Cs : F.PCtx) (Cu : E.PCtx) (Γ' : PEnv) (τ' : PTy) (Γ : PEnv) (τ : PTy) : Prop :=
    ⟪ ⊢ Cs : repEmulCtx Γ' , repEmul τ' → repEmulCtx Γ' , repEmul τ ⟫ ∧
    ⟪ e⊢ Cu : fxToIsCtx Γ' , fxToIs τ' → fxToIsCtx Γ' , fxToIs τ ⟫ ∧
    ∀ ts tu, OpenLR Γ' ts tu τ' → OpenLR Γ (F.pctx_app ts Cs) (E.pctx_app tu Cu) τ.

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
    (∃ vs vu, clos_refl_trans_1n F.Tm F.eval ts vs ∧ tu -->* vu ∧
              valrel d w τ vs vu) ∨
    (forall Cs Cu, F.ECtx Cs → E.ECtx Cu → Obs d (lateri dfc w) (F.pctx_app ts Cs) (E.pctx_app tu Cu)).

  Arguments termreli₀ d dfc w τ ts tu : simpl never.

  Definition termrel₀ d w τ ts tu :=
    termreli₀ d 0 w τ ts tu.

  Arguments termrel₀ d w τ ts tu : simpl never.

End TermRelZero.

Section TermRelZeroNoDiv.
  Definition termrelnd₀ d w τ ts tu :=
    match d with
    | dir_lt => forall vs, F.Value vs -> clos_refl_trans_1n F.Tm F.eval ts vs ->
                     ∃ vu, E.Value vu /\ tu -->* vu ∧ valrel d w τ vs vu
    | dir_gt => forall vu, E.Value vu -> tu -->* vu ->
                     ∃ vs, F.Value vs /\ clos_refl_trans_1n F.Tm F.eval ts vs ∧ valrel d w τ vs vu
    end.

  Arguments termrelnd₀ d w τ ts tu : simpl never.
End TermRelZeroNoDiv.
