Require Export StlcFix.SpecSyntax.
Require Export StlcFix.SpecEvaluation.
Require Export StlcFix.SpecTyping.
Require Export StlcFix.SpecAnnot.
Require Export StlcFix.LemmasTyping.
Require Export StlcFix.LemmasEvaluation.

Definition stlcOmega (ty : Ty) : Tm :=
  app (fixt tunit ty (abs (tunit ⇒ ty) (var 0))) unit.

Lemma stlcOmegaT {Γ ty} : ⟪ Γ ⊢ stlcOmega ty : ty ⟫.
Proof.
  unfold stlcOmega. crushTyping.
Qed.

Definition stlcOmegaA (τ : Ty) : TmA :=
  a_app tunit τ (a_fixt tunit τ (a_abs (tunit ⇒ τ) (tunit ⇒ τ) (a_var 0))) a_unit.

Lemma stlcOmegaAT {Γ ty} : ⟪ Γ a⊢ stlcOmegaA ty : ty ⟫.
Proof.
  unfold stlcOmegaA.
  repeat constructor.
Qed.

Lemma eraseAnnot_stlcOmegaA {τ} :
  eraseAnnot (stlcOmegaA τ) = stlcOmega τ.
Proof.
  unfold stlcOmegaA, stlcOmega.
  now cbn.
Qed.

Hint Resolve stlcOmegaT : typing.
Hint Resolve stlcOmegaAT : typing.

Definition stlcOmegaHelp (ty : Ty) : Tm :=
  app (abs tunit (app (fixt tunit ty (abs (tunit ⇒ ty) (var 0))) (var 0))) unit.

Lemma stlcOmega_cycles {ty} : stlcOmega ty -->+ stlcOmega ty.
Proof.
  cut (stlcOmega ty --> stlcOmegaHelp ty ∧ stlcOmegaHelp ty --> stlcOmega ty).
  - destruct 1. eauto with eval.
  - unfold stlcOmega, stlcOmegaHelp; split.
    + apply (eval_ctx₀ (papp₁ phole unit)); constructor.
    + apply (eval_ctx₀ phole); repeat constructor.
Qed.

Lemma stlcOmega_div {ty} : (stlcOmega ty)⇑.
Proof.
  apply cycles_dont_terminate.
  apply stlcOmega_cycles.
Qed.

Lemma stlcOmega_sub {ty γ} : (stlcOmega ty)[γ] = stlcOmega ty.
Proof.
  unfold stlcOmega.
  simpl; trivial.
Qed.

Arguments stlcOmega : simpl never.
