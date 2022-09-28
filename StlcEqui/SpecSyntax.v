Require Export Db.Spec.
Require Export Db.WellScoping.

Require Import Coq.micromega.Lia.
Require Export RecTypes.SpecTypes.
Require Export RecTypes.InstTy.
Require Export RecTypes.Contraction.

(** ** Simply typed terms. *)
Inductive Tm : Set :=
  | var (i: Ix)
  | abs (τ: Ty) (t: Tm)
  | app (t₁ t₂: Tm)
  | unit
  | true
  | false
  | ite (t₁ t₂ t₃: Tm)
  | pair (t₁ t₂: Tm)
  | proj₁ (t: Tm)
  | proj₂ (t: Tm)
  | inl (t: Tm)
  | inr (t: Tm)
  | caseof (t₁ t₂ t₃: Tm)
  | seq (t₁ t₂: Tm).

Section WellScoping.

  (* Keep this in a section so that the notation for the ws type-class is only
     locally overwritten. *)
  Inductive wsTm (γ: Dom) : Tm → Prop :=
    | WsVar {i}           : γ ∋ i → ⟨ γ ⊢ var i ⟩
    | WsAbs {τ t}         : ⟨ S γ ⊢ t ⟩ → ⟨ γ ⊢ abs τ t ⟩
    | WsApp {t₁ t₂}       : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ app t₁ t₂ ⟩
    | WsUnit              : ⟨ γ ⊢ unit ⟩
    | WsTrue              : ⟨ γ ⊢ true ⟩
    | WsFalse             : ⟨ γ ⊢ false ⟩
    | WsIte {t₁ t₂ t₃}    : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ →
                            ⟨ γ ⊢ t₃ ⟩ → ⟨ γ ⊢ ite t₁ t₂ t₃ ⟩
    | WsProj1 {t}         : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ proj₁ t ⟩
    | WsProj2 {t}         : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ proj₂ t ⟩
    | WsPair {t₁ t₂}      : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ pair t₁ t₂ ⟩
    | WsInj₁ {t}          : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ inl t ⟩
    | WsInj₂ {t}          : ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ inr t ⟩
    | WsCaseof {t₁ t₂ t₃} : ⟨ γ ⊢ t₁ ⟩ → ⟨ S γ ⊢ t₂ ⟩ →
                            ⟨ S γ ⊢ t₃ ⟩ → ⟨ γ ⊢ caseof t₁ t₂ t₃ ⟩
    | WsSeq {t₁ t₂}       : ⟨ γ ⊢ t₁ ⟩ → ⟨ γ ⊢ t₂ ⟩ → ⟨ γ ⊢ seq t₁ t₂ ⟩
  where "⟨ γ ⊢ t ⟩" := (wsTm γ t).

End WellScoping.
Instance WsTm : Ws Tm := wsTm.

(** ** Program contexts *)

Inductive PCtx : Set :=
  | phole
  | pabs (T: Ty) (C: PCtx)
  | papp₁ (C: PCtx) (t: Tm)
  | papp₂ (t: Tm) (C: PCtx)
  | pite₁ (C: PCtx) (t₂ t₃: Tm)
  | pite₂ (t₁: Tm) (C: PCtx) (t₃: Tm)
  | pite₃ (t₁ t₂: Tm) (C: PCtx)
  | ppair₁ (C: PCtx) (t: Tm)
  | ppair₂ (t: Tm) (C: PCtx)
  | pproj₁ (C: PCtx)
  | pproj₂ (C: PCtx)
  | pinl (C: PCtx)
  | pinr (C: PCtx)
  | pcaseof₁ (C: PCtx) (t₂ t₃: Tm)
  | pcaseof₂ (t₁: Tm) (C: PCtx) (t₃: Tm)
  | pcaseof₃ (t₁ t₂: Tm) (C: PCtx)
  | pseq₁ (C: PCtx) (t: Tm)
  | pseq₂ (t: Tm) (C: PCtx).

Fixpoint pctx_app (t₀: Tm) (C: PCtx) {struct C} : Tm :=
  match C with
    | phole            => t₀
    | pabs T C         => abs T (pctx_app t₀ C)
    | papp₁ C t        => app (pctx_app t₀ C) t
    | papp₂ t C        => app t (pctx_app t₀ C)
    | pite₁ C t₂ t₃    => ite (pctx_app t₀ C) t₂ t₃
    | pite₂ t₁ C t₃    => ite t₁ (pctx_app t₀ C) t₃
    | pite₃ t₁ t₂ C    => ite t₁ t₂ (pctx_app t₀ C)
    | ppair₁ C t       => pair (pctx_app t₀ C) t
    | ppair₂ t C       => pair t (pctx_app t₀ C)
    | pproj₁ C         => proj₁ (pctx_app t₀ C)
    | pproj₂ C         => proj₂ (pctx_app t₀ C)
    | pinl C           => inl (pctx_app t₀ C)
    | pinr C           => inr (pctx_app t₀ C)
    | pcaseof₁ C t₁ t₂ => caseof (pctx_app t₀ C) t₁ t₂
    | pcaseof₂ t₁ C t₂ => caseof t₁ (pctx_app t₀ C) t₂
    | pcaseof₃ t₁ t₂ C => caseof t₁ t₂ (pctx_app t₀ C)
    (* | pfold C => fold_ (pctx_app t₀ C) *)
    (* | punfold C => unfold_ (pctx_app t₀ C) *)
    | pseq₁ C t        => seq (pctx_app t₀ C) t
    | pseq₂ t C        => seq t (pctx_app t₀ C)
  end.

Fixpoint pctx_cat (C₀ C: PCtx) {struct C} : PCtx :=
  match C with
    | phole            => C₀
    | pabs T C         => pabs T (pctx_cat C₀ C)
    | papp₁ C t        => papp₁ (pctx_cat C₀ C) t
    | papp₂ t C        => papp₂ t (pctx_cat C₀ C)
    | pite₁ C t₂ t₃    => pite₁ (pctx_cat C₀ C) t₂ t₃
    | pite₂ t₁ C t₃    => pite₂ t₁ (pctx_cat C₀ C) t₃
    | pite₃ t₁ t₂ C    => pite₃ t₁ t₂ (pctx_cat C₀ C)
    | ppair₁ C t       => ppair₁ (pctx_cat C₀ C) t
    | ppair₂ t C       => ppair₂ t (pctx_cat C₀ C)
    | pproj₁ C         => pproj₁ (pctx_cat C₀ C)
    | pproj₂ C         => pproj₂ (pctx_cat C₀ C)
    | pinl C           => pinl (pctx_cat C₀ C)
    | pinr C           => pinr (pctx_cat C₀ C)
    | pcaseof₁ C t₁ t₂ => pcaseof₁ (pctx_cat C₀ C) t₁ t₂
    | pcaseof₂ t₁ C t₂ => pcaseof₂ t₁ (pctx_cat C₀ C) t₂
    | pcaseof₃ t₁ t₂ C => pcaseof₃ t₁ t₂ (pctx_cat C₀ C)
    | pseq₁ C t        => pseq₁ (pctx_cat C₀ C) t
    | pseq₂ t C        => pseq₂ t (pctx_cat C₀ C)
  end.

Section Application.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {wkY: Wk Y}.
  Context {vrTm: Vr Tm}.
  Context {liftYTm: Lift Y Tm}.

  Fixpoint apTm (ζ: Sub Y) (t: Tm) {struct t} : Tm :=
    match t with
      | var x           => lift (ζ x)
      | abs T t₂        => abs T (apTm (ζ↑) t₂)
      | app t₁ t₂       => app (apTm ζ t₁) (apTm ζ t₂)
      | unit            => unit
      | true            => true
      | false           => false
      | ite t₁ t₂ t₃    => ite (apTm ζ t₁) (apTm ζ t₂) (apTm ζ t₃)
      | pair t₁ t₂      => pair (apTm ζ t₁) (apTm ζ t₂)
      | proj₁ t         => proj₁ (apTm ζ t)
      | proj₂ t         => proj₂ (apTm ζ t)
      | inl t           => inl (apTm ζ t)
      | inr t           => inr (apTm ζ t)
      | caseof t₁ t₂ t₃ => caseof (apTm ζ t₁) (apTm (ζ↑) t₂) (apTm (ζ↑) t₃)
      | seq t₁ t₂       => seq (apTm ζ t₁) (apTm ζ t₂)
    end.

  Global Arguments apTm ζ !t.

End Application.

Ltac crushStlcSyntaxMatchH :=
  match goal with
    | [ H: S _ = S _             |- _ ] => apply eq_add_S in H

    | [ H: var _        = var _        |- _ ] => inversion H; clear H
    | [ H: abs _ _      = abs _ _      |- _ ] => inversion H; clear H
    | [ H: app _ _      = app _ _      |- _ ] => inversion H; clear H
    | [ H: pair _ _     = pair _ _     |- _ ] => inversion H; clear H
    | [ H: ite _ _ _    = ite _ _ _    |- _ ] => inversion H; clear H
    | [ H: proj₁ _      = proj₁ _      |- _ ] => inversion H; clear H
    | [ H: proj₂ _      = proj₂ _      |- _ ] => inversion H; clear H
    | [ H: inl _        = inl _        |- _ ] => inversion H; clear H
    | [ H: inr _        = inr _        |- _ ] => inversion H; clear H
    | [ H: caseof _ _ _ = caseof _ _ _ |- _ ] => inversion H; clear H
    | [ H: seq _ _      = seq _ _      |- _ ] => inversion H; clear H

    | [ H: inl _       = inr _         |- _ ] => inversion H
    | [ H: inr _       = inl _         |- _ ] => inversion H

    | [ H: unit        = abs _ _       |- _ ] => inversion H
    | [ H: true        = abs _ _       |- _ ] => inversion H
    | [ H: false       = abs _ _       |- _ ] => inversion H
    | [ H: pair _ _    = abs _ _       |- _ ] => inversion H
    | [ H: inl _       = abs _ _       |- _ ] => inversion H
    | [ H: inr _       = abs _ _       |- _ ] => inversion H

    | [ |- S _          = S _          ] => f_equal
    | [ |- var _        = var _        ] => f_equal
    | [ |- abs _ _      = abs _ _      ] => f_equal
    | [ |- app _ _      = app _ _      ] => f_equal
    | [ |- unit         = unit         ] => reflexivity
    | [ |- true         = true         ] => reflexivity
    | [ |- false        = false        ] => reflexivity
    | [ |- ite _ _ _    = ite _ _ _    ] => f_equal
    | [ |- pair _ _     = pair _ _     ] => f_equal
    | [ |- proj₁ _      = proj₁ _      ] => f_equal
    | [ |- proj₂ _      = proj₂ _      ] => f_equal
    | [ |- inl _        = inl _        ] => f_equal
    | [ |- inr _        = inr _        ] => f_equal
    | [ |- caseof _ _ _ = caseof _ _ _ ] => f_equal

    | [ |- seq _ _      = seq _ _      ] => f_equal
    | [ |- context[apTm ?ξ ?t] ] =>
      change (apTm ξ t) with t[ξ]
  end.
