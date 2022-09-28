Require Export StlcFix.Inst.
Require Export StlcFix.SpecSyntax.
Require Export StlcFix.SpecTyping.
Require Export StlcFix.LemmasTyping.

(* a fully annotated version of iso-recursive terms. *)
Inductive TmA : Set :=
  | a_var (i: Ix)
  | a_abs (τ1 τ2 : Ty) (t: TmA)
  | a_app (τ1 τ2 : Ty) (t₁ t₂ : TmA)
  | a_unit
  | a_true
  | a_false
  | a_ite (τ : Ty) (t₁ t₂ t₃: TmA)
  | a_pair (τ1 τ2 : Ty) (t₁ t₂: TmA)
  | a_proj₁ (τ1 τ2 : Ty) (t: TmA)
  | a_proj₂ (τ1 τ2 : Ty) (t: TmA)
  | a_inl (τ1 τ2 : Ty) (t: TmA)
  | a_inr (τ1 τ2 : Ty) (t: TmA)
  | a_caseof (τ1 τ2 τ : Ty) (t₁ t₂ t₃: TmA)
  | a_seq (τ : Ty) (t₁ t₂: TmA)
  | a_fixt (τ₁ τ₂ : Ty) (t: TmA).

Reserved Notation "⟪  Γ a⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98 ).
Inductive AnnotTyping (Γ : Env) : TmA -> Ty -> Prop :=
  | a_WtVar {i τ} :
      ⟪ i : τ ∈ Γ ⟫ →
      ⟪ Γ a⊢ a_var i : τ ⟫
  | a_WtAbs {t τ₁ τ₂} :
      ⟪ Γ ▻ τ₁ a⊢ t : τ₂ ⟫ →
      ⟪ Γ a⊢ a_abs τ₁ τ₂ t : tarr τ₁ τ₂ ⟫
  | a_WtApp {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ a⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ Γ a⊢ t₂ : τ₁ ⟫ →
      ⟪ Γ a⊢ a_app τ₁ τ₂ t₁ t₂ : τ₂ ⟫
  | a_WtUnit :
      ⟪ Γ a⊢ a_unit : tunit ⟫
  | a_WtTrue :
      ⟪ Γ a⊢ a_true : tbool ⟫
  | a_WtFalse :
      ⟪ Γ a⊢ a_false : tbool ⟫
  | a_WtIte {t₁ t₂ t₃ τ} :
      ⟪ Γ a⊢ t₁ : tbool ⟫ →
      ⟪ Γ a⊢ t₂ : τ ⟫ →
      ⟪ Γ a⊢ t₃ : τ ⟫ →
      ⟪ Γ a⊢ a_ite τ t₁ t₂ t₃ : τ ⟫
  | a_WtPair {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ a⊢ t₁ : τ₁ ⟫ →
      ⟪ Γ a⊢ t₂ : τ₂ ⟫ →
      ⟪ Γ a⊢ a_pair τ₁ τ₂ t₁ t₂ : tprod τ₁ τ₂ ⟫
  | a_WtProj1 {t τ₁ τ₂} :
      ⟪ Γ a⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ a⊢ a_proj₁ τ₁ τ₂ t : τ₁ ⟫
  | a_WtProj2 {t τ₁ τ₂} :
      ⟪ Γ a⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ a⊢ a_proj₂ τ₁ τ₂ t : τ₂ ⟫
  | a_WtInl {t τ₁ τ₂} :
      ⟪ Γ a⊢ t : τ₁ ⟫ →
      ⟪ Γ a⊢ a_inl τ₁ τ₂ t : tsum τ₁ τ₂ ⟫
  | a_WtInr {t τ₁ τ₂} :
      ⟪ Γ a⊢ t : τ₂ ⟫ →
      ⟪ Γ a⊢ a_inr τ₁ τ₂ t : tsum τ₁ τ₂ ⟫
  | a_WtCaseof {t₁ t₂ t₃ τ₁ τ₂ τ} :
      ⟪ Γ a⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ ▻ τ₁ a⊢ t₂ : τ ⟫ →
      ⟪ Γ ▻ τ₂ a⊢ t₃ : τ ⟫ →
      ⟪ Γ a⊢ a_caseof τ₁ τ₂ τ t₁ t₂ t₃ : τ ⟫
  | a_WtSeq {t₁ t₂ τ} :
      ⟪ Γ a⊢ t₁ : tunit ⟫ →
      ⟪ Γ a⊢ t₂ : τ ⟫ →
      ⟪ Γ a⊢ a_seq τ t₁ t₂ : τ ⟫
  | a_WtFixt {τ₁ τ₂ t} :
      ⟪ Γ a⊢ t : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
      ⟪ Γ a⊢ a_fixt τ₁ τ₂ t : tarr τ₁ τ₂ ⟫
where "⟪  Γ a⊢ t : τ  ⟫" := (AnnotTyping Γ t τ).

Inductive PCtxA : Set :=
  | a_phole
  | a_pabs (τ₁ τ₂ : Ty) (C: PCtxA)
  | a_papp₁ (τ₁ τ₂ : Ty) (C: PCtxA) (t: TmA)
  | a_papp₂ (τ₁ τ₂ : Ty) (t: TmA) (C: PCtxA)
  | a_pite₁ (τ : Ty) (C: PCtxA) (t₂ t₃: TmA)
  | a_pite₂ (τ : Ty) (t₁: TmA) (C: PCtxA) (t₃: TmA)
  | a_pite₃ (τ : Ty) (t₁ t₂: TmA) (C: PCtxA)
  | a_ppair₁ (τ₁ τ₂ : Ty) (C: PCtxA) (t: TmA)
  | a_ppair₂ (τ₁ τ₂ : Ty) (t: TmA) (C: PCtxA)
  | a_pproj₁ (τ₁ τ₂ : Ty) (C: PCtxA)
  | a_pproj₂ (τ₁ τ₂ : Ty) (C: PCtxA)
  | a_pinl (τ₁ τ₂ : Ty) (C: PCtxA)
  | a_pinr (τ₁ τ₂ : Ty) (C: PCtxA)
  | a_pcaseof₁ (τ₁ τ₂ τ : Ty) (C: PCtxA) (t₂ t₃: TmA)
  | a_pcaseof₂ (τ₁ τ₂ τ : Ty) (t₁: TmA) (C: PCtxA) (t₃: TmA)
  | a_pcaseof₃ (τ₁ τ₂ τ : Ty) (t₁ t₂: TmA) (C: PCtxA)
  | a_pseq₁ (τ : Ty) (C: PCtxA) (t: TmA)
  | a_pseq₂ (τ : Ty) (t: TmA) (C: PCtxA)
  | a_pfixt (τ₁ τ₂: Ty) (C: PCtxA).

Fixpoint pctxA_app (t : TmA) (C: PCtxA) {struct C} : TmA :=
  match C with
    | a_phole            => t
    | a_pabs τ₁ τ₂ C         => a_abs τ₁ τ₂ (pctxA_app t C)
    | a_papp₁ τ₁ τ₂ C t2        => a_app τ₁ τ₂ (pctxA_app t C) t2
    | a_papp₂ τ₁ τ₂ t1 C        => a_app τ₁ τ₂ t1 (pctxA_app t C)
    | a_pite₁ τ C t₂ t₃    => a_ite τ (pctxA_app t C) t₂ t₃
    | a_pite₂ τ t₁ C t₃    => a_ite τ t₁ (pctxA_app t C) t₃
    | a_pite₃ τ t₁ t₂ C    => a_ite τ t₁ t₂ (pctxA_app t C)
    | a_ppair₁ τ₁ τ₂ C t₂       => a_pair τ₁ τ₂ (pctxA_app t C) t₂
    | a_ppair₂ τ₁ τ₂ t₁ C       => a_pair τ₁ τ₂ t₁ (pctxA_app t C)
    | a_pproj₁ τ₁ τ₂ C         => a_proj₁ τ₁ τ₂ (pctxA_app t C)
    | a_pproj₂ τ₁ τ₂ C         => a_proj₂ τ₁ τ₂ (pctxA_app t C)
    | a_pinl τ₁ τ₂ C           => a_inl τ₁ τ₂ (pctxA_app t C)
    | a_pinr τ₁ τ₂ C           => a_inr τ₁ τ₂ (pctxA_app t C)
    | a_pcaseof₁ τ₁ τ₂ τ C t₁ t₂ => a_caseof τ₁ τ₂ τ (pctxA_app t C) t₁ t₂
    | a_pcaseof₂ τ₁ τ₂ τ t₁ C t₂ => a_caseof τ₁ τ₂ τ t₁ (pctxA_app t C) t₂
    | a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => a_caseof τ₁ τ₂ τ t₁ t₂ (pctxA_app t C)
    | a_pseq₁ τ C t₂        => a_seq τ (pctxA_app t C) t₂
    | a_pseq₂ τ t₁ C        => a_seq τ t₁ (pctxA_app t C)
    | a_pfixt τ₁ τ₂ C    => a_fixt τ₁ τ₂ (pctxA_app t C)
  end.

Fixpoint pctxA_cat (C₀ C: PCtxA) {struct C} : PCtxA :=
  match C with
    | a_phole            => C₀
    | a_pabs τ₁ τ₂ C         => a_pabs τ₁ τ₂ (pctxA_cat C₀ C)
    | a_papp₁ τ₁ τ₂ C t        => a_papp₁ τ₁ τ₂ (pctxA_cat C₀ C) t
    | a_papp₂ τ₁ τ₂ t C        => a_papp₂ τ₁ τ₂ t (pctxA_cat C₀ C)
    | a_pite₁ τ C t₂ t₃    => a_pite₁ τ (pctxA_cat C₀ C) t₂ t₃
    | a_pite₂ τ t₁ C t₃    => a_pite₂ τ t₁ (pctxA_cat C₀ C) t₃
    | a_pite₃ τ t₁ t₂ C    => a_pite₃ τ t₁ t₂ (pctxA_cat C₀ C)
    | a_ppair₁ τ₁ τ₂ C t       => a_ppair₁ τ₁ τ₂ (pctxA_cat C₀ C) t
    | a_ppair₂ τ₁ τ₂ t C       => a_ppair₂ τ₁ τ₂ t (pctxA_cat C₀ C)
    | a_pproj₁ τ₁ τ₂ C         => a_pproj₁ τ₁ τ₂ (pctxA_cat C₀ C)
    | a_pproj₂ τ₁ τ₂ C         => a_pproj₂ τ₁ τ₂ (pctxA_cat C₀ C)
    | a_pinl τ₁ τ₂ C           => a_pinl τ₁ τ₂ (pctxA_cat C₀ C)
    | a_pinr τ₁ τ₂ C           => a_pinr τ₁ τ₂ (pctxA_cat C₀ C)
    | a_pcaseof₁ τ₁ τ₂ τ C t₁ t₂ => a_pcaseof₁ τ₁ τ₂ τ (pctxA_cat C₀ C) t₁ t₂
    | a_pcaseof₂ τ₁ τ₂ τ t₁ C t₂ => a_pcaseof₂ τ₁ τ₂ τ t₁ (pctxA_cat C₀ C) t₂
    | a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ (pctxA_cat C₀ C)
    | a_pseq₁ τ C t        => a_pseq₁ τ (pctxA_cat C₀ C) t
    | a_pseq₂ τ t C        => a_pseq₂ τ t (pctxA_cat C₀ C)
    | a_pfixt τ₁ τ₂ C    => a_pfixt τ₁ τ₂ (pctxA_cat C₀ C)
  end.
(* Hint Constructors AnnotTyping : typing. *)

Reserved Notation "⟪ a⊢ C : Γ₀ , τ₀ → Γ , τ ⟫"
  (at level 0, C at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  a⊢  C  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
Inductive PCtxTypingAnnot (Γ₀: Env) (τ₀: Ty) : Env → PCtxA → Ty → Prop :=
  | a_WtPHole :
      ⟪ a⊢ a_phole : Γ₀, τ₀ → Γ₀, τ₀ ⟫
  | a_WtPAbs {Γ C τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ ▻ τ₁, τ₂ ⟫ →
      ⟪ a⊢ a_pabs τ₁ τ₂ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
  | a_WtPAppl {Γ C t₂ τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ →
      ⟪ Γ a⊢ t₂ : τ₁ ⟫ →
      ⟪ a⊢ a_papp₁ τ₁ τ₂ C t₂ : Γ₀, τ₀ → Γ, τ₂ ⟫
  | a_WtPAppr {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ a⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ a⊢ a_papp₂ τ₁ τ₂ t₁ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | a_WtPIteI {Γ C t₂ t₃ T} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ , tbool ⟫ →
      ⟪ Γ a⊢ t₂ : T ⟫ →
      ⟪ Γ a⊢ t₃ : T ⟫ →
      ⟪ a⊢ a_pite₁ T C t₂ t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | a_WtPIteT {Γ t₁ C t₃ T} :
      ⟪ Γ a⊢ t₁ : tbool ⟫ →
      ⟪ a⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ Γ a⊢ t₃ : T ⟫ →
      ⟪ a⊢ a_pite₂ T t₁ C t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | a_WtPIteE {Γ t₁ t₂ C T} :
      ⟪ Γ a⊢ t₁ : tbool ⟫ →
      ⟪ Γ a⊢ t₂ : T ⟫ →
      ⟪ a⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ a⊢ a_pite₃ T t₁ t₂ C : Γ₀ , τ₀ → Γ , T ⟫
  | a_WtPPair₁ {Γ C t₂ τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ Γ a⊢ t₂ : τ₂ ⟫ →
      ⟪ a⊢ a_ppair₁ τ₁ τ₂ C t₂ : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | a_WtPPair₂ {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ a⊢ t₁ : τ₁ ⟫ →
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ a⊢ a_ppair₂ τ₁ τ₂ t₁ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | a_WtPProj₁ {Γ C τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ a⊢ a_pproj₁ τ₁ τ₂ C : Γ₀, τ₀ → Γ, τ₁ ⟫
  | a_WtPProj₂ {Γ C τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ a⊢ a_pproj₂ τ₁ τ₂ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | a_WtPInl {Γ C τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ a⊢ a_pinl τ₁ τ₂ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | a_WtPInr {Γ C τ₁ τ₂} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ a⊢ a_pinr τ₁ τ₂ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | a_WtPCaseof₁ {Γ C t₂ t₃ τ₁ τ₂ τ} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫ →
      ⟪ Γ ▻ τ₁ a⊢ t₂ : τ ⟫ →
      ⟪ Γ ▻ τ₂ a⊢ t₃ : τ ⟫ →
      ⟪ a⊢ a_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ : Γ₀, τ₀ → Γ, τ ⟫
  | a_WtPCaseof₂ {Γ t₁ C t₃ τ₁ τ₂ τ} :
      ⟪ Γ a⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ a⊢ C : Γ₀, τ₀ → Γ ▻ τ₁, τ ⟫ →
      ⟪ Γ ▻ τ₂ a⊢ t₃ : τ ⟫ →
      ⟪ a⊢ a_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ : Γ₀, τ₀ → Γ, τ ⟫
  | a_WtPCaseof₃ {Γ t₁ t₂ C τ₁ τ₂ τ} :
      ⟪ Γ a⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ ▻ τ₁ a⊢ t₂ : τ ⟫ →
      ⟪ a⊢ C : Γ₀, τ₀ → Γ ▻ τ₂, τ ⟫ →
      ⟪ a⊢ a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C : Γ₀, τ₀ → Γ, τ ⟫
  | a_WtPSeq₁ {Γ C t₂ T} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, tunit ⟫ →
      ⟪ Γ a⊢ t₂ : T ⟫ →
      ⟪ a⊢ a_pseq₁ T C t₂ : Γ₀, τ₀ → Γ, T ⟫
  | a_WtPSeq₂ {Γ t₁ C T} :
      ⟪ Γ a⊢ t₁ : tunit ⟫ →
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ⟪ a⊢ a_pseq₂ T t₁ C : Γ₀, τ₀ → Γ, T ⟫
  | a_WtPFixt {Γ τ₁ τ₂ C} :
      ⟪ a⊢ C : Γ₀, τ₀ → Γ, tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
      ⟪ a⊢ a_pfixt τ₁ τ₂ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
where "⟪ a⊢ C : Γ₀ , τ₀ → Γ , τ ⟫" := (PCtxTypingAnnot Γ₀ τ₀ Γ C τ).

(* Hint Constructors PCtxTypingAnnot : typing. *)

Ltac crushTypingMatchAH :=
  match goal with
    | [ H: ⟪ _ : _ ∈ empty ⟫         |- _ ] =>
      inversion H
    | [ H: ⟪ 0 : _ ∈ _ ⟫         |- _ ] =>
      apply getEvarInvHere in H; repeat subst
    | [ H: ⟪ (S _) : _ ∈ (_ ▻ _) ⟫ |- _ ] =>
      apply getEvarInvThere in H
    | H: ⟪ _ a⊢ a_var _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_abs _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_app _ _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_unit         : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_true         : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_false        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_ite _ _ _ _    : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_pair _ _ _ _     : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_proj₁ _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_proj₂ _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_inl _ _ _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_inr _ _ _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_caseof _ _ _ _ _ _ : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_seq _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ a⊢ a_fixt _ _ _   : _ ⟫ |- _ => inversion H; clear H
    | [ wi : ⟪ ?i : _ ∈ (_ ▻ _) ⟫
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : ⟪ ?i : _ ∈ (_ ▻ _) ⟫
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- ⟪ _ a⊢ a_var _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ a⊢ a_abs _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ a⊢ a_app _ _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ a⊢ a_unit : _ ⟫                     ] => econstructor
    | [ |- ⟪ _ a⊢ a_true : _ ⟫                     ] => econstructor
    | [ |- ⟪ _ a⊢ a_false : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ a⊢ a_ite _ _ _ _ : _ ⟫                ] => econstructor
    | [ |- ⟪ _ a⊢ a_pair _ _ _ _ : _ ⟫                 ] => econstructor
    | [ |- ⟪ _ a⊢ a_proj₁ _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ a⊢ a_proj₂ _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ a⊢ a_inl _ _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ a⊢ a_inr _ _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ a⊢ a_caseof _ _ _ _ _ _ : _ ⟫             ] => econstructor
    | [ |- ⟪ _ a⊢ a_seq _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ a⊢ a_fixt _ _ _ : _ ⟫               ] => econstructor
    | [ |- ⟪ a⊢ a_phole : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ a⊢ a_pabs _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ a⊢ a_papp₁ _ _ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ a⊢ a_papp₂ _ _ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ a⊢ a_pite₁ _ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ a⊢ a_pite₂ _ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ a⊢ a_pite₃ _ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ a⊢ a_ppair₁ _ _ _ _ : _ , _ → _ , _ ⟫     ] => econstructor
    | [ |- ⟪ a⊢ a_ppair₂ _ _ _ _ : _ , _ → _ , _ ⟫     ] => econstructor
    | [ |- ⟪ a⊢ a_pproj₁ _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ a⊢ a_pproj₂ _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ a⊢ a_pinl _ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ a⊢ a_pinr _ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ a⊢ a_pcaseof₁ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ a⊢ a_pcaseof₂ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ a⊢ a_pcaseof₃ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ a⊢ a_pseq₁ _ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ a⊢ a_pseq₂ _ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ a⊢ a_pfixt _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
  end.

Fixpoint eraseAnnot (t : TmA) : Tm :=
  match t with
  | a_var i => var i
  | a_abs τ₁ τ₂ t => abs τ₁ (eraseAnnot t)
  | a_app τ₁ τ₂ t₁ t₂ => app (eraseAnnot t₁) (eraseAnnot t₂)
  | a_unit => unit
  | a_true => true
  | a_false => false
  | a_ite _ t₁ t₂ t₃ => ite (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot t₃)
  | a_pair _ _ t₁ t₂ => pair (eraseAnnot t₁) (eraseAnnot t₂)
  | a_proj₁ _ _ t => proj₁ (eraseAnnot t)
  | a_proj₂ _ _ t => proj₂ (eraseAnnot t)
  | a_inl τ₁ τ₂ t => inl (eraseAnnot t)
  | a_inr τ₁ τ₂ t => inr (eraseAnnot t)
  | a_caseof τ₁ τ₂ τ t₁ t₂ t₃ => caseof (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot t₃)
  | a_seq τ t₁ t₂ => seq (eraseAnnot t₁) (eraseAnnot t₂)
  | a_fixt τ₁ τ₂ t => fixt τ₁ τ₂ (eraseAnnot t)
  end.

Arguments eraseAnnot !t.

Fixpoint eraseAnnot_pctx (C : PCtxA) : PCtx :=
  match C with
  | a_phole => phole
  | a_pabs τ₁ τ₂ t => pabs τ₁ (eraseAnnot_pctx t)
  | a_papp₁ τ₁ τ₂ C t₂ => papp₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | a_papp₂ τ₁ τ₂ t₁ C => papp₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | a_pite₁ _ C t₁ t₂ => pite₁ (eraseAnnot_pctx C) (eraseAnnot t₁) (eraseAnnot t₂)
  | a_pite₂ _ t₁ C t₂ => pite₂ (eraseAnnot t₁) (eraseAnnot_pctx C) (eraseAnnot t₂)
  | a_pite₃ _ t₁ t₂ C => pite₃ (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot_pctx C)
  | a_ppair₁ _ _ C t₁ => ppair₁ (eraseAnnot_pctx C) (eraseAnnot t₁)
  | a_ppair₂ _ _ t₁ C => ppair₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | a_pproj₁ _ _ C => pproj₁ (eraseAnnot_pctx C)
  | a_pproj₂ _ _ C => pproj₂ (eraseAnnot_pctx C)
  | a_pinl τ₁ τ₂ C => pinl (eraseAnnot_pctx C)
  | a_pinr τ₁ τ₂ C => pinr (eraseAnnot_pctx C)
  | a_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ => pcaseof₁ (eraseAnnot_pctx C) (eraseAnnot t₂) (eraseAnnot t₃)
  | a_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ => pcaseof₂ (eraseAnnot t₁) (eraseAnnot_pctx C) (eraseAnnot t₃)
  | a_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => pcaseof₃ (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot_pctx C)
  | a_pseq₁ τ C t₂ => pseq₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | a_pseq₂ τ t₁ C => pseq₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | a_pfixt τ₁ τ₂ C => pfixt τ₁ τ₂ (eraseAnnot_pctx C)
  end.

Arguments eraseAnnot_pctx !C.

Lemma eraseAnnotT {Γ t τ} : ⟪  Γ a⊢ t : τ  ⟫ ->
                            ⟪  Γ ⊢ (eraseAnnot t) : τ  ⟫.
Proof.
  induction 1; cbn; eauto using Typing.
Qed.

Lemma eraseAnnot_pctxT {Γₒ τₒ Γ C τ} : ⟪ a⊢ C : Γₒ , τₒ → Γ , τ ⟫ ->
                            ⟪  ⊢ eraseAnnot_pctx C : Γₒ , τₒ → Γ , τ  ⟫.
Proof.
  induction 1; cbn; eauto using Typing, PCtxTyping, eraseAnnotT.
Qed.

Lemma pctxtyping_app_annot {Γ₀ t₀ τ₀ Γ C τ} :
  ⟪ Γ₀ a⊢ t₀ : τ₀ ⟫ → ⟪ a⊢ C : Γ₀, τ₀ → Γ , τ ⟫ → ⟪ Γ a⊢ pctxA_app t₀ C : τ ⟫.
Proof.
  intros wt₀ wC;
  induction wC; cbn; subst; eauto using AnnotTyping.
Qed.

Lemma pctxtyping_cat_annot {Γ₀ τ₀ C₁ Γ₁ τ₁ C₂ Γ₂ τ₂} :
  ⟪ a⊢ C₁ : Γ₀, τ₀ → Γ₁ , τ₁ ⟫ →
  ⟪ a⊢ C₂ : Γ₁, τ₁ → Γ₂ , τ₂ ⟫ →
  ⟪ a⊢ pctxA_cat C₁ C₂ : Γ₀, τ₀ → Γ₂ , τ₂ ⟫.
Proof.
  intros wC₁ wC₂.
  induction wC₂; cbn; eauto using PCtxTypingAnnot.
Qed.

Lemma eraseAnnot_pctx_cat {C1 C2} :
  eraseAnnot_pctx (pctxA_cat C1 C2) = pctx_cat (eraseAnnot_pctx C1) (eraseAnnot_pctx C2).
Proof.
  induction C2; cbn; f_equal; assumption.
Qed.


Hint Resolve pctxtyping_app_annot : typing.
Hint Resolve pctxtyping_cat_annot : typing.

Ltac crushTypingMatchAH2 :=
  match goal with
    | [ |- ⟪ _ a⊢ pctxA_app _ _ : _ ⟫          ] => apply pctxtyping_app_annot
    | [ |- ⟪ a⊢ pctxA_cat _ _ : _ , _ → _ , _ ⟫          ] => eapply pctxtyping_cat_annot
  end.

Ltac crushTypingA :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchAH;
     repeat crushTypingMatchAH2;
     eauto with ws
    ).

Hint Extern 20 (⟪ _ a⊢ _ : _ ⟫) =>
  crushTypingA : typing.

Hint Extern 20 (⟪ a⊢ _ : _ , _ → _ , _ ⟫) =>
  crushTypingA : typing.
