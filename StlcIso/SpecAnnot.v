Require Export StlcIso.Inst.
Require Export StlcIso.SpecSyntax.
Require Export StlcIso.SpecTyping.
Require Export StlcIso.LemmasTyping.

(* a fully annotated version of iso-recursive terms. *)
Inductive TmA : Set :=
  | ia_var (i: Ix)
  | ia_abs (τ1 τ2 : Ty) (t: TmA)
  | ia_app (τ1 τ2 : Ty) (t₁ t₂ : TmA)
  | ia_unit
  | ia_true
  | ia_false
  | ia_ite (τ : Ty) (t₁ t₂ t₃: TmA)
  | ia_pair (τ1 τ2 : Ty) (t₁ t₂: TmA)
  | ia_proj₁ (τ1 τ2 : Ty) (t: TmA)
  | ia_proj₂ (τ1 τ2 : Ty) (t: TmA)
  | ia_inl (τ1 τ2 : Ty) (t: TmA)
  | ia_inr (τ1 τ2 : Ty) (t: TmA)
  | ia_caseof (τ1 τ2 τ : Ty) (t₁ t₂ t₃: TmA)
  | ia_seq (τ : Ty) (t₁ t₂: TmA)
  | ia_fold_ (τ : Ty) (t : TmA)
  | ia_unfold_ (τ : Ty) (t : TmA).

Section Application.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {wkY: Wk Y}.
  Context {vrTm: Vr TmA}.
  Context {liftYTm: Lift Y TmA}.

  Context {vrTy: Vr Ty}.
  Context {liftYTy: Lift Y Ty}.

  Fixpoint apTmA (ζ: Sub Y) (t: TmA) {struct t} : TmA :=
    match t with
      | ia_var x           => lift (ζ x)
      | ia_abs τ₁ τ₂ t        => ia_abs τ₁ τ₂ (apTmA (ζ↑) t)
      | ia_app τ₁ τ₂ t₁ t₂       => ia_app τ₁ τ₂ (apTmA ζ t₁) (apTmA ζ t₂)
      | ia_unit            => ia_unit
      | ia_true            => ia_true
      | ia_false           => ia_false
      | ia_ite τ t₁ t₂ t₃    => ia_ite τ (apTmA ζ t₁) (apTmA ζ t₂) (apTmA ζ t₃)
      | ia_pair τ₁ τ₂ t₁ t₂      => ia_pair τ₁ τ₂ (apTmA ζ t₁) (apTmA ζ t₂)
      | ia_proj₁ τ₁ τ₂ t         => ia_proj₁ τ₁ τ₂ (apTmA ζ t)
      | ia_proj₂ τ₁ τ₂ t         => ia_proj₂ τ₁ τ₂ (apTmA ζ t)
      | ia_inl τ₁ τ₂ t           => ia_inl τ₁ τ₂ (apTmA ζ t)
      | ia_inr τ₁ τ₂ t           => ia_inr τ₁ τ₂ (apTmA ζ t)
      | ia_caseof τ₁ τ₂ τ t₁ t₂ t₃ => ia_caseof τ₁ τ₂ τ (apTmA ζ t₁) (apTmA (ζ↑) t₂) (apTmA (ζ↑) t₃)
      | ia_seq τ t₁ t₂       => ia_seq τ (apTmA ζ t₁) (apTmA ζ t₂)
      (* | fixt τ₁ τ₂ t    => fixt τ₁ τ₂ (apTmA ζ t) *)
      | ia_fold_ τ t => ia_fold_ τ (apTmA ζ t)
      | ia_unfold_ τ t => ia_unfold_ τ (apTmA ζ t)
    end.

  Global Arguments apTmA ζ !t /.

End Application.

Reserved Notation "⟪  Γ ia⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98 ).
Inductive AnnotTyping (Γ : Env) : TmA -> Ty -> Prop :=
  | ia_WtVar {i T} :
      ⟪ i : T r∈ Γ ⟫ →
      ⟪ Γ ia⊢ ia_var i : T ⟫
  | ia_WtAbs {t τ₁ τ₂} :
      ⟪ Γ r▻ τ₁ ia⊢ t : τ₂ ⟫ →
      ⟪ Γ ia⊢ ia_abs τ₁ τ₂ t : tarr τ₁ τ₂ ⟫
  | ia_WtApp {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ ia⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ Γ ia⊢ t₂ : τ₁ ⟫ →
      ⟪ Γ ia⊢ ia_app τ₁ τ₂ t₁ t₂ : τ₂ ⟫
  | ia_WtUnit :
      ⟪ Γ ia⊢ ia_unit : tunit ⟫
  | ia_WtTrue :
      ⟪ Γ ia⊢ ia_true : tbool ⟫
  | ia_WtFalse :
      ⟪ Γ ia⊢ ia_false : tbool ⟫
  | ia_WtIte {t₁ t₂ t₃ T} :
      ⟪ Γ ia⊢ t₁ : tbool ⟫ →
      ⟪ Γ ia⊢ t₂ : T ⟫ →
      ⟪ Γ ia⊢ t₃ : T ⟫ →
      ⟪ Γ ia⊢ ia_ite T t₁ t₂ t₃ : T ⟫
  | ia_WtPair {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ ia⊢ t₁ : τ₁ ⟫ →
      ⟪ Γ ia⊢ t₂ : τ₂ ⟫ →
      ⟪ Γ ia⊢ ia_pair τ₁ τ₂ t₁ t₂ : tprod τ₁ τ₂ ⟫
  | ia_WtProj1 {t τ₁ τ₂} :
      ⟪ Γ ia⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ ia⊢ ia_proj₁ τ₁ τ₂ t : τ₁ ⟫
  | ia_WtProj2 {t τ₁ τ₂} :
      ⟪ Γ ia⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ ia⊢ ia_proj₂ τ₁ τ₂ t : τ₂ ⟫
  | ia_WtInl {t τ₁ τ₂} :
      ⟪ Γ ia⊢ t : τ₁ ⟫ →
      ⟪ Γ ia⊢ ia_inl τ₁ τ₂ t : tsum τ₁ τ₂ ⟫
  | ia_WtInr {t τ₁ τ₂} :
      ⟪ Γ ia⊢ t : τ₂ ⟫ →
      ⟪ Γ ia⊢ ia_inr τ₁ τ₂ t : tsum τ₁ τ₂ ⟫
  | ia_WtCaseof {t₁ t₂ t₃ τ₁ τ₂ τ} :
      ⟪ Γ ia⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ ia⊢ t₂ : τ ⟫ →
      ⟪ Γ r▻ τ₂ ia⊢ t₃ : τ ⟫ →
      ⟪ Γ ia⊢ ia_caseof τ₁ τ₂ τ t₁ t₂ t₃ : τ ⟫
  | ia_WtFold {t τ} :
      ⟪ Γ ia⊢ t : τ[beta1 (trec τ)] ⟫ →
      ⟪ Γ ia⊢ ia_fold_ τ t : trec τ ⟫
  | ia_WtUnfold {t τ} :
      ⟪ Γ ia⊢ t : trec τ ⟫ →
      ⟪ Γ ia⊢ ia_unfold_ τ t : τ[beta1 (trec τ)] ⟫
  | ia_WtSeq {t₁ t₂ T} :
      ⟪ Γ ia⊢ t₁ : tunit ⟫ →
      ⟪ Γ ia⊢ t₂ : T ⟫ →
      ⟪ Γ ia⊢ ia_seq T t₁ t₂ : T ⟫
where "⟪  Γ ia⊢ t : T  ⟫" := (AnnotTyping Γ t T).

Inductive PCtxA : Set :=
  | ia_phole
  | ia_pabs (τ₁ τ₂ : Ty) (C: PCtxA)
  | ia_papp₁ (τ₁ τ₂ : Ty) (C: PCtxA) (t: TmA)
  | ia_papp₂ (τ₁ τ₂ : Ty) (t: TmA) (C: PCtxA)
  | ia_pite₁ (τ : Ty) (C: PCtxA) (t₂ t₃: TmA)
  | ia_pite₂ (τ : Ty) (t₁: TmA) (C: PCtxA) (t₃: TmA)
  | ia_pite₃ (τ : Ty) (t₁ t₂: TmA) (C: PCtxA)
  | ia_ppair₁ (τ₁ τ₂ : Ty) (C: PCtxA) (t: TmA)
  | ia_ppair₂ (τ₁ τ₂ : Ty) (t: TmA) (C: PCtxA)
  | ia_pproj₁ (τ₁ τ₂ : Ty) (C: PCtxA)
  | ia_pproj₂ (τ₁ τ₂ : Ty) (C: PCtxA)
  | ia_pinl (τ₁ τ₂ : Ty) (C: PCtxA)
  | ia_pinr (τ₁ τ₂ : Ty) (C: PCtxA)
  | ia_pcaseof₁ (τ₁ τ₂ τ : Ty) (C: PCtxA) (t₂ t₃: TmA)
  | ia_pcaseof₂ (τ₁ τ₂ τ : Ty) (t₁: TmA) (C: PCtxA) (t₃: TmA)
  | ia_pcaseof₃ (τ₁ τ₂ τ : Ty) (t₁ t₂: TmA) (C: PCtxA)
  | ia_pseq₁ (τ : Ty) (C: PCtxA) (t: TmA)
  | ia_pseq₂ (τ : Ty) (t: TmA) (C: PCtxA)
  | ia_pfold (τ : Ty) (C : PCtxA)
  | ia_punfold (τ : Ty) (C : PCtxA).

Reserved Notation "⟪ ia⊢ C : Γ₀ , τ₀ → Γ , τ ⟫"
  (at level 0, C at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ia⊢  C  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
Inductive PCtxTypingAnnot (Γ₀: Env) (τ₀: Ty) : Env → PCtxA → Ty → Prop :=
  | ia_WtPHole :
      ⟪ ia⊢ ia_phole : Γ₀, τ₀ → Γ₀, τ₀ ⟫
  | ia_WtPAbs {Γ C τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, τ₂ ⟫ →
      ⟪ ia⊢ ia_pabs τ₁ τ₂ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
  | ia_WtPAppl {Γ C t₂ τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ →
      ⟪ Γ ia⊢ t₂ : τ₁ ⟫ →
      ⟪ ia⊢ ia_papp₁ τ₁ τ₂ C t₂ : Γ₀, τ₀ → Γ, τ₂ ⟫
  | ia_WtPAppr {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ ia⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ ia⊢ ia_papp₂ τ₁ τ₂ t₁ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | ia_WtPIteI {Γ C t₂ t₃ T} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ , tbool ⟫ →
      ⟪ Γ ia⊢ t₂ : T ⟫ →
      ⟪ Γ ia⊢ t₃ : T ⟫ →
      ⟪ ia⊢ ia_pite₁ T C t₂ t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | ia_WtPIteT {Γ t₁ C t₃ T} :
      ⟪ Γ ia⊢ t₁ : tbool ⟫ →
      ⟪ ia⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ Γ ia⊢ t₃ : T ⟫ →
      ⟪ ia⊢ ia_pite₂ T t₁ C t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | ia_WtPIteE {Γ t₁ t₂ C T} :
      ⟪ Γ ia⊢ t₁ : tbool ⟫ →
      ⟪ Γ ia⊢ t₂ : T ⟫ →
      ⟪ ia⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ ia⊢ ia_pite₃ T t₁ t₂ C : Γ₀ , τ₀ → Γ , T ⟫
  | ia_WtPPair₁ {Γ C t₂ τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ Γ ia⊢ t₂ : τ₂ ⟫ →
      ⟪ ia⊢ ia_ppair₁ τ₁ τ₂ C t₂ : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | ia_WtPPair₂ {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ ia⊢ t₁ : τ₁ ⟫ →
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ ia⊢ ia_ppair₂ τ₁ τ₂ t₁ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | ia_WtPProj₁ {Γ C τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ ia⊢ ia_pproj₁ τ₁ τ₂ C : Γ₀, τ₀ → Γ, τ₁ ⟫
  | ia_WtPProj₂ {Γ C τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ⟪ ia⊢ ia_pproj₂ τ₁ τ₂ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | ia_WtPInl {Γ C τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ ia⊢ ia_pinl τ₁ τ₂ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | ia_WtPInr {Γ C τ₁ τ₂} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ ia⊢ ia_pinr τ₁ τ₂ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | ia_WtPCaseof₁ {Γ C t₂ t₃ τ₁ τ₂ τ} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ ia⊢ t₂ : τ ⟫ →
      ⟪ Γ r▻ τ₂ ia⊢ t₃ : τ ⟫ →
      ⟪ ia⊢ ia_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ : Γ₀, τ₀ → Γ, τ ⟫
  | ia_WtPCaseof₂ {Γ t₁ C t₃ τ₁ τ₂ τ} :
      ⟪ Γ ia⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, τ ⟫ →
      ⟪ Γ r▻ τ₂ ia⊢ t₃ : τ ⟫ →
      ⟪ ia⊢ ia_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ : Γ₀, τ₀ → Γ, τ ⟫
  | ia_WtPCaseof₃ {Γ t₁ t₂ C τ₁ τ₂ τ} :
      ⟪ Γ ia⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ ia⊢ t₂ : τ ⟫ →
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ r▻ τ₂, τ ⟫ →
      ⟪ ia⊢ ia_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C : Γ₀, τ₀ → Γ, τ ⟫
  | ia_WtPFold {Γ C τ} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, τ [beta1 (trec τ)] ⟫ →
      ⟪ ia⊢ ia_pfold τ C : Γ₀, τ₀ → Γ, trec τ ⟫
  | ia_WtPUnfold {Γ C τ} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, trec τ ⟫ →
      ⟪ ia⊢ ia_punfold τ C : Γ₀, τ₀ → Γ, τ [beta1 (trec τ)] ⟫
  | ia_WtPSeq₁ {Γ C t₂ T} :
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, tunit ⟫ →
      ⟪ Γ ia⊢ t₂ : T ⟫ →
      ⟪ ia⊢ ia_pseq₁ T C t₂ : Γ₀, τ₀ → Γ, T ⟫
  | ia_WtPSeq₂ {Γ C t₁ T} :
      ⟪ Γ ia⊢ t₁ : tunit ⟫ →
      ⟪ ia⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ⟪ ia⊢ ia_pseq₂ T t₁ C : Γ₀, τ₀ → Γ, T ⟫
where "⟪ ia⊢ C : Γ₀ , τ₀ → Γ , τ ⟫" := (PCtxTypingAnnot Γ₀ τ₀ Γ C τ).

Ltac crushTypingMatchIAH :=
  match goal with
    | [ H: ⟪ _ : _ r∈ empty ⟫         |- _ ] =>
      inversion H
    | [ H: ⟪ 0 : _ r∈ _ ⟫         |- _ ] =>
      apply getEvarInvHere in H; repeat subst
    | [ H: ⟪ (S _) : _ r∈ (_ r▻ _) ⟫ |- _ ] =>
      apply getEvarInvThere in H
    | H: ⟪ _ ia⊢ ia_var _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_abs _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_app _ _ _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_unit         : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_true         : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_false        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_ite _ _ _    : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_pair _ _     : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_proj₁ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_proj₂ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_inl _ _ _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_inr _ _ _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_caseof _ _ _ _ _ _ : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_seq _ _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_fold_ _ _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ia⊢ ia_unfold_ _ _        : _ ⟫ |- _ => inversion H; clear H
    (* | H: ⟪ _ ⊢ seq _ _      : _ ⟫ |- _ => inversion H; clear H *)
    | [ wi : ⟪ ?i : _ r∈ (_ r▻ _) ⟫
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : ⟪ ?i : _ r∈ (_ r▻ _) ⟫
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- ⟪ _ ia⊢ ia_var _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_abs _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_app _ _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_unit : _ ⟫                     ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_true : _ ⟫                     ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_false : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_ite _ _ _ : _ ⟫                ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_pair _ _ : _ ⟫                 ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_proj₁ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_proj₂ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_inl _ _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_inr _ _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_caseof _ _ _ _ _ _ : _ ⟫             ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_seq _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_fold_ _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_unfold_ _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ ia⊢ ia_phole : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ ia⊢ ia_pabs _ _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ ia⊢ ia_papp₁ _ _ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ ia⊢ ia_papp₂ _ _ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ ia⊢ ia_pite₁ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ ia⊢ ia_pite₂ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ ia⊢ ia_pite₃ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor
    | [ |- ⟪ ia⊢ ia_ppair₁ _ _ : _ , _ → _ , _ ⟫     ] => econstructor
    | [ |- ⟪ ia⊢ ia_ppair₂ _ _ : _ , _ → _ , _ ⟫     ] => econstructor
    | [ |- ⟪ ia⊢ ia_pproj₁ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ ia⊢ ia_pproj₂ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ ia⊢ ia_pinl _ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ ia⊢ ia_pinr _ _ _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ ia⊢ ia_pcaseof₁ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ ia⊢ ia_pcaseof₂ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ ia⊢ ia_pcaseof₃ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_pfold _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_punfold _ _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_pseq₁ _ _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ ia⊢ ia_pseq₂ _ _ _ : _ ⟫                  ] => econstructor
  end.


Fixpoint eraseAnnot (t : TmA) : Tm :=
  match t with
  | ia_var i => var i
  | ia_abs τ₁ τ₂ t => abs τ₁ (eraseAnnot t)
  | ia_app τ₁ τ₂ t₁ t₂ => app (eraseAnnot t₁) (eraseAnnot t₂)
  | ia_unit => unit
  | ia_true => true
  | ia_false => false
  | ia_ite τ t₁ t₂ t₃ => ite (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot t₃)
  | ia_pair τ₁ τ₂ t₁ t₂ => pair (eraseAnnot t₁) (eraseAnnot t₂)
  | ia_proj₁ τ₁ τ₂ t => proj₁ (eraseAnnot t)
  | ia_proj₂ τ₁ τ₂ t => proj₂ (eraseAnnot t)
  | ia_inl τ₁ τ₂ t => inl (eraseAnnot t)
  | ia_inr τ₁ τ₂ t => inr (eraseAnnot t)
  | ia_caseof τ₁ τ₂ τ t₁ t₂ t₃ => caseof (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot t₃)
  | ia_seq τ t₁ t₂ => seq (eraseAnnot t₁) (eraseAnnot t₂)
  | ia_fold_ τ t => fold_ (eraseAnnot t)
  | ia_unfold_ τ t => unfold_ (eraseAnnot t)
  end.

Fixpoint eraseAnnot_pctx (C : PCtxA) : PCtx :=
  match C with
  | ia_phole => phole
  | ia_pabs τ₁ τ₂ t => pabs τ₁ (eraseAnnot_pctx t)
  | ia_papp₁ τ₁ τ₂ C t₂ => papp₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | ia_papp₂ τ₁ τ₂ t₁ C => papp₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | ia_pite₁ τ C t₂ t₃ => pite₁ (eraseAnnot_pctx C) (eraseAnnot t₂) (eraseAnnot t₃)
  | ia_pite₂ τ t₁ C t₃ => pite₂ (eraseAnnot t₁) (eraseAnnot_pctx C) (eraseAnnot t₃)
  | ia_pite₃ τ t₁ t₂ C => pite₃ (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot_pctx C)
  | ia_ppair₁ τ₁ τ₂ C t₂ => ppair₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | ia_ppair₂ τ₁ τ₂ t₁ C => ppair₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | ia_pproj₁ τ₁ τ₂ C => pproj₁ (eraseAnnot_pctx C)
  | ia_pproj₂ τ₁ τ₂ C => pproj₂ (eraseAnnot_pctx C)
  | ia_pinl τ₁ τ₂ C => pinl (eraseAnnot_pctx C)
  | ia_pinr τ₁ τ₂ C => pinr (eraseAnnot_pctx C)
  | ia_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ => pcaseof₁ (eraseAnnot_pctx C) (eraseAnnot t₂) (eraseAnnot t₃)
  | ia_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ => pcaseof₂ (eraseAnnot t₁) (eraseAnnot_pctx C) (eraseAnnot t₃)
  | ia_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => pcaseof₃ (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot_pctx C)
  | ia_pseq₁ τ C t₂ => pseq₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | ia_pseq₂ τ t₁ C => pseq₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | ia_pfold τ t => pfold (eraseAnnot_pctx t)
  | ia_punfold τ C => punfold (eraseAnnot_pctx C)
  end.

Lemma eraseAnnotT {Γ t τ} : ⟪  Γ ia⊢ t : τ  ⟫ ->
                            ⟪  Γ i⊢ (eraseAnnot t) : τ  ⟫.
Proof.
  induction 1; cbn; eauto using Typing.
Qed.

Lemma eraseAnnot_pctxT {Γₒ τₒ Γ C τ} : ⟪ ia⊢ C : Γₒ , τₒ → Γ , τ ⟫ ->
                            ⟪  i⊢ eraseAnnot_pctx C : Γₒ , τₒ → Γ , τ  ⟫.
Proof.
  induction 1; cbn; eauto using Typing, PCtxTyping, eraseAnnotT.
Qed.

(* #[export]
Hint Resolve pctxtyping_app_annot : typing. *)
(* #[export]
Hint Resolve pctxtyping_cat_annot : typing. *)

(* Ltac crushTypingMatchIAH2 := *)
(*   match goal with *)
(*     | [ |- ⟪ _ ia⊢ pctxA_app _ _ : _ ⟫          ] => apply pctxtyping_app_annot *)
(*     | [ |- ⟪ ia⊢ pctxA_cat _ _ : _ , _ → _ , _ ⟫          ] => eapply pctxtyping_cat_annot *)
(*   end. *)

Ltac crushTypingIA :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchIAH;
     eauto with ws
    ).

#[export]
Hint Extern 20 (⟪ _ ia⊢ _ : _ ⟫) =>
  crushTypingIA : typing.

#[export]
Hint Extern 20 (⟪ ia⊢ _ : _ , _ → _ , _ ⟫) =>
  crushTypingIA : typing.
