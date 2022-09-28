Require Export StlcEqui.Inst.
Require Export StlcEqui.SpecSyntax.
Require Export StlcEqui.SpecTyping.
Require Export StlcEqui.LemmasTyping.

(* a fully annotated version of iso-recursive terms. *)
Inductive TmA : Set :=
  | ea_var (i: Ix)
  | ea_abs (τ1 τ2 : Ty) (t: TmA)
  | ea_app (τ1 τ2 : Ty) (t₁ t₂ : TmA)
  | ea_unit
  | ea_true
  | ea_false
  | ea_ite (τ : Ty) (t₁ t₂ t₃: TmA)
  | ea_pair (τ1 τ2 : Ty) (t₁ t₂: TmA)
  | ea_proj₁ (τ1 τ2 : Ty) (t: TmA)
  | ea_proj₂ (τ1 τ2 : Ty) (t: TmA)
  | ea_inl (τ1 τ2 : Ty) (t: TmA)
  | ea_inr (τ1 τ2 : Ty) (t: TmA)
  | ea_caseof (τ1 τ2 τ : Ty) (t₁ t₂ t₃: TmA)
  | ea_seq (τ : Ty) (t₁ t₂: TmA)
  | ea_coerce (τ : Ty) (t : TmA).

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
      | ea_var x                   => lift (ζ x)
      | ea_abs τ₁ τ₂ t             => ea_abs τ₁ τ₂ (apTmA (ζ↑) t)
      | ea_app τ₁ τ₂ t₁ t₂         => ea_app τ₁ τ₂ (apTmA ζ t₁) (apTmA ζ t₂)
      | ea_unit                    => ea_unit
      | ea_true                    => ea_true
      | ea_false                   => ea_false
      | ea_ite τ t₁ t₂ t₃          => ea_ite τ (apTmA ζ t₁) (apTmA ζ t₂) (apTmA ζ t₃)
      | ea_pair τ₁ τ₂ t₁ t₂        => ea_pair τ₁ τ₂ (apTmA ζ t₁) (apTmA ζ t₂)
      | ea_proj₁ τ₁ τ₂ t           => ea_proj₁ τ₁ τ₂ (apTmA ζ t)
      | ea_proj₂ τ₁ τ₂ t           => ea_proj₂ τ₁ τ₂ (apTmA ζ t)
      | ea_inl τ₁ τ₂ t             => ea_inl τ₁ τ₂ (apTmA ζ t)
      | ea_inr τ₁ τ₂ t             => ea_inr τ₁ τ₂ (apTmA ζ t)
      | ea_caseof τ₁ τ₂ τ t₁ t₂ t₃ => ea_caseof τ₁ τ₂ τ (apTmA ζ t₁) (apTmA (ζ↑) t₂) (apTmA (ζ↑) t₃)
      | ea_seq τ t₁ t₂             => ea_seq τ (apTmA ζ t₁) (apTmA ζ t₂)
      | ea_coerce τ t              => ea_coerce τ (apTmA ζ t)
    end.

  Global Arguments apTmA ζ !t /.

End Application.

Reserved Notation "⟪  Γ ea⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98 ).
Inductive AnnotTyping (Γ : Env) : TmA -> Ty -> Prop :=
  | ea_WtVar {i T} :
      ⟪ i : T r∈ Γ ⟫ →
      ⟪ Γ ea⊢ ea_var i : T ⟫
  | ea_WtAbs {t τ₁ τ₂} :
    ValidTy τ₁ ->
      ⟪ Γ r▻ τ₁ ea⊢ t : τ₂ ⟫ →
      ⟪ Γ ea⊢ ea_abs τ₁ τ₂ t : tarr τ₁ τ₂ ⟫
  | ea_WtApp {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ ea⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ Γ ea⊢ t₂ : τ₁ ⟫ →
      ⟪ Γ ea⊢ ea_app τ₁ τ₂ t₁ t₂ : τ₂ ⟫
  | ea_WtUnit :
      ⟪ Γ ea⊢ ea_unit : tunit ⟫
  | ea_WtTrue :
      ⟪ Γ ea⊢ ea_true : tbool ⟫
  | ea_WtFalse :
      ⟪ Γ ea⊢ ea_false : tbool ⟫
  | ea_WtIte {t₁ t₂ t₃ T} :
      ⟪ Γ ea⊢ t₁ : tbool ⟫ →
      ⟪ Γ ea⊢ t₂ : T ⟫ →
      ⟪ Γ ea⊢ t₃ : T ⟫ →
      ⟪ Γ ea⊢ ea_ite T t₁ t₂ t₃ : T ⟫
  | ea_WtPair {t₁ t₂ τ₁ τ₂} :
      ⟪ Γ ea⊢ t₁ : τ₁ ⟫ →
      ⟪ Γ ea⊢ t₂ : τ₂ ⟫ →
      ⟪ Γ ea⊢ ea_pair τ₁ τ₂ t₁ t₂ : tprod τ₁ τ₂ ⟫
  | ea_WtProj1 {t τ₁ τ₂} :
      ⟪ Γ ea⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ ea⊢ ea_proj₁ τ₁ τ₂ t : τ₁ ⟫
  | ea_WtProj2 {t τ₁ τ₂} :
      ⟪ Γ ea⊢ t : tprod τ₁ τ₂ ⟫ →
      ⟪ Γ ea⊢ ea_proj₂ τ₁ τ₂ t : τ₂ ⟫
  | ea_WtInl {t τ₁ τ₂} :
      ValidTy τ₂ ->
      ⟪ Γ ea⊢ t : τ₁ ⟫ →
      ⟪ Γ ea⊢ ea_inl τ₁ τ₂ t : tsum τ₁ τ₂ ⟫
  | ea_WtInr {t τ₁ τ₂} :
      ValidTy τ₁ ->
      ⟪ Γ ea⊢ t : τ₂ ⟫ →
      ⟪ Γ ea⊢ ea_inr τ₁ τ₂ t : tsum τ₁ τ₂ ⟫
  | ea_WtCaseof {t₁ t₂ t₃ τ₁ τ₂ τ} :
      ⟪ Γ ea⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ ea⊢ t₂ : τ ⟫ →
      ⟪ Γ r▻ τ₂ ea⊢ t₃ : τ ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ Γ ea⊢ ea_caseof τ₁ τ₂ τ t₁ t₂ t₃ : τ ⟫
  | ea_WtSeq {t₁ t₂ T} :
      ⟪ Γ ea⊢ t₁ : tunit ⟫ →
      ⟪ Γ ea⊢ t₂ : T ⟫ →
      ⟪ Γ ea⊢ ea_seq T t₁ t₂ : T ⟫
  | ea_WtCoerce {t T U} :
      ⟪ T ≗ U ⟫ ->
      ValidTy T ->
      ValidTy U ->
      ⟪ Γ ea⊢ t : T ⟫ ->
      ⟪ Γ ea⊢ ea_coerce T t : U ⟫
where "⟪  Γ ea⊢ t : T  ⟫" := (AnnotTyping Γ t T).

Inductive PCtxA : Set :=
  | ea_phole
  | ea_pabs (τ₁ τ₂ : Ty) (C: PCtxA)
  | ea_papp₁ (τ₁ τ₂ : Ty) (C: PCtxA) (t: TmA)
  | ea_papp₂ (τ₁ τ₂ : Ty) (t: TmA) (C: PCtxA)
  | ea_pite₁ (τ : Ty) (C: PCtxA) (t₂ t₃: TmA)
  | ea_pite₂ (τ : Ty) (t₁: TmA) (C: PCtxA) (t₃: TmA)
  | ea_pite₃ (τ : Ty) (t₁ t₂: TmA) (C: PCtxA)
  | ea_ppair₁ (τ₁ τ₂ : Ty) (C: PCtxA) (t: TmA)
  | ea_ppair₂ (τ₁ τ₂ : Ty) (t: TmA) (C: PCtxA)
  | ea_pproj₁ (τ₁ τ₂ : Ty) (C: PCtxA)
  | ea_pproj₂ (τ₁ τ₂ : Ty) (C: PCtxA)
  | ea_pinl (τ₁ τ₂ : Ty) (C: PCtxA)
  | ea_pinr (τ₁ τ₂ : Ty) (C: PCtxA)
  | ea_pcaseof₁ (τ₁ τ₂ τ : Ty) (C: PCtxA) (t₂ t₃: TmA)
  | ea_pcaseof₂ (τ₁ τ₂ τ : Ty) (t₁: TmA) (C: PCtxA) (t₃: TmA)
  | ea_pcaseof₃ (τ₁ τ₂ τ : Ty) (t₁ t₂: TmA) (C: PCtxA)
  | ea_pseq₁ (τ : Ty) (C: PCtxA) (t: TmA)
  | ea_pseq₂ (τ : Ty) (t: TmA) (C: PCtxA)
  | ea_pcoerce (τ : Ty) (C: PCtxA).

Reserved Notation "⟪ ea⊢ C : Γ₀ , τ₀ → Γ , τ ⟫"
  (at level 0, C at level 98,
   Γ₀ at level 98, τ₀ at level 98,
   Γ at level 98, τ at level 98,
   format "⟪  ea⊢  C  :  Γ₀ ,  τ₀  →  Γ ,  τ  ⟫").
Inductive PCtxTypingAnnot (Γ₀: Env) (τ₀: Ty) : Env → PCtxA → Ty → Prop :=
  | ea_WtPHole :
      ⟪ ea⊢ ea_phole : Γ₀, τ₀ → Γ₀, τ₀ ⟫
  | ea_WtPAbs {Γ C τ₁ τ₂} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, τ₂ ⟫ →
      ValidTy τ₁ ->
      ⟪ ea⊢ ea_pabs τ₁ τ₂ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫
  | ea_WtPAppl {Γ C t₂ τ₁ τ₂} :
    ValidTy τ₂ ->
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, tarr τ₁ τ₂ ⟫ →
      ⟪ Γ ea⊢ t₂ : τ₁ ⟫ →
      ⟪ ea⊢ ea_papp₁ τ₁ τ₂ C t₂ : Γ₀, τ₀ → Γ, τ₂ ⟫
  | ea_WtPAppr {Γ t₁ C τ₁ τ₂} :
    ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ Γ ea⊢ t₁ : tarr τ₁ τ₂ ⟫ →
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ ea⊢ ea_papp₂ τ₁ τ₂ t₁ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | ea_WtPIteI {Γ C t₂ t₃ T} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ , tbool ⟫ →
      ⟪ Γ ea⊢ t₂ : T ⟫ →
      ⟪ Γ ea⊢ t₃ : T ⟫ →
      ⟪ ea⊢ ea_pite₁ T C t₂ t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | ea_WtPIteT {Γ t₁ C t₃ T} :
      ⟪ Γ ea⊢ t₁ : tbool ⟫ →
      ⟪ ea⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ Γ ea⊢ t₃ : T ⟫ →
      ⟪ ea⊢ ea_pite₂ T t₁ C t₃ : Γ₀ , τ₀ → Γ , T ⟫
  | ea_WtPIteE {Γ t₁ t₂ C T} :
      ⟪ Γ ea⊢ t₁ : tbool ⟫ →
      ⟪ Γ ea⊢ t₂ : T ⟫ →
      ⟪ ea⊢ C : Γ₀ , τ₀ → Γ , T ⟫ →
      ⟪ ea⊢ ea_pite₃ T t₁ t₂ C : Γ₀ , τ₀ → Γ , T ⟫
  | ea_WtPPair₁ {Γ C t₂ τ₁ τ₂} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ⟪ Γ ea⊢ t₂ : τ₂ ⟫ →
      ⟪ ea⊢ ea_ppair₁ τ₁ τ₂ C t₂ : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | ea_WtPPair₂ {Γ t₁ C τ₁ τ₂} :
      ⟪ Γ ea⊢ t₁ : τ₁ ⟫ →
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ⟪ ea⊢ ea_ppair₂ τ₁ τ₂ t₁ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫
  | ea_WtPProj₁ {Γ C τ₁ τ₂} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ValidTy (tprod τ₁ τ₂) ->
      ⟪ ea⊢ ea_pproj₁ τ₁ τ₂ C : Γ₀, τ₀ → Γ, τ₁ ⟫
  | ea_WtPProj₂ {Γ C τ₁ τ₂} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, tprod τ₁ τ₂ ⟫ →
      ValidTy (tprod τ₁ τ₂) ->
      ⟪ ea⊢ ea_pproj₂ τ₁ τ₂ C : Γ₀, τ₀ → Γ, τ₂ ⟫
  | ea_WtPInl {Γ C τ₁ τ₂} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, τ₁ ⟫ →
      ValidTy τ₂ ->
      ⟪ ea⊢ ea_pinl τ₁ τ₂ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | ea_WtPInr {Γ C τ₁ τ₂} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, τ₂ ⟫ →
      ValidTy τ₁ ->
      ⟪ ea⊢ ea_pinr τ₁ τ₂ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫
  | ea_WtPCaseof₁ {Γ C t₂ t₃ τ₁ τ₂ τ} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ ea⊢ t₂ : τ ⟫ →
      ⟪ Γ r▻ τ₂ ea⊢ t₃ : τ ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ ea⊢ ea_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ : Γ₀, τ₀ → Γ, τ ⟫
  | ea_WtPCaseof₂ {Γ t₁ C t₃ τ₁ τ₂ τ} :
      ⟪ Γ ea⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ r▻ τ₁, τ ⟫ →
      ⟪ Γ r▻ τ₂ ea⊢ t₃ : τ ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ ea⊢ ea_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ : Γ₀, τ₀ → Γ, τ ⟫
  | ea_WtPCaseof₃ {Γ t₁ t₂ C τ₁ τ₂ τ} :
      ⟪ Γ ea⊢ t₁ : tsum τ₁ τ₂ ⟫ →
      ⟪ Γ r▻ τ₁ ea⊢ t₂ : τ ⟫ →
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ r▻ τ₂, τ ⟫ →
      ValidTy τ₁ -> ValidTy τ₂ ->
      ⟪ ea⊢ ea_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C : Γ₀, τ₀ → Γ, τ ⟫
  | ea_WtPSeq₁ {Γ C t₂ T} :
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, tunit ⟫ →
      ⟪ Γ ea⊢ t₂ : T ⟫ →
      ⟪ ea⊢ ea_pseq₁ T C t₂ : Γ₀, τ₀ → Γ, T ⟫
  | ea_WtPSeq₂ {Γ C t₁ T} :
      ⟪ Γ ea⊢ t₁ : tunit ⟫ →
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ⟪ ea⊢ ea_pseq₂ T t₁ C : Γ₀, τ₀ → Γ, T ⟫
  | ea_WtPCoerce {Γ C T U} :
      ⟪ T ≗ U ⟫ ->
      ⟪ ea⊢ C : Γ₀, τ₀ → Γ, T ⟫ →
      ValidTy T -> ValidTy U ->
      ⟪ ea⊢ ea_pcoerce T C : Γ₀, τ₀ → Γ, U ⟫
where "⟪ ea⊢ C : Γ₀ , τ₀ → Γ , τ ⟫" := (PCtxTypingAnnot Γ₀ τ₀ Γ C τ).

Ltac crushTypingMatchEAH :=
  match goal with
    | [ H: ⟪ _ : _ r∈ empty ⟫         |- _ ] =>
      inversion H
    | [ H: ⟪ 0 : _ r∈ _ ⟫         |- _ ] =>
      apply getEvarInvHere in H; repeat subst
    | [ H: ⟪ (S _) : _ r∈ (_ r▻ _) ⟫ |- _ ] =>
      apply getEvarInvThere in H
    | H: ⟪ _ ea⊢ ea_var _        : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_abs _ _ _      : _ ⟫ |- _     => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_app _ _ _ _      : _ ⟫ |- _   => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_unit         : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_true         : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_false        : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_ite _ _ _    : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_pair _ _     : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_proj₁ _      : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_proj₂ _      : _ ⟫ |- _       => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_inl _ _ _        : _ ⟫ |- _   => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_inr _ _ _        : _ ⟫ |- _   => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_caseof _ _ _ _ _ _ : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_seq _ _        : _ ⟫ |- _     => inversion H; clear H
    | H: ⟪ _ ea⊢ ea_coerce _ _        : _ ⟫ |- _  => inversion H; clear H
    (* | H: ⟪ _ ⊢ seq _ _      : _ ⟫ |- _ => inversion H; clear H *)
    | [ wi : ⟪ ?i : _ r∈ (_ r▻ _) ⟫
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : ⟪ ?i : _ r∈ (_ r▻ _) ⟫
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- ⟪ _ ea⊢ ea_var _ : _ ⟫              ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_abs _ _ _ : _ ⟫          ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_app _ _ _ _ : _ ⟫        ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_unit : _ ⟫               ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_true : _ ⟫               ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_false : _ ⟫              ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_ite _ _ _ : _ ⟫          ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_pair _ _ : _ ⟫           ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_proj₁ _ : _ ⟫            ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_proj₂ _ : _ ⟫            ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_inl _ _ _ : _ ⟫          ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_inr _ _ _ : _ ⟫          ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_caseof _ _ _ _ _ _ : _ ⟫ ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_seq _ _ : _ ⟫            ] => econstructor
    | [ |- ⟪ _ ea⊢ ea_coerce _ _ : _ ⟫         ] => econstructor
    | [ |- ⟪ ea⊢ ea_phole : _ , _ → _ , _ ⟫                ] => econstructor
    | [ |- ⟪ ea⊢ ea_pabs _ _ _ : _ , _ → _ , _ ⟫           ] => econstructor
    | [ |- ⟪ ea⊢ ea_papp₁ _ _ _ _ : _ , _ → _ , _ ⟫        ] => econstructor
    | [ |- ⟪ ea⊢ ea_papp₂ _ _ _ _ : _ , _ → _ , _ ⟫        ] => econstructor
    | [ |- ⟪ ea⊢ ea_pite₁ _ _ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ ea⊢ ea_pite₂ _ _ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ ea⊢ ea_pite₃ _ _ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ ea⊢ ea_ppair₁ _ _ : _ , _ → _ , _ ⟫           ] => econstructor
    | [ |- ⟪ ea⊢ ea_ppair₂ _ _ : _ , _ → _ , _ ⟫           ] => econstructor
    | [ |- ⟪ ea⊢ ea_pproj₁ _ : _ , _ → _ , _ ⟫             ] => econstructor
    | [ |- ⟪ ea⊢ ea_pproj₂ _ : _ , _ → _ , _ ⟫             ] => econstructor
    | [ |- ⟪ ea⊢ ea_pinl _ _ _ : _ , _ → _ , _ ⟫           ] => econstructor
    | [ |- ⟪ ea⊢ ea_pinr _ _ _ : _ , _ → _ , _ ⟫           ] => econstructor
    | [ |- ⟪ ea⊢ ea_pcaseof₁ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ ea⊢ ea_pcaseof₂ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ ea⊢ ea_pcaseof₃ _ _ _ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ ea⊢ ea_pseq₁ _ _ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ ea⊢ ea_pseq₂ _ _ _ : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ ea⊢ ea_pcoerce _ _ : _ , _ → _ , _ ⟫          ] => econstructor
  end.


Fixpoint eraseAnnot (t : TmA) : Tm :=
  match t with
  | ea_var i                   => var i
  | ea_abs τ₁ τ₂ t             => abs τ₁ (eraseAnnot t)
  | ea_app τ₁ τ₂ t₁ t₂         => app (eraseAnnot t₁) (eraseAnnot t₂)
  | ea_unit                    => unit
  | ea_true                    => true
  | ea_false                   => false
  | ea_ite τ t₁ t₂ t₃          => ite (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot t₃)
  | ea_pair τ₁ τ₂ t₁ t₂        => pair (eraseAnnot t₁) (eraseAnnot t₂)
  | ea_proj₁ τ₁ τ₂ t           => proj₁ (eraseAnnot t)
  | ea_proj₂ τ₁ τ₂ t           => proj₂ (eraseAnnot t)
  | ea_inl τ₁ τ₂ t             => inl (eraseAnnot t)
  | ea_inr τ₁ τ₂ t             => inr (eraseAnnot t)
  | ea_caseof τ₁ τ₂ τ t₁ t₂ t₃ => caseof (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot t₃)
  | ea_seq τ t₁ t₂             => seq (eraseAnnot t₁) (eraseAnnot t₂)
  | ea_coerce τ t              => eraseAnnot t
  end.

Fixpoint eraseAnnot_pctx (C : PCtxA) : PCtx :=
  match C with
  | ea_phole                    => phole
  | ea_pabs τ₁ τ₂ t             => pabs τ₁ (eraseAnnot_pctx t)
  | ea_papp₁ τ₁ τ₂ C t₂         => papp₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | ea_papp₂ τ₁ τ₂ t₁ C         => papp₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | ea_pite₁ τ C t₂ t₃          => pite₁ (eraseAnnot_pctx C) (eraseAnnot t₂) (eraseAnnot t₃)
  | ea_pite₂ τ t₁ C t₃          => pite₂ (eraseAnnot t₁) (eraseAnnot_pctx C) (eraseAnnot t₃)
  | ea_pite₃ τ t₁ t₂ C          => pite₃ (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot_pctx C)
  | ea_ppair₁ τ₁ τ₂ C t₂        => ppair₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | ea_ppair₂ τ₁ τ₂ t₁ C        => ppair₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | ea_pproj₁ τ₁ τ₂ C           => pproj₁ (eraseAnnot_pctx C)
  | ea_pproj₂ τ₁ τ₂ C           => pproj₂ (eraseAnnot_pctx C)
  | ea_pinl τ₁ τ₂ C             => pinl (eraseAnnot_pctx C)
  | ea_pinr τ₁ τ₂ C             => pinr (eraseAnnot_pctx C)
  | ea_pcaseof₁ τ₁ τ₂ τ C t₂ t₃ => pcaseof₁ (eraseAnnot_pctx C) (eraseAnnot t₂) (eraseAnnot t₃)
  | ea_pcaseof₂ τ₁ τ₂ τ t₁ C t₃ => pcaseof₂ (eraseAnnot t₁) (eraseAnnot_pctx C) (eraseAnnot t₃)
  | ea_pcaseof₃ τ₁ τ₂ τ t₁ t₂ C => pcaseof₃ (eraseAnnot t₁) (eraseAnnot t₂) (eraseAnnot_pctx C)
  | ea_pseq₁ τ C t₂             => pseq₁ (eraseAnnot_pctx C) (eraseAnnot t₂)
  | ea_pseq₂ τ t₁ C             => pseq₂ (eraseAnnot t₁) (eraseAnnot_pctx C)
  | ea_pcoerce τ C              => eraseAnnot_pctx C
  end.

Lemma eraseAnnotT {Γ t τ} : ⟪  Γ ea⊢ t : τ  ⟫ ->
                            ⟪  Γ e⊢ (eraseAnnot t) : τ  ⟫.
Proof.
  induction 1; cbn; eauto using Typing.
Qed.

Lemma eraseAnnot_pctxT {Γₒ τₒ Γ C τ} : ⟪ ea⊢ C : Γₒ , τₒ → Γ , τ ⟫ ->
                            ⟪  e⊢ eraseAnnot_pctx C : Γₒ , τₒ → Γ , τ  ⟫.
Proof.
  induction 1; cbn; eauto using Typing, PCtxTyping, eraseAnnotT.
Qed.

(* Hint Resolve pctxtyping_app_annot : typing. *)
(* Hint Resolve pctxtyping_cat_annot : typing. *)

(* Ltac crushTypingMatchEAH2 := *)
(*   match goal with *)
(*     | [ |- ⟪ _ ea⊢ pctxA_app _ _ : _ ⟫          ] => apply pctxtyping_app_annot *)
(*     | [ |- ⟪ ea⊢ pctxA_cat _ _ : _ , _ → _ , _ ⟫          ] => eapply pctxtyping_cat_annot *)
(*   end. *)

Ltac crushTypingEA :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchEAH;
     eauto with ws
    ).

Hint Extern 20 (⟪ _ ea⊢ _ : _ ⟫) =>
  crushTypingEA : typing.

Hint Extern 20 (⟪ ea⊢ _ : _ , _ → _ , _ ⟫) =>
  crushTypingEA : typing.
