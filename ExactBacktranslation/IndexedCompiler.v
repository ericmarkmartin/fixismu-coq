Require Import ExactBacktranslation.CertificateIndexed.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecTyping.
Require Import StlcEqui.SpecAnnot.

Module I := StlcIso.SpecSyntax.
Module IT := StlcIso.SpecTyping.
Module E := StlcEqui.SpecAnnot.

(** Equi terms with computational equality evidence at conversions.  The
    certificate is closed: its internal environment represents only cyclic
    assumptions local to that equality proof. *)
Inductive ICTm : Set :=
| ic_var (i : Ix)
| ic_abs (A B : Ty) (body : ICTm)
| ic_app (A B : Ty) (f x : ICTm)
| ic_unit
| ic_true
| ic_false
| ic_ite (A : Ty) (b t e : ICTm)
| ic_pair (A B : Ty) (x y : ICTm)
| ic_proj1 (A B : Ty) (p : ICTm)
| ic_proj2 (A B : Ty) (p : ICTm)
| ic_inl (A B : Ty) (x : ICTm)
| ic_inr (A B : Ty) (x : ICTm)
| ic_case (A B C : Ty) (s l r : ICTm)
| ic_seq (A : Ty) (x y : ICTm)
| ic_coerce (A B : Ty) (d : ClosedCastEq A B) (x : ICTm).

Fixpoint erase_indexed_certificate (t : ICTm) : E.TmA :=
  match t with
  | ic_var i => E.ea_var i
  | ic_abs A B body => E.ea_abs A B (erase_indexed_certificate body)
  | ic_app A B f x => E.ea_app A B (erase_indexed_certificate f)
                                   (erase_indexed_certificate x)
  | ic_unit => E.ea_unit
  | ic_true => E.ea_true
  | ic_false => E.ea_false
  | ic_ite A b t e => E.ea_ite A (erase_indexed_certificate b)
                                  (erase_indexed_certificate t)
                                  (erase_indexed_certificate e)
  | ic_pair A B x y => E.ea_pair A B (erase_indexed_certificate x)
                                      (erase_indexed_certificate y)
  | ic_proj1 A B p => E.ea_proj₁ A B (erase_indexed_certificate p)
  | ic_proj2 A B p => E.ea_proj₂ A B (erase_indexed_certificate p)
  | ic_inl A B x => E.ea_inl A B (erase_indexed_certificate x)
  | ic_inr A B x => E.ea_inr A B (erase_indexed_certificate x)
  | ic_case A B C s l r => E.ea_caseof A B C
      (erase_indexed_certificate s) (erase_indexed_certificate l)
      (erase_indexed_certificate r)
  | ic_seq A x y => E.ea_seq A (erase_indexed_certificate x)
                               (erase_indexed_certificate y)
  | ic_coerce A B d x => E.ea_coerce A (erase_indexed_certificate x)
  end.

Fixpoint compile_indexed (t : ICTm) : I.Tm :=
  match t with
  | ic_var i => I.var i
  | ic_abs A B body => I.abs A (compile_indexed body)
  | ic_app A B f x => I.app (compile_indexed f) (compile_indexed x)
  | ic_unit => I.unit
  | ic_true => I.true
  | ic_false => I.false
  | ic_ite A b t e => I.ite (compile_indexed b) (compile_indexed t)
                            (compile_indexed e)
  | ic_pair A B x y => I.pair (compile_indexed x) (compile_indexed y)
  | ic_proj1 A B p => I.proj₁ (compile_indexed p)
  | ic_proj2 A B p => I.proj₂ (compile_indexed p)
  | ic_inl A B x => I.inl (compile_indexed x)
  | ic_inr A B x => I.inr (compile_indexed x)
  | ic_case A B C s l r => I.caseof (compile_indexed s)
      (compile_indexed l) (compile_indexed r)
  | ic_seq A x y => I.seq (compile_indexed x) (compile_indexed y)
  | ic_coerce A B d x => I.app (compile_global_up d) (compile_indexed x)
  end.

Reserved Notation "⟪  Γ ic⊢ t : T  ⟫"
  (at level 0, Γ at level 98, t at level 98, T at level 98).
Inductive ICTyping (Γ : Env) : ICTm -> Ty -> Prop :=
| IC_WtVar {i A} : ⟪ i : A r∈ Γ ⟫ -> ⟪ Γ ic⊢ ic_var i : A ⟫
| IC_WtAbs {A B t} :
    ValidTy A -> ⟪ Γ r▻ A ic⊢ t : B ⟫ ->
    ⟪ Γ ic⊢ ic_abs A B t : tarr A B ⟫
| IC_WtApp {A B f x} :
    ⟪ Γ ic⊢ f : tarr A B ⟫ -> ⟪ Γ ic⊢ x : A ⟫ ->
    ⟪ Γ ic⊢ ic_app A B f x : B ⟫
| IC_WtUnit : ⟪ Γ ic⊢ ic_unit : tunit ⟫
| IC_WtTrue : ⟪ Γ ic⊢ ic_true : tbool ⟫
| IC_WtFalse : ⟪ Γ ic⊢ ic_false : tbool ⟫
| IC_WtIte {A b t e} :
    ⟪ Γ ic⊢ b : tbool ⟫ -> ⟪ Γ ic⊢ t : A ⟫ -> ⟪ Γ ic⊢ e : A ⟫ ->
    ⟪ Γ ic⊢ ic_ite A b t e : A ⟫
| IC_WtPair {A B x y} :
    ⟪ Γ ic⊢ x : A ⟫ -> ⟪ Γ ic⊢ y : B ⟫ ->
    ⟪ Γ ic⊢ ic_pair A B x y : tprod A B ⟫
| IC_WtProj1 {A B p} :
    ⟪ Γ ic⊢ p : tprod A B ⟫ -> ⟪ Γ ic⊢ ic_proj1 A B p : A ⟫
| IC_WtProj2 {A B p} :
    ⟪ Γ ic⊢ p : tprod A B ⟫ -> ⟪ Γ ic⊢ ic_proj2 A B p : B ⟫
| IC_WtInl {A B x} :
    ValidTy B -> ⟪ Γ ic⊢ x : A ⟫ -> ⟪ Γ ic⊢ ic_inl A B x : tsum A B ⟫
| IC_WtInr {A B x} :
    ValidTy A -> ⟪ Γ ic⊢ x : B ⟫ -> ⟪ Γ ic⊢ ic_inr A B x : tsum A B ⟫
| IC_WtCase {A B C s l r} :
    ⟪ Γ ic⊢ s : tsum A B ⟫ ->
    ⟪ Γ r▻ A ic⊢ l : C ⟫ -> ⟪ Γ r▻ B ic⊢ r : C ⟫ ->
    ValidTy A -> ValidTy B -> ⟪ Γ ic⊢ ic_case A B C s l r : C ⟫
| IC_WtSeq {A x y} :
    ⟪ Γ ic⊢ x : tunit ⟫ -> ⟪ Γ ic⊢ y : A ⟫ ->
    ⟪ Γ ic⊢ ic_seq A x y : A ⟫
| IC_WtCoerce {A B d x} :
    ValidTy A -> ValidTy B -> ⟪ Γ ic⊢ x : A ⟫ ->
    ⟪ Γ ic⊢ ic_coerce A B d x : B ⟫
where "⟪  Γ ic⊢ t : T  ⟫" := (ICTyping Γ t T).

Theorem erase_indexed_certificate_typing {Γ t A} :
  ⟪ Γ ic⊢ t : A ⟫ -> ⟪ Γ ea⊢ erase_indexed_certificate t : A ⟫.
Proof.
  induction 1; cbn; eauto using E.AnnotTyping.
  eapply E.ea_WtCoerce; eauto using casteq_sound.
Qed.

Theorem compile_indexed_typing {Γ t A} :
  ⟪ Γ ic⊢ t : A ⟫ -> ⟪ Γ i⊢ compile_indexed t : A ⟫.
Proof.
  induction 1; cbn; eauto using IT.Typing.
  eapply IT.WtApp; [now apply compile_global_up_typing|exact IHICTyping].
Qed.

(** The source computation is an application argument, hence is evaluated in
    the original CBV order rather than delayed under an eta-expanded lambda. *)
Lemma compile_indexed_coerce_strict A B d x :
  compile_indexed (ic_coerce A B d x) =
  I.app (compile_global_up d) (compile_indexed x).
Proof. reflexivity. Qed.
