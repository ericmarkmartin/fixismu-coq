Require Import ExactBacktranslation.IndexedCompiler.
Require Import ExactBacktranslation.GlobalCoercions.
Require Import ExactBacktranslation.CertificateIndexed.
Require Import CompilerIE.Compiler.
Require Import StlcEqui.SpecEquivalent.
Require Import StlcEqui.LemmasTyping.

Module CE := CompilerIE.Compiler.E.

(** Raw source term: computational certificates annotate typing only and are
    absent from the Equi runtime syntax. *)
Definition erase_indexed_raw (t : ICTm) : CE.Tm :=
  CE.eraseAnnot (erase_indexed_certificate t).

Theorem erase_indexed_raw_typing {Γ t A} :
  ⟪ Γ ic⊢ t : A ⟫ -> ⟪ Γ e⊢ erase_indexed_raw t : A ⟫.
Proof.
  intros Ht. unfold erase_indexed_raw.
  apply CE.eraseAnnotT, erase_indexed_certificate_typing. exact Ht.
Qed.

(** An Equi identity can be assigned the heterogeneous function type [A -> B]
    whenever the certificate proves [A ≡ B]. *)
Definition equi_identity (A : Ty) : CE.Tm := CE.abs A (CE.var 0).

Lemma equi_identity_heterogeneous_typing {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ CE.empty e⊢ equi_identity A : tarr A B ⟫.
Proof.
  intros VA VB. unfold equi_identity.
  eapply CE.WtEq.
  - refine (@EqArr A A A B _ _).
    + now apply tyeq_refl.
    + exact (casteq_sound d).
  - now apply ValidTy_arr.
  - now apply ValidTy_arr.
  - apply CE.WtAbs.
    + apply CE.WtVar. constructor.
    + exact VA.
Qed.

Lemma equi_identity_reverse_heterogeneous_typing {A B}
    (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ CE.empty e⊢ equi_identity B : tarr B A ⟫.
Proof.
  intros VA VB. unfold equi_identity.
  eapply CE.WtEq.
  - refine (@EqArr B B B A _ _).
    + now apply tyeq_refl.
    + exact (tyeq_symm (casteq_sound d)).
  - now apply ValidTy_arr.
  - now apply ValidTy_arr.
  - apply CE.WtAbs.
    + apply CE.WtVar. constructor.
    + exact VB.
Qed.

Lemma erased_global_up_typing {A B} (d : ClosedCastEq A B) :
  ValidTy A -> ValidTy B ->
  ⟪ CE.empty e⊢ CompilerIE.Compiler.compie (compile_global_up d) :
      tarr A B ⟫.
Proof.
  intros VA VB. apply CompilerIE.Compiler.compie_typing_works.
  now apply compile_global_up_typing.
Qed.

(** Semantic identity of generated casts is stated at the common Equi type
    [A -> B], so it composes directly with ordinary contextual equivalence. *)
Definition CastIdentity : Prop :=
  forall A B (d : ClosedCastEq A B),
    ValidTy A -> ValidTy B ->
    ⟪ CE.empty e⊢ CompilerIE.Compiler.compie (compile_global_up d)
       ≃ equi_identity A : tarr A B ⟫.

(** Expansion of the round trip. It is the original raw Equi term except that
    every conversion is represented by an application of its erased cast. *)
Fixpoint roundtrip_expansion (t : ICTm) : CE.Tm :=
  match t with
  | ic_var i => CE.var i
  | ic_abs A B body => CE.abs A (roundtrip_expansion body)
  | ic_app A B f x => CE.app (roundtrip_expansion f) (roundtrip_expansion x)
  | ic_unit => CE.unit
  | ic_true => CE.true
  | ic_false => CE.false
  | ic_ite A b x y => CE.ite (roundtrip_expansion b)
                            (roundtrip_expansion x) (roundtrip_expansion y)
  | ic_pair A B x y => CE.pair (roundtrip_expansion x) (roundtrip_expansion y)
  | ic_proj1 A B p => CE.proj₁ (roundtrip_expansion p)
  | ic_proj2 A B p => CE.proj₂ (roundtrip_expansion p)
  | ic_inl A B x => CE.inl (roundtrip_expansion x)
  | ic_inr A B x => CE.inr (roundtrip_expansion x)
  | ic_case A B C s l r => CE.caseof (roundtrip_expansion s)
      (roundtrip_expansion l) (roundtrip_expansion r)
  | ic_seq A x y => CE.seq (roundtrip_expansion x) (roundtrip_expansion y)
  | ic_coerce A B d x =>
      CE.app (CompilerIE.Compiler.compie (compile_global_up d))
             (roundtrip_expansion x)
  end.

Theorem compiler_erasure_is_roundtrip_expansion t :
  CompilerIE.Compiler.compie (compile_indexed t) = roundtrip_expansion t.
Proof.
  induction t; cbn; congruence.
Qed.

Inductive CastFree : ICTm -> Prop :=
| cf_var i : CastFree (ic_var i)
| cf_abs A B t : CastFree t -> CastFree (ic_abs A B t)
| cf_app A B f x : CastFree f -> CastFree x -> CastFree (ic_app A B f x)
| cf_unit : CastFree ic_unit
| cf_true : CastFree ic_true
| cf_false : CastFree ic_false
| cf_ite A b x y : CastFree b -> CastFree x -> CastFree y ->
    CastFree (ic_ite A b x y)
| cf_pair A B x y : CastFree x -> CastFree y -> CastFree (ic_pair A B x y)
| cf_proj1 A B p : CastFree p -> CastFree (ic_proj1 A B p)
| cf_proj2 A B p : CastFree p -> CastFree (ic_proj2 A B p)
| cf_inl A B x : CastFree x -> CastFree (ic_inl A B x)
| cf_inr A B x : CastFree x -> CastFree (ic_inr A B x)
| cf_case A B C s l r : CastFree s -> CastFree l -> CastFree r ->
    CastFree (ic_case A B C s l r)
| cf_seq A x y : CastFree x -> CastFree y -> CastFree (ic_seq A x y).

Theorem cast_free_roundtrip_exact t :
  CastFree t ->
  CompilerIE.Compiler.compie (compile_indexed t) = erase_indexed_raw t.
Proof.
  unfold erase_indexed_raw. induction 1; cbn; congruence.
Qed.
