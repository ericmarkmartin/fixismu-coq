# fixismu-coq
[![build](https://github.com/dominiquedevriese/fixismu-coq/actions/workflows/build.yml/badge.svg)](https://github.com/dominiquedevriese/fixismu-coq/actions/workflows/build.yml)

Rocq proofs for the results reported in [_On the Semantic Expresiveness of
Recursive Types_][arxiv]. They establish semantic equi-expressiveness results
between simply-typed lambda calculi with
1. a fixpoint combinator
2. iso-recurisve types
3. equi-recursive types

The proof uses a technique called approximate backtranslation, which is
discussed in detail in [the paper][arxiv] and its references.

This artifact was developed by [Dominique Devriese] and [Eric Mark Martin]. It leverages machinery developed by [Steven Keuchel].

[Dominique Devriese]: mailto:dominique.devriese@cs.kuleuven.be
[Eric Mark Martin]: https://github.com/ericmarkmartin
[Steven Keuchel]: mailto:steven.keuchel@ugent.be

## Structure of the Proof

Here is a list of Rocq files with a short description of what they contain, in
dependency order. 

* Common/Common.v: A few simple arithmetic lemmas that we didn't immediately
find in the Rocq standard library
* Common/Relations.v: Lemmas and definitions concerning the transitive and transitive-reflexive closure of relations and the transitive-reflexive closure indexed with a step count.
* Db: Definitions and lemmas for working with De Bruijn binding structure
  * Db/Spec.v: A generic specification of languages with a De Bruijn binding structure, along with a set of type classes that may be instantiated for such languages.
  * Db/Inst.v: Some instances for the type classes in Db/Spec.v.
  * Db/Tactics.v: A (weird?) tactic used in Db/Lemmas.v.
  * Db/Lemmas.v: a set of lemmas about languages instantiating the type classes in Db/Spec.v
  * Db/WellScoping.v: A set of lemmas related to well-scopedness of terms and substitutions.
* RecTypes/*.v: Definitions and lemmas for the type grammar shared by StlcIso and StlcEqui
* Stlc: Definitions and lemmas for the simply-typed lambda calculi we work with
  * StlcFix/*.v: STLC with a fixpoint operator
  * StlcIso/*.v: STLC with iso-recurisve types
  * StlcEqui/*.v: STLC with equi-recursive types
* UVal: Definition and lemmas for the backtranslation types
  * UValFI/UVal.v: The backtranslation type for the StlcFix-StlcIso relation
  * UValFE/UVal.v: The backtranslation type for the StlcFix-StlcEqui relation
  * UValIE/UVal.v: The backtranslation type for the StlcIso-StlcEqui relation
* LogRel: Definition of the cross-language logical relations, and lemmas.
  * LogRelFI/*.v: Relation between StlcFix and StlcIso
  * LogRelFE/*.v: Relation between StlcFix and StlcEqui
  * LogRelIE/*.v: Relation between StlcIso and StlcEqui
* Compiler: Definition of the compilers and proof of equivalence reflection
  * LogRelFI/*.v: Compiler from StlcFix to StlcIso
  * LogRelFE/*.v: Compiler from StlcFix to StlcEqui
  * LogRelIE/*.v: Compiler from StlcIso to StlcEqui
* BackTrans: Definitions of the back-translation and lemmas
  * LogRelFI/*.v: Backtranslation from StlcIso to StlcFix
  * LogRelFE/*.v: Backtranslation from StlcEqui to StlcFix
  * LogRelIE/*.v: Backtranslation from StlcEqui to StlcIso
* FullAbstraction:  Proofs of equivalence preservation and full abstraction
  * FullAbstractionFI.v: From StlcFix to StlcIso
  * FullAbstractionFE.v: From StlcFix to StlcEqui
  * FullAbstractionIE.v: From StlcIso to StlcEqui

[arxiv]: https://arxiv.org/abs/2010.10859
[STLC]: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

## Building the proof

1. Clone the repository
2. run `make` from the repo root

### Compatible Rocq version

- 9.1.1

This is checked using the [Docker-Coq GitHub Action] (see the badge at the top of this readme).

[Docker-Coq GitHub Action]: https://github.com/rocq-prover/docker-opam-action

### Assumptions

We depend on only two Axioms

* [`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`][functional_extensionality_dep]
* [`Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`][eq_rect_eq]

[functional_extensionality_dep]: https://rocq-prover.org/doc/V9.1.0/stdlib/Stdlib.Logic.FunctionalExtensionality.html#functional_extensionality_dep
[eq_rect_eq]: https://rocq-prover.org/doc/V9.1.0/stdlib/Stdlib.Logic.Eqdep.html#Eq_rect_eq.eq_rect_eq

## Differences to the Paper

1. Each of the languages has a second specification of their terms, contexts,
   and typing rules (for both terms and contexts) in SpecAnnot.v. These
   specifications fully annotate the types in all terms (e.g. terms of type `τ x
   σ` are annotated with `τ` and `σ`). These specifications come with
   `eraseAnnot` functions to convert back into the normal specification by
   erasing these annotations, along with proofs that these conversions are
   type-sound.
   
   This is only an implementation detail—the top-level full abstraction results
   are stated with respect to the "normal" language specifications.

2. This artifact, unlike the paper, cannot elide the contractiveness of
   recursive types for consision. You will see `ValidTy τ` throughout the
   artifact, which says that `τ` is both contractive and closed.

## Paper-to-artifact correspondence guide

Note that we indicate which compiler we are working with (or proving claims about) with abbreviations:
* *FI* indicates the compiler from *F*ix to *I*so
* *FE* indicates the compiler from *F*ix to *E*qui
* *IE* indicates the compiler from *I*so to *E*qui

| Definition / Theorem | Paper | File | Name of Formalization | Notation |
|---|---|---|---|---|
| Syntax of STLCs | Page 7 | Stlc{Fix, Iso, Equi}/SpecSyntax.v | `Inductive Tm` |  |
| Syntax of Program contexts | Page 7 | Stlc{Fix, Iso, Equi}/SpecSyntax.v | `Inductive PCtx` |  |
| Size of STLC terms | Page 7 | Stlc{Fix, Iso, Equi}/Size.v | `Fixpoint size` |  |
| 2.2 STLC Static Semantics | Page 7-8 | Stlc{Fix, Iso, Equi}/SpecTyping.v | `Inductive Typing` | `⟪  Γ `?`⊢ t : T  ⟫` where ? is either the empty string, i, or e for Stlc `Fix`, `Iso`, or `Equi` respectively |
| 2.2 Program context static Semantics | Page 8-9 | Stlc{Fix, Iso, Equi}/SpecTyping.v | `Inductive PCtxTyping` | `⟪ `?`⊢ C : Γ₀ , τ₀ → Γ , τ ⟫`, with ? as above
| 2.3 Dynamic Semantics primitive reductions | Page 10 | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Inductive eval₀` | `t₁ -->₀ t₂` |
| 2.3 Dynamic Semantics non-primitive reductions | Page 10 | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Inductive eval` | `t₁ --> t₂` |
| 2.4 Termination | Page 10, Definition 1 | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Definition Terminating` | `t ⇓` |
| 2.4 (Bounded termination) | Page 10 | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Definition TerminatingN` | `t ⇓_ n` |
| 2.4 (Size-bounded termination) | Page 10 | Stlc{Fix, Iso, Equi}/Size.v  | `Definition TermHor` |  |
| Relation between Termination and Size-Bound Termination | Page 11, Theorem 1 | Stlc{Fix, Iso, Equi}/Size.v | `Lemma evalHor_evaln` and `Lemma TermHor_TerminatingN` | |
| Observation relation | Page 11, Figure 2 | LogRel{FI, FE, IE}/LR.v | `Definition Obs` |  |
| Pseudo types | Page 12 | LogRel{FI, FE, IE}/PseudoType.v | `Inductive PTy` | |
| Pseudo type conversions | Page 12 | LogRel{FI, FE, IE}/PseudoType.v | `Fixpoint repEmul`, `Fixpoint fxToIs`, `Fixpoint isToEq`, `Definition OfType`, `Definition OfTypeStlcIso`, `Definition OfTypeStlcEqui` | |
| Value relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition valrel` |  |
| Term relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition termrel` | |
| Context relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition contrel` | |
| Substitution relation | Page 13, Figure 3 | LogRel{FI, FE, IE}/LR.v | `Definition envrel` | |
| Logical relation up to _n_ steps for FI | Page 14, Definition 2 | LogRel{FI, FE, IE}/LR.v | `Definition OpenLRN` | `⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ ⟫` (`d` is the direction of the relation—▽ in the paper) |
| Logical relations for FI, FE, and IE | Page 14, Definitions 3-5 | LogRel{FI, FE, IE}/LR.v | `Definition OpenLR` | `⟪ Γ ⊩ ts ⟦ d ⟧ tu : τ ⟫` |
| Logical relations for FI, FE, and IE program contexts | Page 15, Definitions 6-8 | LogRel{FI, FE, IE}/LR.v | `Definition OpenLRCtx` | `⟪ ⊩ Cs ⟦ d ⟧ Cu : Γ₀ , τ₀ → Γ , τ ⟫` |
| Adequacy for ≈ for FI | Page 15, Lemma 1 | LogRelFI/LemmasLR.v | `Lemma adequacy_lt` and `Lemma adequacy_gt` | |
| Contextual Equivalence | Page 16, Definition 9 | Stlc{Fix, Iso, Equi}/SpecEquivalent.v | `Definition PCtxEquivalent` | `⟪  Γ ⊢ t₁ ≃ t₂ : τ  ⟫` |
| Fully-abstract compilation | Page 16, Definition 10 | FullAbstraction{FI, FE, IE}.v | `Definition FullAbstraction` | |
| The type of backtranslated terms | Page 18, Figure 5 | UVal{FI, FE, IE}/UVal.v | `Fixpoint UVal`{`FI`, `FE`, `IE`} | |
| The upgrade function | Page 20, Figure 6 | BackTrans{FI, FE, IE}/UpgradeDowngrade.v | `Fixpoint upgrade` | |
| The downgrade function | Page 21, Figure 7 | BackTrans{FI, FE, IE}/UpgradeDowngrade.v | `Fixpoint downgrade` | |
| Compacted functions used to manipulate backtranslated values | Page 23, Figure 8 | BackTrans{FI, FE, IE}/UValHelpers.v | `Section Intro` and `Section Destruct` | |
| Missing bits of the logical relation | Page 23, Figure 9 | LogRel{FI, FE, IE}/LR.v | `Definition valrel` |  |
| Missing auxiliary functions of the logical relation | Page 24, Figure 10 | LogRel{FI, FE, IE}/PseudoType.v | `Fixpoint repEmul`, `Fixpoint fxToIs`, `Fixpoint isToEq`
| Compatibility lemma for λ | Page 25, Lemma 2 | Compiler{FI, FE, IE}/Compiler.v | `Lemma compat_lambda` | |
| Compilers are semantics preserving | Page 25, Lemmas 3-5 | Compiler{FI, FE, IE}/Compiler.v | `Lemma comp`{`fi`, `fe`, `ie`}`_correct`
| Definition of our compilers | Page 26, Figure 11 | Compiler{FI, FE, IE}/Compiler.v | `Fixpoint comp`{`fi`, `fe`, `ie`} | |
| Compilers are semantics preserving for contexts | Page 26, Lemmas 6-8 | Compiler{FI, FE, IE}/Compiler.v | `Lemma comp`{`fi`, `fe`, `ie`}`_ctx_correct` | |
| Compilers reflect equivalence | Page 27, Theorems 2-4 | Compiler{FI, FE, IE}/Compiler.v | `Lemma equivalenceReflection` | |
| Emulation of targets terms into source ones | Page 28, Figure 12 | Backtrans{FI, FE, IE}/Emulate.v | `Fixpoint emulate` | | 
| Emulation of targets contexts into source ones | Page 29, Figure 13 | Backtrans{FI, FE, IE}/Emulate.v | `Fixpoint emulate_pctx` | |
| Equivalent types are backtranslated to the same type | Page 29, Theorem 5 | UValIE/UVal.v | `Lemma UVal_eq` | |
| Compatibility for λ emulation | Page 30, Lemma 9 | Backtrans{FI, FE, IE}/Emulate.v | `Lemma compat_emul_abs` | |
| Compatibility lemma for emulation of type equality | Page 30, Lemma 10 | LogRel{FE, IE}/LemmasInversion.v | `Lemma compat_type_eq` | |
| Equivalent types have the same term relation | Page 30, Corollary 1 | LogRel{FE, IE}/LemmasInversion.v | `Lemma valrel_tyeq'` | |
| Emulate is semantics preserving | Page 30, Lemma 11 | Backtrans{FI, FE, IE}/Emulate.v | `Lemma emulate_works` | |
| Emulate is semantics preserving for contexts | Page 31, Lemma 12 | Backtrans{FI, FE, IE}/Emulate.v | `Lemma emulate_pctx_works` | |
| Inject and extract functions | Page 31, Figure 14 | Backtrans{FI, FE, IE}/InjectExtract.v | `Definition inject`, `Definition extract` | |
| Inject and extract are semantics preserving | Page 32, Lemma 13 | Backtrans{FI, FE, IE}/InjectExtract.v | `Lemma inject_works with extract_works` | |
| Approximate backtranslation | Page 34, Definition 11 | Backtrans{FI, FE, IE}/Backtrans.v | `Definition backtranslateCtx` | |
| Correctness of backtranslation | Page 35, Lemma 14 | Backtrans{FI, FE, IE}/Backtrans.v | `Lemma backtranslateCtx_works` | |
| Compilation preserves equivalence | Page 35-36, Theorems 6-8 | FullAbstraction{FI, FE, IE}.v | `Lemma equivalencePreservation` | |
| Compilation is fully abstract | Page 36, Theorems 9-11 | FullAbstraction{FI, FE, IE}.v | `Lemma FullAbstraction` | |
