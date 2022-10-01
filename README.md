# fixismu-coq
Coq proofs establishing semantic equi-expressiveness results for recursive types between [STLC] with
1. a fixpoint combinator
2. iso-recurisve types
3. equi-recursive types

See the paper [on arxiv][arxiv]

[arxiv]: https://arxiv.org/abs/2010.10859
[STLC]: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

## Building the proof

1. Clone the repository
2. run `make` from the repo root

### Verified compatible coq versions
- 8.13.2

## Paper-to-artifact correspondence guide

| Definition / Theorem | Paper | File | Name of Formalization | Notation |
|---|---|---|---|---|
| Syntax of STLCs | Page 7, Figure ? | Stlc{Fix, Iso, Equi}/SpecSyntax.v | `Inductive Tm` |  |
| Syntax of Program contexts | Page 7, Figure ? | Stlc{Fix, Iso, Equi}/SpecSyntax.v | `Inductive PCtx` |  |
| Size of STLC terms | Page 7, Figure ? | Stlc{Fix, Iso, Equi}/Size.v | `Fixpoint size` |  |
| 2.2 STLC Static Semantics | Page 7-8, Figure ? | Stlc{Fix, Iso, Equi}/SpecTyping.v | `Inductive Typing` | `⟪  Γ `?`⊢ t : T  ⟫` where ? is either the empty string, i, or e for STLC `Fix`, `Iso`, or `Equi` respectively |
| 2.2 Program context static Semantics | Page 8-9, Figure ? | Stlc{Fix, Iso, Equi}/SpecTyping.v | `Inductive PCtxTyping` | `⟪ `?`⊢ C : Γ₀ , τ₀ → Γ , τ ⟫`, with ? as above
| 2.3 Dynamic Semantics primitive reductions | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Inductive eval₀` | `t₁ -->₀ t₂` |
| 2.3 Dynamic Semantics non-primitive reductions | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Inductive eval` | `t₁ --> t₂` |
| 2.4 Termination | Page 10, Definition 1 | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Definition Terminating` | `t ⇓` |
| 2.4 (Bounded termination) | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/SpecEvaluation.v | `Definition TerminatingN` | `t ⇓_ n` |
| 2.4 (Size-bounded termination) | Page 10, Figure ? | Stlc{Fix, Iso, Equi}/Size.v  | `Definition TermHor` |  |
| Relation between Termination and Size-Bound Termination | Page 11, Theorem 1 | Stlc{Fix, Iso, Equi}/Size.v | `Lemma evalHor_evaln` and `Lemma TermHor_TerminatingN` | |
| Observation relation | Page 11, Figure 2 | LogRel{FI, FE, IE}/LR.v | `Definition Obs` |   |
| Pseudo types| Page 12, Figure ? | LogRel{FI, FE, IE}/PseudoType.v
