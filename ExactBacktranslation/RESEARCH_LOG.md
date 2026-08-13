# Exact backtranslation research log

## 2026-08-11

- Baseline: the repository builds from clean sources with Coq 8.16.1 using
  `nix-shell -p coq_8_16 --run 'make V=0 JOBS=-j2'`.
- The checked-in `.vo` files were from Coq 9.1 and first had to be removed with
  the repository's `make clean` target.
- `RecTypes.Contraction.Tyeq` is coinductive in `Prop`, with structural nodes
  for unit, bool, variables, arrows, products, and sums, plus independent left
  and right unfolding nodes.
- `StlcEqui.SpecAnnot.ea_coerce` stores only the source type syntactically; its
  typing derivation supplies the target type and `Tyeq` evidence. A constructive
  compiler therefore needs a finite certificate in addition to the raw term.
- `CompilerIE.compie_annot` confirms that iso `fold` and `unfold` erase to equi
  coercions.
- First mechanized layer: an explicit finite cyclic equality graph whose local
  validity mirrors `Tyeq`, plus a guarded coinductive soundness proof.
- Certificate tests cover direct unfolding, equality below an arrow, products
  and sums, and the genuinely cyclic equality
  `mu a. Unit -> a = mu b. Unit -> Unit -> b`. The last graph has a real
  backedge from its final arrow node to its root.
- The graph interpreter uses the existing `StlcIso.Fix.ufix` at type
  `unit -> bundle`, where `bundle` is a nested heterogeneous product containing
  both `A_i -> B_i` and `B_i -> A_i` for every node. Backedges project from
  `self unit` underneath the generated cast lambdas.
- `GraphOK` alone is insufficient for term typing: the iso typing rules require
  contractive closed binder types. `GraphValid` records validity of every
  endpoint in the bundle.
- `graph_up_typing` and `graph_down_typing` prove, without admits, that both
  ordinary iso terms have the expected function types.
- The repository's `ea_coerce` cannot itself drive computation because its
  target and `Tyeq` proof occur only in the `Prop` typing derivation. `CTm`
  mirrors the annotated syntax but stores a finite graph at conversions.
  `erase_certificate_typing` proves it is a sound annotation of an Equi term,
  while `compile_typing` proves the derivation-directed Equi-to-Iso compiler.
- Conversion compilation is syntactically `graph_up g root (compile x)`, an
  application, so CBV evaluation of `x` is not delayed under a lambda.
- The end-to-end compiler test uses the genuinely cyclic certificate to cast a
  variable from `cycle_t` to `cycle_s`; both the generated Iso term and the
  certificate-erased Equi term are proven well typed.

## Remaining semantic gap

- No cast-identity or round-trip theorem has yet been proved. The existing IE
  logical relation relates an Iso term to its own erasure at one pseudo-type;
  the required result instead compares the erased heterogeneous cast with an
  Equi identity across `Tyeq`-equal endpoint types. This needs a new fundamental
  lemma indexed by graph nodes (and likely the existing step index), not a
  direct invocation of `CompilerIE.compie_correct`.
- Consequently completeness/decision for certificates, structural context
  translation, exact round trips, and the alternative full-abstraction proof
  remain open in this development.

## Indexed certificate redesign

- `CertificateIndexed.v` introduces `CastEq H A B : Type`. Each structural or
  unfolding rule extends `H` with its own endpoint pair; `ce_back` contains
  computational `Assumed H A B` membership evidence.
- A naive soundness proof that puts the current `Tyeq` result in a semantic
  environment is rejected by Coq as nested corecursion. The accepted proof
  uses a finite `Frames` zipper: backreferences jump to an ancestor `CastNode`,
  `observe` exposes one equality layer, and `focus_sound` is conventionally
  guarded beneath a `Tyeq` constructor.
- `search_casteq` is executable fuel-bounded proof search and automatically
  produces certificates for direct unfolding and the cyclic
  `mu a. Unit -> a = mu b. Unit -> Unit -> b` example.
- A total complete decider is not yet claimed. It requires a mechanized finite
  bound for the regular-tree state space induced by de Bruijn substitution.
  The active repository contains no such bound or equality decider; an older,
  inactive contraction file contains unfinished admitted attempts and is not
  used.
- Right unfolding now carries `NotMu A`; when both endpoints are recursive,
  search deterministically unfolds the left endpoint first. This removes a
  completeness ambiguity between certificates and deterministic search.
- The fuel-taking function has deliberately been renamed
  `search_casteq_bounded`. It is an internal proof-search approximant, not the
  exact compiler and not the public total decider still to be constructed.
- `StructuralCoercions.v` now gives the fuel-free interpretation of `CastEq`
  into ordinary Iso terms. It constructs the forward and reverse functions as
  one product, uses contravariance for arrow domains, and realizes a backedge
  through an ancestor cast pair tied by `StlcIso.Fix.ufix`.
- The cast-term environment is a type-indexed nested product computed from the
  assumed-pair environment. This avoids the heterogeneous equality transports
  produced by a second inductive parallel list.
- `compile_casteq_typing` and `compile_castnode_typing` are a mutual, fully
  checked typing proof for the interpreter. Closed forward and reverse typing
  corollaries are exposed separately.
- `StructuralCoercionTests.v` checks direct unfolding, arrow variance,
  products/sums, and both directions of the genuine cyclic backedge example.
- The current indexed interpreter ties one local `ufix` at each certificate
  step. It is exact and fuel-free, but consolidation into the requested single
  heterogeneous global fixed-point bundle remains future work.
- `IndexedCompiler.v` connects the indexed certificates to a derivation-directed
  certified Equi syntax. `erase_indexed_certificate_typing` uses
  `casteq_sound`, while `compile_indexed_typing` uses the ordinary-Iso cast
  typing theorem. A conversion compiles literally to
  `compile_closed_up d (compile_indexed x)` as an application, preserving CBV
  strictness.
- `IndexedCompilerTests.v` checks the complete path on the cyclic backedge:
  certified source typing, Equi annotation erasure typing, Iso compiler typing,
  and the strict application equation.
- `GlobalCoercions.v` replaces the transitional per-node fixed points with a
  certificate-shaped heterogeneous bundle. Every `ce_step` contributes a
  cast-pair cell and a recursively shaped payload; `ce_back` contributes no
  cell and selects an ancestor pair through the indexed assumption environment.
- `build_certificate_bundle` and `build_node_bundle` contain no object-language
  fixed point. `tied_certificate_bundle` contains the single `ufix` tying the
  entire heterogeneous bundle.
- The global construction has checked proofs of bundle-type validity,
  backreference/root projection typing, structural node-cast typing, mutual
  bundle-builder typing, fixed-point-functional typing, and closed forward and
  reverse coercion typing.
- `IndexedCompiler.v` now uses `compile_global_up`, so the actual exact
  Equi-to-Iso compiler—not only a side experiment—uses the single global knot.
- `GlobalCoercionTests.v` checks direct unfolding, arrows, products/sums, and
  both cyclic directions, plus a definitional equation exposing the one
  top-level tie.
- `RoundTrip.v` isolates the semantic obligation. It proves that the erased
  generated cast and the Equi identity are both typable at the same
  heterogeneous function type `A -> B`; `CastIdentity` states their required
  contextual equivalence.
- The Iso-to-Equi erasure of the indexed compiler is definitionally equal to
  `roundtrip_expansion`: the original term with precisely one erased cast
  application at every conversion. For certificate-free terms the round trip
  is proved syntactically exact.
- The existing `LogRelIE.valrel_tyeq` is not directly sufficient for
  `CastIdentity`: it changes the object type inside the approximate
  `pEmulDV` pseudo-type, whose Iso representation is `UValIE`, while generated
  casts operate on ordinary Iso values of endpoint type `A` and `B`. The next
  semantic layer must therefore be heterogeneous on the ordinary Iso side (or
  prove an equivalent certificate-indexed fundamental lemma).
- `HeterogeneousLR.v` introduces certificate-indexed, step-indexed value and
  term relations over ordinary Iso and Equi terms. It uses `observe : Focus ->
  EqView Focus`, so a backedge is followed through the finite frame zipper and
  every observable equality layer consumes one index.
- Both orientations are defined. `cast_value` compares Iso-at-left with
  Equi-at-right (reverse coercion); `cast_value_up` compares Iso-at-right with
  Equi-at-left (forward compiler coercion). The distinction matters at
  recursive nodes: `fold` is removed from the Iso endpoint only on the side
  whose endpoint is recursive.
- `GlobalEvaluation.v` proves the operational guardedness property rather than
  merely asserting it. `build_certificate_bundle_value` shows the finite bundle
  body is always a value—recursive self projections occur only inside cast
  lambdas. `tied_certificate_bundle_terminates` then explicitly uses the
  repository's `ufix` reduction lemmas. The closed pair, forward cast, and
  reverse cast are all proved terminating with no admits.
- `SemanticBridge.v` connects the generated ordinary-Iso cast to the existing
  open logical relation against the heterogeneous Equi identity.  The theorem
  is now proved through world one: the generated cast is evaluated eagerly to
  an Iso lambda, related to the Equi identity lambda, and their bodies are
  discharged at world zero.  `SemanticBridgeTests.v` instantiates this theorem
  with the genuinely cyclic certificate containing a backedge.
- Arbitrary worlds remain the central semantic obligation.  They require a
  guarded invariant for the entire tied bundle, not fuel in the compiler.

## 2026-08-12: exact package completed

- Replaced certificate-relative bounded search with an endpoint-derived total
  decision procedure for valid types.  The bound is the size of a finite pair
  universe computed from the regular-tree closures of the endpoints.
  `decide_casteq_complete`, `decide_casteq_iff`, and
  `casteq_decide_valid` close both soundness and completeness.
- Completed the structural and native bundle invariants for every certificate
  node, including arrows and both recursive-unfold cases.  The tied bundle now
  satisfies the heterogeneous logical relation at every world.
- Proved both erased casts contextually identical to the heterogeneous Equi
  identity: `generated_cast_contextually_identity` and
  `generated_down_cast_contextually_identity`.
- Added computational frontends for the repository's ordinary annotated Equi
  and Iso syntax.  Certificate inference is internal; no certificate or fuel is
  supplied by the compiler user.  The Equi conversion remains a strict
  application under CBV.
- Added a structural annotated-context frontend, with no abstraction around
  the hole and no observation index.
- Proved the concrete exact round trips `F (G e) ≈ e` and `G (F i) ≈ i`, exact
  structural context backtranslation, and full abstraction.
- Deleted the obsolete literal parallel-list `EqGraph` prototype and retained
  only the indexed `CastEq` architecture requested by the user.
- Refactored environment invariants to structural recursion, eliminating the
  accidental `Eqdep.Eq_rect_eq.eq_rect_eq` dependency.  The public assumption
  audit now reports only the repository's pre-existing
  `functional_extensionality_dep`.
- Coq 8.16.1 successfully compiles the entire repository with `make -B V=0
  -j2`; all executable and theorem-level stress tests pass.

## 2026-08-13: computational Iso annotation insertion

- Corrected the Equi-to-Iso frontend interface: `compile_equi_annot` now maps
  `StlcEqui.SpecAnnot.TmA` to `StlcIso.SpecAnnot.TmA`, rather than taking an
  annotated source and silently returning raw Iso syntax.  Raw syntax is
  exposed separately as `compile_equi_raw` and only used at semantic APIs that
  are defined over raw terms.
- Added `AnnotatedGlobalCoercions.v`, a direct annotated interpretation of the
  same finite cyclic certificate and single heterogeneous fixed-point bundle.
  The `cn_mu_l` and `cn_mu_r` cases computationally emit `ia_fold_ body` and
  `ia_unfold_ body`; no typing derivation in `Prop` is eliminated to recover
  those bodies.
- Proved direct annotated typing for the entire bundle functional, tied bundle,
  forward cast, and reverse cast.  Proved erasure agreement with every public
  raw cast (`erase_compile_global_pair_annot`,
  `erase_compile_global_up_annot`, and
  `erase_compile_global_down_annot`).
- Added `compile_indexed_annot` and `compile_indexed_context_annot`, with direct
  annotated typing, structural plugging, CBV-strict conversion equations, and
  erasure agreement with the established raw term/context compilers.
- `compile_equi_context_annot` now returns an annotated Iso context directly.
  `ContextAnnotation.compile_indexed_context_has_annotation` uses that concrete
  compiler output as its witness, replacing the old post-hoc reconstruction
  from raw typing derivations on the exact compiler codepath.
- Updated exact round-trip, context-backtranslation, and FAC statements to
  erase the annotated target only at the repository's raw contextual-
  equivalence boundary.  The underlying semantic theorems and generated raw
  programs are unchanged by the erasure-agreement proofs.
- Added executable/proof tests for annotated cyclic casts in both directions,
  annotated compiler strictness and erasure, annotated structural contexts,
  and a direct recursive node whose generated syntax visibly contains
  `ia_unfold_ tunit` and `ia_fold_ tunit`.
