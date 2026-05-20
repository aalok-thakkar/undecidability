# Architecture and proof chain

This document describes the proof architecture of the results currently
landed in the repository. For the project vision see
[`README.md`](README.md); for the forward-looking work plan see
[`TODO.md`](TODO.md).

## The reduction graph

DiagonaLean's reduction graph has **13 registered edges** at this
point. Visualised as a chain of `List Bool`-input encoded problems
(the form compatible with `TMComputable`):

```
selfHaltPred                                                    (List Bool → Prop)
  ↑ tm-anchor: selfHaltPred_TMUndecidable [REAL theorem from halt_undecidable]
  │
CanonicalSelfHalt          ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─→ HaltsOnEverything
  ↑ tm-anchor                  canonicalSelfHalt_to_                (Rice extender)
  │ CanonicalSelfHalt_         haltsOnEverything
  │ TMUndecidable
  │
EncodedSelfHalt
  │ encodedSelfHalt_to_encodedHalt
  ▼
EncodedHalt   ←─ ─ ─ ─ ─ ─ ─ HaltTMCode ≡ₘ EncodedHalt
  │                          (via haltTMCode_to_encodedHalt,
  │ encodedHalt_to_           encodedHalt_to_haltTMCode)
  │ encodedHaltMPCP
  ▼ (HUM-normalising wrapper)
EncodedHaltMPCP   ←─ ─ ─ ─ ─ MPCP_LB
  │                          (via encodedHaltMPCP_to_mpcpLB)
  │ encodedHaltMPCP_to_       
  │ encodedMPCP_LB           Also: HaltTM ≤ HaltTMCode
  ▼
EncodedMPCP_LB             EncodedPCP ←─ ─ ─ mpcpToPcp α
  │                          ↑
  │ encodedMPCP_LB_to_       │ encodedPCP_to_
  │ encodedPCP_LB            │ encodedCFGIntersection
  ▼                          ▼
EncodedPCP_LB              EncodedCFGIntersection
  │
  │ encodedPCP_LB_to_encodedCFGI_LB
  ▼
EncodedCFGI_LB
```

The thick chain on the left (`selfHaltPred → … → EncodedCFGI_LB`) is
the spine through which `by reduce_diag` propagates undecidability.
The `mpcpToPcp α` polymorphic edge and the non-`List Bool` middle
nodes (`MPCP_LB`, `EncodedPCP`, `EncodedCFGIntersection`,
`HaltTMCode`, `HaltTM`) are registered but currently only used by the
classical `Undecidable` mode of the tactic.

## Anchor nodes

### Halting problem — [`Halt/Undecidable.lean`](Halt/Undecidable.lean)

```lean
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```

No `SingleTapeTM Bool` decides the self-halt problem
`K = { c : TMCode | c.toTM halts on encodeTMCode c }`. Proved via a
compositional diagonal: build `diagTM D` by inlining the
"simulate-then-invert" pattern as a single TM, apply
`Halt.CodeOf.halts_codeOf_iff` plus deterministic confluence on
`ReflTransGen` to derive a contradiction. See
[`Halt/ROADMAP.md`](Halt/ROADMAP.md) for the detailed construction.

### TM-level bridge — [`Reduction/HaltUndecidable.lean`](Reduction/HaltUndecidable.lean)

```lean
theorem selfHaltPred_TMUndecidable : TMUndecidable selfHaltPred
```

Lifts `halt_undecidable` to the framework's `TMUndecidable`: any
total TM-decider for `selfHaltPred` (the `List Bool → Prop` form of
the self-halt question) would in particular be an `IsSelfHaltDecider`,
contradicting `halt_undecidable`. Tagged `@[tm_undecidable_anchor]`
via `EncodedSelfHalt_TMUndecidable`.

A second `@[tm_undecidable_anchor]` at `CanonicalSelfHalt.predicate`
(`Halt/Rice/Theorem.lean`) supplies the canonical form `Halts c.toTM
(encodeTMCode c)` needed for the Rice reduction.

## Edges in the graph

### MPCP ≤_m PCP — [`PCP/Reduction.lean`](PCP/Reduction.lean)

Full `mpcp_iff_pcp` via the Hopcroft–Ullman symbol-padding
construction (alphabet extension, `hashL`/`hashR` interleaving, three
tile classes `tileStart`/`tileReg`/`tileEnd`, `match_start`, both
directions).

### Halt ≤_m MPCP — [`PCP/Reductions/HaltToMPCP.lean`](PCP/Reductions/HaltToMPCP.lean)

The bulk of the project (~4100 LoC). Both directions of the canonical
iff `Halts tm w ↔ MHasSolution (startTile tm w) (haltTiles tm)` under
the HUM side conditions `NoBlankWrites` and `NoLeftBoundary`.

### Halt ≤_m PCP — [`PCP/Reductions/HaltToPCP.lean`](PCP/Reductions/HaltToPCP.lean)

Composition of the two iffs.

### PCP ≤_m CFG-Intersection-Nonempty — [`CFG/PcpReduction.lean`](CFG/PcpReduction.lean)

```lean
theorem hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔ ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

For each tile `t ∈ P`, two production rules over alphabet `α ⊕ Tile α`.
A derivation traces a tile sequence; the reverse order of markers
forces both grammars to commit to the same sequence; the `.inl`/`.inr`
alphabet split lets us recover the PCP witness uniquely.

### HUM-normalising wrapper — [`Halt/Normalise.lean`](Halt/Normalise.lean)

Postulated `NormalisingWrapper`: a function `(c, w) ↦ (c', w')`
together with proofs of `NoBlankWrites c'.toTM`, `NoLeftBoundary
c'.toTM w'`, and `Halts c.toTM w ↔ Halts c'.toTM w'`. Used in
[`Reduction/EncodedHaltNormalised.lean`](Reduction/EncodedHaltNormalised.lean)
to build the real edge `EncodedHalt ≤ₘ EncodedHaltMPCP`. The standard
construction is a 2-bit alphabet shift with reserved bit-pairs for a
left-edge marker and a synthetic blank symbol.

### Rice extender — [`Halt/Rice/Extender.lean`](Halt/Rice/Extender.lean)

`riceConstTM c : SingleTapeTM Bool` — the four-phase TM (erase → write
`encodeTMCode c` → move back → simulate `c.toTM`). The behaviour
theorem `SemHalt (riceConstTM c) = univ ↔ Halts c.toTM (encodeTMCode c)`
(and the `= ∅` contrapositive) is postulated in
[`Halt/Rice/Theorem.lean`](Halt/Rice/Theorem.lean) as
`semHalt_riceConstTM_dichotomy`. Used in
`canonicalSelfHalt_to_haltsOnEverything` to close
`TMUndecidable HaltsOnEverything.predicate`.

### Encoded variants — `Reduction/Encoded*.lean`, `Reduction/StackEncoding.lean`

`List Bool`-input wrappers around every problem in the chain, with
encoder/decoder infrastructure for `Tile (List Bool)`,
`Stack (List Bool)`, and `Tile × Stack`. Round-trip lemmas at every
layer. These provide the stable graph-node identities the tactic
needs.

## Tactic infrastructure

| Component | File | LoC | Status |
|---|---|---|---|
| `@[reduction_graph]` attribute + env extension | `Reduction/Graph.lean` | ~120 | ✅ |
| Anchor extensions (`@[undecidable_anchor]`, `@[tm_undecidable_anchor]`) | `Reduction/Graph.lean` | included | ✅ |
| Backward DFS search (with cycle detection, polymorphic instantiation) | `Reduction/Search.lean` | ~110 | ✅ |
| Term emission (compose path, dispatch on goal form) | `Reduction/Tactic.lean` | ~160 | ✅ |

The `by reduce_diag` tactic dispatches on the goal:

* `Undecidable P` (or its unfold `Decidable P → False`) — composes via
  `ManyOneReduction.trans` and applies `Undecidable.of_manyOne`.
* `TMUndecidable (Problem.predicate P)` — composes the
  `ManyOneReduction` chain *and* the per-edge `<name>_TMComputable`
  witnesses, then applies the axiomatic `TMUndecidable.of_TMReduction`.

## Encoding infrastructure

`Halt/` provides the encoding pipeline used by the halting-problem
diagonal:

* **`Halt.TMCode`** — normalised TM record (alphabet `Bool`, state set
  `Fin (n + 1)`) with `TMCode.toTM : TMCode → SingleTapeTM Bool`.
* **`Halt.Encoding`** — self-delimiting bit encoding
  `encodeTMCode : TMCode → List Bool` with round-trip lemmas at every
  layer.
* **`Halt.CodeOf`** — generic state-renaming
  `codeOf : SingleTapeTM Bool → TMCode` with the bisimulation theorem
  `halts_codeOf_iff : Halts (codeOf tm).toTM w ↔ PCP.Halts tm w`.
* **`Halt.Diagonal`** isolates the purely-logical kernel — Cantor's
  theorem and the abstract self-referential contradiction —
  independently of any computation model.
* **`Halt.Pair`** — pair encoding `encodePair u v` for the
  `(codeBits, input)` form used by `EncodedHalt`.

## Postulates (what still needs to be discharged)

DiagonaLean is **complete as a framework**, but several TM-level
constructions are postulated rather than fully formalised. They fall
into two categories:

**Substantive mathematical content** (each ~1000+ LoC to formalise):

* `normalisingWrapper` — the HUM-normalising TM wrapper (2-bit
  alphabet shift). Standard textbook construction.
* `semHalt_riceConstTM_dichotomy` — the four-phase Rice extender
  bisimulation.

**Per-edge `TMComputable` witnesses** (6 currently): each asserts a
specific concrete reduction function is TM-computable. True, but
requires building the explicit TM for that function.

The **TM-composition machinery** was previously postulated; it is now
**proved**. `TMComputable f` is defined as `Nonempty (TimeComputable f)`
on cslib's `SingleTapeTM.TimeComputable`. cslib ships `TimeComputable.id`
and `TimeComputable.comp` (the latter needing a monotone time bound,
supplied by `monotoniseTC`), so:

* `TMComputable.id` — proved from `TimeComputable.id`.
* `TMComputable.comp` — proved from `TimeComputable.comp` + `monotoniseTC`.
* `TMUndecidable.of_TMReduction` — proved: `boolIndicator (pred₂ ∘ f) =
  boolIndicator pred₁`, then `TMComputable.comp`.

## Build invariant

Every commit keeps `lake build` clean with **no `sorry`** and no
warnings.
