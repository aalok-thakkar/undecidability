# DiagonaLean

**A Compositional Lean 4 Framework for Turing Reductions, Diagonalisation, and Undecidability Proofs.**

DiagonaLean is a foundational research project to develop the first
fully compositional, tactic-driven toolkit for mechanising
computability-theoretic reasoning in Lean 4. It delivers a reusable
library of certified Turing and many-one reductions, diagonalisation
arguments, and undecidability transfer theorems, together with a
proof-search tactic `by reduce_diag` that traverses a registered
reduction graph.

For a prioritised work plan, see [`TODO.md`](TODO.md).
For implementation details of the proofs landed so far, see
[`ROADMAP.md`](ROADMAP.md).

## Headline result

```lean
@[tm_undecidable_anchor]
theorem CanonicalSelfHalt_TMUndecidable :
    TMUndecidable CanonicalSelfHalt.predicate := …

example : TMUndecidable HaltsOnEverything.predicate := by reduce_diag
example : TMUndecidable EncodedCFGI_LB.predicate    := by reduce_diag
```

The tactic searches the registered graph for a chain of reductions
from the anchor (a real theorem derived from cslib's `halt_undecidable`)
to the goal, composes them, and applies the TM-level undecidability
transfer. Every example in [`Reduction/Smoke.lean`](Reduction/Smoke.lean)
closes this way.

## Phased work plan

* **Phase 1 — Core Framework**. Formal definitions of `Problem`,
  `ManyOneReduction`, `Decidable`, `Undecidable`. Composition laws,
  classical and TM-level undecidability-transfer theorems, public
  notation layer, `@[reduction_graph]` attribute, `by reduce_diag`
  proof-search tactic.
* **Phase 2 — Canonical Base Problems**. Self-contained
  undecidability proofs for the Halting Problem and the PCP / CFG /
  Rice chain, all wired into the reduction graph as `List Bool`-input
  encoded variants.
* **Phase 3 — Standard Reduction Library**. Mechanisation of the
  undecidability results in Hopcroft–Motwani–Ullman, plus selected
  results from Rogers and Soare. The target is a comprehensive,
  textbook-aligned reduction graph in which every node is a certified
  formal object and every edge is a machine-checked reduction.

## Current state

**Phases 1 and 2 are functionally landed.** The reduction graph has
13 registered edges; the smoke test closes 13 examples via
`by reduce_diag` (4 classical `Undecidable` + 9 TM-level
`TMUndecidable`). The full TM-undecidability chain is grounded at
`halt_undecidable` with no problem-specific postulates:

```
selfHaltPred_TMUndecidable           (real, from halt_undecidable)
  → EncodedSelfHalt                  (encoded predicate)
  → EncodedHalt                      (duplication reduction)
  → EncodedHaltMPCP                  (HUM normalising wrapper)
  → EncodedMPCP_LB                   (List Bool encoding)
  → EncodedPCP_LB                    (MPCP→PCP via flattenStack)
  → EncodedCFGI_LB                   (PCP→CFG-intersection identity)

CanonicalSelfHalt → HaltsOnEverything   (Rice extender)
```

### Phase 1 — Framework

| Deliverable | Status |
|---|---|
| `Problem`, `ManyOneReduction`, classical `Decidable`/`Undecidable` | ✅ [`Reduction/Basic.lean`](Reduction/Basic.lean) |
| Composition laws (`.id`, `.trans`, identity / assoc) | ✅ [`Reduction/Composition.lean`](Reduction/Composition.lean) |
| Transfer theorems (`Decidable.of_manyOne`, contrapositive) | ✅ [`Reduction/Transfer.lean`](Reduction/Transfer.lean) |
| Notation `≤ₘ`, `≡ₘ` | ✅ [`Reduction/Notation.lean`](Reduction/Notation.lean) |
| `@[reduction_graph]` attribute + env extension | ✅ [`Reduction/Graph.lean`](Reduction/Graph.lean) |
| Backward DFS search with cycle detection | ✅ [`Reduction/Search.lean`](Reduction/Search.lean) |
| `by reduce_diag` tactic (term emission) | ✅ [`Reduction/Tactic.lean`](Reduction/Tactic.lean) |
| TM-level `TMDecidable`/`TMUndecidable`/`TMComputable` (on cslib `TimeComputable`) | ✅ [`Reduction/TMDecidable.lean`](Reduction/TMDecidable.lean) |
| `TMComputable.id`/`.comp`, `TMUndecidable.of_TMReduction` (proved, not postulated) | ✅ [`Reduction/TMDecidable.lean`](Reduction/TMDecidable.lean) |
| TM-mode dispatch + `@[tm_undecidable_anchor]` | ✅ in `Graph.lean` + `Tactic.lean` |
| `TuringReduction` (oracle-machine notion) | 🚧 not yet (Phase 3 prerequisite) |

### Phase 2 — Canonical problems

| Deliverable | Status |
|---|---|
| Halting problem (`halt_undecidable` for cslib `SingleTapeTM Bool`) | ✅ [`Halt/Undecidable.lean`](Halt/Undecidable.lean) |
| `Halt ≤_m MPCP ≤_m PCP` (`halts_iff_pcp` under HUM side conditions) | ✅ [`PCP/Reductions/HaltToMPCP.lean`](PCP/Reductions/HaltToMPCP.lean), [`PCP/Reductions/HaltToPCP.lean`](PCP/Reductions/HaltToPCP.lean) |
| `PCP ≤_m CFG-Intersection-Nonempty` | ✅ [`CFG/PcpReduction.lean`](CFG/PcpReduction.lean) |
| `List Bool`-input encoded variants of all problems | ✅ `Reduction/Encoded*.lean` |
| TM-level bridge `halt_undecidable → TMUndecidable selfHaltPred` | ✅ [`Reduction/HaltUndecidable.lean`](Reduction/HaltUndecidable.lean) |
| HUM normalisation reduction `EncodedHalt → EncodedHaltMPCP` | ✅ [`Reduction/EncodedHaltNormalised.lean`](Reduction/EncodedHaltNormalised.lean) (with postulated `normalisingWrapper`) |
| Rice's theorem (restricted form, `HaltsOnEverything`) | ✅ [`Halt/Rice/Theorem.lean`](Halt/Rice/Theorem.lean) (with postulated bisimulation) |
| TM acceptance (ATM) | 🚧 not yet |
| CFG universality / equivalence / ambiguity | 🚧 not yet |
| Rice's theorem (general non-trivial semantic) | 🚧 not yet (only restricted form for now) |

The proof contains **no `sorry`** anywhere and is verified against
`leanprover/lean4:v4.29.0-rc4`. `lake build` is clean.

## Postulates

DiagonaLean follows the discipline of clearly cataloguing which
statements are postulated (because formal Lean proof is currently
prohibitively expensive in cslib's TM model) versus proved. The
postulates are stratified by content:

| Postulate | Type | Location |
|---|---|---|
| `normalisingWrapper` | **HUM construction**: 2-bit alphabet shift with sentinel marker + synthetic blank | [`Halt/Normalise.lean`](Halt/Normalise.lean) |
| `semHalt_riceConstTM_dichotomy` | **Rice extender bisimulation**: four-phase erase/write/move-back/simulate | [`Halt/Rice/Theorem.lean`](Halt/Rice/Theorem.lean) |
| Per-edge `<edgeName>_TMComputable` (6 total) | **"This Lean function is TM-computable"** for each reduction's `f` | scattered |

The **TM-composition machinery** is no longer postulated. `TMComputable`
is now defined as `Nonempty (TimeComputable f)` on top of cslib's
`SingleTapeTM.TimeComputable`, so `TMComputable.id`, `TMComputable.comp`,
and `TMUndecidable.of_TMReduction` are **proved theorems** (see
[`Reduction/TMDecidable.lean`](Reduction/TMDecidable.lean)).

Discharging the remaining postulates is the main work of completing the
project. See [`TODO.md`](TODO.md) for the prioritised plan.

## Repository layout

```
PCP/                   ← Halt ≤_m MPCP ≤_m PCP chain
  Basic.lean, MPCP.lean, Reduction.lean, Halt.lean
  Reductions/HaltToMPCP.lean (4100 LoC, the main reduction)
  Reductions/HaltToPCP.lean  (composition)

CFG/                   ← PCP ≤_m CFG-Intersection-Nonempty
  Basic.lean, PcpReduction.lean

Halt/                  ← halting-problem undecidability
  Diagonal.lean, Basic.lean, TMCode.lean, Encoding.lean,
  Pair.lean, Helpers.lean, CodeOf.lean, Undecidable.lean
  Normalise.lean        ← postulated HUM-normalising wrapper
  Rice/
    Basic.lean, TrivialTMs.lean, Extender.lean,
    Theorem.lean        ← restricted Rice + HaltsOnEverything

Reduction/             ← Phase 1 framework + DiagonaLean abstractions
  Basic.lean, Composition.lean, Transfer.lean, Notation.lean
  Graph.lean            ← @[reduction_graph], @[undecidable_anchor],
                           @[tm_undecidable_anchor]
  Search.lean           ← backward DFS path search
  Tactic.lean           ← `by reduce_diag`
  TMDecidable.lean      ← TM-level undecidability primitives
  Instances.lean, Encoded.lean
  HaltUndecidable.lean  ← halt_undecidable → TMUndecidable bridge
  EncodedHaltNormalised.lean  ← HUM reduction
  StackMap.lean, EncodedPCP.lean, EncodedHaltMPCP.lean, EncodedCFG.lean
  StackEncoding.lean, EncodedLB.lean  ← List Bool-input variants
  Smoke.lean            ← #evals graph + tests `by reduce_diag`

PCP.lean / CFG.lean / Halt.lean / Reduction.lean  ← library roots
Main.lean                ← executable entry point
TODO.md                  ← prioritised work plan
ROADMAP.md               ← proof-chain architecture
```

## Conventions

The development uses [`cslib`](https://github.com/leanprover/cslib)'s
`Turing.SingleTapeTM` for the Turing-machine machinery and follows
cslib's conventions (module-style headers, `public import`,
`@[expose] public section` for code, `public meta section` for
metaprogramming). The CFG module uses Mathlib's `ContextFreeGrammar`.

The `Halt ≤_m MPCP` reduction follows the Hopcroft–Ullman–Motwani
one-sided-tape design: the simulation tile set does not include a
`leftMoveBoundaryTile`, and the TM is required to satisfy
`NoLeftBoundary` (no left-move at the left tape boundary) in addition
to `NoBlankWrites` (no blank symbol written). The HUM-normalising
wrapper in `Halt.Normalise` lifts these side conditions for the
end-to-end chain.

## Building

```sh
lake build
```

builds the four current libraries (`PCP`, `CFG`, `Halt`, `Reduction`)
and the `pcp` executable. Cold-cache build (including Mathlib) takes
~20–40 minutes; incremental builds are seconds.

To run the smoke test:

```sh
lake build Reduction.Smoke
```

This `#eval`s the registered graph and exercises `by reduce_diag` on
13 examples across the chain.

## License

Apache 2.0.
