# DiagonaLean

**A Compositional Lean 4 Framework for Turing Reductions, Diagonalisation, and Undecidability Proofs.**

DiagonaLean is a foundational research project to develop the first
fully compositional, tactic-driven toolkit for mechanising
computability-theoretic reasoning in Lean 4. It will deliver a reusable
library of certified Turing and many-one reductions, diagonalisation
arguments, and undecidability transfer theorems, together with a
proof-search tactic that traverses a registered reduction graph. The
long-term aim is to make formal undecidability proofs as modular and
reusable as algebraic or topological reasoning libraries.

For a prioritised work plan, see [`TODO.md`](TODO.md).
For implementation details of the proofs landed so far, see
[`ROADMAP.md`](ROADMAP.md).

## Phased work plan

* **Phase 1 — Core Framework** (Months 1–6). Formal definitions of
  `Problem`, `ManyOneReduction`, `TuringReduction`. Composition laws,
  undecidability transfer theorems, public notation layer.
* **Phase 2 — Canonical Base Problems** (Months 4–10). Self-contained
  undecidability proofs for the Halting Problem, TM acceptance (ATM),
  the Post Correspondence Problem, and selected language-theoretic
  problems (CFG universality, CFG intersection-emptiness). Each is
  registered in the reduction graph via `@[reduction_graph]`.
* **Phase 3 — Standard Reduction Library** (Months 8–18). Mechanisation
  of the undecidability results in Hopcroft–Motwani–Ullman, plus
  selected results from Rogers and Soare. The target is a comprehensive,
  textbook-aligned reduction graph in which every node is a certified
  formal object and every edge is a machine-checked reduction.

## Current state

Substantial **Phase 2** content is in place, ahead of the **Phase 1**
abstraction layer. The reductions exist as concrete `Iff` theorems
that will be wrapped into `ManyOneReduction` instances once the
framework lands.

| Phase 2 deliverable | Status |
|---|---|
| Halting problem (`halt_undecidable` for cslib `SingleTapeTM Bool`) | ✅ complete |
| `Halt ≤_m MPCP ≤_m PCP` (`halts_iff_pcp` under HUM side conditions) | ✅ complete |
| `PCP ≤_m CFG-Intersection-Nonempty` | ✅ complete |
| TM acceptance (ATM) | 🚧 not yet (only `Halts` so far) |
| CFG universality | 🚧 not yet |
| Rice's theorem | 🚧 scaffolding + extender constructed; bisim + theorem pending |

| Phase 1 deliverable | Status |
|---|---|
| `Problem`, `ManyOneReduction` | ✅ in [`Reduction/Basic.lean`](Reduction/Basic.lean) |
| Composition laws (`.id`, `.trans`, identity / assoc) | ✅ in [`Reduction/Composition.lean`](Reduction/Composition.lean) |
| Transfer theorems (`Decidable.of_manyOne`, contrapositive) | ✅ in [`Reduction/Transfer.lean`](Reduction/Transfer.lean) |
| Notation `≤ₘ`, `≡ₘ` | ✅ in [`Reduction/Notation.lean`](Reduction/Notation.lean) |
| `TuringReduction` (oracle-machine notion) | 🚧 not yet |
| TM-computable reduction layer | 🚧 not yet |
| `@[reduction_graph]` attribute | 🚧 not yet |
| Proof-search tactic | 🚧 not yet |

The proof contains **no `sorry`** anywhere and is verified against
`leanprover/lean4:v4.29.0-rc4`. `lake build` is clean (2211 jobs, no
warnings).

## Headline theorems

```lean
theorem Halt.halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D

theorem PCP.halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm))

theorem CFG.hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔
    ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

## Repository layout

```
PCP/                   ← Halt ≤_m MPCP ≤_m PCP chain
  Basic.lean           -- core types: Word, Tile, Stack; HasSolution
  MPCP.lean            -- the MPCP variant: MHasSolution
  Reduction.lean       -- MPCP ≤_m PCP: full mpcp_iff_pcp
  Halt.lean            -- the Halts predicate for SingleTapeTM
  Reductions/
    HaltToMPCP.lean    -- Halt ≤_m MPCP construction + proofs
    HaltToPCP.lean     -- halts_iff_pcp by composition

CFG/                   ← PCP ≤_m CFG-Intersection-Nonempty
  Basic.lean           -- IntersectionEmpty / IntersectionNonempty
  PcpReduction.lean    -- the full reduction iff

Halt/                  ← halting-problem undecidability
  Diagonal.lean        -- Cantor + abstract halting contradiction
  Basic.lean           -- decider predicates: HaltDecidable,
                          IsHaltDecider, IsSelfHaltDecider
  TMCode.lean          -- normalised TM rep (Bool, Fin (n+1) states)
  Encoding.lean        -- Gödel numbering: encodeTMCode
  Pair.lean            -- pair encoding: encodePair
  Helpers.lean         -- worked example: invertTM
  CodeOf.lean          -- generic SingleTapeTM Bool → TMCode embedding
  Undecidable.lean     -- the final halt_undecidable theorem
  Rice/                -- Rice's theorem (in progress)
    Basic.lean         -- SemHalt, IsSemantic, IsPropDecider
    TrivialTMs.lean    -- tm_alwaysHalt + tm_loop
    Extender.lean      -- riceConstTM construction

Reduction/             ← Phase 1 framework (DiagonaLean abstractions)
  Basic.lean           -- Problem, ManyOneReduction, Decidable, Undecidable
  Composition.lean     -- .id, .trans, identity / associativity
  Transfer.lean        -- Decidable.of_manyOne, Undecidable.of_manyOne
  Notation.lean        -- ≤ₘ, ≡ₘ
  Instances.lean       -- ManyOneReduction wrappers around existing iffs

PCP.lean / CFG.lean / Halt.lean / Reduction.lean  -- library roots
Main.lean                         -- executable entry point
TODO.md                           -- prioritised work plan
ROADMAP.md                        -- proof-chain architecture
```

## Conventions

The `Halt ≤_m MPCP` reduction follows the Hopcroft–Ullman–Motwani
one-sided-tape design: the simulation tile set does not include a
`leftMoveBoundaryTile`, and the TM is required to satisfy
`NoLeftBoundary` (no left-move at the left tape boundary) in addition
to the standard `NoBlankWrites` (no blank symbol written).

The development uses [`cslib`](https://github.com/leanprover/cslib)'s
`Turing.SingleTapeTM` for the Turing-machine machinery and follows
cslib's conventions (module-style headers, `public import`,
`@[expose] public section`). The CFG module uses Mathlib's
`ContextFreeGrammar`.

## Building

```sh
lake build
```

builds the three current libraries (`PCP`, `CFG`, `Halt`) and the
`pcp` executable. Cold-cache build (including Mathlib) takes ~20–40
minutes; incremental builds are seconds.

## License

Apache 2.0.
