# Undecidability

A Lean 4 formalisation of the standard reduction chain

```
Lu ≤_m MPCP ≤_m PCP
```

connecting the Halting Problem to the Post Correspondence Problem (PCP).
The top-level theorem (`halts_iff_pcp` in `PCP/Reductions/LuToPCP.lean`)
shows that

  `Halts tm w ↔ HasSolution (mpcpToPcp (startTile tm w) (luTiles tm))`

for any single-tape Turing machine `tm` and input `w` satisfying the
Hopcroft–Ullman–Motwani side conditions `NoBlankWrites` and
`NoLeftBoundary`.

## What this repository does *not* prove

To conclude "PCP is undecidable" from `halts_iff_pcp`, two more pieces
are required, neither of which is in this repository:

1. A proof that `Halts` for cslib's `Turing.SingleTapeTM` is undecidable.
   Mathlib *does* prove the Halting Problem
   ([`Mathlib.Computability.Halting.halting_problem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Halting.html)),
   but for `Nat.Partrec.Code` (partial recursive function codes) rather
   than `Turing.SingleTapeTM`. Bridging the two — showing that cslib's
   `SingleTapeTM` can simulate `Nat.Partrec.Code` (or vice versa) — is a
   substantial development of its own and is left for future work.
2. **HUM normalisation** — a construction lifting the side conditions
   `NoBlankWrites` and `NoLeftBoundary` to an arbitrary TM (the standard
   sentinel-shift construction).

What we prove here is the reduction chain itself, which is the
mathematical core of the standard PCP-undecidability argument. See
`ROADMAP.md` for the dependency tree.

## Conventions

The `Lu ≤_m MPCP` reduction follows the **Hopcroft–Ullman–Motwani
one-sided-tape design**: the simulation tile set does not include a
`leftMoveBoundaryTile`, and the TM is required to satisfy
`NoLeftBoundary` (no left-move at the left tape boundary) in addition
to the standard `NoBlankWrites` (no blank symbol written).

The development uses [`cslib`](https://github.com/leanprover/cslib)'s
`Turing.SingleTapeTM` for the Turing-machine machinery and follows
cslib's conventions (module-style headers, `public import`,
`@[expose] public section`). The proof contains **no `sorry`** and is
verified against `leanprover/lean4:v4.29.0-rc4` (see `lake-manifest.json`).

## Project layout

```
PCP/
  Basic.lean                 -- Core types: Word, Tile, Stack; concatenations
                                tau1, tau2; the `HasSolution` predicate.
  MPCP.lean                  -- The MPCP variant `MHasSolution`.
  Reduction.lean             -- MPCP ≤_m PCP. Alphabet extension, interleaving,
                                tile classes, `mpcpToPcp`, and the complete
                                `mpcp_iff_pcp`.
  Lu.lean                    -- The halting predicate `Halts` for cslib's
                                `Turing.SingleTapeTM`.
  Reductions/
    LuToMPCP.lean            -- Lu ≤_m MPCP construction and proofs.
    LuToPCP.lean             -- `halts_iff_pcp`: composition of
                                Lu ≤_m MPCP with MPCP ≤_m PCP.
PCP.lean                     -- Library root.
Main.lean                    -- Executable entry point.
ROADMAP.md                   -- Detailed proof plan and external deps.
```

## Status

| Component                                                  | Status                |
|------------------------------------------------------------|-----------------------|
| Core PCP / MPCP API                                        | ✅ complete           |
| `MPCP ≤_m PCP` (full `mpcp_iff_pcp`)                       | ✅ complete           |
| `Halts` predicate for `SingleTapeTM`                       | ✅ complete           |
| `Lu ≤_m MPCP`: tile set + HUM refactor (`NoLeftBoundary`)  | ✅ complete           |
| `Lu ≤_m MPCP`: forward direction (`Halts → MHasSolution`)  | ✅ complete           |
| `Lu ≤_m MPCP`: backward direction (`MHasSolution → Halts`) | ✅ complete           |
| Canonical `lu_le_mpcp` (`Halts ↔ MHasSolution`)            | ✅ complete           |
| `halts_iff_pcp` (composition `Halts ↔ HasSolution …`)      | ✅ complete           |
| Halting-problem undecidability for `SingleTapeTM`          | 🚧 Mathlib proves it for `Nat.Partrec.Code`; bridge to cslib's `SingleTapeTM` is future work |
| HUM normalisation (lifting `NoBlankWrites`/`NoLeftBoundary`)| 🚧 future work        |

## What is proved

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`

The full `mpcp_iff_pcp` equivalence via the Hopcroft–Ullman construction:
extend the alphabet with `⋕`-prefixed hash symbols, interleave the tile
top/bot words, produce a `tileStart`/`tileReg`/`tileEnd` triple, and prove
`match_start` (any solution must begin with the start tile) plus the
complete forward and backward directions.

### `Lu ≤_m MPCP` (forward) — `PCP/Reductions/LuToMPCP.lean`

Given `Halts tm w` together with the two side conditions `NoBlankWrites`
and `NoLeftBoundary`, constructs a tile sequence
`A ⊆ startTile :: luTiles tm` satisfying the MPCP matching equation.
The proof:

1. Prepends `stepTiles tm q tape` for each TM step, dispatching over
   transition direction × tape-boundary status:

   | Case              | Tiles used                                         |
   |-------------------|----------------------------------------------------|
   | No move           | `left-copies · noMoveTile · right-copies · sep`    |
   | Right (interior)  | `left-copies · rightMoveTile · right-copies · sep` |
   | Right (boundary)  | `left-copies · rightMoveBoundaryTile`              |
   | Left (interior)   | `tail-copies · leftMoveTile · right-copies · sep`  |

   The **left-boundary case is unreachable** under `NoLeftBoundary`, so
   no corresponding tile group is needed.

2. Closes with `absorbAndFinish` once the TM halts: iteratively absorbs
   tape symbols via `absorbLeftTile`/`absorbRightTile`, then applies
   `finalTile` to equalise top and bot.

Top-level lemma: `halts_implies_mhasSolution`
`(tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm) (w : List Symbol)`
`(h_nlb : NoLeftBoundary tm w) (h : Halts tm w) : MHasSolution …`.

### `Lu ≤_m MPCP` (backward) — canonical iff complete

The backward direction inverts the forward construction in two layers.

**Strong-A form** (`lu_le_mpcp_strong`): handles `A ⊆ luTiles tm` via
strong induction on `A.length`, peeling one canonical "block" off the
front of `A` per TM step.

| Lemma                                  | Role                                             |
|----------------------------------------|--------------------------------------------------|
| `mem_luTiles_top`                      | Identify each tile in `luTiles` by its constructor |
| `copy_prefix_forced`                   | Force `copyTile`s on a `liftTape`-prefix         |
| `transition_forced`                    | Force the transition tile after a state marker   |
| `copy_prefix_forced_state_lead`        | Strip copies up to a state marker (non-left)     |
| `sep_forced`                           | Force `sepTile` when the lead is `#`             |
| `no_tile_for_state_sharp`              | Rule out `↟ₛq :: # :: …` lookaheads             |
| `starts_with_stepTilesNoMove`          | Backward step, no-move                           |
| `starts_with_stepTilesRightInterior`   | Backward step, right-move, `t.right ≠ []`        |
| `starts_with_stepTilesRightBoundary`   | Backward step, right-move, `t.right = []`        |
| `starts_with_stepTilesLeftInterior`    | Backward step, left-move, `t.left ≠ []`          |
| `backward_aux`                         | Main strong-induction driver (strong hypothesis) |
| `lu_le_mpcp_strong`                    | Strong-A top-level theorem                       |

The left-boundary sub-case is *removed* by the HUM refactor: the
`NoLeftBoundary` constraint ensures no reachable cfg ever invokes a
left-move at the left boundary, so no corresponding sub-lemma is needed.
The halt-now sub-case in `backward_aux` is handled directly (single TM
step to a halted cfg, then `ReflTransGen.refl`) — this sidesteps the
need for a `starts_with_absorbAndFinish` lemma, which would otherwise
fail because the absorption-phase decomposition is non-unique.

**Canonical form** (`lu_le_mpcp`): handles `A ⊆ startTile :: luTiles tm`
via `backward_aux_weak`, which threads a chain-tracked cfg queue
`List (Σ' c, ReflTransGen ... initCfg c)`. When `startTile` appears
mid-stream in `A`, it pushes an extra `initCfg` (with a `refl` chain)
onto the queue, alongside the natural `stepResult` advancement. The
right-boundary alternative `rightMoveTile` path is ruled out by
`tau1_no_state_marker_then_sharp`, a structural property showing that
`tau1 A` never contains `↟ₛq :: # :: …` as a sublist (no tile's top has
`↟ₛq` followed by `#`, and no top ends with `↟ₛq`).

### `Lu ≤_m PCP` — `PCP/Reductions/LuToPCP.lean`

```lean
theorem halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (luTiles tm)) :=
  (lu_le_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)
```

The transitive composition of the two reductions: `Halts` and PCP
solvability of the explicit, computably constructed instance
`mpcpToPcp (startTile tm w) (luTiles tm)` are equivalent.

## Next steps

The reduction chain is closed; what remains for a complete PCP-undecidability
proof in Lean 4 is external to this repository:

1. **Halting-problem undecidability for `SingleTapeTM`.** Mathlib already
   proves the Halting Problem for partial recursive function codes
   ([`Mathlib.Computability.Halting.halting_problem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Halting.html):
   `¬ ComputablePred fun c => (eval c n).Dom`).
   What's needed to apply this here is a bridge between cslib's
   `Turing.SingleTapeTM` and `Nat.Partrec.Code` — i.e., a proof that
   `SingleTapeTM` can simulate every partial recursive function (or vice
   versa). Mathlib's `Computability.TMToPartrec` provides such a bridge
   for *its own* TM model; an analogous bridge for cslib's `SingleTapeTM`
   would close the gap.

2. **HUM normalisation.** A construction
   `tm ↦ (tm', w')` producing an equivalent machine satisfying both
   `NoBlankWrites` and `NoLeftBoundary`. The standard sentinel-shift
   technique is straightforward but bulky (~500–1000 LoC); left for a
   future `PCP.Normalize` module.

See `ROADMAP.md` for further details.

## CFG-intersection-emptiness reduction

A companion library [`CFG/`](CFG/) contains the standard Hopcroft–Ullman
reduction

```lean
theorem hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔ ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

connecting PCP to *CFG-intersection-emptiness* — given two context-free
grammars `G₁` and `G₂`, is `L(G₁) ∩ L(G₂) = ∅`? With this reduction, if
PCP is undecidable then CFG-intersection-emptiness is too. The library
uses Mathlib's `ContextFreeGrammar` (cslib has no CFG framework).
