# Undecidability

A Lean 4 formalisation that the Post Correspondence Problem (PCP) is
undecidable, via the standard reduction chain

```
Lu ≤_m MPCP ≤_m PCP
```

- **Lu (Universal Language / Halting Problem)**: undecidability is assumed.
- **MPCP**: encodes a Turing-machine computation trace as a forced-start
  string-matching problem.
- **PCP**: the Hopcroft–Ullman symbol-padding technique reduces forced-start
  MPCP to general PCP.

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
PCP.lean                     -- Library root.
Main.lean                    -- Executable entry point.
ROADMAP.md                   -- Detailed proof plan and next steps.
```

## Status

| Component                                              | Status         |
|--------------------------------------------------------|----------------|
| Core PCP / MPCP API                                    | ✅ complete    |
| `MPCP ≤_m PCP` (full `mpcp_iff_pcp`)                   | ✅ complete    |
| `Halts` predicate for `SingleTapeTM`                   | ✅ complete    |
| `Lu ≤_m MPCP`: tile-set infrastructure                 | ✅ complete    |
| `Lu ≤_m MPCP`: forward direction (`Halts → MHasSolution`) | ✅ complete |
| `Lu ≤_m MPCP`: backward direction (`MHasSolution → Halts`) | 🚧 ~80% (see below) |
| Final theorem `lu_le_mpcp`                             | 🚧 not yet    |

## What is proved

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`

The full `mpcp_iff_pcp` equivalence via the Hopcroft–Ullman construction:
extend the alphabet with `⋕`-prefixed hash symbols, interleave the tile
top/bot words, produce a `tileStart`/`tileReg`/`tileEnd` triple, and prove
`match_start` (any solution must begin with the start tile) plus the
complete forward and backward directions.

### `Lu ≤_m MPCP` (forward) — `PCP/Reductions/LuToMPCP.lean`

Given `Halts tm w` (with the `NoBlankWrites` side condition), constructs
a tile sequence `A ⊆ startTile :: luTiles tm` satisfying the MPCP matching
equation. The proof:

1. Prepends `stepTiles tm q tape` for each TM step, dispatching over
   transition direction × tape-boundary status:

   | Case              | Tiles used                                         |
   |-------------------|----------------------------------------------------|
   | No move           | `left-copies · noMoveTile · right-copies · sep`    |
   | Right (interior)  | `left-copies · rightMoveTile · right-copies · sep` |
   | Right (boundary)  | `left-copies · rightMoveBoundaryTile`              |
   | Left (interior)   | `tail-copies · leftMoveTile · right-copies · sep`  |
   | Left (boundary)   | `leftMoveBoundaryTile · right-copies · sep`        |

2. Closes with `absorbAndFinish` once the TM halts: iteratively absorbs
   tape symbols via `absorbLeftTile`/`absorbRightTile`, then applies
   `finalTile` to equalise top and bot.

Top-level lemma: `halts_implies_mhasSolution`.

### `Lu ≤_m MPCP` (backward) — partial

The backward direction inverts the forward construction. Strategy:
strong induction on `A.length`, peeling one canonical "block" off the
front of `A` per TM step. Pieces in place:

| Lemma                                  | Role                                             | Status |
|----------------------------------------|--------------------------------------------------|--------|
| `mem_luTiles_top`                      | Identify each tile in `luTiles` by its constructor | ✅ |
| `copy_prefix_forced`                   | Force `copyTile`s on a `liftTape`-prefix         | ✅ |
| `transition_forced`                    | Force the transition tile after a state marker   | ✅ |
| `copy_prefix_forced_state_lead`        | Strip copies up to a state marker (non-left)     | ✅ |
| `sep_forced`                           | Force `sepTile` when the lead is `#`             | ✅ |
| `no_tile_for_state_sharp`              | Rule out `↟ₛq :: # :: …` lookaheads             | ✅ |
| `starts_with_stepTilesNoMove`          | Backward step, no-move                           | ✅ |
| `starts_with_stepTilesRightInterior`   | Backward step, right-move, `t.right ≠ []`        | ✅ |
| `starts_with_stepTilesRightBoundary`   | Backward step, right-move, `t.right = []`, `qNew = some _` | ✅ |
| `starts_with_stepTilesLeftInterior`    | Backward step, left-move, `t.left ≠ []`          | ✅ |
| `starts_with_absorbAndFinish`          | Backward extraction for halted cfg               | 🚧 |
| `backward_aux`                         | Main strong-induction driver                     | 🚧 |
| `mhasSolution_implies_halts`           | Top-level backward theorem                       | 🚧 |

The left-boundary case is *removed* by the HUM refactor (the
`NoLeftBoundary` constraint ensures no reachable cfg ever invokes a
left-move at the left boundary, so no corresponding sub-lemma is
needed).

## What remains

1. **`starts_with_absorbAndFinish`** — for a halted cfg `⟨none, tape⟩`,
   force `A` to start with `absorbAndFinish tape.left.toList
   (tape.head :: tape.right.toList)`. Same flavour as the step lemmas:
   force copies up to the `h⊥` marker, then peel absorption iterations.

2. **`backward_aux`** — strong induction on `A.length`. Three cases:
   * `A = []` → contradiction (the matching invariant requires a non-empty
     lookahead).
   * `cfg = ⟨none, _⟩` → apply `starts_with_absorbAndFinish`; the
     resulting `A'` is shorter, conclude with `ReflTransGen.refl`.
   * `cfg = ⟨some q, tape⟩` → dispatch on `tm.tr q tape.head`:
     - If the result is `qNew = none` (halt-now), produce the single TM
       step `cfg → ⟨none, …⟩` directly and conclude.
     - Otherwise apply the appropriate `starts_with_stepTiles*` lemma
       (which requires `qNew = some _`), get a shorter `A'`, recurse,
       chain the TM step.

3. **Final theorem**:
   ```lean
   theorem lu_le_mpcp (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
       (w : List Symbol) :
       Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
   ```
   Forward direction: `halts_implies_mhasSolution` (done). Backward
   direction: unpack `MHasSolution`, cancel the leading `[#]` from the
   matching equation, call `backward_aux` with `cfg = initCfg tm w`.

See `ROADMAP.md` for the full plan including auxiliary lemmas and the
estimated line counts for the remaining pieces.
