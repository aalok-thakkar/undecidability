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
`@[expose] public section`).

## Project layout

```
PCP/
  Basic.lean                 -- Core types: Word, Tile, Stack;
                                concatenations (tau1, tau2) and the
                                `HasSolution` predicate.
  MPCP.lean                  -- The MPCP variant `MHasSolution`.
  Reduction.lean             -- MPCP ≤_m PCP. Alphabet extension,
                                interleaving, tile classes, the
                                reduction `mpcpToPcp`, and the
                                complete proof of `mpcp_iff_pcp`.
  Lu.lean                    -- The halting predicate `Halts` for
                                cslib's `Turing.SingleTapeTM`, with
                                the equivalence to `HaltsWithinTime`.
  Reductions/
    LuToMPCP.lean            -- Lu ≤_m MPCP construction and proofs.
PCP.lean                     -- Library root.
Main.lean                    -- Executable entry point.
ROADMAP.md                   -- Detailed proof plan and next steps.
```

## Status

| Step                          | Status       |
|-------------------------------|--------------|
| Core PCP API                  | ✅ complete  |
| MPCP API                      | ✅ complete  |
| `MPCP ≤_m PCP`                | ✅ complete  |
| `Halts` predicate             | ✅ complete  |
| `Lu ≤_m MPCP` infrastructure  | ✅ complete  |
| Lu→MPCP: no-move step         | ✅ complete  |
| Lu→MPCP: right-move step      | ✅ complete  |
| Lu→MPCP: left-move step       | ✅ complete  |
| Lu→MPCP: halt absorption      | ✅ complete  |
| Lu→MPCP: forward direction    | ✅ complete  |
| Lu→MPCP: `mem_luTiles_top`    | ✅ complete  |
| Lu→MPCP: `copy_prefix_forced` | ✅ complete  |
| Lu→MPCP: `transition_forced`  | ✅ complete  |
| Lu→MPCP: backward step (no-move) | ✅ complete  |
| Lu→MPCP: backward step (right interior) | ✅ complete  |
| Lu→MPCP: backward step (left boundary)  | ✅ complete  |
| Lu→MPCP: backward direction   | 🚧 in progress |

The development contains **no `sorry`**. Verified against
`leanprover/lean4:v4.29.0-rc4` + cslib (see `lake-manifest.json`).

## What is proved

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`

The full `mpcp_iff_pcp` equivalence via the Hopcroft–Ullman construction:
extend the alphabet with `⋕`-prefixed hash symbols, interleave the tile
top/bot words, produce a `tileStart`/`tileReg`/`tileEnd` triple and prove
`match_start` (any solution must begin with the start tile) plus the
complete forward and backward directions.

### `Lu ≤_m MPCP` (forward) — `PCP/Reductions/LuToMPCP.lean`

Given `Halts tm w` (with the `NoBlankWrites` side condition), constructs
a tile sequence `A ⊆ startTile :: luTiles tm` satisfying the MPCP matching
equation. The proof inductively builds `A` by:

1. Prepending `stepTiles tm q tape` for each TM step, using one of four
   tile-group constructors depending on the transition direction and whether
   the head is at a tape boundary:

   | Case              | Tiles used                                         |
   |-------------------|----------------------------------------------------|
   | No move           | `left-copies · noMoveTile · right-copies · sep`    |
   | Right (interior)  | `left-copies · rightMoveTile · right-copies · sep` |
   | Right (boundary)  | `left-copies · rightMoveBoundaryTile · sep`        |
   | Left (interior)   | `tail-copies · leftMoveTile · right-copies · sep`  |
   | Left (boundary)   | `leftMoveBoundaryTile · right-copies · sep`        |

2. Closing with `absorbAndFinish` once the TM halts: iteratively absorbs
   tape symbols via `absorbLeftTile`/`absorbRightTile`, then applies
   `finalTile` to equalise top and bot.

Key lemmas: `tau1_stepTiles`, `tau2_stepTiles`, `stepTiles_subset_luTiles`,
`absorbAndFinish_matching`, `absorbAndFinish_subset_luTiles`,
`halts_implies_mhasSolution`.

## What remains

### `Lu ≤_m MPCP` (backward) — `MHasSolution → Halts`

Given any tile sequence `A` from `luTiles` satisfying
`tau1 A = encodeCfg(initCfg) ++ [#] ++ tau2 A`,
show that `tm` halts on `w`. See `ROADMAP.md` for the detailed proof plan.

The top-level goal is:
```lean
theorem lu_le_mpcp (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (w : List Symbol) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```
