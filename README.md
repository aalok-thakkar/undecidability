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
    LuToMPCP.lean            -- Lu ≤_m MPCP construction:
                                * Alphabet `Alpha`
                                * Configuration encoding
                                  (`encodeRunningCfg`/`encodeHaltedCfg`)
                                * Tile constructors (start, copy,
                                  separator, transitions for
                                  no-move/right/left & boundaries,
                                  halt-absorb left/right, final)
                                * Tile enumeration (`luTiles`)
                                * Reduction `luToMpcp`
                                * Membership lemmas for every family
                                * tau1/tau2 of copy-tile sequences
                                * **Proven**: full simulation
                                  invariant for the *no-move* step
                                  case (tau1 = encodeRunningCfg + #,
                                  tau2 = encoded next config + #,
                                  membership in luTiles).
PCP.lean                     -- Library root.
Main.lean                    -- Executable entry point.
```

## Status

| Step                        | Status     |
|-----------------------------|------------|
| Core PCP API                | ✓ complete |
| MPCP API                    | ✓ complete |
| `MPCP ≤_m PCP`              | ✓ complete |
| `Halts` predicate           | ✓ complete |
| `Lu ≤_m MPCP` infrastructure| ✓ complete |
| Lu→MPCP: no-move step proof | ✓ complete |
| Lu→MPCP: right-move step    | TODO       |
| Lu→MPCP: left-move step     | TODO       |
| Lu→MPCP: halt absorption    | TODO       |
| Lu→MPCP: forward direction  | TODO       |
| Lu→MPCP: backward direction | TODO       |

The development contains **no `sorry`**. Verified against
`leanprover/lean4:v4.29.0-rc4` + cslib + Mathlib (see `lake-manifest.json`).

## Roadmap (Lu ≤_m MPCP)

The simulation invariant is

  `bot = top ++ "lookahead by one configuration"`.

The forward direction proceeds by induction on the number of TM steps.
For each step the tile sequence is

  copy-l_n … copy-l_1 · transition · copy-r_1 … copy-r_m · sepTile

with `tau1 = encodeCfg(C) ++ #` and `tau2 = encodeCfg(C') ++ #`. The
no-move case is proven (`tau1_stepTilesNoMove`, `tau2_stepTilesNoMove`,
`stepTilesNoMove_subset_luTiles` in `PCP/Reductions/LuToMPCP.lean`).

The right- and left-move cases are similar but introduce one subtlety
because cslib's `BiTape` strips trailing blanks (via `StackTape.cons`):
when the head moves into a previously-blank cell *and* writes a blank
*and* the corresponding side of the tape is empty, the encoding drops a
symbol that the naïve tile sequence would emit. The boundary tiles
already in place handle the standard cases; the proofs need to thread
this StackTape behaviour carefully (likely via separate lemmas for
`(t.write w).move_right` etc.).

After all step lemmas, the halt-absorption phase iterates
`absorbLeftTile` / `absorbRightTile` to shrink the halt configuration
to just `h⊥`, after which `finalTile` closes the match.
