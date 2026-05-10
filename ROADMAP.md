# Roadmap

The reduction chain `Lu ≤_m MPCP ≤_m PCP` and what's done / what's next.

## ✅ Complete

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`
Full proof of `mpcp_iff_pcp` via the Hopcroft–Ullman symbol-padding
reduction (alphabet `Ext`, `hashL`/`hashR` interleaving, three tile
classes, `match_start`, generalised backward direction).

### `Halts` predicate — `PCP/Lu.lean`
`Halts tm w` and `HaltsWithinTime tm w n` for cslib's
`Turing.SingleTapeTM`, with the equivalence
`Halts ↔ ∃ n, HaltsWithinTime n` proved.

### `Lu ≤_m MPCP` infrastructure — `PCP/Reductions/LuToMPCP.lean`
* Alphabet `Alpha Q S` (4 constructors) with `DecidableEq` and notation.
* Configuration encoding: `liftTape`, `biTapeToList`,
  `encodeRunningCfg`, `encodeHaltedCfg`, `encodeCfg`, `block`,
  `initBlock` — plus `simp` lemmas for the encoding.
* Tile constructors: `startTile`, `copyTile`, `sepTile`,
  `noMoveTile`, `rightMoveTile`, `rightMoveBoundaryTile`,
  `leftMoveTile`, `leftMoveBoundaryTile`, `absorbLeftTile`,
  `absorbRightTile`, `finalTile`, plus `stateMarker`.
* Tile-projection `simp` lemmas (`copyTile_top`/`bot`, `sepTile_top`/`bot`,
  `noMoveTile_top`/`bot`, `finalTile_top`/`bot`,
  `stateMarker_some`/`none`, `tau1_singleton`/`tau2_singleton`).
* Tile enumeration (`copyTiles`, `absorbTilesFor`, `absorbTiles`,
  `transitionTilesFor`, `transitionTiles`, `luTiles`) and the reduction
  `luToMpcp`. Marked `noncomputable` because they go through
  `Finset.toList`.
* Membership lemmas: every constructor's tile is in `luTiles`
  (`copyTile_mem_luTiles`, `sepTile_mem_luTiles`, `finalTile_mem_luTiles`,
  `absorbLeftTile_mem_luTiles`, `absorbRightTile_mem_luTiles`,
  `transitionTile_mem_luTiles`, plus `map_copyTile_subset_luTiles`).
* `tau1`/`tau2` of a `List.map (copyTile tm)` is `liftTape tm syms`.
* Structural facts: `startTile_top`, `startTile_bot`, `block_eq`.

### `Lu ≤_m MPCP`: no-move step
`stepTilesNoMove` — the tile sequence simulating one no-move TM step,
with a complete proof of:
* `tau1_stepTilesNoMove`: `tau1 = encodeRunningCfg(q, t) ++ [#]`.
* `tau2_stepTilesNoMove`: `tau2` produces the next configuration.
* `stepTilesNoMove_subset_luTiles`: every tile is in `luTiles`.

## 🚧 Remaining work

### 1. Right-move step simulation
Mirror `stepTilesNoMove` for `tm.tr q a = (⟨w, some right⟩, qNew)`.
Two sub-cases:
* **Interior** (`t.right.toList ≠ []`): use `rightMoveTile`. Encoding
  after step has new head = `t.right.head`.
* **Boundary** (`t.right.toList = []`): use `rightMoveBoundaryTile`,
  which inserts an explicit `none` for the new (blank) head.

Lemmas to prove: `tau1_stepTilesRight{Interior,Boundary}`,
`tau2_stepTilesRight{Interior,Boundary}`,
`stepTilesRight_subset_luTiles` (one combined or two specialised).

**Subtlety.** cslib's `BiTape.move_right` performs
`StackTape.cons (t.write w).head t.left` for the new left side, and
`StackTape.cons` swallows a leading `none` when the StackTape is empty.
This means when `w = none ∧ t.left.toList = []` the encoding loses a
symbol that the naïve tile output would emit. Either:
* (a) thread this through the lemmas explicitly with separate cases,
  or
* (b) introduce an auxiliary "logical" encoding that is independent of
  `StackTape.cons`'s normalisation, and prove its equivalence to
  `encodeCfg` on the `BiTape`s actually produced by `tm.step`.

### 2. Left-move step simulation
Symmetric: `tm.tr q a = (⟨w, some left⟩, qNew)`, two sub-cases
(`t.left.toList = []` boundary vs. interior). Same `StackTape.cons`
subtlety on the right side. Tiles already in place: `leftMoveTile`,
`leftMoveBoundaryTile`.

### 3. Halt-absorption iteration lemmas
After the TM halts, `bot` ends with `# … h⊥ … #`. One absorption
iteration applies `absorbLeftTile` or `absorbRightTile` to remove a
single tape symbol from one side. Lemmas:
* `tau1_absorbIterLeft` / `tau2_absorbIterLeft`: when `t.left ≠ []`,
  `tau1 = encodeHaltedCfg(t) ++ [#]`,
  `tau2 = encodeHaltedCfg(t with one fewer left symbol) ++ [#]`.
* Symmetric for the right.
* Termination: after `len(left) + len(right)` iterations the encoded
  config is just `[h⊥]`, so the *final tile* applies and equalises
  top with bot.

### 4. Forward direction `Halts → MHasSolution`
Construct a tile sequence by induction on `RelatesInSteps` (or by an
explicit fold over the halting computation), gluing together step
sequences and the absorption phase. The matching condition
`(startTile tm w).top ++ tau1 A = (startTile tm w).bot ++ tau2 A`
follows from telescoping the per-step `tau1`/`tau2` lemmas.

### 5. Backward direction `MHasSolution → Halts`
Given a matching `A`, recover a halting computation. The strategy
mirrors the proof of `pcp_to_mpcp_solution_gen` in `PCP/Reduction.lean`:
* A `match_start`-style lemma forcing the first tile of any solution
  to be `startTile`.
* A "match-step" lemma showing each block of the matching corresponds
  to one TM transition (per direction case).
* Termination: any solution must eventually reach `finalTile`, which is
  only applicable when the TM has halted.

### 6. Final theorem
```lean
theorem lu_le_mpcp (tm : SingleTapeTM Symbol) (w : List Symbol) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```

## Estimated scope

The Coq counterpart in
[`coq-library-undecidability`](https://github.com/uds-psl/coq-library-undecidability)
runs to roughly 1500 lines for this single reduction. Expect 5–8
focused sessions to complete steps 1–6, with step 4 (forward) being
roughly half the work and step 5 (backward) the other half.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings.
