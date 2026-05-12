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

### `Lu ≤_m MPCP`: all step-simulation lemmas
All four TM-step families fully simulated:
* **No-move** (`stepTilesNoMove`): `tau1`, `tau2`, subset lemmas.
* **Right-interior** (`stepTilesRightInterior`): `tau1`, `tau2`,
  `tau2_stepTilesRightInterior_eq_encodeCfg`, subset lemmas.
* **Right-boundary** (`stepTilesRightBoundary`): analogous, with the
  `StackTape.cons` blank-stripping subtlety handled via the
  `NoBlankWrites` side condition.
* **Left-interior** (`stepTilesLeftInterior`): `tau1`, `tau2`,
  `tau2_stepTilesLeftInterior_eq_encodeCfg`, subset lemmas.
* **Left-boundary** (`stepTilesLeftBoundary`): analogous.
* Unified dispatcher: `stepTilesAux`, `stepTiles`, `tau1_stepTiles`,
  `tau2_stepTiles`, `stepTiles_subset_luTiles`.
* `stepResult` and `tm_step_running`.

### `Lu ≤_m MPCP`: halt-absorption phase
Full absorption sequence `absorbAndFinish`:
* `encodeHaltList`, `encodeHaltedCfg_eq_encodeHaltList`.
* Per-iteration tile sequences `stepTilesAbsorbLeft` /
  `stepTilesAbsorbRight` with `tau1`, `tau2`, and subset lemmas.
* `absorbAndFinish_matching`: the matching invariant
  `tau1 = encodeHaltList left right ++ [#] ++ tau2`
  proved by structural induction.
* `absorbAndFinish_subset_luTiles`.

### `Lu ≤_m MPCP`: forward direction `Halts → MHasSolution`
* `forward_aux`: induction on the length of the halting chain
  (`RelatesInSteps`), gluing `stepTiles` blocks and `absorbAndFinish`.
* `halts_implies_mhasSolution`: the main forward theorem (requires
  `NoBlankWrites`).

## 🚧 Remaining work

### 1. Backward direction `MHasSolution → Halts`

Given any tile sequence `A` satisfying

```
tau1 A = encodeCfg tm (initCfg tm w) ++ [#] ++ tau2 A
∀ t ∈ A, t ∈ luTiles tm
```

recover a halting computation of `tm` on `w`.

**Proof strategy** (induction on `A.length`):

1. ✅ **`mem_luTiles_top`** — complete characterisation of every tile in
   `luTiles`: each `t ∈ luTiles tm` is identified as one of eight
   concrete tiles (`copyTile a`, `sepTile`, `noMoveTile`/`rightMoveTile`
   /`rightMoveBoundaryTile`/`leftMoveBoundaryTile`/`leftMoveTile`
   together with the matching `tm.tr q a` equation, `absorbLeftTile a`,
   `absorbRightTile a`, or `finalTile`).  Used everywhere downstream
   to identify the next tile from its top character.

2. ✅ **`copy_prefix_forced`** — if `tau1 A = liftTape tm L ++ tail`,
   `(∀ t ∈ A, t ∈ luTiles tm)`, and `tail` does not start with `h⊥` or
   `↟ₛq`, then `A = L.map (copyTile tm) ++ A'` with
   `tau1 A' = tail` and `tau2 A = liftTape tm L ++ tau2 A'`.  Key:
   `liftTape` symbols can only be consumed by `copyTile` (not
   `leftMoveTile`, whose second char is `↟ₛ_`, nor `absorbLeftTile`,
   whose second char is `h⊥`).

3. ✅ **`transition_forced`** — when `tau1 A = ↟ₛq :: ↟ₜa :: rest` and
   every tile of `A` is in `luTiles tm`, the head of `A` is a tile in
   `transitionTilesFor tm q a`.  The six non-transition cases of
   `mem_luTiles_top` (copy / sep / leftMove / absorbLeft / absorbRight /
   final) all have a top whose first character is not `↟ₛq`, ruling them
   out by `Alpha` constructor disequality.  The four valid cases
   (`noMoveTile`, `rightMoveTile`, `rightMoveBoundaryTile`,
   `leftMoveBoundaryTile`) match `[↟ₛq', ↟ₜa', …]` against the lead,
   forcing `q' = q` and `a' = a`.

4. **`starts_with_stepTiles`** — combines the copy and transition forcing
   to show `A = stepTiles tm q tape ++ A'` and the residual invariant
   holds for `(stepResult tm q tape, A')`.  Three of the five sub-cases
   are done:
   * ✅ `starts_with_stepTilesNoMove`
   * ✅ `starts_with_stepTilesRightInterior`
   * ✅ `starts_with_stepTilesLeftBoundary`
   * 🚧 `starts_with_stepTilesRightBoundary`  — needs an auxiliary
     lemma ruling out an alternative `rightMoveTile :: sepTile`
     decomposition whose residual invariant `liftTape t.left.reverse ++
     [↟ₜw, stateMarker qNew, #] ++ tau2 A'` does not encode any
     `tm.Cfg` (the state marker sits adjacent to `#` with no head
     symbol between).
   * 🚧 `starts_with_stepTilesLeftInterior` — similar ambiguity between
     `copyTile :: leftMoveBoundaryTile` and `leftMoveTile`.

   Helpers proved en route:
   * ✅ `copy_prefix_forced_state_lead` — strip copies right up to `↟ₛq`
     when `tm.tr q a` is *not* a left move.  No `leftMoveTile` can
     swallow the last copy together with `↟ₛq`.
   * ✅ `sep_forced` — if the lead is `#`, the head tile is `sepTile`.

5. **`backward_halt`** — for a halted cfg `⟨none, tape⟩`, the absorption
   tiles force `A` to start with `absorbAndFinish ...`, which closes with
   `finalTile` and terminates.

6. **`backward_aux`** — strong induction on `A.length`:
   * `A = []` → contradiction (lead is nonempty).
   * `cfg = ⟨none, _⟩` → `ReflTransGen.refl`.
   * `cfg = ⟨some q, tape⟩` → apply `starts_with_stepTiles`, get `A'`
     with `A'.length < A.length`; apply IH; chain the TM step.

**Subtlety.** Extra `copyTile`s at the front of `A` are transparent
(they cancel in tau1 and tau2) but they make the residual lead longer,
not shorter.  The induction terminates because `A.length` strictly
decreases each time we consume at least one tile; the number of tiles
consumed per logical step is ≥ 2 (transition tile + sepTile at minimum).

### 2. Final theorem

```lean
theorem lu_le_mpcp (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (w : List Symbol) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```

Forward direction: `halts_implies_mhasSolution` (done).
Backward direction: `mhasSolution_implies_halts` (step 1 above).

## Estimated scope

The Coq counterpart in
[`coq-library-undecidability`](https://github.com/uds-psl/coq-library-undecidability)
runs to roughly 1500 lines for this single reduction. Steps 1–4
(forward direction and simulation infrastructure) are complete at ~1683
lines. The backward direction (step 5) and final theorem (step 6) are
estimated at 400–600 additional lines, requiring 2–3 focused sessions.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings.
