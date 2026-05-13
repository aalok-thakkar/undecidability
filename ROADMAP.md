# Roadmap

The reduction chain `Lu ≤_m MPCP ≤_m PCP` — what's done and what's next.

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
  `leftMoveTile`, `absorbLeftTile`, `absorbRightTile`, `finalTile`,
  plus `stateMarker`. (The Lean definition of `leftMoveBoundaryTile`
  is retained for completeness but, following Hopcroft–Ullman–Motwani's
  one-sided-tape design, it is *not* a member of `luTiles`.)
* Tile-projection `simp` lemmas (`copyTile_top`/`bot`, `sepTile_top`/`bot`,
  `noMoveTile_top`/`bot`, `finalTile_top`/`bot`,
  `stateMarker_some`/`none`, `tau1_singleton`/`tau2_singleton`).
* Tile enumeration (`copyTiles`, `absorbTilesFor`, `absorbTiles`,
  `transitionTilesFor`, `transitionTiles`, `luTiles`) and the reduction
  `luToMpcp`. Marked `noncomputable` because they go through
  `Finset.toList`.
* Membership lemmas: every constructor's tile in `luTiles`
  (`copyTile_mem_luTiles`, `sepTile_mem_luTiles`, `finalTile_mem_luTiles`,
  `absorbLeftTile_mem_luTiles`, `absorbRightTile_mem_luTiles`,
  `transitionTile_mem_luTiles`, plus `map_copyTile_subset_luTiles`).
* `tau1`/`tau2` of a `List.map (copyTile tm)` is `liftTape tm syms`.
* Structural facts: `startTile_top`, `startTile_bot`, `block_eq`.
* Side conditions: `NoBlankWrites tm` (TM never writes a blank) and
  `NoLeftBoundary tm w` (no reachable cfg from `initCfg tm w` invokes
  a left-move at the left boundary).

### `Lu ≤_m MPCP`: step-simulation lemmas (forward direction)
The four step families used by the forward proof:
* **No-move** (`stepTilesNoMove`): `tau1`, `tau2`, subset lemmas.
* **Right-interior** (`stepTilesRightInterior`): `tau1`, `tau2`,
  `tau2_stepTilesRightInterior_eq_encodeCfg`, subset lemmas.
* **Right-boundary** (`stepTilesRightBoundary`): analogous, with the
  `StackTape.cons` blank-stripping subtlety handled via `NoBlankWrites`.
* **Left-interior** (`stepTilesLeftInterior`): `tau1`, `tau2`,
  `tau2_stepTilesLeftInterior_eq_encodeCfg`, subset lemmas.

Dispatcher: `stepTilesAux`, `stepTiles`, `tau1_stepTiles`,
`tau2_stepTiles`, `stepTiles_subset_luTiles`. The dispatcher's
left-boundary branch is unreachable under `NoLeftBoundary` and is
discharged by `absurd` in `stepTilesAux_subset_luTiles`.
`stepResult` and `tm_step_running` complete the kit.

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
  (`RelatesInSteps`), gluing `stepTiles` blocks and `absorbAndFinish`;
  threads `NoLeftBoundary` + reachability from `initCfg`.
* `halts_implies_mhasSolution`: the main forward theorem (requires
  `NoBlankWrites` *and* `NoLeftBoundary`).

### `Lu ≤_m MPCP`: backward direction infrastructure
* **`mem_luTiles_top`** — complete characterisation of every tile in
  `luTiles`: each `t ∈ luTiles tm` is identified as one of seven
  concrete tile families (`copyTile a`, `sepTile`,
  `noMoveTile`/`rightMoveTile`/`rightMoveBoundaryTile`/`leftMoveTile`
  together with the matching `tm.tr q a` equation, `absorbLeftTile a`,
  `absorbRightTile a`, or `finalTile`). Used everywhere downstream to
  identify the next tile from its top character.

* **`copy_prefix_forced`** — if `tau1 A = liftTape tm L ++ tail`,
  `(∀ t ∈ A, t ∈ luTiles tm)`, and `tail` does not start with `h⊥` or
  `↟ₛq`, then `A = L.map (copyTile tm) ++ A'` with `tau1 A' = tail` and
  `tau2 A = liftTape tm L ++ tau2 A'`. Key: `liftTape` symbols can only
  be consumed by `copyTile` (not `leftMoveTile`, whose second char is
  `↟ₛ_`, nor `absorbLeftTile`, whose second char is `h⊥`).

* **`transition_forced`** — when `tau1 A = ↟ₛq :: ↟ₜa :: rest` and
  every tile of `A` is in `luTiles tm`, the head of `A` is a tile in
  `transitionTilesFor tm q a`. Under HUM, only `noMoveTile`,
  `rightMoveTile`, and `rightMoveBoundaryTile` match a `↟ₛq`-lead;
  the proof rules out the other five `mem_luTiles_top` cases by
  constructor disequality at the first character of the tile's top.

* **Helpers**:
  - `copy_prefix_forced_state_lead` — strip copies right up to `↟ₛq`
    when `tm.tr q a` is *not* a left move. No `leftMoveTile` can
    swallow the last copy together with `↟ₛq`.
  - `sep_forced` — if the lead is `#`, the head tile is `sepTile`.
  - `no_tile_for_state_sharp` — if `tau1 A = ↟ₛq :: # :: rest` and
    `A ⊆ luTiles tm`, then `False` (every transition tile's second
    character is a tape lift, never `#`).

### `Lu ≤_m MPCP`: per-step backward lemmas
All five sub-cases of `starts_with_stepTiles*` are in place:
* ✅ `starts_with_stepTilesNoMove`
* ✅ `starts_with_stepTilesRightInterior`
* ✅ `starts_with_stepTilesRightBoundary` (under `qNew = some _`;
  the `qNew = none` halt-now branch will be handled directly in
  `backward_aux` via `Halts` reachability)
* ✅ `starts_with_stepTilesLeftInterior` (unambiguous under HUM since
  `leftMoveBoundaryTile` is not in `luTiles`, so the alternative
  `copyTile b :: leftMoveBoundaryTile` decomposition cannot be
  constructed)
* The **left-boundary** case is *removed* by HUM: `NoLeftBoundary`
  ensures no reachable cfg invokes a left-move at the left boundary,
  so the dispatcher (`stepTilesAux`) never enters that branch.

## ✅ Step 6 — `backward_aux` and `lu_le_mpcp` (strong-A iff)

`backward_aux` is now complete (~150 LoC). Strong induction on
`A.length`:
* `A = []` → contradiction via length of `encodeCfg cfg ++ [#]`.
* `cfg = ⟨none, tape⟩` → `ReflTransGen.refl` (no `starts_with_absorbAndFinish`
  needed; see below).
* `cfg = ⟨some q, tape⟩` → dispatch on `tm.tr q tape.head`:
  - **`qNew = none`** at the right boundary (halt-now): single TM step
    via `tm_step_running` reaches a halted cfg, close with
    `Relation.ReflTransGen.single`.
  - **Other cases**: apply the appropriate `starts_with_stepTiles*`
    lemma (no-move / right-interior / right-boundary with
    `qNew = some _` / left-interior); recurse via the IH; chain the TM
    step with `Relation.ReflTransGen.head`.

The top-level `lu_le_mpcp` is also complete in its strong-A form:

```lean
theorem lu_le_mpcp (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    ∃ A : Stack (Alpha tm.State Symbol),
      (∀ t ∈ A, t ∈ luTiles tm) ∧
      [#] ++ tau1 A = # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A
```

Forward: `forward_aux` produces such an `A`. Backward: cancel the
leading `#` from the matching equation, then `backward_aux`.

### Why no `starts_with_absorbAndFinish`?

The original plan called for a `starts_with_absorbAndFinish` lemma that
would force a halted-cfg solution to begin with the canonical absorption
sequence `absorbAndFinish left right`. We discovered this lemma is *not*
provable as stated: the absorption-phase decomposition is non-unique.
For example, with `left = [l]` and `right = [r]`, both

* `[absorbLeftTile l, copyTile r, sepTile, absorbRightTile r, sepTile, finalTile]`
  (the canonical one), and
* `[copyTile l, absorbRightTile r, sepTile, absorbLeftTile l, sepTile, finalTile]`
  (an alternative that swaps which side `l` is absorbed from),

are valid solutions of the halted-cfg matching equation. The lemma
"`A` starts with the canonical sequence" cannot be proved if the
alternative is also valid.

The fix: skip the halted-cfg peeling entirely. In `backward_aux`, when
`cfg.state = none`, return `ReflTransGen.refl` directly — there is no
need to look at `A` at all. The halt-now sub-case is handled in the
running-cfg branch by producing one TM step via `tm_step_running`.

## 🚧 Remaining work — canonical `Halts ↔ MHasSolution` iff

The full canonical iff is:

```lean
theorem lu_le_mpcp_canonical (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```

The forward direction is `halts_implies_mhasSolution` (already proved).
The backward direction needs a **membership-purification step**:
showing that for any `A` drawn from `startTile :: luTiles tm`
satisfying the MHasSolution matching, every tile of `A` is in fact in
`luTiles tm` alone. Once that is established, `backward_aux` applies
directly.

### Why purification is non-trivial

At every block boundary, the matching invariant's lookahead starts with
a character from `encodeCfg cfg` (a tape lift, state marker, or `h⊥`),
never `#`. Since `startTile.top = [#]`, `startTile` is ruled out at
block boundaries by character mismatch.

Within a step block, the existing forcing lemmas (`copy_prefix_forced`,
`transition_forced`, `copy_prefix_forced_state_lead`) likewise rule out
`startTile` at every intermediate position via character analysis —
their lookahead first characters are `↟ₜ_` or `↟ₛq`, again incompatible
with `[#]`.

The remaining ambiguity is at the **`sepTile` position** of each step
block: the lookahead is `# :: tau2 A` and both `sepTile.top = [#]` and
`startTile.top = [#]` match. A solution that uses `startTile` at a
sep position is a valid MHasSolution (with a doubled lookahead
`encodeCfg next_cfg ++ # :: encodeCfg(initCfg) ++ [#] ++ tau2 A` for
the residual), but the canonical decomposition fails to apply.

### Strategy options

Two viable approaches:

1. **Disambiguating `sep_forced`.** Extend `sep_forced` to take a
   tau2-side hypothesis distinguishing the canonical `sepTile` case
   (tau2 of `A` starts with `[#]`) from the `startTile` alternative.
   Requires threading additional structural information through each
   step lemma.

2. **Generalised `backward_aux` with extra accumulator.** Track an
   `extra : List (Alpha tm.State Symbol)` representing the accumulated
   tail of additional initCfg encodings inserted by mid-stream
   `startTile` uses. The matching invariant becomes
   `tau1 A = encodeCfg cfg ++ [#] ++ extra ++ tau2 A`. Recurse on a
   smaller `A` with the appropriately-updated `(cfg, extra)`. The cfg
   progression is no longer a pure TM-step chain, so the halt-witness
   extraction must be reformulated (e.g., follow the first complete
   simulation block, accept multiple halts, etc.).

Either path adds significant code (~300–500 LoC) and is left for a
future session.

## Estimated scope

The Coq counterpart in
[`coq-library-undecidability`](https://github.com/uds-psl/coq-library-undecidability)
runs to roughly 1500 lines for this single reduction. Through `Step 7`
(forward direction + strong-A backward direction + strong-A `lu_le_mpcp`
iff) we are at ~2960 lines. The canonical-iff purification step is
estimated at 300–500 additional lines.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings.
