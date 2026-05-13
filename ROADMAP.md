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

## 🚧 Remaining work

### Step 5 — `starts_with_absorbAndFinish`
For a halted cfg `⟨none, tape⟩` with
`tau1 A = encodeHaltedCfg tm tape ++ [#] ++ tau2 A`,
force `A` to start with
`absorbAndFinish tm tape.left.toList (tape.head :: tape.right.toList)`,
yielding a residual `A'` with `tau1 A' = tau2 A'` (matching closed).

**Proof sketch** (analogous to the step lemmas):
1. Reshape the lookahead so the `h⊥` marker is exposed after stripping
   the left-tape copies.
2. Use `copy_prefix_forced` to strip the bulk of left-tape copies, then
   peel one `absorbLeftTile` per remaining left symbol via
   `mem_luTiles_top` case analysis.
3. Once `tape.left.toList` is exhausted, peel `absorbRightTile`s for
   the head + right symbols.
4. Close with `finalTile`.

Estimated ~150 LoC.

### Step 6 — `backward_aux`
Strong induction on `A.length`:
* `A = []` → contradiction (matching invariant requires a non-empty
  lookahead).
* `cfg = ⟨none, tape⟩` → apply `starts_with_absorbAndFinish`; recurse
  on a shorter `A'` and close with `ReflTransGen.refl`.
* `cfg = ⟨some q, tape⟩` → dispatch on `tm.tr q tape.head`:
  - **`qNew = none`** (halt-now): the single TM step
    `cfg → ⟨none, …⟩` reaches a halted cfg directly. Conclude without
    needing a `starts_with_stepTiles*` invocation.
  - **`qNew = some q'`** (continuing): apply the appropriate
    `starts_with_stepTiles*` lemma (no-move / right-interior /
    right-boundary / left-interior) — each requires `qNew = some _`
    — get a shorter `A'`, recurse on `(stepResult tm q tape, A')`,
    and chain the TM step.

**Subtlety.** `A.length` strictly decreases each iteration: the
canonical decomposition consumes ≥ 2 tiles (transition tile + sepTile
at minimum; the right-boundary case consumes ≥ 1 tile, but it is
followed by `absorbAndFinish` which also strictly decreases the
remaining length until `[finalTile]`).

Estimated ~100 LoC.

### Step 7 — Final theorem
```lean
theorem lu_le_mpcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```
* Forward direction: `halts_implies_mhasSolution` (done).
* Backward direction: unpack `MHasSolution` to obtain `A` and the
  matching equation `[#] ++ tau1 A = [#] ++ encodeCfg(initCfg) ++ [#]
  ++ tau2 A`, cancel the leading `[#]`, call `backward_aux` with
  `cfg = initCfg tm w` and the resulting `RelatesInSteps`-style chain
  to produce a halting trace.

Estimated ~30 LoC.

## Estimated scope

The Coq counterpart in
[`coq-library-undecidability`](https://github.com/uds-psl/coq-library-undecidability)
runs to roughly 1500 lines for this single reduction. Through Step 4
(forward direction + 5/5 backward step lemmas) we are at ~2540 lines.
Steps 5–7 (halt absorption + main induction + final theorem) are
estimated at 280–350 additional lines, requiring 1–2 focused sessions.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings.
