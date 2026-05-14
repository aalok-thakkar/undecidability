# Roadmap

The reduction chain `Lu ≤_m MPCP ≤_m PCP` — what is done and what would
have to happen for a complete undecidability proof.

## ✅ Complete in this repo

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`
Full proof of `mpcp_iff_pcp` via the Hopcroft–Ullman symbol-padding
reduction (alphabet `Ext`, `hashL`/`hashR` interleaving, three tile
classes, `match_start`, generalised backward direction).

### `Halts` predicate — `PCP/Lu.lean`
`Halts tm w` and `HaltsWithinTime tm w n` for cslib's
`Turing.SingleTapeTM`, with the equivalence
`Halts ↔ ∃ n, HaltsWithinTime n` proved. The undecidability of `Halts`
itself is **not** proved here (and is not currently in cslib) — see
"External dependencies" below.

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
* Tile-projection `simp` lemmas, tile enumeration
  (`copyTiles`, `absorbTilesFor`, `absorbTiles`, `transitionTilesFor`,
  `transitionTiles`, `luTiles`), and the reduction `luToMpcp`. Marked
  `noncomputable` because the enumeration goes through `Finset.toList`.
* Membership lemmas: every constructor's tile in `luTiles`.
* `tau1`/`tau2` of a `List.map (copyTile tm)` is `liftTape tm syms`.
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
  concrete tile families.
* **`copy_prefix_forced`** — `liftTape tm L`-prefix forces a
  `L.map (copyTile tm)` prefix on `A`.
* **`transition_forced`** — a `↟ₛq :: ↟ₜa :: rest` lookahead forces the
  head of `A` to be a tile in `transitionTilesFor tm q a`.
* **Helpers**: `copy_prefix_forced_state_lead`, `sep_forced`,
  `no_tile_for_state_sharp`.

### `Lu ≤_m MPCP`: per-step backward lemmas
* `starts_with_stepTilesNoMove`
* `starts_with_stepTilesRightInterior`
* `starts_with_stepTilesRightBoundary` (`qNew = some _` branch; the
  `qNew = none` halt-now branch is handled directly in `backward_aux`
  via `Halts` reachability)
* `starts_with_stepTilesLeftInterior`

The left-boundary case is *removed* by HUM: `NoLeftBoundary` ensures no
reachable cfg invokes a left-move at the left boundary.

### `Lu ≤_m MPCP`: strong-A backward direction (`backward_aux`)

Strong induction on `A.length`:
* `A = []` → contradiction via length of `encodeCfg cfg ++ [#]`.
* `cfg = ⟨none, tape⟩` → `ReflTransGen.refl` (no
  `starts_with_absorbAndFinish` needed; see below).
* `cfg = ⟨some q, tape⟩` → dispatch on `tm.tr q tape.head`:
  - **`qNew = none`** at the right boundary (halt-now): a single TM step
    via `tm_step_running` reaches a halted cfg, then
    `Relation.ReflTransGen.single`.
  - **Other cases**: apply the appropriate `starts_with_stepTiles*`
    lemma; recurse via the IH; chain the TM step with
    `Relation.ReflTransGen.head`.

#### Why no `starts_with_absorbAndFinish`?

The original plan called for a `starts_with_absorbAndFinish` lemma that
would force a halted-cfg solution to begin with the canonical absorption
sequence `absorbAndFinish left right`. This lemma is *not* provable as
stated: the absorption-phase decomposition is non-unique. For example,
with `left = [l]` and `right = [r]`, both

* `[absorbLeftTile l, copyTile r, sepTile, absorbRightTile r, sepTile, finalTile]`
  (the canonical one), and
* `[copyTile l, absorbRightTile r, sepTile, absorbLeftTile l, sepTile, finalTile]`
  (an alternative that swaps which side `l` is absorbed from)

are valid solutions of the halted-cfg matching equation. The fix: skip
the halted-cfg peeling entirely. In `backward_aux`, when
`cfg.state = none`, return `ReflTransGen.refl` directly. The halt-now
sub-case is handled in the running-cfg branch by producing one TM step
via `tm_step_running`.

### `Lu ≤_m MPCP`: canonical `Halts ↔ MHasSolution` iff

`lu_le_mpcp` is closed in the canonical `MHasSolution` form via
`backward_aux_weak`, which threads a chain-tracked cfg queue
(`List (Σ' c, ReflTransGen ... initCfg c)`). When `startTile` appears
mid-stream in `A`, it pushes an extra `initCfg` onto the queue (in
addition to the natural `stepResult`); each queued cfg carries its own
`ReflTransGen` chain from `initCfg`. The right-boundary alternative
`rightMoveTile` path is ruled out by `tau1_no_state_marker_then_sharp`,
a structural property showing that `tau1 A` never contains
`↟ₛq :: # :: …` as a sublist.

```lean
theorem lu_le_mpcp (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```

### `Lu ≤_m PCP` composition — `PCP/Reductions/LuToPCP.lean`

```lean
theorem halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (luTiles tm))
```

The transitive composition of `lu_le_mpcp` with `mpcp_iff_pcp`.

## 🚧 External dependencies (out of scope for this repo)

To conclude "PCP is undecidable" from `halts_iff_pcp`, two more pieces
are required. Neither is in this repo nor in cslib.

### 1. Halting-problem undecidability for `Turing.SingleTapeTM`

A theorem of the form

```lean
¬ ∃ (decide : (Σ tm : SingleTapeTM Symbol, List Symbol) → Bool),
    ∀ x, decide x = true ↔ Halts x.1 x.2
```

**Mathlib has a halting-problem undecidability proof, but for a
different model.** Specifically,
[`Mathlib.Computability.Halting.halting_problem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Halting.html)
proves

```lean
theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom
```

where `c : Nat.Partrec.Code` and `eval c n : Part ℕ`. This is the
Halting Problem for **partial recursive function codes**, not for cslib's
`Turing.SingleTapeTM`.

Bridging the two would require either:
- showing `Turing.SingleTapeTM` can simulate every `Nat.Partrec.Code`
  (then transport Mathlib's `halting_problem` via the simulation), or
- showing the reverse: `Nat.Partrec.Code` can simulate every
  `Turing.SingleTapeTM` (so cslib's `Halts` reduces to Mathlib's
  halting predicate).

Mathlib's `Computability.TMToPartrec` provides such a bridge for
*Mathlib's own* TM model (`Turing.PartrecToTM2`), not for cslib's
`SingleTapeTM`. Building the analogous bridge for cslib's model is a
substantial development of its own; we leave it as future work.

A first-principles proof (Cantor / diagonalisation against a universal
cslib `SingleTapeTM`) is an alternative — comparable in size to
Mathlib's existing proof for `Nat.Partrec.Code`.

### 2. HUM normalisation

`halts_iff_pcp` carries the side conditions `NoBlankWrites tm` and
`NoLeftBoundary tm w`. These are real restrictions: a generic TM may
write blanks and may attempt left-moves at the left boundary. A
normalisation pass

```lean
theorem hum_normalise (tm : SingleTapeTM Symbol) (w : List Symbol) :
    ∃ tm' w', NoBlankWrites tm' ∧ NoLeftBoundary tm' w'
            ∧ (Halts tm w ↔ Halts tm' w')
```

would lift these. The standard construction: shift the tape by one cell
to introduce a sentinel marker, refuse to overwrite the blank
(`NoBlankWrites`), and refuse to move off the sentinel
(`NoLeftBoundary`). Estimated ~500–1000 LoC; deferred.

## Estimated scope

The Coq counterpart in
[`coq-library-undecidability`](https://github.com/uds-psl/coq-library-undecidability)
runs to roughly 1500 lines for the `Lu ≤_m MPCP ≤_m PCP` chain alone.
Our Lean development reaches ~4200 lines for the same content (more
verbose decidability/structural plumbing). HUM normalisation and
halting-problem undecidability would each add ~500–1000 LoC.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings.
