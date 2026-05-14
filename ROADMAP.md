# Roadmap

The reduction chain

```
Halt  ≤_m  MPCP  ≤_m  PCP  ≤_m  CFG-Intersection-Nonempty
```

is closed end-to-end as iffs in this repository. The halting-problem
undecidability is proved separately as `Halt.halt_undecidable`. This
file records the architecture; for the entry point see
[`README.md`](README.md).

## ✅ Complete in this repo

### `MPCP ≤_m PCP` — [`PCP/Reduction.lean`](PCP/Reduction.lean)
The full `mpcp_iff_pcp` equivalence via the Hopcroft–Ullman
symbol-padding reduction (alphabet `Ext`, `hashL`/`hashR` interleaving,
three tile classes `tileStart`/`tileReg`/`tileEnd`, `match_start`,
and the complete forward and backward directions).

### `Halts` predicate — [`PCP/Halt.lean`](PCP/Halt.lean)
`Halts tm w` and `HaltsWithinTime tm w n` for cslib's
`Turing.SingleTapeTM`, with their equivalence.

### `Halt ≤_m MPCP` — [`PCP/Reductions/HaltToMPCP.lean`](PCP/Reductions/HaltToMPCP.lean)
Forward and backward directions of the canonical iff
`Halts tm w ↔ MHasSolution (startTile tm w) (haltTiles tm)`
under the HUM side conditions `NoBlankWrites` and `NoLeftBoundary`.
The forward direction interleaves step-simulation tile groups; the
backward direction inverts via per-tile forcing lemmas plus a
chain-tracked configuration queue.

### `Halt ≤_m PCP` (composition) — [`PCP/Reductions/HaltToPCP.lean`](PCP/Reductions/HaltToPCP.lean)
```lean
theorem halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔ HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm))
```
Transitive composition of `halt_le_mpcp` with `mpcp_iff_pcp`.

### `PCP ≤_m CFG-Intersection-Nonempty` — [`CFG/PcpReduction.lean`](CFG/PcpReduction.lean)
```lean
theorem hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔ ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```
Two context-free grammars over `α ⊕ Tile α` whose intersection is
non-empty iff the PCP instance has a solution. Uses Mathlib's
`ContextFreeGrammar` (cslib has no CFG framework).

### Halting-problem undecidability — [`Halt/Undecidable.lean`](Halt/Undecidable.lean)
```lean
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```
No `SingleTapeTM Bool` decides the self-halt problem
`K = { c : TMCode | c.toTM halts on encodeTMCode c }`. Proved via a
*compositional* diagonal: build `diagTM D` by inlining the
"simulate-then-invert" pattern as a single TM, apply
`Halt.CodeOf.halts_codeOf_iff` plus deterministic confluence on
`ReflTransGen` to derive a contradiction. See
[`Halt/ROADMAP.md`](Halt/ROADMAP.md) for the detailed construction.

## 🚧 Optional follow-ups

These are not on the critical path of any current theorem; they are
recorded for completeness.

### HUM normalisation

`halts_iff_pcp` carries side conditions `NoBlankWrites tm` and
`NoLeftBoundary tm w`. A normalisation pass

```lean
theorem hum_normalise (tm : SingleTapeTM Symbol) (w : List Symbol) :
    ∃ tm' w', NoBlankWrites tm' ∧ NoLeftBoundary tm' w'
            ∧ (Halts tm w ↔ Halts tm' w')
```

would lift these. The standard construction: shift the tape by one
cell to introduce a sentinel marker; refuse to write blanks
(`NoBlankWrites`); refuse to move off the sentinel (`NoLeftBoundary`).
Estimated ~500–1000 LoC; not started.

### HALT_TM (pair-form) undecidability

`halt_undecidable` is for the self-halt form `K`. To extend to the
pair form `HALT_TM = { (c, w) | c.toTM halts on w }`, the cleanest
route is `K ≤_m HALT_TM` via a `dupTM`-style construction that on
input `c` produces `encodePair c c`. Estimated ~200 LoC.

### `decodeTMCode` left-inverse

`Halt.Encoding` proves `decodeTMCode (encodeTMCode c)` is *defined* but
not yet that it equals `some c`. Closing this requires the pointwise
lookup `(trToList tr)[3 * q.val + symbolIdx ob] = tr q ob`. Used only
for full injectivity, not for `halt_undecidable`.

## Scope

The Coq counterpart in
[`coq-library-undecidability`](https://github.com/uds-psl/coq-library-undecidability)
runs to roughly 1500 lines for the `Halt ≤_m MPCP ≤_m PCP` chain alone.
Our Lean development reaches ~4200 lines for the same content (more
verbose decidability/structural plumbing). The Halt-undecidability
module adds ~1425 LoC; the CFG module adds another ~660 LoC.

## Build invariant

Every commit MUST keep `lake build` clean with **no `sorry`** and no
warnings.
