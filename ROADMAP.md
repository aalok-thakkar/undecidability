# Architecture and proof chain

This document describes the proof architecture of the results currently
landed in the repository. For the project vision see
[`README.md`](README.md); for the forward-looking work plan see
[`TODO.md`](TODO.md).

The reductions assembled here form the spine of the eventual
DiagonaLean reduction graph:

```
Halt  ≤_m  MPCP  ≤_m  PCP  ≤_m  CFG-Intersection-Nonempty
```

plus the stand-alone proof that the halting problem itself is
undecidable for cslib's `SingleTapeTM Bool`. All edges of this chain
are closed as iffs.

## Anchor nodes

### Halting problem — [`Halt/Undecidable.lean`](Halt/Undecidable.lean)

```lean
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```

No `SingleTapeTM Bool` decides the self-halt problem
`K = { c : TMCode | c.toTM halts on encodeTMCode c }`. Proved via a
compositional diagonal: build `diagTM D` by inlining the
"simulate-then-invert" pattern as a single TM, apply
`Halt.CodeOf.halts_codeOf_iff` plus deterministic confluence on
`ReflTransGen` to derive a contradiction. See
[`Halt/ROADMAP.md`](Halt/ROADMAP.md) for the detailed construction.

### MPCP ≤_m PCP — [`PCP/Reduction.lean`](PCP/Reduction.lean)

Full `mpcp_iff_pcp` via the Hopcroft–Ullman symbol-padding
construction (alphabet extension, `hashL`/`hashR` interleaving, three
tile classes `tileStart`/`tileReg`/`tileEnd`, `match_start`, both
directions).

### Halt ≤_m MPCP — [`PCP/Reductions/HaltToMPCP.lean`](PCP/Reductions/HaltToMPCP.lean)

The bulk of the project (~4100 LoC). Both directions of the canonical
iff `Halts tm w ↔ MHasSolution (startTile tm w) (haltTiles tm)` under
the HUM side conditions `NoBlankWrites` and `NoLeftBoundary`.

* **Forward**: interleave step-simulation tile groups
  (`stepTilesNoMove`, `stepTilesRightInterior`, `stepTilesRightBoundary`,
  `stepTilesLeftInterior`) over the halting trace, closing with
  `absorbAndFinish`.
* **Backward (strong-A form)**: `halt_le_mpcp_strong` via strong
  induction on `A.length`. Per-tile forcing lemmas
  (`mem_haltTiles_top`, `copy_prefix_forced`, `transition_forced`,
  `sep_forced`, `no_tile_for_state_sharp`, etc.) identify each tile
  uniquely from its top character. The halt-now sub-case is handled
  directly to sidestep the non-unique absorption-phase decomposition.
* **Backward (canonical form)**: `halt_le_mpcp` extends to
  `A ⊆ startTile :: haltTiles tm` via `backward_aux_weak` threading a
  chain-tracked configuration queue.

### Halt ≤_m PCP — [`PCP/Reductions/HaltToPCP.lean`](PCP/Reductions/HaltToPCP.lean)

```lean
theorem halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm)) :=
  (halt_le_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)
```

Composition of the two iffs.

### PCP ≤_m CFG-Intersection-Nonempty — [`CFG/PcpReduction.lean`](CFG/PcpReduction.lean)

```lean
theorem hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔ ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

For each tile `t ∈ P`, two production rules over alphabet `α ⊕ Tile α`:

| Grammar  | Recursive rule                       | Base rule                   |
|----------|--------------------------------------|-----------------------------|
| `topCFG` | `S → t.top.inl ++ S ++ [.inr t]`     | `S → t.top.inl ++ [.inr t]` |
| `botCFG` | `S → t.bot.inl ++ S ++ [.inr t]`     | `S → t.bot.inl ++ [.inr t]` |

A derivation traces a tile sequence `[t₁, …, t_k]` and emits
`(tau_proj A).map .inl ++ A.reverse.map .inr`. The reverse order of
markers forces both grammars to commit to the same sequence; the
`.inl`/`.inr` alphabet split lets us recover the PCP witness uniquely
via `list_inl_inr_split`.

## Encoding infrastructure

`Halt/` provides the encoding pipeline used by the halting-problem
diagonal:

* **`Halt.TMCode`** — normalised TM record (alphabet `Bool`, state set
  `Fin (n + 1)`) with `TMCode.toTM : TMCode → SingleTapeTM Bool`.
* **`Halt.Encoding`** — self-delimiting bit encoding
  `encodeTMCode : TMCode → List Bool` with round-trip lemmas at every
  layer.
* **`Halt.CodeOf`** — generic state-renaming
  `codeOf : SingleTapeTM Bool → TMCode` with the bisimulation theorem
  `halts_codeOf_iff : Halts (codeOf tm).toTM w ↔ PCP.Halts tm w`. The
  bisim goes through an `Equiv` of `Cfg`s plus `step`-commutation,
  lifted to `ReflTransGen` via `Relation.ReflTransGen.lift`.

`Halt.Diagonal` isolates the purely-logical kernel — Cantor's theorem
and the abstract self-referential contradiction — independently of
any computation model.

## In progress: Rice's theorem

`Halt/Rice/` contains the scaffolding for Rice's theorem.

* `Rice.Basic` defines `SemHalt`, `BehaviourEquiv`, `IsSemantic`,
  `IsPropDecider`, `NonTrivial`, and the semantic-set form
  (`BehaviourClassProp` + `liftClassProp`).
* `Rice.TrivialTMs` provides the witnesses `tm_alwaysHalt`
  (`SemHalt = univ`) and `tm_loop` (`SemHalt = ∅`).
* `Rice.Extender` defines `riceConstTM : TMCode → SingleTapeTM Bool`,
  the four-phase TM (erase → write `encodeTMCode c` → move back →
  simulate `c.toTM`). The construction is complete; the behaviour
  theorem `SemHalt (riceConstTM c) = univ ↔ Halts c.toTM
  (encodeTMCode c)` (four-phase bisimulation) is the next chunk.

See [`Halt/ROADMAP.md`](Halt/ROADMAP.md) for the construction-level
notes specific to `Halt/`.

## What's deferred

Not on the critical path of any current theorem; recorded for
completeness. The forward-looking plan, including how to lift these
into the DiagonaLean framework, lives in [`TODO.md`](TODO.md).

* **HUM normalisation** removes the `NoBlankWrites` / `NoLeftBoundary`
  side conditions from `halts_iff_pcp`.
* **`HALT_TM` (pair-form)** undecidability via `K ≤_m HALT_TM`.
* **`decodeTMCode` left-inverse** completion in `Halt.Encoding`
  (requires the deferred pointwise `trToList` lookup lemma).
* **Symbol-to-Bool simulation** bridge for general-alphabet
  undecidability.

## Build invariant

Every commit MUST keep `lake build` clean with **no `sorry`** and no
warnings.
