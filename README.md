# Undecidability

A Lean 4 formalisation of three classical undecidability results,
linked by reductions, all built on top of cslib's
[`Turing.SingleTapeTM`](https://github.com/leanprover/cslib):

| Library | Top-level theorem | Status |
|---|---|---|
| **`PCP/`** | `halts_iff_pcp : Halts tm w ↔ HasSolution (mpcpToPcp …)` | ✅ complete |
| **`CFG/`** | `hasSolution_iff_intersectionNonempty : HasSolution P ↔ ∃ w, w ∈ L(topCFG) ∩ L(botCFG)` | ✅ complete |
| **`Halt/`** | `halt_undecidable : ¬ ∃ computable decider for Halts` | 🚧 in progress (Path C, Phase 1 of 4) |

The proof contains **no `sorry`** anywhere and is verified against
`leanprover/lean4:v4.29.0-rc4` (see `lake-manifest.json`).
`lake build` is clean (2185 jobs, no warnings).

## What is proved end-to-end

Composing `PCP/` and `CFG/`, this repository proves the entire reduction
chain

```
Halt  ≤_m  MPCP  ≤_m  PCP  ≤_m  CFG-Intersection-Nonempty
```

as iffs under HUM (Hopcroft–Ullman–Motwani) side conditions:

```lean
theorem halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm))

theorem hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔
    ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

Composed, an explicit computable function `f` produces a pair of
context-free grammars `(G₁, G₂)` from a Turing machine + input, such
that `Halts tm w ↔ L(G₁) ∩ L(G₂) ≠ ∅`. Both reductions are many-one and
both directions of each iff are proved.

## What this repository does *not* yet prove

The reductions are closed as iffs; the missing piece for an end-to-end
**undecidability** statement is:

1. **Halting-problem undecidability for cslib's `Turing.SingleTapeTM`.**
   This is the subject of the new `Halt/` library. The kernel diagonal
   argument is in (`Halt/Diagonal.lean`) and Phase 1 of the chosen
   construction (Path C — direct universal `SingleTapeTM` +
   self-application) is in (`Halt/TMCode.lean`). Phases 2–4 are
   substantial future work; see `Halt/ROADMAP.md` for the plan.

   Note that Mathlib *does* prove the Halting Problem
   ([`Mathlib.Computability.Halting.halting_problem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Halting.html)),
   but for `Nat.Partrec.Code` (partial recursive function codes) rather
   than `Turing.SingleTapeTM`. Reusing it would require a simulation
   bridge — see `Halt/ROADMAP.md` Path A for that alternative.

2. **HUM normalisation** — a construction `(tm, w) ↦ (tm', w')`
   producing an equivalent TM satisfying `NoBlankWrites tm'` and
   `NoLeftBoundary tm' w'`. The standard sentinel-shift construction
   is straightforward but bulky (~500–1000 LoC); deferred to a future
   `PCP.Normalize` module.

Once (1) and (2) land, the iff chain immediately yields concrete
undecidability theorems for PCP and CFG-intersection-emptiness.

## Conventions

The `Halt ≤_m MPCP` reduction follows the **Hopcroft–Ullman–Motwani
one-sided-tape design**: the simulation tile set does not include a
`leftMoveBoundaryTile`, and the TM is required to satisfy
`NoLeftBoundary` (no left-move at the left tape boundary) in addition
to the standard `NoBlankWrites` (no blank symbol written).

The development uses [`cslib`](https://github.com/leanprover/cslib)'s
`Turing.SingleTapeTM` for the Turing-machine machinery and follows
cslib's conventions (module-style headers, `public import`,
`@[expose] public section`).

## Project layout

```
PCP/                            ← Halt ≤_m MPCP ≤_m PCP chain (complete)
  Basic.lean                    -- core types: Word, Tile, Stack;
                                   tau1, tau2; HasSolution predicate
  MPCP.lean                     -- MPCP variant: MHasSolution
  Reduction.lean                -- MPCP ≤_m PCP: full mpcp_iff_pcp
  Halt.lean                     -- Halts predicate for SingleTapeTM
  Reductions/
    HaltToMPCP.lean             -- Halt ≤_m MPCP construction + proofs
    HaltToPCP.lean              -- halts_iff_pcp: composition

CFG/                            ← PCP ≤_m CFG-Intersection-Nonempty (complete)
  Basic.lean                    -- IntersectionEmpty / IntersectionNonempty
  PcpReduction.lean             -- the full reduction iff

Halt/                           ← Halting-Problem undecidability (in progress)
  Diagonal.lean                 -- Cantor + abstract halting contradiction
  Basic.lean                    -- HaltDecidable predicate
  TMCode.lean                   -- normalised TM rep (Bool alphabet,
                                   Fin (n+1) states) — Phase 1 of Path C
  ROADMAP.md                    -- Path C plan (4 phases)

PCP.lean / CFG.lean / Halt.lean  ← library roots
Main.lean                        ← executable entry point
ROADMAP.md                       ← reduction-chain roadmap + external deps
```

## Detailed status

### `PCP/` — `Halt ≤_m MPCP ≤_m PCP` (complete)

| Component                                                  | Status      |
|------------------------------------------------------------|-------------|
| Core PCP / MPCP API                                        | ✅ complete |
| `MPCP ≤_m PCP` (full `mpcp_iff_pcp`)                       | ✅ complete |
| `Halts` predicate for `SingleTapeTM`                       | ✅ complete |
| `Halt ≤_m MPCP`: tile set + HUM refactor (`NoLeftBoundary`)| ✅ complete |
| `Halt ≤_m MPCP`: forward direction                         | ✅ complete |
| `Halt ≤_m MPCP`: backward direction                        | ✅ complete |
| Canonical `halt_le_mpcp` (`Halts ↔ MHasSolution`)          | ✅ complete |
| `halts_iff_pcp` (composition `Halts ↔ HasSolution …`)      | ✅ complete |

### `CFG/` — `PCP ≤_m CFG-Intersection-Nonempty` (complete)

| Component                                                  | Status      |
|------------------------------------------------------------|-------------|
| `IntersectionEmpty` / `IntersectionNonempty` predicates    | ✅ complete |
| Forward (PCP solution → word in both languages)            | ✅ complete |
| Backward (word in both languages → PCP solution)           | ✅ complete |
| `Form`-invariant proof of language characterisation        | ✅ complete |
| `inl`/`inr` disjointness lemma                             | ✅ complete |
| Top-level `hasSolution_iff_intersectionNonempty`           | ✅ complete |

Uses Mathlib's `ContextFreeGrammar`; cslib has no CFG framework.

### `Halt/` — Halting-Problem undecidability (in progress, Path C)

| Phase / Component                                          | Status              |
|------------------------------------------------------------|---------------------|
| `Halt.Diagonal` — Cantor + abstract halting contradiction  | ✅ complete         |
| `Halt.Basic` — `HaltDecidable` predicate                   | ✅ complete         |
| **Phase 1**: `Halt.TMCode` (normalised TM representation)  | ✅ complete         |
| **Phase 2**: Gödel numbering (`encodeTMCode`)              | 🚧 not yet started  |
| **Phase 3**: Universal `SingleTapeTM` (the bulk of Path C) | 🚧 not yet started  |
| **Phase 4**: Self-application diagonal + final theorem     | 🚧 not yet started  |

See `Halt/ROADMAP.md` for the full plan. Total estimated scope:
~2650–5500 LoC across many sessions (Phase 3 dominates).

### External dependencies (out of scope for this repo)

| Dependency                                                   | Status              |
|--------------------------------------------------------------|---------------------|
| HUM normalisation (lifting `NoBlankWrites`/`NoLeftBoundary`) | 🚧 future work      |

## What is proved (details)

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`

The full `mpcp_iff_pcp` equivalence via the Hopcroft–Ullman construction:
extend the alphabet with `⋕`-prefixed hash symbols, interleave the tile
top/bot words, produce a `tileStart`/`tileReg`/`tileEnd` triple, and prove
`match_start` (any solution must begin with the start tile) plus the
complete forward and backward directions.

### `Halt ≤_m MPCP` (forward) — `PCP/Reductions/HaltToMPCP.lean`

Given `Halts tm w` together with the two side conditions `NoBlankWrites`
and `NoLeftBoundary`, constructs a tile sequence
`A ⊆ startTile :: haltTiles tm` satisfying the MPCP matching equation.
The proof:

1. Prepends `stepTiles tm q tape` for each TM step, dispatching over
   transition direction × tape-boundary status:

   | Case              | Tiles used                                         |
   |-------------------|----------------------------------------------------|
   | No move           | `left-copies · noMoveTile · right-copies · sep`    |
   | Right (interior)  | `left-copies · rightMoveTile · right-copies · sep` |
   | Right (boundary)  | `left-copies · rightMoveBoundaryTile`              |
   | Left (interior)   | `tail-copies · leftMoveTile · right-copies · sep`  |

   The **left-boundary case is unreachable** under `NoLeftBoundary`, so
   no corresponding tile group is needed.

2. Closes with `absorbAndFinish` once the TM halts: iteratively absorbs
   tape symbols via `absorbLeftTile`/`absorbRightTile`, then applies
   `finalTile` to equalise top and bot.

Top-level lemma: `halts_implies_mhasSolution`
`(tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm) (w : List Symbol)`
`(h_nlb : NoLeftBoundary tm w) (h : Halts tm w) : MHasSolution …`.

### `Halt ≤_m MPCP` (backward) — canonical iff complete

The backward direction inverts the forward construction in two layers.

**Strong-A form** (`halt_le_mpcp_strong`): handles `A ⊆ haltTiles tm` via
strong induction on `A.length`, peeling one canonical "block" off the
front of `A` per TM step.

| Lemma                                  | Role                                             |
|----------------------------------------|--------------------------------------------------|
| `mem_haltTiles_top`                    | Identify each tile in `haltTiles` by its constructor |
| `copy_prefix_forced`                   | Force `copyTile`s on a `liftTape`-prefix         |
| `transition_forced`                    | Force the transition tile after a state marker   |
| `copy_prefix_forced_state_lead`        | Strip copies up to a state marker (non-left)     |
| `sep_forced`                           | Force `sepTile` when the lead is `#`             |
| `no_tile_for_state_sharp`              | Rule out `↟ₛq :: # :: …` lookaheads             |
| `starts_with_stepTilesNoMove`          | Backward step, no-move                           |
| `starts_with_stepTilesRightInterior`   | Backward step, right-move, `t.right ≠ []`        |
| `starts_with_stepTilesRightBoundary`   | Backward step, right-move, `t.right = []`        |
| `starts_with_stepTilesLeftInterior`    | Backward step, left-move, `t.left ≠ []`          |
| `backward_aux`                         | Main strong-induction driver (strong hypothesis) |
| `halt_le_mpcp_strong`                  | Strong-A top-level theorem                       |

The left-boundary sub-case is *removed* by the HUM refactor: the
`NoLeftBoundary` constraint ensures no reachable cfg ever invokes a
left-move at the left boundary, so no corresponding sub-lemma is needed.
The halt-now sub-case in `backward_aux` is handled directly (single TM
step to a halted cfg, then `ReflTransGen.refl`) — this sidesteps the
need for a `starts_with_absorbAndFinish` lemma, which would otherwise
fail because the absorption-phase decomposition is non-unique.

**Canonical form** (`halt_le_mpcp`): handles `A ⊆ startTile :: haltTiles tm`
via `backward_aux_weak`, which threads a chain-tracked cfg queue
`List (Σ' c, ReflTransGen ... initCfg c)`. When `startTile` appears
mid-stream in `A`, it pushes an extra `initCfg` (with a `refl` chain)
onto the queue, alongside the natural `stepResult` advancement. The
right-boundary alternative `rightMoveTile` path is ruled out by
`tau1_no_state_marker_then_sharp`, a structural property showing that
`tau1 A` never contains `↟ₛq :: # :: …` as a sublist.

### `Halt ≤_m PCP` — `PCP/Reductions/HaltToPCP.lean`

```lean
theorem halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm)) :=
  (halt_le_mpcp tm h_nbw w h_nlb).trans (mpcp_iff_pcp _ _)
```

### `PCP ≤_m CFG-Intersection-Nonempty` — `CFG/PcpReduction.lean`

For each tile `t ∈ P`, build two rules over alphabet `α ⊕ Tile α`:

| Grammar  | Recursive rule                       | Base rule               |
|----------|--------------------------------------|-------------------------|
| `topCFG` | `S → t.top.inl ++ S ++ [.inr t]`     | `S → t.top.inl ++ [.inr t]` |
| `botCFG` | `S → t.bot.inl ++ S ++ [.inr t]`     | `S → t.bot.inl ++ [.inr t]` |

A derivation traces a tile sequence `[t₁, …, t_k]` and emits
`(tau_proj A).map .inl ++ A.reverse.map .inr`. The reverse order of
markers forces both grammars to commit to the same sequence; the
`.inl`/`.inr` alphabet split lets us recover the PCP witness uniquely
via `list_inl_inr_split`.

```lean
theorem hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔
    ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

### `Halt.Diagonal` — the kernel of the halting-problem proof

Model-independent diagonalisation, no Turing machines:

```lean
theorem cantor_diag (f : α → α → Bool) :
    ∃ g : α → Bool, ∀ a, g ≠ f a

theorem not_surjective_cantor (f : α → α → Bool) :
    ¬ Function.Surjective f

theorem halt_diag_contradiction (H : α → α → Bool)
    (d : α) (hd : (! H d d) = H d d) : False
```

The last theorem is the purely logical heart of the standard halting
argument: any `H : α → α → Bool` admitting a `d` with `! H d d = H d d`
collapses to `False`. Producing the witness `d` for a concrete
computation model is the substantive work of `Halt/` Phases 2–4.

### `Halt.TMCode` — Phase 1 of the universal-TM construction

A normalised TM record (`Bool` alphabet, `Fin (numStates + 1)` states,
explicit transition table) with an interpretation function
`tmCodeToTM : TMCode → SingleTapeTM Bool`. This is the canonical
representation that a universal `SingleTapeTM` will eventually
consume off its input tape.

## Next steps

1. **Phase 2 of `Halt/`** — Gödel numbering of `TMCode` as `List Bool`.
2. **Phase 3 of `Halt/`** — universal `SingleTapeTM` (the bulk of the
   work, ~2000–4000 LoC).
3. **Phase 4 of `Halt/`** — self-application diagonal closing
   `halt_undecidable`.
4. **HUM normalisation** — separate workstream, lifts the side
   conditions to a generic TM.

Once 1–3 land, the iff chain `Halt ≤_m MPCP ≤_m PCP ≤_m CFG-int` immediately yields
concrete undecidability theorems for both PCP and CFG-intersection-emptiness.

See `Halt/ROADMAP.md` and `ROADMAP.md` for full dependency trees.
