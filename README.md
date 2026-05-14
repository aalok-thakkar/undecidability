# Undecidability

A Lean 4 formalisation of three classical undecidability results,
linked by reductions, all built on top of cslib's
[`Turing.SingleTapeTM`](https://github.com/leanprover/cslib):

| Library | Top-level theorem | Status |
|---|---|---|
| **[`Halt/`](Halt/)** | `halt_undecidable : ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D` | ✅ complete |
| **[`PCP/`](PCP/)** | `halts_iff_pcp : Halts tm w ↔ HasSolution (mpcpToPcp …)` | ✅ complete |
| **[`CFG/`](CFG/)** | `hasSolution_iff_intersectionNonempty : HasSolution P ↔ ∃ w, w ∈ L(topCFG) ∩ L(botCFG)` | ✅ complete |

The proof contains **no `sorry`** anywhere and is verified against
`leanprover/lean4:v4.29.0-rc4` (see [`lean-toolchain`](lean-toolchain)
and [`lake-manifest.json`](lake-manifest.json)).
`lake build` is clean (2208 jobs, no warnings).

## What this proves

Composing the three modules, this repository proves:

1. **The halting problem is undecidable for cslib's `SingleTapeTM Bool`**:
   no TM `D` over `Bool` decides whether a TM-code `c` halts on its own
   description.

2. **PCP is undecidable** (under the HUM side conditions
   `NoBlankWrites` and `NoLeftBoundary`): there is no algorithm deciding
   whether a finite Post Correspondence Problem instance has a solution.

3. **The CFG-intersection-emptiness problem is undecidable** (same
   side conditions, composed through PCP): there is no algorithm
   deciding, given two context-free grammars `G₁`, `G₂`, whether
   `L(G₁) ∩ L(G₂)` is empty.

Statements (2) and (3) are conditional on lifting the HUM side
conditions to a fully general TM, which is left as future work.

## The headline theorems

```lean
theorem Halt.halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D

theorem PCP.halts_iff_pcp (tm : SingleTapeTM Symbol) (w : List Symbol)
    (h_nbw : NoBlankWrites tm) (h_nlb : NoLeftBoundary tm w) :
    Halts tm w ↔
    HasSolution (mpcpToPcp (startTile tm w) (haltTiles tm))

theorem CFG.hasSolution_iff_intersectionNonempty (P : Stack α) :
    HasSolution P ↔
    ∃ w, w ∈ (topCFG P).language ∧ w ∈ (botCFG P).language
```

## Project layout

```
PCP/                   ← Halt ≤_m MPCP ≤_m PCP chain
  Basic.lean           -- core types: Word, Tile, Stack; HasSolution
  MPCP.lean            -- the MPCP variant: MHasSolution
  Reduction.lean       -- MPCP ≤_m PCP: full mpcp_iff_pcp
  Halt.lean            -- the Halts predicate for SingleTapeTM
  Reductions/
    HaltToMPCP.lean    -- Halt ≤_m MPCP construction + proofs
    HaltToPCP.lean     -- halts_iff_pcp by composition

CFG/                   ← PCP ≤_m CFG-Intersection-Nonempty
  Basic.lean           -- IntersectionEmpty / IntersectionNonempty
  PcpReduction.lean    -- the full reduction iff

Halt/                  ← halting-problem undecidability
  Diagonal.lean        -- Cantor + abstract halting contradiction
  Basic.lean           -- decider predicates: HaltDecidable,
                          IsHaltDecider, IsSelfHaltDecider
  TMCode.lean          -- normalised TM rep (Bool, Fin (n+1) states)
  Encoding.lean        -- Gödel numbering: encodeTMCode
  Pair.lean            -- pair encoding: encodePair
  Helpers.lean         -- worked example: invertTM
  CodeOf.lean          -- generic SingleTapeTM Bool → TMCode embedding
  Undecidable.lean     -- the final halt_undecidable theorem
  ROADMAP.md           -- detailed construction notes

PCP.lean / CFG.lean / Halt.lean  -- library roots
Main.lean                         -- executable entry point
ROADMAP.md                        -- reduction-chain architecture
```

## Conventions

The `Halt ≤_m MPCP` reduction follows the **Hopcroft–Ullman–Motwani
one-sided-tape design**: the simulation tile set does not include a
`leftMoveBoundaryTile`, and the TM is required to satisfy
`NoLeftBoundary` (no left-move at the left tape boundary) in addition
to the standard `NoBlankWrites` (no blank symbol written).

The development uses [`cslib`](https://github.com/leanprover/cslib)'s
`Turing.SingleTapeTM` for the Turing-machine machinery and follows
cslib's conventions (module-style headers, `public import`,
`@[expose] public section`). The CFG module uses Mathlib's
`ContextFreeGrammar`.

## Building

```sh
lake build
```

builds the three libraries (`PCP`, `CFG`, `Halt`) and the `pcp`
executable. Cold-cache build (including Mathlib) takes ~20–40 minutes;
incremental builds are seconds.

## What is proved (in detail)

### `MPCP ≤_m PCP` — `PCP/Reduction.lean`

The full `mpcp_iff_pcp` equivalence via the Hopcroft–Ullman
construction: extend the alphabet with `⋕`-prefixed hash symbols,
interleave tile top/bot words, produce a `tileStart`/`tileReg`/`tileEnd`
triple, and prove `match_start` (any solution must begin with the
start tile) plus the complete forward and backward directions.

### `Halt ≤_m MPCP` (forward) — `PCP/Reductions/HaltToMPCP.lean`

Given `Halts tm w` together with the two side conditions
`NoBlankWrites` and `NoLeftBoundary`, constructs a tile sequence
`A ⊆ startTile :: haltTiles tm` satisfying the MPCP matching equation.
The proof:

1. Prepends `stepTiles tm q tape` for each TM step, dispatching over
   transition direction × tape-boundary status:

   | Case             | Tiles used                                         |
   |------------------|----------------------------------------------------|
   | No move          | `left-copies · noMoveTile · right-copies · sep`    |
   | Right (interior) | `left-copies · rightMoveTile · right-copies · sep` |
   | Right (boundary) | `left-copies · rightMoveBoundaryTile`              |
   | Left (interior)  | `tail-copies · leftMoveTile · right-copies · sep`  |

   The left-boundary case is unreachable under `NoLeftBoundary`.

2. Closes with `absorbAndFinish` once the TM halts: iteratively absorbs
   tape symbols via `absorbLeftTile`/`absorbRightTile`, then applies
   `finalTile` to equalise top and bot.

Top-level lemma: `halts_implies_mhasSolution`.

### `Halt ≤_m MPCP` (backward) — canonical iff

The backward direction inverts the forward construction in two layers.

**Strong-A form** (`halt_le_mpcp_strong`): handles
`A ⊆ haltTiles tm` via strong induction on `A.length`, peeling one
canonical "block" off the front of `A` per TM step. Per-tile forcing
lemmas (`copy_prefix_forced`, `transition_forced`, `sep_forced`, etc.)
identify each tile uniquely from its top character.

**Canonical form** (`halt_le_mpcp`): handles
`A ⊆ startTile :: haltTiles tm` via `backward_aux_weak`, which threads
a chain-tracked cfg queue. When `startTile` appears mid-stream in `A`,
it pushes an extra `initCfg` onto the queue alongside the natural
`stepResult` advancement.

The halt-now sub-case is handled directly (a single TM step to a
halted cfg, then `ReflTransGen.refl`) — this sidesteps the need for a
`starts_with_absorbAndFinish` lemma, which would otherwise fail
because the absorption-phase decomposition is non-unique.

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

| Grammar  | Recursive rule                       | Base rule                   |
|----------|--------------------------------------|-----------------------------|
| `topCFG` | `S → t.top.inl ++ S ++ [.inr t]`     | `S → t.top.inl ++ [.inr t]` |
| `botCFG` | `S → t.bot.inl ++ S ++ [.inr t]`     | `S → t.bot.inl ++ [.inr t]` |

A derivation traces a tile sequence `[t₁, …, t_k]` and emits
`(tau_proj A).map .inl ++ A.reverse.map .inr`. The reverse order of
markers forces both grammars to commit to the same sequence; the
`.inl`/`.inr` alphabet split lets us recover the PCP witness uniquely
via `list_inl_inr_split`.

### Halting-problem undecidability — `Halt/Undecidable.lean`

```lean
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```

For any putative decider `D`, build `diagTM D` (state space
`D.State ⊕ DiagPost`, where `DiagPost = {reading, loop}`): simulate
`D` until it would halt, then transition to `reading`. From
`reading`, head `some true` → `loop` (which is closed under stepping);
otherwise → halt.

Let `c_diag := codeOf (diagTM D)`. By `Halt.CodeOf.halts_codeOf_iff`,
`c_diag.toTM` halts on `encodeTMCode c_diag` iff `diagTM D` does.
Applying `IsSelfHaltDecider D` at `c_diag` and case-splitting yields a
contradiction in both branches — the "loop" case via deterministic
confluence on `ReflTransGen` plus a loop-state invariant.

See [`Halt/ROADMAP.md`](Halt/ROADMAP.md) for the full construction.

## What's deferred

Two follow-ups would tighten the headline statements but don't change
what is proved. See [`ROADMAP.md`](ROADMAP.md):

1. **HUM normalisation** — removes the `NoBlankWrites` /
   `NoLeftBoundary` side conditions from `halts_iff_pcp`.
2. **HALT_TM (pair-form) undecidability** — extends `halt_undecidable`
   from the self-halt problem `K` to the pair-input form via
   `K ≤_m HALT_TM`.

## License

Apache 2.0. See [`LICENSE`](LICENSE) (if present) or the file headers.
