# Halt — retrospective and construction notes

The halting-problem undecidability proof for cslib's
`Turing.SingleTapeTM Bool`, completed in this directory. This document
records the construction; for the top-level chain see [`../README.md`](../README.md).

## What is proved

```lean
theorem halt_undecidable :
    ¬ ∃ D : SingleTapeTM Bool, IsSelfHaltDecider D
```

— there is no `SingleTapeTM Bool` `D` that decides the self-halt
problem `K = { c : TMCode | c.toTM halts on encodeTMCode c }` by
emitting `[true]` / `[false]` on its output tape.

## Module layout

| Module           | Role                                                                 |
|------------------|----------------------------------------------------------------------|
| `Halt.Diagonal`  | Model-independent diagonal kernel (Cantor + abstract contradiction). |
| `Halt.Basic`     | The three decider predicates: `HaltDecidable`, `IsHaltDecider`, `IsSelfHaltDecider`. |
| `Halt.TMCode`    | Normalised TM record (alphabet `Bool`, state set `Fin (n + 1)`). |
| `Halt.Encoding`  | Bit-encoding `encodeTMCode : TMCode → List Bool` with round-trip lemmas. |
| `Halt.Pair`      | Pair encoding `encodePair u v` (used by `IsHaltDecider`).            |
| `Halt.Helpers`   | Worked example: `invertTM`, a 2-state TM that halts on `[false]` and loops on `[true]`. (Not on the proof-chain critical path.) |
| `Halt.CodeOf`    | Generic `codeOf : SingleTapeTM Bool → TMCode` with the bisim theorem `halts_codeOf_iff`. |
| `Halt.Undecidable` | Inlined diagonal TM `diagTM D` and the final `halt_undecidable`. |

## Proof outline

The proof targets the *self-halt* form `K` (single-input decider)
rather than the pair-form `HALT_TM` (two-input decider). This lets us
sidestep a separate "input duplicator" TM: the decider's input is just
`encodeTMCode c`, so the diagonal applies `c` to itself by construction.

### Step 1 — the diagonal TM

For any assumed decider `D`, build `diagTM D : SingleTapeTM Bool` with
state space `D.State ⊕ DiagPost`, where `DiagPost = {reading, loop}`:

* `.inl q` states behave exactly like `D` in state `q`.
* When `D` would halt (`D.tr q a = (stmt, none)`), `diagTM` transitions
  to `.inr reading` instead.
* `.inr reading` inspects the current head symbol: `some true` → loop
  forever (`.inr loop`); `some false` (or blank) → halt.
* `.inr loop` is a sink — every transition stays in `.inr loop`.

### Step 2 — lifting `D`'s traces

`liftCfg : D.Cfg → (diagTM D).Cfg` sends `D`-running cfgs into `.inl`
and the `D`-halt cfg `⟨none, t⟩` into the seam `⟨some (.inr reading), t⟩`.
`step_liftCfg` verifies that one `D`-step commutes; `trace_liftCfg`
extends this to `ReflTransGen` via `Relation.ReflTransGen.lift`.

### Step 3 — the two behaviour lemmas

* **`diagTM_halts_of_outputs_false`**: backward direction. Lift `D`'s
  `[false]`-output trace to a `diagTM` trace ending at
  `⟨some (.inr reading), mk₁ [false]⟩`. One more step lands in
  `⟨none, _⟩`. Halts.

* **`diagTM_loops_of_outputs_true`**: forward direction. Lift `D`'s
  `[true]`-output trace, take one step into `.inr loop`. The
  `loop_persistent` invariant says every reachable cfg from there is
  in `.inr loop`. The assumed halt trace `(initCfg) →* ⟨none, _⟩`
  and the lifted-into-loop trace share their start point, so by
  *deterministic confluence* (`reflTransGen_diamond`) one extends
  the other. `loop_persistent` rules out the only viable case.

### Step 4 — the diagonal contradiction

`c_diag := codeOf (diagTM D)`. Apply `IsSelfHaltDecider D` at `c_diag`:

* If `c_diag.toTM` halts on `encodeTMCode c_diag`, then `D` outputs
  `[true]` (by the decider's spec) and `diagTM D` also halts (by
  `halts_codeOf_iff`) — contradicting `diagTM_loops_of_outputs_true`.
* If `c_diag.toTM` does not halt, then `D` outputs `[false]` and
  `diagTM D` halts (by `diagTM_halts_of_outputs_false`) — but then
  `halts_codeOf_iff` says `c_diag.toTM` halts. Contradiction.

## Scope

| Module             | LoC  |
|--------------------|------|
| `Halt.Diagonal`    | ~120 |
| `Halt.Basic`       | ~95  |
| `Halt.TMCode`      | ~80  |
| `Halt.Encoding`    | ~400 |
| `Halt.Pair`        | ~55  |
| `Halt.Helpers`     | ~145 |
| `Halt.CodeOf`      | ~220 |
| `Halt.Undecidable` | ~310 |
| **Total**          | **~1425** |

For comparison, a textbook universal-TM construction (which would
generalise to pair-form `HALT_TM` directly) is typically estimated at
2000–4000 LoC.

## Rice's theorem — in progress

Files under [`Rice/`](Rice/):

* `Rice.Basic` ✅ — definitions: `SemHalt`, `BehaviourEquiv`,
  `IsSemantic`, `IsPropDecider`, `NonTrivial`, and the semantic-set
  re-packaging (`BehaviourClassProp`, `liftClassProp`).
* `Rice.TrivialTMs` ✅ — concrete witnesses `tm_alwaysHalt` (halts on
  every input) and `tm_loop` (loops on every input), with
  `SemHalt = univ` and `SemHalt = ∅` respectively.
* `Rice.Extender` ✅ — the *constant-Sem* reduction TM
  `riceConstTM : TMCode → SingleTapeTM Bool`. The construction is
  four-phase: erase the input, write `encodeTMCode c` past the erased
  region, move the head back to the start of the written code, then
  simulate `c.toTM`. After the move-back phase, the layout is
  isomorphic (via position offset) to `initCfg c.toTM (encodeTMCode c)`,
  so the simulation phase is behaviourally identical to running
  `c.toTM` on `encodeTMCode c`.

  *Construction is complete; the behaviour theorem*

      `SemHalt (riceConstTM c) = univ ↔ Halts c.toTM (encodeTMCode c)`

  *requires a four-phase bisimulation argument and is the next chunk.*

* `Rice.Theorem` 🚧 — once the behaviour theorem is established,
  *Restricted Rice* (Rice for properties that distinguish
  `tm_alwaysHalt` from `tm_loop`) follows by reducing K-decidability
  to `IsPropDecider`-decidability via `riceConstTM`. Concrete
  corollaries: "halts on `[]`", "halts on at least one input",
  "halts on all inputs", "halts on no inputs", etc. — all undecidable.
  Full Rice (arbitrary semantic witnesses) needs an
  *input-preserving* extender (a more elaborate construction with
  scratch space).

## Other deferred items

* **`HALT_TM` (pair-form) undecidability.** Follows from
  `halt_undecidable` via `K ≤_m HALT_TM` (a small `dupTM`-style
  reduction). Not pursued here; would extend `IsHaltDecider`'s
  treatment.
* **Pointwise `trToList` lookup lemma** in `Halt.Encoding`. Needed for
  the full left-inverse `decodeTMCode (encodeTMCode c) = some c`. The
  current proof uses `encodeTMCode` only as an injection; the round-trip
  follows once the lookup is closed.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings, same as the rest of the project.
