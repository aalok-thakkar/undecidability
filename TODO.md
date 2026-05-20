# DiagonaLean — TODO

Prioritised work plan. Items tagged **P0** (blocker / load-bearing),
**P1** (next deliverable), **P2** (after P1), **P3** (nice-to-have).

For the project vision see [`README.md`](README.md); for completed
proofs see [`ROADMAP.md`](ROADMAP.md).

---

## Current status

**Phase 1 (framework) + Phase 2 (canonical problems): functionally
landed.** 13 edges registered in the reduction graph; 13 examples
closed via `by reduce_diag` in [`Reduction/Smoke.lean`](Reduction/Smoke.lean).
The full TM-undecidability chain from `halt_undecidable` to
`EncodedCFGI_LB.predicate` and `HaltsOnEverything.predicate` is
operational.

The remaining work is **discharging postulates** to make the
framework's claims fully grounded in cslib's TM model, plus extending
the Phase 3 reduction library.

---

## Postulates to discharge

Listed by impact: discharging earlier items removes the most "magic"
from the framework.

### Substantive mathematical content (~1000+ LoC each)

* [ ] **P1** `normalisingWrapper` in [`Halt/Normalise.lean`](Halt/Normalise.lean).
  The HUM 2-bit alphabet shift: build a `wrap : (TMCode, w) ↦ (TMCode', w')`
  function in Lean satisfying `NoBlankWrites c'.toTM`, `NoLeftBoundary
  c'.toTM w'`, and `Halts c.toTM w ↔ Halts c'.toTM w'`. Standard textbook
  construction (sentinel marker + synthetic blank). ~1000-1500 LoC by
  analogy with `PCP/Reductions/HaltToMPCP.lean`.
* [ ] **P1** `semHalt_riceConstTM_dichotomy` in [`Halt/Rice/Theorem.lean`](Halt/Rice/Theorem.lean).
  Four-phase bisimulation of the Rice extender (erase / write /
  move-back / simulate). ~1000 LoC.

### TM-composition machinery — ✅ DISCHARGED

`TMComputable` is now `Nonempty (TimeComputable f)` over cslib's
`SingleTapeTM.TimeComputable`. cslib ships `TimeComputable.id` and
`TimeComputable.comp`, so:

* [x] **P1** `TMComputable.id` — proved from `TimeComputable.id`. ✅
* [x] **P1** `TMComputable.comp` — proved from `TimeComputable.comp`
  (cslib's `comp` needs a monotone time bound; `monotoniseTC` upgrades
  any `TimeComputable` to one whose bound is the running supremum). ✅
* [x] **P1** `TMUndecidable.of_TMReduction` — proved:
  `boolIndicator pred₁ = boolIndicator pred₂ ∘ f` (from the reduction
  iff), then `TMComputable.comp`. ✅

### Per-edge `TMComputable` witnesses (remaining TM-bookkeeping)

* [x] **P2** `encodedPCP_LB_to_encodedCFGI_LB_TMComputable` — proved
  (`= TMComputable.id`, the edge's `f` is `id`). ✅
* [ ] **P2** Discharge the remaining 5 per-edge `<edgeName>_TMComputable`
  witnesses (`encodedSelfHalt_to_encodedHalt`,
  `encodedHalt_to_encodedHaltMPCP`, `encodedHaltMPCP_to_encodedMPCP_LB`,
  `encodedMPCP_LB_to_encodedPCP_LB`,
  `canonicalSelfHalt_to_haltsOnEverything`). Each is now honestly typed
  as `Nonempty (TimeComputable f)` for a *genuinely computable* `f`
  (see soundness fix below) — requires building the explicit TM for a
  specific Lean function. Tedious but mechanical; the cslib
  `idComputer`/`compComputer` primitives plus per-operation TMs
  (bit-copy, length-prefix, etc.) suffice.

### Soundness fix (landed)

* [x] **P0** `EncodedHaltMPCP` no longer bakes `NoBlankWrites ∧
  NoLeftBoundary` into its predicate. The old design forced
  `encodedHaltMPCP_to_mpcpLB.f` to branch on the *undecidable*
  `NoLeftBoundary`, making the function non-computable and its
  `TMComputable` witness a false axiom. Fixed: the predicate is now the
  bare `MHasSolution` of the HMU instance; the side conditions are
  discharged on the `EncodedHalt ≤ₘ EncodedHaltMPCP` edge from the
  normalising wrapper's proof fields. No reduction branches on anything
  undecidable. ✅

---

## Phase 1 — Framework polish

The framework MVP is landed. Remaining items are polish.

* [ ] **P2** `TuringReduction` (oracle-machine notion). Phase 3
  prerequisite. ~100 LoC.
* [ ] **P2** Polymorphic edges in `composeReductions`
  (`Reduction/Tactic.lean`). Currently throws on edges with
  unresolved binders (e.g. `mpcpToPcp α`). Thread metavariables
  from search through composition.
* [ ] **P2** Better tactic ergonomics:
  * `by reduce_diag via mpcpToPcp` — user hint to force a specific edge.
  * Helpful errors when no path is found.
  * `#diagonalean_graph` command to print the registered graph.
* [ ] **P3** Visualisation export (dot/graphviz from the registered
  graph).
* [ ] **P3** Documentation generator (per-node summary card).

---

## Phase 2 — Remaining canonical problems

* [ ] **P1** **TM acceptance (ATM)**. Define `Accepts tm w` (variant
  of `Halts` distinguishing accept/reject; in cslib's model with a
  single halt state this collapses to `Halts` — decide on the right
  formulation). Prove `Halt ≤_m ATM`. ~200 LoC.
* [ ] **P1** **HALT_TM** (pair-form) via `K ≤_m HALT_TM`. ~200 LoC.
* [ ] **P2** **General-alphabet halting**: generalise to
  `SingleTapeTM Symbol` for arbitrary `[Fintype Symbol]` with
  `|Symbol| ≥ 2` via a binary-encoding simulation. ~400–600 LoC.
* [ ] **P2** **CFG universality** is undecidable. Reduces from PCP:
  build a CFG whose language is the complement of "well-formed PCP
  witness encodings". ~400 LoC.
* [ ] **P2** **CFG equivalence** is undecidable. Follows from
  universality.
* [ ] **P2** **CFG ambiguity** is undecidable. Separate PCP reduction.

---

## Phase 3 — Standard reduction library

The Phase 3 target: a comprehensive, textbook-aligned reduction graph
where every node is a certified formal object and every edge is a
machine-checked reduction. ~2000-5000 LoC.

### From HMU (Hopcroft–Motwani–Ullman)

* [ ] **P2** **Rice's theorem** (general non-trivial semantic). The
  restricted form (distinguishes `univ` from `∅`) is landed. The
  general form requires the index-set reduction generalisation. ~300 LoC.
* [ ] **P2** Rice's theorem corollaries: emptiness, finiteness,
  regular language emptiness, total function-ness.
* [ ] **P2** **Linear bounded automaton (LBA) universality** is
  undecidable.
* [ ] **P3** **Two-counter machine halting** via Minsky-style
  encoding.

### From Rogers (Theory of Recursive Functions)

* [ ] **P3** **Index set theorem** — every non-trivial index set is
  recursively enumerable iff its complement is. Implies Rice.
* [ ] **P3** **Recursion theorem** (Kleene's second).
* [ ] **P3** **Productive / creative set machinery**.

### From Soare (Computability and Complexity)

* [ ] **P3** **Friedberg–Muchnik theorem** (existence of
  incomparable r.e. degrees). Major undertaking.

### Wang tilings / domino problem

* [ ] **P3** **Wang tiling undecidability** via PCP. ~500 LoC.

---

## Cross-cutting infrastructure

* [x] **P0** Encoded `List Bool`-input variants of all problems.
  ✅ in `Reduction/Encoded*.lean`, `Reduction/StackEncoding.lean`,
  `Reduction/EncodedLB.lean`.
* [x] **P0** TM-level `TMDecidable`/`TMUndecidable`/`TMComputable`
  notions. ✅ in `Reduction/TMDecidable.lean`.
* [x] **P0** Bridge from cslib's `halt_undecidable` to the framework's
  TM-undecidability. ✅ in `Reduction/HaltUndecidable.lean`.
* [x] **P0** HUM-normalisation reduction `EncodedHalt → EncodedHaltMPCP`.
  ✅ in `Reduction/EncodedHaltNormalised.lean` (with postulated
  `normalisingWrapper`).
* [ ] **P2** `decodeTMCode` left-inverse completion (currently we have
  the round-trip but not full injectivity proof).
* [ ] **P3** Computability hierarchy: `Decidable < r.e. < arithmetical
  hierarchy` machinery, for Phase 3 corollaries.

---

## Documentation / outreach

* [x] **P1** Update README.md, ROADMAP.md, TODO.md to reflect current
  state. ✅
* [ ] **P2** Per-module docstrings consistent (most exist; review for
  completeness).
* [ ] **P2** Worked example walkthrough: take a concrete undecidability
  claim and trace it through the chain step-by-step.
* [ ] **P3** Blog post / preprint describing the framework.

---

## Engineering polish

* [ ] **P2** CI workflow (GitHub Actions) running `lake build` on
  push.
* [ ] **P2** Per-PR build matrix verifying no `sorry` and no warnings.
* [ ] **P3** Linter configuration (no unused imports / arguments /
  simp args).

---

## Convention

Every commit keeps `lake build` clean with **no `sorry`** and no
warnings. Postulates (`axiom`) are catalogued in `README.md` and
documented at their introduction site.
