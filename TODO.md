# DiagonaLean — TODO

Prioritised work plan for the three phases of the project. Items are
tagged **P0** (blocker / load-bearing), **P1** (next deliverable),
**P2** (after P1 lands), **P3** (nice-to-have, defer).

For the project vision see [`README.md`](README.md); for completed
proofs see [`ROADMAP.md`](ROADMAP.md).

---

## Immediate next chunk

Phase 1 framework MVP is **landed**. The next high-leverage item is
either (a) wrap the remaining existing iffs as reductions, which is
gated by an alphabet-uniformity issue (see "Cross-cutting" below),
or (b) finish Rice's theorem (independent of the framework gap).

* [x] **P0** `Reduction/Basic.lean` — `Problem`, `ManyOneReduction`,
  `Decidable`, `Undecidable`. ✅
* [x] **P0** `Reduction/Composition.lean` — `.id`, `.trans`,
  identity/assoc lemmas, `ofInverse`. ✅
* [x] **P0** `Reduction/Transfer.lean` — `Decidable.of_manyOne` and
  `Undecidable.of_manyOne`. ✅
* [x] **P0** `Reduction/Notation.lean` — `≤ₘ`, `≡ₘ`. ✅
* [x] **P1** Re-package existing iffs as `ManyOneReduction` instances:
  * `mpcp_iff_pcp` → `Reductions.mpcpToPcp : MPCP α ≤ₘ PCP (Ext α)`. ✅
  * `halts_codeOf_iff` → `Reductions.haltTM_to_haltTMCode`. ✅
  * **Pending — alphabet uniformity issue**:
    * `halt_le_mpcp` — destination alphabet `Alpha tm.State Symbol`
      depends on input, so no single fixed `Problem` node fits. Needs
      either a uniform `List Bool`-encoded MPCP variant, or a notion
      of "indexed problem family" in the framework.
    * `halts_iff_pcp` — same blocker (it's `halt_le_mpcp` composed
      with `mpcpToPcp`).
    * `hasSolution_iff_intersectionNonempty` — destination CFGs over
      alphabet `α ⊕ Tile α`. Same flavour of issue.
* [ ] **P1** Finish Rice's theorem expressed in the new framework:
  * `Halt/Rice/Theorem.lean` — `SemHalt (riceConstTM c) = univ ↔ Halts
    c.toTM (encodeTMCode c)` (four-phase bisimulation, ~400–600 LoC).
  * Restricted Rice as `ManyOneReduction K P` for any non-trivial
    `P` distinguishing `univ` from `∅` Sem.
  * Concrete corollaries: "halts on `[]`", "halts on some input",
    "halts on every input", "halts on no input".
* [ ] **P1** Address the alphabet-uniformity issue. Two options:
  * (a) Define `EncodedPCP` and `EncodedCFGIntersection` over a fixed
    alphabet (`List Bool`) by encoding inputs.
  * (b) Extend the framework with `IndexedProblem` (problem families
    parameterised by an index, with reductions between families).

---

## Phase 1 — Core framework

Definitions, composition laws, transfer theorems, notation, tactic.

* [ ] **P0** `Problem` record (Input type + predicate).
* [ ] **P0** `ManyOneReduction P₁ P₂` (function `f`, computability
  witness, spec `∀ x, P₁.pred x ↔ P₂.pred (f x)`).
* [ ] **P0** `TuringReduction P₁ P₂` (oracle-machine notion: a TM that
  decides `P₁` given an oracle for `P₂`).
* [ ] **P0** Composition laws:
  * `ManyOneReduction.trans : MOR P Q → MOR Q R → MOR P R`.
  * `TuringReduction.trans : TR P Q → TR Q R → TR P R`.
  * Identity reductions.
* [ ] **P0** Transfer theorems:
  * `Undecidable P → ManyOneReduction P Q → Undecidable Q`.
  * Contrapositive: `Decidable Q → MOR P Q → Decidable P`.
  * Same for `TuringReduction`.
* [ ] **P1** Public notation: `P ≤ₘ Q`, `P ≤ᵀ Q`, `P ≡ₘ Q`, etc.
* [ ] **P1** `Undecidable` predicate definition + basic lemmas.
* [ ] **P1** Connection to cslib's `IsSelfHaltDecider`-style strict
  deciders (so the existing `halt_undecidable` is a witness of
  `Undecidable Halt`).
* [ ] **P2** `@[reduction_graph]` attribute. Metaprogramming to scan a
  `ManyOneReduction P Q` declaration and register the edge.
* [ ] **P2** `by reduce` / `by reduce_to <node>` tactic. Searches the
  registered graph for a path from the goal node to a known-undecidable
  node and emits the composed reduction.
* [ ] **P2** Termination/loop-detection in the search (the graph is
  acyclic by construction for many-one reductions modulo equivalence).
* [ ] **P3** Visualisation export (dot/graphviz from the registered
  graph).
* [ ] **P3** Documentation generator (per-node summary card).

---

## Phase 2 — Canonical base problems

Self-contained undecidability proofs for the "anchor" nodes.

### Halting problem

* [x] `Halt.halt_undecidable` (for `SingleTapeTM Bool`, self-halt
  form). ✅
* [ ] **P1** Wrap as `Undecidable Halt` in the framework.
* [ ] **P2** `HALT_TM` (pair-form) via `K ≤_m HALT_TM` (a small
  `dupTM`-style construction). ~200 LoC.
* [ ] **P2** Generalise to `SingleTapeTM Symbol` for arbitrary
  `[Fintype Symbol]` with `|Symbol| ≥ 2` via a binary-encoding
  simulation. ~400–600 LoC.

### TM acceptance (ATM)

* [ ] **P1** Define `Accepts tm w` (variant of `Halts` that
  distinguishes accept/reject states; in cslib's model with a single
  halt state, this collapses to `Halts` — decide on the right
  formulation).
* [ ] **P1** `Halt ≤_m ATM`. Trivial if `Accepts = Halts`; otherwise
  via a per-step state-marking simulation.

### Post Correspondence Problem

* [x] `mpcp_iff_pcp` (`MPCP ≤_m PCP` and back). ✅
* [x] `halt_le_mpcp` (`Halt ≤_m MPCP` under HUM). ✅
* [x] `halts_iff_pcp` (`Halt ≤_m PCP` under HUM, by composition). ✅
* [ ] **P2** **HUM normalisation** — lift the `NoBlankWrites` and
  `NoLeftBoundary` side conditions. Standard sentinel-shift
  construction. ~500–1000 LoC.
* [ ] **P1** Wrap all three as `ManyOneReduction`s.

### Language-theoretic problems

* [x] `hasSolution_iff_intersectionNonempty` (CFG-intersection-nonempty).
  ✅
* [ ] **P1** Wrap as `ManyOneReduction PCP CFGIntersection`.
* [ ] **P1** **CFG universality** is undecidable. Reduces from PCP:
  build a CFG whose language is the complement of "well-formed PCP
  witness encodings". Estimated ~400 LoC.
* [ ] **P2** **CFG equivalence** is undecidable. Follows from
  universality.
* [ ] **P2** **CFG ambiguity** is undecidable. Separate PCP reduction.

### Encoding infrastructure

* [x] `TMCode` normalised TM rep. ✅
* [x] `encodeTMCode` Gödel numbering. ✅
* [x] `codeOf` generic state-renaming + bisim. ✅
* [ ] **P2** Pointwise `trToList` lookup lemma in `Halt.Encoding`
  (needed for full injectivity of `decodeTMCode`).

---

## Phase 3 — Standard reduction library

Mechanise textbook results. Each entry is a registered edge in the
reduction graph.

### From HMU (Hopcroft–Motwani–Ullman)

* [ ] **P1** **Rice's theorem** (full form, semantic predicate). Needs
  an *input-preserving* extender on top of the current `riceConstTM`.
  ~500–700 LoC.
* [ ] **P2** Rice's theorem corollaries: emptiness, finiteness,
  regularity, equivalence with a fixed TM — each as a one-line
  application of full Rice.
* [ ] **P2** **PCP variants**: 2-counter machine halting; tag
  systems; integer linear programming in ℤ (Hilbert 10th, but easier
  forms first).
* [ ] **P2** **Reachability for queue machines / counter automata**.
* [ ] **P3** **Halting for Minsky 2-counter machines** ≤_m Halt.
  Classical reduction, ~600 LoC.

### From Rogers

* [ ] **P2** **Recursion theorem** (Kleene's fixed-point) for
  `SingleTapeTM Bool`. Bridge between `Halt.Diagonal` and the
  reduction graph.
* [ ] **P2** **m-completeness** of K. Show K is m-complete for the
  class of c.e. problems (within our reduction framework).
* [ ] **P3** **Index sets and arithmetic hierarchy** — defer to a
  separate development.

### From Soare

* [ ] **P3** **Turing degrees**, **post's problem**, **Friedberg–Muchnik**.
  These are degree-theoretic and well beyond Phase 3's scope; record
  as long-horizon items.

### Wang tilings / domino problem

* [ ] **P2** **Domino problem is undecidable**. Standard reduction
  from Halt via a "trace tiling" encoding. ~700 LoC.

---

## Cross-cutting infrastructure

* [ ] **P1** A `Computable f` predicate for `f : List Bool → List Bool`,
  matching cslib's `SingleTapeTM Bool` model. Used in
  `ManyOneReduction`'s computability witness field.
* [ ] **P1** `compComputer`'s composition lemmas as **public** wrappers
  (cslib has them as `private`). Either upstream to cslib or wrap
  locally.
* [ ] **P2** A `Decidable`-vs-`Computable` bridge.
* [ ] **P3** Bridge to Mathlib's `Nat.Partrec.Code` (so Mathlib's
  existing `halting_problem` can be transported to cslib's model
  and vice versa).

---

## Documentation / outreach

* [ ] **P1** A "first reduction" tutorial: how to add a new node to the
  reduction graph (definition + reduction + `@[reduction_graph]` tag).
* [ ] **P2** A worked example showing the tactic in action.
* [ ] **P2** API documentation (`doc-gen4`).
* [ ] **P3** Comparison to Coq's `coq-library-undecidability` and
  Isabelle equivalents.

---

## Engineering polish

* [ ] **P2** Split `PCP/Reductions/HaltToMPCP.lean` (currently ~4100
  LoC) into logical sub-modules. Forward / backward / canonical-iff
  could each be their own file.
* [ ] **P2** Lakefile cleanups: add `DiagonaLean` as a `lean_lib`
  re-exporting the framework once it lands.
* [ ] **P3** CI: minimal GitHub Actions config for `lake build`.

---

## Convention

Every commit on this plan MUST keep `lake build` clean with **no
`sorry`** and no warnings.
