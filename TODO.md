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

## The tactic — architecture

The headline `by reduce` tactic that traverses the registered
reduction graph is the most distinctive deliverable of DiagonaLean.
It splits into three components, in dependency order. The first two
are plumbing; the third is where the proof-search magic happens.

### Component 1: `@[reduction_graph]` attribute (~100 LoC) ✅

**Landed** in `Reduction/Graph.lean`. The seven existing reductions
(`mpcpToPcp`, `haltTM_to_haltTMCode`, `haltTMCode_to_encodedHalt`,
`encodedHalt_to_haltTMCode`, `mpcpLB_to_encodedPCP`,
`encodedHaltMPCP_to_mpcpLB`, `encodedPCP_to_encodedCFGIntersection`)
are tagged and registered. `Reduction.Smoke` `#eval`s the graph to
confirm registration.

Original spec:

The reduction graph is an `Environment` extension that maps
`Problem`-term keys to outgoing edges. The `@[reduction_graph]`
attribute is the registration mechanism:

```lean
@[reduction_graph]
def mpcpToPcp α : MPCP α ≤ₘ PCP (Ext α) := …
```

The attribute's elaborator inspects the declaration's type (expecting
`ManyOneReduction P Q`), extracts `P` and `Q`, and adds an entry to
the global graph. Implementation skeleton:

```lean
structure Edge where
  source : Expr     -- P
  target : Expr     -- Q
  declName : Name   -- the reduction's identifier

initialize reductionGraphExt :
    SimpleScopedEnvExtension Edge (List Edge) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s e => e :: s
    initial := []
  }

initialize registerBuiltinAttribute {
  name := `reduction_graph
  add := fun decl _ kind => MetaM.run' do
    let info ← getConstInfo decl
    let some (P, Q) ← extractReductionEndpoints info.type
      | throwError "expected ManyOneReduction"
    reductionGraphExt.add ⟨P, Q, decl⟩ kind
}
```

### Component 2: Graph search (~150 LoC)

Backward BFS from the goal node to any registered undecidability
fact. Pseudo:

```lean
partial def searchPath (target : Expr) (depth : Nat := 10) :
    MetaM (Option (List Edge)) := do
  if depth = 0 then return none
  if ← isKnownUndecidable target then return some []
  for e in (← graph).filter (·.target ≈ target) do
    if let some rest ← searchPath e.source (depth - 1) then
      return some (e :: rest)
  return none
```

Hard parts: unification across alphabet parameters (`MPCP α` vs
`MPCP Bool`), avoiding loops, ordering edges to prefer shorter paths,
respecting metavariable scope.

### Component 3: Term emission (~200 LoC)

Compose the path into `Undecidable.of_manyOne` applications:

```lean
elab "reduce" : tactic => withMainContext do
  let some target := (← getMainTarget).getAppFnArgs.matchTarget ``Undecidable
    | throwError "expected `Undecidable ?`"
  let some path ← searchPath target
    | throwError "no path found"
  let composite ← composeReductions path
  let knownUndec ← findUndecidabilityProof path[0]!.source
  closeMainGoal `reduce (← mkAppM ``Undecidable.of_manyOne #[composite, knownUndec])
```

So `example : Undecidable PCP := by reduce` finds
`Halt ≤ₘ MPCP ≤ₘ PCP`, composes, applies transfer.

### Effort tiers

| Tier | LoC | What works |
|---|---|---|
| **MVP** | ~500 | Naive search + emission; types must match literally; no unification |
| **Useful** | ~1500 | + unification, depth bounds, user hints (`by reduce via mpcpToPcp`), helpful errors |
| **Production** | ~3000+ | + caching, visualisation, `decide` integration, fuel parameters |

### Dependency: the tactic is blocked by encoded variants

For the tactic to do useful work, **every node in the graph must have
a stable identity**. Currently `MPCP α` for varying `α` is many
different nodes, and `Halt ≤ₘ MPCP` produces destinations whose
alphabet depends on the input TM. The tactic would have to unify
across these parameters, which is doable but adds substantial
complexity to Component 2.

The cleaner path is to encode every problem over a fixed alphabet
(`List Bool`) so each problem has a single `Problem` instance with
fixed `Input` type. Then Components 1–3 work with literal type
matching. This is **step 1** of the immediate plan below.

---

## Step 1 (in progress): Encoded variants

The goal is to give every Phase 2 problem a *fixed* `Input` type
(`List Bool` or `Stack (List Bool)`), so that the reduction graph has
unambiguous node identities.

* [x] **P0** Close the deferred `trToList_getElem` lookup lemma in
  `Halt.Encoding`. ✅ `trToList_getElem?`.
* [x] **P0** Prove `decodeTMCode_encodeTMCode : decodeTMCode (encodeTMCode c) = some c`.
  ✅ (`decodeTMCode` refactored to nested `match` for clean reduction).
* [x] **P0** Define `EncodedHalt : Problem` (Input `List Bool`,
  predicate "decoding succeeds with `(c, w)` and `c.toTM` halts on `w`").
  ✅ in `Reduction/Encoded.lean`.
* [x] **P0** Prove `HaltTMCode ≤ₘ EncodedHalt` and the reverse,
  giving `HaltTMCode ≡ₘ EncodedHalt`. ✅ via `loopingTMCode` for
  malformed inputs (which doesn't halt by `not_halts_loopingTMCode`).
* [x] **P1** Define `EncodedPCP : Problem` over `Stack (List Bool)`.
  ✅ in `Reduction/EncodedPCP.lean`.
* [x] **P1** Encode `mpcpToPcp` at the `List Bool` alphabet via
  `flattenExt : Ext (List Bool) → List Bool` plus
  `hasSolution_flattenStack_iff` (both directions, with classical
  preimage selection for the reverse). ✅
* [x] **P1** Generic `StackMap` module for per-symbol alphabet
  shifts: `mapTile`/`mapStack`, `tau` commutativity, injectivity,
  `HasSolution`/`MHasSolution` preservation under any injective
  `σ : α → β`. ✅ in `Reduction/StackMap.lean`. `EncodedPCP` now
  specialises at `σ = flattenExt`, dropping ~120 LoC of duplication.
* [x] **P1** Wrap `halt_le_mpcp` as `EncodedHaltMPCP ≤ₘ MPCP_LB` via
  `encodeAlpha : Alpha (Fin (n+1)) Bool → List Bool` (tag-prefix
  injection with a `decodeAlpha` left inverse) composed with
  `StackMap.mhasSolution_mapStack_iff`. ✅ in
  `Reduction/EncodedHaltMPCP.lean`. Malformed / non-normalised inputs
  route to a `noSolutionSentinel` `(Tile, Stack)` pair admitting no
  `MHasSolution`. The `NoBlankWrites ∧ NoLeftBoundary` conditions are
  baked into the predicate — see HUM normalisation below for the
  remaining `EncodedHalt ≤ₘ EncodedHaltMPCP` bridge.
* [x] **P1** Wrap `hasSolution_iff_intersectionNonempty` as
  `EncodedPCP ≤ₘ EncodedCFGIntersection`. ✅ in
  `Reduction/EncodedCFG.lean` (no further encoding needed — the
  destination alphabet `Term (List Bool)` is already fixed).

Step 1 **landed** (~770 LoC). The chain
`EncodedHaltMPCP ≤ₘ MPCP_LB ≤ₘ EncodedPCP ≤ₘ EncodedCFGIntersection`
runs end-to-end at fixed `List Bool`-flavoured types.

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
