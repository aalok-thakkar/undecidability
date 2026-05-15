/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction

public meta section

/-!
# Smoke test for the reduction graph

`#eval`s the registered graph. Run with `lake env lean Reduction/Smoke.lean`
to see the registered edges.
-/

open Lean DiagonaLean.ReductionGraph

/-- Print all registered edges. -/
def printReductionGraph : CoreM Unit := do
  let edges ← getReductionGraph
  IO.println s!"Graph has {edges.length} edge(s):"
  for e in edges.reverse do
    IO.println s!"  • {e.declName}"

#eval printReductionGraph
