
module

--public import Cslib.Foundations.Data.BiTape
public import Cslib.Foundations.Data.RelatesInSteps
public import Mathlib.Algebra.Polynomial.Eval.Defs
--public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

namespace PCP

variable {α : Type} [DecidableEq α]

/-- A word over alphabet α -/
abbrev Word α:= List α

/-- A PCP tile consists of a top and bottom word -/
structure Tile (α : Type) where
  top    : List α
  bottom : List α

/-- A PCP PCP_Instance is a finite list of tiles -/
abbrev PCP_Instance (α : Type):= List (Tile α)

/-- Concatenate the top strings according to a list of indices -/
def concatTop {α}
  (P : PCP_Instance α)
  (idxs : List (Fin P.length)) :
  List α := idxs.flatMap (fun i => (P.get i).top)


/-- Concatenate the bottom strings according to a list of indices -/
def concatBot {α}
  (P : PCP_Instance α)
  (idxs : List (Fin P.length)) :
  List α :=
  idxs.flatMap (fun i => (P.get i).bottom)


/-- A sequence of indices is a solution if:
    - it is nonempty
    - the concatenated top and bottom strings agree -/
def IsSolution (P : PCP_Instance α) (idxs : List (Fin P.length)) : Prop :=
  idxs ≠ [] ∧
  concatTop P idxs = concatBot P idxs

/-- The PCP predicate: there exists a nonempty matching index sequence -/
def HasSolution (P : List (Tile α)) :=
  ∃ idxs : List (Fin P.length), IsSolution P idxs

def getTile (P : List (Tile α)) (i : Fin P.length) : Tile α :=
  P.get ⟨i.val, i.isLt⟩



structure MPCP_Instance (α : Type) :=
  (first : Tile α)
  (rest  : List (Tile α))

@[simp]
def NMconcatTop {α}
  (P : MPCP_Instance α)
  (idxs : List (Fin P.rest.length)) :
  List α :=
  P.first.top ++
    idxs.flatMap (fun i => (P.rest.get i).top)

def NMconcatBottom {α}
  (P : MPCP_Instance α)
  (idxs : List (Fin P.rest.length)) :
  List α :=
  P.first.bottom ++
    idxs.flatMap (fun i => (P.rest.get i).bottom)

def MHasSolution {α}
  (P : MPCP_Instance α) : Prop :=
  ∃ idxs : List (Fin P.rest.length),
    NMconcatTop P idxs =
    NMconcatBottom P idxs

lemma MconcatTop_nil {α} (P : MPCP_Instance α) :
  NMconcatTop P [] = P.first.top := by
  simp

lemma MconcatTop_cons {α}
  (P : MPCP_Instance α)
  (i : Fin P.rest.length)
  (is : List (Fin P.rest.length)) :
  NMconcatTop P (i :: is) =
    P.first.top ++
      (P.rest.get i).top ++
      is.flatMap (fun j => (P.rest.get j).top) := by
  simp

/-MPCP tp PCP conversion-/

inductive SymbolExt (α : Type) : Type
| old : α → SymbolExt α
| marker : SymbolExt α
| endMarker : SymbolExt α

notation "⋆" => SymbolExt.marker
notation "⋄" => SymbolExt.endMarker

-- Optional: Use an up-arrow to lift normal alphabet characters
prefix:max "↑" => SymbolExt.old

-- For the Goal State (infoview)
instance {α : Type} [Repr α] : Repr (SymbolExt α) where
  reprPrec
    | SymbolExt.old a, _ => f!"↑{repr a}"
    | SymbolExt.marker, _ => f!"⋆"
    | SymbolExt.endMarker, _ => f!"⋄"

-- For string conversions (like `#eval`)
instance {α : Type} [ToString α] : ToString (SymbolExt α) where
  toString
    | SymbolExt.old a => toString a
    | SymbolExt.marker => "⋆"
    | SymbolExt.endMarker => "⋄"

def leftInterleave {α : Type} (l : List α) : List (SymbolExt α) :=
  l.flatMap (fun x => [⋆, ↑(x: α)])

#eval leftInterleave ['a', 'b', 'c']
-- Output: [⋆, ↑'a', ⋆, ↑'b', ⋆, ↑'c']


def rightInterleave {α : Type} (l : List α) : List (SymbolExt α) :=
  l.flatMap (fun x => [↑(x : α), ⋆])

#eval rightInterleave ['a', 'b', 'c']

-- The start tile matches the MPCP first tile but adds the extra marker on the bottom
-- Normal tiles interleave right on top (y_i), left on bottom (z_i)
def liftTile {α : Type} (t : Tile α) : Tile (SymbolExt α) :=
{ top    := rightInterleave t.top,
  bottom := leftInterleave t.bottom }

#eval liftTile ⟨['a', 'c'], ['b', 'd']⟩

-- The start tile adds the extra marker on the top to match y_0 = *y_1
def startTile {α : Type} (P : MPCP_Instance α) : Tile (SymbolExt α) :=
{ top    := SymbolExt.marker :: rightInterleave P.first.top,
  bottom := leftInterleave P.first.bottom }

#eval startTile ⟨⟨['d','e'],['x','y']⟩, [⟨['a','c'], ['e','f']⟩]⟩

-- The end tile caps off the sequence with y_{k+1} = $ and z_{k+1} = *$
def endTile {α : Type} : Tile (SymbolExt α) :=
{ top    := [SymbolExt.endMarker],
  bottom := [SymbolExt.marker, SymbolExt.endMarker] }

#eval (endTile: Tile (SymbolExt Nat))


-- The full PCP PCP_Instance
/- Note that the startTile and endTile come from the SymbolExt of α, P is an MPCP instance means it has a list of tiles, along with a specific tile marked as end. The following function transforms a list of tiles in MPCP (which excludes the start and endTiles, to the list of Tiles, not the solution)-/
def MPCP_to_PCP {α : Type} (P : MPCP_Instance α) : List (Tile (SymbolExt α)) :=
  startTile P ::
  endTile ::
  liftTile P.first ::
  List.map liftTile P.rest


@[simp]
lemma concatTop_cons {α} (P : PCP_Instance α) (i : Fin P.length) (is : List (Fin P.length)) :
  concatTop P (i :: is) = (P.get i).top ++ concatTop P is := by
  simp [concatTop, List.flatMap]

@[simp]
lemma concatTop_append {α} (P : PCP_Instance α) (l1 l2 : List (Fin P.length)) :
  concatTop P (l1 ++ l2) = concatTop P l1 ++ concatTop P l2 := by
  simp[concatTop]

@[simp]
lemma concatBot_cons {α} (P : PCP_Instance α) (i : Fin P.length) (is : List (Fin P.length)) :
  concatBot P (i :: is) = (P.get i).bottom ++ concatBot P is := by

  simp [concatBot, List.flatMap]

@[simp]
lemma concatBot_append {α} (P : PCP_Instance α) (l1 l2 : List (Fin P.length)) :
  concatBot P (l1 ++ l2) = concatBot P l1 ++ concatBot P l2 := by
   simp[concatBot]

def shiftIndex {α: Type}
  (P : MPCP_Instance α)
  (i : Fin P.rest.length) :
  Fin (MPCP_to_PCP P).length := ⟨i.val + 3, by
    -- Get the upper bound of our input index
    have hi := i.isLt
    -- Unfold the definition to expose the list length
    simp [MPCP_to_PCP]
    -- Let Lean's arithmetic solver handle the inequality
    ⟩

/- Induction on hidxs-/

-- Proves that mapping the shifted indices gives you the interleaved tops of the rest of the tiles
lemma concatTop_mid_idxs {α : Type} (P : MPCP_Instance α) (hidxs : List (Fin P.rest.length)) :
  concatTop (MPCP_to_PCP P) (hidxs.map (shiftIndex P)) =
  rightInterleave (hidxs.flatMap (fun i => (P.rest.get i).top)) := by
  induction hidxs with
  |nil => simp[concatTop, rightInterleave]
  |cons x xs ih =>
    simp[concatTop, rightInterleave, MPCP_to_PCP, shiftIndex, liftTile] at *
    simp[ih]




 -- Usually proven by induction on hidxs

-- Proves the same for the bottoms
lemma concatBot_mid_idxs {α : Type} (P : MPCP_Instance α) (hidxs : List (Fin P.rest.length)) :
  concatBot (MPCP_to_PCP P) (hidxs.map (shiftIndex P)) =
  leftInterleave (hidxs.flatMap (fun i => (P.rest.get i).bottom)) := by
 induction hidxs with
  |nil => simp[concatBot, leftInterleave]
  |cons x xs ih =>
    simp[concatBot, leftInterleave, MPCP_to_PCP, shiftIndex, liftTile] at *
    simp[ih]



lemma length_MPCP_to_PCP (α: Type) (P : MPCP_Instance α) :
  (MPCP_to_PCP P).length = P.rest.length + 3 :=
by
  simp [MPCP_to_PCP]

@[simp]
lemma leftInterleave_append {α : Type} (l1 l2 : List α) :
  leftInterleave (l1 ++ l2) = leftInterleave l1 ++ leftInterleave l2 := by
  simp [leftInterleave, List.flatMap_append]

@[simp]
lemma rightInterleave_append {α : Type} (l1 l2 : List α) :
  rightInterleave (l1 ++ l2) = rightInterleave l1 ++ rightInterleave l2 := by
  simp [rightInterleave, List.flatMap_append]

-- The core mathematical trick of the reduction
lemma marker_right_eq_left_marker {α : Type} (l : List α) :
  [SymbolExt.marker] ++ rightInterleave l = leftInterleave l ++ [SymbolExt.marker] := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [leftInterleave, rightInterleave]
    -- Group the lists to use the inductive hypothesis
    have h : [SymbolExt.marker, SymbolExt.old hd, SymbolExt.marker] ++ rightInterleave tl =
             [SymbolExt.marker, SymbolExt.old hd] ++ ([SymbolExt.marker] ++ rightInterleave tl) := by simp
    exact List.reverse_inj.mp (congrArg List.reverse ih)

theorem mpcp_to_pcp_correct {α : Type}
  (P : MPCP_Instance α) :
  MHasSolution P ↔
  HasSolution (MPCP_to_PCP P) := by
  constructor
  intro h
  unfold MHasSolution at h
  unfold HasSolution IsSolution
  rcases h with ⟨hidxs, hi⟩
  unfold NMconcatTop NMconcatBottom at hi
  -- 1. Define your specific index pointers (adjust the proofs `by ...` based on your exact list length)
  let start_idx : Fin (MPCP_to_PCP P).length := ⟨0, by simp [MPCP_to_PCP]⟩
  let end_idx : Fin (MPCP_to_PCP P).length := ⟨1, by simp [MPCP_to_PCP]⟩

  -- 2. Shift the MPCP indices to point to the correct translated tiles
  let mid_idxs := hidxs.map (shiftIndex P)

  -- 3. Construct the full PCP solution sequence
  let pcp_idxs := start_idx :: ((mid_idxs) ++ [end_idx])

  -- Provide this sequence to the existential goal
  use pcp_idxs

  -- Split the AND goal (idxs ≠ [] ∧ concatTop = concatBot)
  constructor
  · simp

  · sorry
  · sorry
/-
    simp [pcp_idxs, concatTop_cons, concatBot_cons, concatTop_append, concatBot_append]
    simp [start_idx, end_idx, MPCP_to_PCP, startTile, endTile]
    simp [concatTop, concatBot, List.flatMap_nil]
    change ⋆ :: (rightInterleave P.first.top ++ (concatTop (MPCP_to_PCP P) (hidxs.map (shiftIndex P)) ++ [⋄])) =
           leftInterleave P.first.bottom ++ (concatBot (MPCP_to_PCP P) (hidxs.map (shiftIndex P)) ++ [⋆, ⋄])
    rw [concatTop_mid_idxs, concatBot_mid_idxs]
    sorry

    apply (concatTop_cons (startTile P :: endTile :: liftTile P.first :: List.map liftTile P.rest) (0 :: (mid_idxs ++ [end_idx])))
    simp[concatBot_cons]
    sorry

  · -- Goal 1: Prove it's not empty
    intro contra
    sorry -- or `simp` / `decide` depending on your setup, since a `::` list is never empty

  · -- Goal 2: Prove concatTop (MPCP_to_PCP P) pcp_idxs = concatBot ...
    let start : Fin (pcpTiles P).length := ⟨0, by simp [pcpTiles]⟩
    let first : Fin (pcpTiles P).length := ⟨1, by simp [pcpTiles]⟩
    let idxs : List (Fin (pcpTiles P).length) := start :: first :: hidxs.map (shiftIndex P)
    refine ⟨idxs, ?hne, ?heq⟩
    simp
    unfold concatTop concatBot MPCP_to_PCP
    simp[idxs]
    simp [pcpTiles,
      start, first,
      startWrapper,
      liftTile] at *

  repeat
  (simp [List.append_assoc] at *;
   simp [List.cons_append] at *)
  rw [List.cons_append]
  rw [List.cons.inj]




simp [pcpTiles,
      start, first,
      startWrapper,
      liftTile,
      shiftIndex,
      List.map_append,
      List.map_flatMap,
      List.append_assoc] at *
  have l :=congrArg (List.map SymbolExt.old) hi
  simp [List.cons_append, List.append_assoc]
  simpa using l
  congr


  unfold pcpTiles
  simp [pcpTiles, startWrapper, liftTile]
  have l:= congrArg (List.map SymbolExt.old) hi
  simp [pcpTiles] at *

  simp [List.map_append, List.map_flatMap]

  have len_eq: ([startWrapper P] ++ liftTile P.first :: List.map liftTile P.rest).length = (P.rest.length + 2) := by
    simp

  sorry
  sorry

-/
#eval 1 + 2
