import Std

namespace Pinion

-- A path is just a list of booleans representing steps.
structure Path where
  steps : List Bool
  deriving Repr

-- PinionState holds a path.
structure PinionState where
  path : Path
  deriving Repr

-- Shift is either left or right.
inductive Shift
| left
| right

-- Convert a Shift to a Bool: left = false, right = true.
def s2b (s : Shift) : Bool :=
  match s with
  | Shift.left  => false
  | Shift.right => true

-- Apply a shift by prepending the new step to the path.
def applyShift (p : PinionState) (s : Shift) : PinionState :=
  PinionState.mk (Path.mk ([s2b s] ++ p.path.steps))

-- The base state P0 has an empty path.
def P0 : PinionState := ⟨Path.mk []⟩

-- Define recursivePinion: given n and a list of shifts,
-- build a PinionState by encoding the first n shifts in order.
def recursivePinion : Nat → List Shift → PinionState
| 0,       _       => P0
| _+1,     []      => P0   -- Use _+1 instead of n+1 here since we don't need n in this branch
| n+1,     (h :: t) => applyShift (recursivePinion n t) h

-- Theorem: The path constructed by (recursivePinion n shifts)
-- is exactly the first n shifts of `shifts`, converted to booleans.
theorem selfReferentialEncoding (n : Nat) (shifts : List Shift) :
  (recursivePinion n shifts).path.steps = (shifts.take n).map s2b := by
  induction n generalizing shifts with
  | zero =>
    -- n = 0: (recursivePinion 0 shifts) = P0, so steps = []
    -- (shifts.take 0).map s2b = [] as well
    simp [recursivePinion, P0]
    --rfl
  | succ n ih =>
    cases shifts with
    | nil =>
      -- If shifts is empty, (recursivePinion (n+1) []) = P0, steps = []
      -- ( [].take (n+1) ).map s2b = [] as well
      simp [recursivePinion, P0]
      --rfl
    | cons h t =>
      -- (recursivePinion (n+1) (h::t)) = applyShift (recursivePinion n t) h
      simp [recursivePinion, applyShift]
      -- Use induction hypothesis on (recursivePinion n t)
      rw [ih t]
      simp [List.take, List.map]
      --rfl

-- Test evaluations
#eval (recursivePinion 3 [Shift.left, Shift.right, Shift.left]).path.steps   -- [false, true, false]
#eval (recursivePinion 0 [Shift.left, Shift.right]).path.steps               -- []
#eval (recursivePinion 2 [Shift.left, Shift.right]).path.steps               -- [false, true]

end Pinion
