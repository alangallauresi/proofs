import Std

namespace Pinion

-- **1. Declare U as a type**
variable (U : Type) -- U is a "normal" type, like Nat or Bool

-- **2. Existence predicate**: E(x) means "x exists" (x : U)
def E {U : Type} (x : U) : Prop := x = x -- Use x explicitly

-- **3. Non-existence predicate**: N(x) means "x does not exist"
def N {U : Type} (x : U) : Prop := ¬ E x

-- **4. Theorem 2: E and N are exhaustive for all x ∈ U**
theorem exhaustive (x : U) : E x ∨ N x :=
by
  unfold E N -- Unfold E and N so Lean knows their definitions
  apply Classical.em (x = x) -- Law of the Excluded Middle for "x = x"

end Pinion
