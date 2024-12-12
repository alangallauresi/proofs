import Std

namespace Pinion

-- **1. Declare U as a type**
variable (U : Type) -- U is a "normal" type, like Nat or Bool

-- **2. Existence predicate**: E(x) means "x exists" (x : U)
def E {U : Type} (x : U) : Prop := x = x -- Use x explicitly

-- **3. Non-existence predicate**: N(x) means "x does not exist"
def N {U : Type} (x : U) : Prop := ¬ E x

-- **4. Theorem 1: E and N are opposites for all x ∈ U**
theorem oppositional (x : U) : (E x ↔ ¬ N x) ∧ (N x ↔ ¬ E x) :=
by simp [E, N] -- Magic one-liner!

end Pinion
