import Std

namespace Pinion

-- **1. Declare U as a generic type (universe-polymorphic)**
universe u
variable {U : Type u} -- Allows U to be of any universe

-- **2. Existence predicate**: E(x) means "x exists" (x : U)
def E {U : Type u} (x : U) : Prop := x = x -- Reflexivity to prevent "unused variable" warning

-- **3. Non-existence predicate**: N(x) means "x does not exist"
def N {U : Type u} (x : U) : Prop := ¬ E x -- N(x) is the negation of E(x)

-- **4. Theorem 1: E and N are opposites for all x ∈ U**
theorem oppositional {U : Type u} (x : U) : (E x ↔ ¬ N x) ∧ (N x ↔ ¬ E x) := by
  apply And.intro
  -- Prove (E x ↔ ¬ N x)
  apply Iff.intro
  · intro hx hN
    exact hN hx
  · intro hnx
    unfold N at hnx
    exact Eq.refl x

  -- Prove (N x ↔ ¬ E x)
  apply Iff.intro
  · intro hN
    exact hN
  · intro hNE
    unfold N
    exact hNE

-- **5. Theorem 2: E and N are exhaustive for all x ∈ U**
theorem exhaustive {U : Type u} (x : U) : E x ∨ N x := by
  apply Classical.em (x = x)

-- **6. Theorem 3: E and N are disjoint for all x ∈ U**
theorem disjoint {U : Type u} (x : U) : ¬ (E x ∧ N x) := by
  intro h
  cases h with
  | intro he hn =>
    exact hn he

-- **Test cases**
#reduce E (0 : Nat)
#reduce N (0 : Nat)
#reduce E 0
#reduce N 0
#reduce E 1
#reduce N 1
#reduce E 42
#reduce N 42

#check oppositional (0 : Nat)
#check oppositional (1 : Nat)
#check oppositional (42 : Nat)

#check exhaustive (0 : Nat)
#check exhaustive (1 : Nat)
#check exhaustive (42 : Nat)

#check disjoint (0 : Nat)
#check disjoint (1 : Nat)
#check disjoint (42 : Nat)

end Pinion
