import Std

namespace Pinion

-- **1. Declare U as a type**
universe u -- Allows for U to be from any universe (Type, Type 1, etc.)
variable {U : Type u} -- Keeps U as a generic type from universe u

-- **2. Existence predicate**: E(x) means "x exists" (x : U)
def E {U : Type u} (x : U) : Prop := x = x -- Use x explicitly to prevent unused variable warnings

-- **3. Non-existence predicate**: N(x) means "x does not exist"
def N {U : Type u} (x : U) : Prop := ¬ E x -- N(x) is the negation of E(x)

-- **4. Theorem 1: E and N are opposites for all x ∈ U**
theorem oppositional (x : U) : (E x ↔ ¬ N x) ∧ (N x ↔ ¬ E x) := by
  apply And.intro
  -- Prove (E x ↔ ¬ N x)
  apply Iff.intro
  · -- (→) direction: E x → ¬ N x
    intro hx hN
    exact hN hx -- Contradiction since N(x) = ¬ E(x)
  · -- (←) direction: ¬ N x → E x
    intro hnx
    unfold N at hnx
    unfold E
    exact Eq.refl x -- Reflexivity of equality

  -- Prove (N x ↔ ¬ E x)
  apply Iff.intro
  · -- (→) direction: N x → ¬ E x
    intro hN
    unfold N at hN
    exact hN
  · -- (←) direction: ¬ E x → N x
    intro hNE
    unfold N
    exact hNE

-- **5. Theorem 2: E and N are exhaustive for all x ∈ U**
-- Exhaustion: Account for each x inside the set'; this is from the perspective of set member x
-- This is equivalent to self-containement in classical logic, but not paraconsistent logic
theorem exhaustive (x : U) : E x ∨ N x := by
  unfold E N
  apply Classical.em (x = x) -- Classical logic: x = x ∨ ¬(x = x)

-- **6. Theorem 3: E and N are disjoint for all x ∈ U**
-- Disjoint: There is no element that can exist in both sets
theorem disjoint (x : U) : ¬ (E x ∧ N x) := by
  intro h
  cases h with
  | intro he hn =>
    exact hn he -- Contradiction since E x and ¬ E x can't both be true

-- **7. Theorem 4: Self-containment of Existence for all x ∈ U**
-- Self-containment: Ensure that no x is outside the set; this is from the perspective of the superset
-- This is equivalent to exhaustion in classical logic, but not paraconsistent logic
theorem self_containment (x : U) : ¬ (¬ E x ∧ ¬ N x) := by
  -- Assume ¬ E(x) ∧ ¬ N(x) holds, and aim to reach a contradiction
  intro h
  -- Decompose h into its parts: ¬ E(x) and ¬ N(x)
  have h1 : ¬ E x := h.1  -- ¬ E(x)
  have h2 : ¬ N x := h.2  -- ¬ N(x)
  -- Use the definition of N(x)
  unfold N at h2
  -- h2 is ¬ ¬ E(x)
  -- By classical logic, ¬ ¬ E(x) implies E(x)
  have e : E x := Classical.byContradiction h2
  -- We now have both ¬ E(x) (h1) and E(x) (e), which is a contradiction
  exact h1 e

-- **Test cases for basic functionality**
#reduce E (0 : Nat)
#reduce N (0 : Nat)

#reduce E 0
#reduce N 0

#reduce E 1
#reduce N 1

#reduce E 42
#reduce N 42

-- **Check theorems for specific values**
#check oppositional (0 : Nat)
#check oppositional (1 : Nat)
#check oppositional (42 : Nat)

#check exhaustive (0 : Nat)
#check exhaustive (1 : Nat)
#check exhaustive (42 : Nat)

#check disjoint (0 : Nat)
#check disjoint (1 : Nat)
#check disjoint (42 : Nat)

#check self_containment (0 : Nat)
#check self_containment (1 : Nat)
#check self_containment (42 : Nat)

end Pinion
