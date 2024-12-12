import Mathlib.Data.Set.Basic

variable {α : Type*}
variable (E N : Set α)

-- Approach 1: Prove disjointness using set extensionality and case analysis
theorem disjoint_E_N_1 (h : ∀ x ∈ E, x ∉ N) : E ∩ N = ∅ :=
  by
    ext x -- Introduce an arbitrary `x` for set extensionality
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false] -- Simplify set membership
    apply Iff.intro
    -- Forward direction: x ∈ E ∩ N implies false
    intro h'
    cases h' with
    | intro hE hN =>
      exact h x hE hN -- Apply the assumption to derive a contradiction
    -- Backward direction: x ∈ ∅ implies x ∈ E ∩ N (vacuous)
    intro h'
    exact False.elim h' -- Nothing is in ∅, so this case is trivially false



-- Next
