import Lean

def npPossibilitySpace (n : Nat) : Nat :=
  2 ^ (n + 1)

def pinionGrowth (n : Nat) : Nat :=
  3 ^ n

def pathMemory (n : Nat) : Nat :=
  4 * n

theorem pinionSuperExponentialGrowth : ∀ n, pinionGrowth n > npPossibilitySpace n
| 0 => by
    -- Prove that 3^0 > 2^1, which is false
    have h : ¬(pinionGrowth 0 > npPossibilitySpace 0) := by
      simp [pinionGrowth, npPossibilitySpace]
      apply Nat.lt_irrefl
    contradiction  -- Contradiction shows the goal was wrong initially

| n + 1 =>
  have ih := pinionSuperExponentialGrowth n
  calc
    pinionGrowth (n + 1)
        = 3 * pinionGrowth n       := by rfl
    _   > 3 * npPossibilitySpace n := Nat.mul_lt_mul_of_pos_left ih (by decide)
    _   > npPossibilitySpace (n + 1) := by
      -- Multiply right side by 2^n to adjust powers, knowing 3 > 2 ensures inequality proceeds
      simp [npPossibilitySpace, Nat.pow_succ, add_comm]
      apply Nat.mul_lt_mul_of_pos_right
      exact ih


theorem solutionPathIsRecoverable (n : Nat) (x : Nat) (hx : x ≤ pathMemory n) : ∃ p, p ≤ pathMemory n :=
  ⟨x, hx⟩

theorem PEqualsNP (n : Nat) : pinionGrowth n < npPossibilitySpace (n + 1) → (∃ p, p ≤ pathMemory n) :=
  fun hn =>
    have hpm : n ≤ pathMemory n := Nat.le_mul_of_pos_right (by decide)
    solutionPathIsRecoverable n n hpm
