import Std
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring

def BDS : ℕ → ℚ
| 0     => 1
| (n+1) => BDS n / 2

theorem BDS_closed_form (n : ℕ) : BDS n = 1 / 2^n := by
  induction n with
  | zero => simp [BDS, pow_zero]
  | succ n ih =>
    rw [BDS]
    rw [ih]
    rw [pow_succ]
    ring

#reduce BDS 0 -- 1
#reduce BDS 1 -- 1/2
#reduce BDS 2 -- 1/4
#reduce BDS 3 -- 1/8
