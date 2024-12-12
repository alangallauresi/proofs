import Mathlib

-- 🟢 **Binary Difference Sequence (BDS) Definition**
def BDS : ℕ → ℚ
| 0     => 1
| (n+1) => 2 * BDS n

-- 🟢 **Prove that BDS follows a closed form**
theorem BDS_closed_form (n : ℕ) : BDS n = 2 ^ n := by
  induction n with
  | zero =>
    simp [BDS, pow_zero]
  | succ n ih =>
    simp [BDS]
    rw [ih]
    rw [pow_succ]
    ring

-- 🟢 **Binary Search Tree (BST) Definition**
structure BST (α : Type) where
  val : α
  left : Option (BST α)
  right : Option (BST α)

-- 🟢 **Generate a BST with rational values based on depth**
def generateBST : ℕ → BST ℚ
| 0 => ⟨1, none, none⟩
| (n+1) =>
  let left := generateBST n
  let right := generateBST n
  ⟨BDS (n + 1), some left, some right⟩

-- 🟢 **Sum all the values in a BST**
def sumBST : BST ℚ → ℚ
| ⟨v, none, none⟩ => v
| ⟨v, some l, none⟩ => v + sumBST l
| ⟨v, none, some r⟩ => v + sumBST r
| ⟨v, some l, some r⟩ => v + sumBST l + sumBST r

-- 🟢 **Main Theorem**
-- Prove that the sum of the BST follows the specific formula
theorem sumBST_formula (n : ℕ) : sumBST (generateBST n) = (n + 1) * 2 ^ n := by
  induction n with
  | zero =>
    simp [generateBST, sumBST, pow_one]
    -- 'simp' already simplifies to '1 = 1', so no further tactics are needed.
  | succ n ih =>
    simp [generateBST, sumBST]
    rw [BDS_closed_form (n + 1)]
    rw [pow_succ]
    rw [ih]
    ring

-- 🟢 **Example Proof Demonstrating sumBST_formula**
example (n : ℕ) : sumBST (generateBST n) = (n + 1) * 2 ^ n := by
  rw [sumBST_formula]

-- 🟢 **Test Cases for BDS**
#reduce BDS 0 -- 1
#reduce BDS 1 -- 2
#reduce BDS 2 -- 4
#reduce BDS 3 -- 8

-- 🟢 **Test Cases for BST**
#reduce generateBST 0
#reduce generateBST 1
#reduce generateBST 2

-- 🟢 **Test Cases for sum of BST**
#reduce sumBST (generateBST 0) -- 1 = (0 +1)*2^0
#reduce sumBST (generateBST 1) -- 4 = (1 +1)*2^1
#reduce sumBST (generateBST 2) -- 12 = (2 +1)*2^2
#reduce sumBST (generateBST 3) -- 32 = (3 +1)*2^3
