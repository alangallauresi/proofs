import Mathlib

-- 🟢 **Binary Difference Sequence (BDS) Definition**
def BDS (n : ℕ) : ℚ :=
  match n with
  | 0     => 1
  | (n+1) => 2 * BDS n

-- 🟢 **Theorem: BDS follows the closed form BDS(n) = 2^n**
theorem BDS_closed_form (n : ℕ) : BDS n = 2 ^ n := by
  -- Use induction on n
  induction n with
  | zero =>
    simp only [BDS, pow_zero] -- Base case BDS(0) = 1, 2^0 = 1
  | succ n ih =>
    simp only [BDS] -- Unfold BDS (n+1) = 2 * BDS(n)
    rw [ih] -- Apply induction hypothesis BDS(n) = 2^n
    rw [pow_succ] -- Use 2^(n+1) = 2^n * 2
    ring_nf -- Normalize and finish

-- 🟢 **Binary Search Tree (BST) Definition**
structure BST (α : Type) where
  val : α
  left : Option (BST α)
  right : Option (BST α)

-- 🟢 **Generate a BST with rational values based on depth**
def generateBST : ℕ → BST ℚ
| 0 => ⟨ 1, none, none ⟩
| (n+1) =>
  let left := generateBST n
  let right := generateBST n
  ⟨ BDS (n + 1), some left, some right ⟩

-- 🟢 **Test Cases for BDS**
#reduce BDS 0 -- 1
#reduce BDS 1 -- 2
#reduce BDS 2 -- 4
#reduce BDS 3 -- 8
#reduce BDS 4 -- 16
#reduce BDS 5 -- 32
#reduce BDS 10 -- 1024

-- 🟢 **Test Cases for BST**
#reduce generateBST 0 -- BST with one node, value 1
#reduce generateBST 1 -- BST with 3 nodes
#reduce generateBST 2 -- BST with 7 nodes
