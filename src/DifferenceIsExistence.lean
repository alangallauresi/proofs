/-!
 **Theorem: Difference Implies Existence**
 **Axiom:** Difference exists, i.e., there exist x and y such that x ≠ y.
 **Goal:** To prove that if difference exists, then existence follows.
-/

/--
 **Definition: Nontrivial Type**
 A type is nontrivial if it has at least two distinct elements.
-/
def Nontrivial (α : Type) : Prop :=
 ∃ (x y : α), x ≠ y

/--
 **Definition of MyExists (E):**
 A term `z` exists if there is some type α and a term `z` of type α.
-/
inductive MyExists { α : Type } (z : α) : Prop
| mk : MyExists z

/--
 **Theorem (Difference Implies Existence):**
 If there exist x and y such that x ≠ y, then there exists a z such that E(z) holds.
-/
theorem difference_implies_existence { α : Type } :
 ( ∃ (x y : α), x ≠ y ) → ∃ (z : α), MyExists z := by
   intro h_diff
   obtain ⟨x, y, hxy⟩ := h_diff
   exists x
   constructor

/--
 **Theorem (Existence Implies Difference):**
 If a type is nontrivial and something exists in it, then difference exists in that type.
-/
theorem existence_implies_difference { α : Type } (h_nontriv : Nontrivial α) :
 ( ∃ (z : α), MyExists z ) → ∃ (x y : α), x ≠ y := by
   intro _
   exact h_nontriv

/--
 **Theorem (Difference is Existence):**
 For nontrivial types, difference and existence are equivalent.
-/
theorem difference_is_existence { α : Type } (h_nontriv : Nontrivial α) :
 ( ∃ (x y : α), x ≠ y ) ↔ ( ∃ (z : α), MyExists z ) := by
   constructor
   · exact difference_implies_existence
   · exact existence_implies_difference h_nontriv

/-- Proof that Bool is nontrivial -/
theorem bool_nontrivial : Nontrivial Bool := 
 ⟨true, false, fun h => nomatch h⟩

/-- Proof that Nat is nontrivial -/
theorem nat_nontrivial : Nontrivial Nat := 
 ⟨0, 1, fun h => nomatch h⟩

/-- Proof that String is nontrivial -/
theorem string_nontrivial : Nontrivial String := 
 ⟨"a", "b", fun h => nomatch h⟩

/-- Basic tests -/
def check_difference (x y : Nat) : Bool := x ≠ y
#eval check_difference 0 1