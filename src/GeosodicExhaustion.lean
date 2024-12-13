import Std

open List

/-!
  **Theorem:**
  The Pinion is a geosodic structure, meaning it exhaustively explores all finite binary bitstrings \( \{0, 1\}^* \) **after 0**, as either a path, a subpath, or a transformation/representation within the Pinion's traversal.
-/

def binary_string : Nat → List (List Bool)
| 0 => [[]]
| n + 1 => (binary_string n).flatMap (fun bs => [bs ++ [false], bs ++ [true]])

theorem binary_string_contains_all_bitstrings (n : Nat) :
  ∀ binary_list : List Bool, binary_list.length = n → binary_list ∈ binary_string n := by
  intro binary_list h_length
  induction n generalizing binary_list with
  | zero =>
    cases binary_list with
    | nil => simp [binary_string]
    | cons _ _ => contradiction
  | succ d hd =>
    cases binary_list with
    | nil => contradiction
    | cons head tail =>
      rw [List.length_cons] at h_length
      have h_tail_length : tail.length = d := Nat.pred_eq_of_succ_eq h_length
      have h_tail_in : tail ∈ binary_string d := hd tail h_tail_length
      simp [binary_string]
      cases head with
      | false =>
        apply List.Mem.append_left
        exact h_tail_in
      | true  =>
        apply List.Mem.append_right
        exact h_tail_in

def pinion_path : Nat → List (List Bool)
| 0 => [[]]
| n + 1 => (pinion_path n).flatMap (fun path => [path ++ [false], path ++ [true]])

theorem pinion_is_geosodic (binary_list : List Bool) :
  binary_list ≠ [] → ∃ n, binary_list ∈ pinion_path n := by
  intro h_nonempty
  let n := binary_list.length
  use n
  have h := binary_string_contains_all_bitstrings n binary_list rfl
  rw [pinion_traverses_all_paths n]
  exact h
