import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- Example 4.1.6

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x
  intro y
  intro h_xy
  have h_x3 : (x + y) ^ 2 ≤ 3 ^ 2 := by
    calc
      (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
      _ = 2 * (x ^ 2 + y ^ 2) := by ring
      _ ≤ 2 * 4 := by rel [h_xy]
      _ ≤ 3 ^ 2 := by numbers
  have h_3 : (0 ≤ 3) := by numbers
  have h_ : -3 ≤ x + y ∧ x + y ≤ 3 := by 
    apply abs_le_of_sq_le_sq' h_x3
    numbers
  obtain ⟨h_ge, _⟩ := h_ 
  apply h_ge
  
