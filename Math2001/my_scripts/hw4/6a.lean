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

-- Example 4.2.5

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h_fac : (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw [h]
    have h_sols := eq_zero_or_eq_zero_of_mul_eq_zero h_fac
    cases h_sols with
    | inl l => 
      left
      have h3 : x = -3 := by 
        calc
          x = x + 3 - 3 := by ring
          _ = 0 - 3 := by rw [l]
          _ = -3 := by numbers
      apply h3
    | inr r =>
      right
      have hn2 : x = 2 := by
        calc
          x = x - 2 + 2 := by ring
          _ = 0 + 2 := by rw [r]
          _ = 2 := by numbers
      apply hn2
  · intro h_sols
    cases h_sols with
    | inl l =>
      calc
        x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [l]
        _ = 0 := by numbers
    | inr r =>
      calc
        x ^ 2 + x - 6 = (2) ^ 2 + (2) - 6 := by rw [r]
        _ = 0 := by numbers
    