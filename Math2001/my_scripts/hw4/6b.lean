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

-- Example 4.2.6

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h_ineq
    have h_sq : (2 * a - 5) ^ 2 ≤ 1 ^ 2 := by
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel [h_ineq]
        _ = 1 ^ 2 := by numbers
    have h_abs_sq : (-1 ≤ 2 * a - 5) ∧ (2 * a - 5 ≤ 1) := by
      apply abs_le_of_sq_le_sq' h_sq
      numbers
    obtain ⟨h_n1, h_1⟩ := h_abs_sq
    have h_2 : 2 * 2 ≤ 2 * a := by addarith [h_n1]
    cancel 2 at h_2
    have h_3 : 2 * 3 ≥ 2 * a := by addarith [h_1]
    cancel 2 at h_3
    have h_cases := le_or_succ_le a 2
    cases h_cases with
    | inl l =>
      left
      have a2 : a = 2 := by 
        apply le_antisymm l h_2
      apply a2
    | inr r =>
      right
      have a3 : a = 3 := by 
        apply le_antisymm h_3 r
      apply a3
  · intro h_sols 
    cases h_sols with
    | inl l =>
      extra
    | inr r =>
      extra