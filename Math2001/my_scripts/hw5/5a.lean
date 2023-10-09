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

-- Example 4.3.2

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a
    intro h_ge1
    intro h_le3
    have h_lin1 : -1 ≤ a - 2 := by addarith [h_ge1]
    have h_lin3 : a - 2 ≤ 1 := by addarith [h_le3]
    have h_sq : (a - 2) ^ 2 ≤ 1 ^ 2 := by apply sq_le_sq' h_lin1 h_lin3
    numbers at h_sq
    apply h_sq
  · intro y hy
    have h_y1 := hy 1
    have h_y3 := hy 3
    have h_y1' := by
      apply h_y1
      simp
      simp
    have h_y3' := by
      apply h_y3
      simp
      simp
    have h_le0 : (y - 2) ^ 2 ≤ 0 := by
      calc
        (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + (3 - y) ^ 2 - 2) / 2 := by rel [h_y1']
        _ ≤ (1 + 1 - 2) / 2 := by rel [h_y3']
        _ = 0:= by numbers
    have h_ge0 : (y - 2) ^ 2 ≥ 0 := by extra
    have h_0 : (y - 2) ^ 2 = 0 := by apply le_antisymm h_le0 h_ge0
    have h_factor : (y - 2) * (y - 2) = 0 := by
      calc
        (y - 2) * (y - 2) = (y - 2) ^ 2 := by ring
        _ = 0 := by rw [h_0]
    have h_sols := eq_zero_or_eq_zero_of_mul_eq_zero h_factor
    cases h_sols with
    | inl l => addarith [l]
    | inr r => addarith [r]
    
    


