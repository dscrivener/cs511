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

-- Example 4.1.3

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h_a | h_b := h1
  · calc
      b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [h_a]
      _ = a := by ring
  · calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [h_b]
      _ = b := by ring