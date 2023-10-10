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

-- 4.4.6 Exercise 1

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have h_cases := le_or_lt y x
  cases h_cases with
  | inl h_ylex => apply h_ylex
  | inr h_ygtx =>
    have h_contra_1 : x ^ n < y ^ n := by rel [h_ygtx]
    have h_contra_2 := not_le_of_lt h_contra_1
    contradiction