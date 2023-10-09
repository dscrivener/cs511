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

-- 4.3.5 Exercise 2

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · simp
  · simp
    intro n
    intro h_n
    have h_ge0 : n ≥ 0 := by extra
    have h_le0 := by apply h_n 0
    apply le_antisymm h_le0 h_ge0

