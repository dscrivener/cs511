import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 2.5.7

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  have pl := by 
    calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  have pr := by
    calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by rel [h]
  apply And.intro pl pr