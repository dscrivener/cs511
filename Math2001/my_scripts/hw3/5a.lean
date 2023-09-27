import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 2.5.9, Ex. 5

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have hn := le_or_gt x 1
  obtain hx | hx := hn
  · use 2
    numbers
    have h : 4 > x := by
      calc 
        x ≤ 1 := by rel [hx]
        _ < 4 := by numbers
    apply h
  · use x
    calc
      x ^ 2 = x * x := by ring
      _ > 1 * x := by rel [hx]
      _ = x := by ring
