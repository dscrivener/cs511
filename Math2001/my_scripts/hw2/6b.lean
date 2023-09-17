import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = ((a + 2 * b) + a) / 2 := by ring
    _ ≥ ((a + 2 * b) + 3) / 2 := by rel [h1]
    _ ≥ (4 + 3) / 2 := by rel [h2]
    _ ≥ 3.5 := by numbers
    _ ≥ 3 := by numbers

