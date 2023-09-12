import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = (a - 5 * b) + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = 4 + 5 * ((b + 2) - 2) := by ring
    _ = 4 + 5 * ((3) - 2) := by rw [h2]
    _ = 9 := by ring