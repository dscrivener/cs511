import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
     x ^ 3 - 8 * x ^ 2 + 2 * x = x * x ^ 2 - 8 * x ^ 2 + 2 * x := by ring
     _ ≥ 9 * (x ^ 2) - 8 * (x ^ 2) + 2 * x := by rel [hx]
     _ = (x ^ 2) + 2 * x := by ring
     _ ≥ 9 ^ 2 + 2 * 9 := by rel [hx]
     _ ≥ 3 := by numbers 