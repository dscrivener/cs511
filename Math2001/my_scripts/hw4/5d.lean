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

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- 4.1.10 Ex. 4

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 20
  intro x
  intro h_x20
  calc
    x ^ 3 + 3 * x = x * x ^ 2 + 3 * x := by ring
    _ ≥ 20 * x ^ 2 + 3 * x := by rel [h_x20] 
    _ ≥ 20 * x ^ 2 + 3 * (20) := by rel [h_x20]
    _ = 7 * x ^ 2 + 13 * x * x + 60 := by ring
    _ ≥ 7 * x ^ 2 + (13 * 20 * 20) + 60 := by rel [h_x20]
    _ = 7 * x ^ 2 + 5248 + 12 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra
  