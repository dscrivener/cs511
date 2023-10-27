import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- 6.1.7, Exercise 6

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro x
  intro h_x_ge_5
  induction_from_starting_point x, h_x_ge_5 with k hk IH
  · numbers
  · calc
      (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 100) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 100 + (100 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra
