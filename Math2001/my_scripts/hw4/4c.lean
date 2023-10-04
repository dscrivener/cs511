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

-- Example 3.1.8

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even] at *
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5 = (k + k) ^ 2 + 2 * (k + k) - 5 := by rw [hk]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring