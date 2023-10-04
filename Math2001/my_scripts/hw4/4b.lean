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

-- Example 3.1.6

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨k_1, hk_1⟩ := hx
  obtain ⟨k_2, hk_2⟩ := hy
  use 2 * k_1 * k_2 + 3 * k_2 + k_1 + 1
  calc
    x * y + 2 * y = (2 * k_1 + 1) * (2 * k_2 + 1) + 2 * (2 * k_2 + 1) := by rw [hk_1, hk_2]
    _ = 2 * (2 * k_1 * k_2 + 3 * k_2 + k_1 + 1) + 1 := by ring
