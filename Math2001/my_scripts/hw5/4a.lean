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

-- 4.2.10 Exercise 2

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h_63
    obtain ⟨a, ha⟩ := h_63
    constructor
    · use 9 * a
      calc
        n = 63 * a := by rw [ha]
        _ = 7 * (9 * a) := by ring
    · use 7 * a
      calc
        n = 63 * a := by rw [ha]
        _ = 9 * (7 * a) := by ring
  · intro h_7_9
    obtain ⟨h_7, h_9⟩ := h_7_9
    obtain ⟨a, ha⟩ := h_7
    obtain ⟨b, hb⟩ := h_9
    use (4 * b - 3 * a)
    calc
      n = 28 * n - 27 * n := by ring
      _ = 28 * (9 * b) - 27 * n := by rw [hb]
      _ = 28 * (9 * b) - 27 * (7 * a) := by rw [ha]
      _ = 63 * (4 * b - 3 * a) := by ring