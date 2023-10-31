import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

-- 6.1.7, Exercise 2

theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · ring
    numbers
  · have h_2 : 0 ≤ 1 + a := by addarith [ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
      _ ≥ (1 + k * a) * (1 + a) := by rel [IH]
      _ = k * a ^ 2 + k * a + a + 1 := by ring
      _ ≥ k * a + a + 1 := by extra
      _ = 1 + (k + 1) * a := by ring