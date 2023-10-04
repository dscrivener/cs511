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

-- 4.1.10 Ex. 2

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h_3 := hn 3
  simp at h_3
  have h_5 := hn 5
  simp at h_5
  obtain ⟨b, hb⟩ := h_3
  obtain ⟨a, ha⟩ := h_5
  use 2 * a - b
  calc
    n = 6 * n - 5 * n := by ring
    _ = 6 * (5 * a) - 5 * n := by rw [ha]
    _ = 6 * (5 * a) - 5 * (3 * b) := by rw [hb]
    _ = 15 * (2 * a - b) := by ring





