import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 2.5.9, Ex. 6

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, hat⟩ := h
  intro contra
  have l_s : a * t + 1 = a + 1 := by
    calc
      a * t + 1 = a * 1 + 1 := by rw [contra]
      _ = a + 1 := by ring
  have r_s : a + t = a + 1 := by
    calc
      a + t = a + t := by ring
      _ = a + 1 := by rw [contra]
  have h_contra_1 : a + 1 < a + 1 := by
    calc
      a + 1 = a * t + 1 := by rw [l_s]
      _ < a + t := by rel [hat]
      _ = a + 1 := by rw [r_s]
  have h_contra_2 : 1 < 1 := by addarith [h_contra_1]
  numbers at h_contra_2