import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 2.5.9, Ex. 7

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ham⟩ := h
  have hn := le_or_succ_le a 2
  obtain h_1 | h_2 := hn
  · apply ne_of_lt
    -- is 4 or less
    calc 
      m = 2 * a := by rel [ham]
      _ ≤ 2 * 2 := by rel [h_1]
      _ = 4 := by numbers
    numbers
  · apply ne_of_gt
    -- is 6 or more
    calc 
      m = 2 * a := by rel [ham]
      _ ≥ 2 * 3 := by rel [h_2]
      _ = 6 := by numbers