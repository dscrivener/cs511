import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 2.5.2

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0 
  obtain hx | hx := H 
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have htx' : 0 < (-t) * x := by
      calc
        0 < (-x) * t := by rel [hxt']
        _ = (-t) * x := by ring
    cancel x at htx'
    apply ne_of_lt
    have ht' : (t < 0) := by addarith[htx']
    apply ht'