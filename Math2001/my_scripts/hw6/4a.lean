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

-- 5.1.7 Exercise 11

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h_Px
    obtain ⟨x, h_Px'⟩ := h_Px
    use x
    obtain h_forthisx := h x
    rw [h_forthisx] at h_Px'
    apply h_Px'
  · intro h_Qx
    obtain ⟨x, h_Qx'⟩ := h_Qx
    use x
    obtain h_forthisx := h x
    rw [←h_forthisx] at h_Qx'
    apply h_Qx'