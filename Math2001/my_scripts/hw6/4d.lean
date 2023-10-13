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

-- 5.1.7 Exercise 14

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h_xworks_and_q
    obtain ⟨h_xworks, q⟩ := h_xworks_and_q
    obtain ⟨x, h_Px⟩ := h_xworks
    use x
    constructor
    · apply h_Px
    · apply q
  · intro h_xworks
    obtain ⟨x, h_PxQ⟩ := h_xworks
    obtain ⟨h_Px, q⟩ := h_PxQ
    constructor
    · use x
      apply h_Px
    · apply q
    