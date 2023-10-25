import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 5.3.6 Exercise 2

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h_left
    by_cases h_right : P ∧ ¬Q
    · apply h_right
    · rw [not_and_or] at h_right
      rw [not_not] at h_right
      have h_contra : P → Q := by
        intro h_p
        cases h_right with
        | inl l => contradiction
        | inr r => apply r
      contradiction
  · intro h_right
    obtain ⟨h_p, h_not_q⟩ := h_right
    intro h_contra
    have h_q : Q := by apply h_contra h_p
    contradiction