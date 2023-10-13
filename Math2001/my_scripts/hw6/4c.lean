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

-- 5.1.7 Exercise 13

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h_allxy
    intro y
    intro x
    have h_forthisxy := h_allxy x y
    apply h_forthisxy
  · intro h_allyx
    intro y
    intro x
    have h_forthisyx := h_allyx x y
    apply h_forthisyx