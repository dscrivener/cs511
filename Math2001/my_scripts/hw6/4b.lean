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

-- 5.1.7 Exercise 12

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h_xyworks
    obtain ⟨x, h_forthisx⟩ := h_xyworks
    obtain ⟨y, h_forthisxy⟩ := h_forthisx
    use y
    use x
    apply h_forthisxy
  · intro h_yxworks
    obtain ⟨y, h_forthisy⟩ := h_yxworks
    obtain ⟨x, h_forthisyx⟩ := h_forthisy
    use x
    use y
    apply h_forthisyx
