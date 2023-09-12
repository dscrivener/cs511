import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {p q r : Prop} (h : (p ∧ q) → r) : p → (q → r) := by
  intro h_p
  intro h_q
  have h_pq : p ∧ q := And.intro h_p h_q
  apply h h_pq