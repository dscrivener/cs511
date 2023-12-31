import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {p q r : Prop} (h : p → (q → r)) : (p → q) → (p → r) := by
  intro h_pq
  intro h_p
  have h_q : q := by apply h_pq h_p
  have h_qr : q → r := by apply h h_p
  apply h_qr h_q