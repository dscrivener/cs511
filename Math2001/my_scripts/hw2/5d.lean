import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q)  := by
  intro h_npnq
  intro h_pq
  obtain ⟨h_p, h_q⟩ := h_pq
  cases h_npnq with
  | inl h_np => contradiction
  | inr h_nq => contradiction