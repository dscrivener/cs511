import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q)  := by
  intro h_npnq
  obtain ⟨h_np, h_nq⟩ := h_npnq
  intro h_pq
  cases h_pq with
  | inl h_p => contradiction
  | inr h_q => contradiction