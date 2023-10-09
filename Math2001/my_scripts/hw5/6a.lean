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

-- Example 4.4.4

example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    have h_mlep : m ≤ p := by apply Nat.le_of_dvd hp' hmp
    have h_mlp_or_mep : m = p ∨ m < p := eq_or_lt_of_le h_mlep
    cases h_mlp_or_mep with
    | inl l =>
      right
      apply l
    | inr h_mlp =>
      have h_contra1 := H m
      have h_contra2 : ¬m ∣ p := by
        apply h_contra1
        apply hm_left
        apply h_mlp
      contradiction