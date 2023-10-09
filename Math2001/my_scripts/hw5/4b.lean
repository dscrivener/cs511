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

-- 4.2.10 Exercise 5

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h_ksq6
    have h_kl3 : k ^ 2 < 3 ^ 2 :=
      calc
        k ^ 2 ≤ 6 := by rel [h_ksq6]
        _ < 3 ^ 2 := by numbers
    cancel 2 at h_kl3
    have h_kg0 : k ≥ 0 := by extra
    have h_split_1 := le_or_succ_le k 0
    cases h_split_1 with
    | inl l => 
      left
      apply le_antisymm l h_kg0
    | inr r =>
      right
      have h_split_2 := le_or_succ_le k 1
      cases h_split_2 with
      | inl l_2 => 
        left
        apply le_antisymm l_2 r
      | inr r_2 =>
        have h_split_3 := le_or_succ_le k 2
        cases h_split_3 with
        | inl l_3 => 
          right
          apply le_antisymm l_3 r_2
        | inr r_3 =>
          have h_contra : ¬k < 3 := by
            apply not_lt_of_ge
            apply r_3
          contradiction
  · intro h_k012
    cases h_k012 with
    | inl h_k0 => extra
    | inr r_k12 => 
      cases r_k12 with
      | inl h_k1 =>
        calc
          k ^ 2 = 1 ^ 2 := by rw [h_k1]
          _ ≤ 6 := by numbers 
      | inr h_k2 =>
        calc
          k ^ 2 = 2 ^ 2 := by rw [h_k2]
          _ ≤ 6 := by numbers 