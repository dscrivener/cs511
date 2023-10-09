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

-- Example 4.4.5
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by

  have h_a_geq1 : a ≥ 1 := by apply ha
  have h_b_geq1 : b ≥ 1 := by apply hb
  have h_c_geq1 : c ≥ 1 := by apply hc

  have h_cases := le_or_succ_le a 2
  cases h_cases with
  | inl h_ale2 =>
    have h_cases_2 := le_or_succ_le b 1
    cases h_cases_2 with
    | inl h_ble1 =>

      have h_cl3 : c ^ 2 < 3 ^ 2 := by
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel [h_ale2]
          _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [h_ble1]
          _ < 3 ^ 2 := by numbers
      cancel 2 at h_cl3

      have h_c_leq2 : c ≤ 2 := by
        obtain c_le_2 | c_ge_3 := le_or_succ_le c 2
        · apply c_le_2
        · have h_c_contra : ¬c < 3 := by
            apply not_lt_of_ge
            apply c_ge_3
          contradiction

      -- enforce values for a, b, c and exhaust all the cases... oh dear
      have h_a_vals : a = 1 ∨ a = 2 := by
        obtain h_a_le1 | h_a_ge2 := le_or_succ_le a 1
        · left
          apply le_antisymm h_a_le1 h_a_geq1
        · right
          apply le_antisymm h_ale2 h_a_ge2
      have h_b_1 : b = 1 := by
        apply le_antisymm h_ble1 h_b_geq1
      have h_c_vals : c = 1 ∨ c = 2 := by
        obtain h_c_le1 | h_c_ge2 := le_or_succ_le c 1
        · left
          apply le_antisymm h_c_le1 h_c_geq1
        · right
          apply le_antisymm h_c_leq2 h_c_ge2

      have h_contra : a ^ 2 + b ^ 2 ≠ c ^ 2 := by
        cases h_a_vals with
        | inl h_a_1 =>
          cases h_c_vals with
          | inl h_c_1 =>
            calc
              a ^ 2 + b ^ 2 = 1 ^ 2 + b ^ 2 := by rw [h_a_1]
              _ = 1 ^ 2 + 1 ^ 2 := by rw [h_b_1]
              _ ≠ 1 ^ 2 := by numbers
              _ = c ^ 2 := by rw [h_c_1]
          | inr h_c_2 =>
            calc
              a ^ 2 + b ^ 2 = 1 ^ 2 + b ^ 2 := by rw [h_a_1]
              _ = 1 ^ 2 + 1 ^ 2 := by rw [h_b_1]
              _ ≠ 2 ^ 2 := by numbers
              _ = c ^ 2 := by rw [h_c_2]
        | inr h_a_2 =>
          cases h_c_vals with
            | inl h_c_1 =>
            calc
              a ^ 2 + b ^ 2 = 2 ^ 2 + b ^ 2 := by rw [h_a_2]
              _ = 2 ^ 2 + 1 ^ 2 := by rw [h_b_1]
              _ ≠ 1 ^ 2 := by numbers
              _ = c ^ 2 := by rw [h_c_1]
            | inr h_c_2 =>
            calc
              a ^ 2 + b ^ 2 = 2 ^ 2 + b ^ 2 := by rw [h_a_2]
              _ = 2 ^ 2 + 1 ^ 2 := by rw [h_b_1]
              _ ≠ 2 ^ 2 := by numbers
              _ = c ^ 2 := by rw [h_c_2]
      contradiction

    | inr h_bge2 =>
      have b_l_c : b ^ 2 < c ^ 2 := by
        calc
          b ^ 2 < a ^ 2 + b ^ 2 := by extra
          _ = c ^ 2 := by rw [h_pyth]
      cancel 2 at b_l_c

      have bp1_le_c : b + 1 ≤ c := by apply b_l_c

      have c_l_bp1 : c ^ 2 < (b + 1) ^ 2 := by
        calc
          c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth]
          _ ≤ 2 ^ 2 + b ^ 2 := by rel [h_ale2]
          _ = b ^ 2 + 2 * 2 := by ring
          _ ≤ b ^ 2 + 2 * b := by rel [h_bge2]
          _ < b ^ 2 + 2 * b + 1 := by extra
          _ = (b + 1) ^ 2 := by ring
      cancel 2 at c_l_bp1
      
      have h_contra : ¬c < b + 1 := by
        apply not_lt_of_ge
        apply bp1_le_c

      contradiction

  | inr r => apply r
