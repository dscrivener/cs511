import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

-- Example 6.1.3

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · -- base case
    use 0
    calc
      a ^ 0 - b ^ 0 = 0 := by ring
      _ = d * 0 := by ring
  · -- inductive step
    obtain ⟨x, h_x⟩ := IH
    obtain ⟨y, h_y⟩ := h
    use (a * x + b ^ k * y)
    calc
      a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d * x) + b ^ k * (a - b) := by rw [h_x]
      _ = a * (d * x) + b ^ k * (d * y):= by rw [h_y]
      _ = d * (a * x + b ^ k * y) := by ring