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

-- 5.2.7 Exercise 1

def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

-- 1 will be the LEM case

-- show that 0 is tribalanced
theorem zero_tribalanced : Tribalanced 0 := by
  intro n
  conv => ring -- lean said "try ring_nf" when I attempted to use ring
  numbers

-- show that 2 is not tribalanced
theorem not_two_tribalanced : ¬ Tribalanced 2 := by
  intro h
  have three_less_three := h 3
  numbers at three_less_three

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h_1 : Tribalanced 1
  · use 1
    constructor
    · apply h_1
    · numbers
      have h_n2 := not_two_tribalanced
      apply h_n2
  · use 0
    constructor
    · have h_0 := zero_tribalanced
      apply h_0
    · numbers
      apply h_1