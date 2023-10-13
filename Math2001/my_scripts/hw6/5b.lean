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

-- 5.2.7 Exercise 3

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

-- from 5.2.2
theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

-- show that 2 is not superpowered, modeled after 5.2.4
theorem not_superpowered_two : ¬ Superpowered 2 := by
  intro h_2
  dsimp [Superpowered] at h_2
  have h_4294967297_prime := h_2 5
  numbers at h_4294967297_prime
  have h_4294967297_not_prime : ¬ Prime 4294967297 := by
    apply not_prime 6700417 641
    numbers
    numbers
    numbers
  contradiction

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  numbers
  constructor
  · have h_1 := superpowered_one
    apply h_1
  · have h_n2 := not_superpowered_two
    apply h_n2