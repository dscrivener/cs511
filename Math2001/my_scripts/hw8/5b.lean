import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

-- Proof: "The sum of the first n >= 1 odd natural numbers is a perfect square"

-- define sum as recursive function
def first_n_odd_nats : ℕ → ℕ
| 0 => 0
| n + 1 => first_n_odd_nats n + 2 * n + 1

theorem problem5b : ∀ n : ℕ, ∃ j, n ≥ 1 → first_n_odd_nats n = j ^ 2 := by
  intro n
  use n
  intro n_ge_1
  induction_from_starting_point n, n_ge_1 with k hk IH
  · dsimp [first_n_odd_nats]
    numbers
  · dsimp [first_n_odd_nats]
    ring
    calc
      1 + k * 2 + first_n_odd_nats k = 1 + k * 2 + k ^ 2 := by rw [IH]



    