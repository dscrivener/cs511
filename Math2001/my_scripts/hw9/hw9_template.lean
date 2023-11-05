import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
-- 6.2.7, Exercise 4
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · dsimp [B]
    numbers
  · calc
      B (k + 1) = B k + (k + 1 : ℚ) ^ 2 := by rw [B]
      _ = ↑k * (↑k + 1) * (2 * ↑k + 1) / 6 + (k + 1 : ℚ) ^ 2 := by rw [IH]
      _ = (↑k + 1) * (↑k + 1 + 1) * (2 * (↑k + 1) + 1) / 6 := by ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
-- 6.2.7, Exercise 5
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · dsimp [S]
    numbers
  · calc
      S (k + 1) = S k + 1 / 2 ^ (k + 1) := by rw [S]
      _ = (2 - 1 / 2 ^ k) + 1 / 2 ^ (k + 1) := by rw [IH]
      _ = 2 - 1 / 2 ^ (k + 1) := by ring

/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  rw [problem4b]
  have h_nn : 1 / 2 ^ n ≥ (0 : ℚ) := by extra
  calc
    (2 : ℚ) - 1 / 2 ^ n = 2 - (1 / 2 ^ n) := by ring
    _ ≤ 2 := by addarith [h_nn]

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
-- 6.2.7, Exercise 8
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k IH
  · dsimp [factorial]
    numbers
  · have h_k2_k1 : (k + 2) >= (k + 1) := by
      have h_cases := lt_or_le (k + 2) (k + 1)
      cases h_cases with
      | inl l => addarith
      | inr r => apply r 
    have h_base : (k + 2) ^ k ≥ (k + 1) ^ k := by rel [h_k2_k1]
    calc
      (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ = (k + 2) * (k + 1)! := by extra
      _ ≤ (k + 2) * (k + 1) ^ k := by rel [IH]
      _ ≤ (k + 2) * (k + 2) ^ k := by rel [h_base]
      _ = (k + 2) ^ (k + 1) := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

/- 3 points -/
-- 6.3.6, Exercise 4
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · dsimp [q]
    numbers
  · dsimp [q]
    numbers
  · calc
      q (k + 1 + 1) = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * q (k + 1) - (↑k ^ 3 + 1) + 6 * k + 6 := by rw [IH1]
      _ = 2 * ((↑k + 1) ^ 3 + 1) - (↑k ^ 3 + 1) + 6 * k + 6 := by rw [IH2]
      _ = (↑k + 1 + 1) ^ 3 + 1 := by ring

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
-- 6.3.6, Exercise 7
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro x
  intro h_ge
  two_step_induction_from_starting_point x, h_ge with k hk IH1 IH2
  · dsimp [r]
    numbers
  · dsimp [r]
    numbers
  · calc
      r (k + 1 + 1) = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * r (k + 1) + 2 ^ k := by rel [IH1]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH2]
      _ = 2 ^ (k + 2) + 2 ^ k := by ring
      _ = 2 ^ (k + 1 + 1) + 2 ^ k := by extra
      _ ≥ 2 ^ (k + 1 + 1) := by extra

/- 3 points -/
-- 6.4.3, Exercise 1
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h_n_even | h_n_odd := Nat.even_or_odd n
  · obtain ⟨b, h_b⟩ := h_n_even 
    obtain h_b_even | h_b_odd := Nat.even_or_odd b
    · have IH1 := problem5c b
      have b_ge_0 : (b ≥ 0) := by extra
      have b_g_0 : (b > 0) := by
        have b_cases := le_or_succ_le b 0
        cases b_cases with
        | inl l => 
          have b_0 : b = 0 := by apply le_antisymm l b_ge_0
          have n_0 : n = 0 := by
            calc
              n = 2 * b := by rw [h_b]
              _ = 2 * 0 := by rw [b_0]
          have h_ge_0 : (n ≤ 0) := by
            calc
              n = 0 := by rel [n_0]
              _ ≤ 0 := by numbers
          have h_n_ge_0 : ¬(n > 0) := not_lt_of_ge h_ge_0
          contradiction
        | inr r => apply r
      have IH1_mod : ∃ a x, Odd x ∧ b = 2 ^ a * x := by
        apply IH1
        apply b_g_0
      obtain ⟨a_works, IH1_mod⟩ := IH1_mod
      obtain ⟨x_works, IH1_mod⟩ := IH1_mod
      obtain ⟨h_x_odd, h_eq⟩ := IH1_mod
      use a_works + 1
      use x_works
      constructor
      · apply h_x_odd
      · calc
          n = 2 * b := by rw [h_b]
          _ = 2 * (2 ^ a_works * x_works) := by rw [h_eq]
          _ = 2 ^ (a_works + 1) * x_works := by ring
    · use 1
      use b
      constructor
      · apply h_b_odd
      · calc
          n = 2 * b := by rw [h_b]
          _ = (2 ^ 1) * b := by extra
  · use 0
    use n
    constructor
    · apply h_n_odd
    · numbers
      ring
