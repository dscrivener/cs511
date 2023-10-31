import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/- 2 points -/
theorem problem4a {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
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

/- 3 points -/
theorem problem4b : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH] 
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by addarith

/- 2 points -/
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · ring
    numbers
  · have h_2 : 0 ≤ 1 + a := by addarith [ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
      _ ≥ (1 + k * a) * (1 + a) := by rel [IH]
      _ = k * a ^ 2 + k * a + a + 1 := by ring
      _ ≥ k * a + a + 1 := by extra
      _ = 1 + (k + 1) * a := by ring

/- 3 points -/
theorem problem4d : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro x
  intro h_x_ge_5
  induction_from_starting_point x, h_x_ge_5 with k hk IH
  · numbers
  · calc
      (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 100) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 100 + (100 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra

/- 5 points -/
def foo : ℕ → ℕ
  | 0     => 1
  | n + 1 => foo (n) + 2 * n + 3

/- 5 points -/
theorem problem5b {n : ℕ} : ∃ (k : ℕ), foo (n) = k ^ 2 := by
  use n + 1
  simple_induction n with k IH
  · dsimp [foo]
    numbers
  · dsimp [foo]
    ring
    rw [IH]
    ring