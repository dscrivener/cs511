import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.InjectiveSurjective
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

/- 3 points -/
theorem problem4a : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
    dsimp
    push_neg
    use 5
    constructor
    · use 1
      numbers
    · apply Nat.not_dvd_of_exists_lt_and_lt
      use 0
      numbers
      simp

/- 3 points -/
theorem problem4b : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by
  ext x
  dsimp
  constructor
  · intro h_left
    obtain ⟨k, h_97⟩ := h_left
    use 4 * x - 3 * k
    calc
      x = 28 * x - 27 * x := by ring
      _ = 28 * x - 3 * (9 * x) := by ring
      _ = 28 * x - 3 * (7 * k) := by rw [h_97]
      _ = 7 * (4 * x - 3 * k) := by ring
  · intro h_left
    obtain ⟨k, h_7⟩ := h_left
    use 9 * k
    rw [h_7]
    ring

/- 4 points -/
theorem problem4c : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by
  ext x
  dsimp
  constructor
  · intro h_left
    have h_factor : (x + 1) * (x + 2) = 0 := by
      calc
        (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by ring
        _ = 0 := by rw [h_left]
    have h_sols := eq_zero_or_eq_zero_of_mul_eq_zero h_factor
    cases h_sols with
    | inl l =>
      left
      addarith [l]
    | inr r =>
      right
      addarith [r]
  · intro h_left
    cases h_left with
    | inl l =>
      rw [l]
      numbers
    | inr r =>
      rw [r]
      numbers

/- 3 points -/
theorem problem5a : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp
  intro x
  intro h_left
  obtain ⟨k, h_mod7⟩ := h_left
  constructor
  · use 5 * k + 3
    calc
      x - 1 = x - 7 + 6 := by ring
      _ = 10 * k + 6 := by rw [h_mod7]
      _ = 2 * (5 * k + 3) := by ring
  · use 2 * k + 1
    calc
      x - 2 = x - 7 + 5 := by ring
      _ = 10 * k + 5 := by rw [h_mod7]
      _ = 5 * (2 * k + 1) := by ring

/- 3 points -/
theorem problem5b : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp
  intro x
  intro h_left
  obtain ⟨h_5, h_8⟩ := h_left
  obtain ⟨k_1, h_5d⟩ := h_5
  obtain ⟨k_2, h_8d⟩ := h_8
  use -3 * k_2 + 2 * k_1
  calc
    x = -15 * x + 16 * x := by ring
    _ = -15 * (8 * k_2) + 16 * x := by rw [h_8d]
    _ = -15 * (8 * k_2) + 16 * (5 * k_1) := by rw [h_5d]
    _ = 40 * (-3 * k_2 + 2 * k_1) := by ring


/- 4 points -/
theorem problem5c :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  dsimp
  intro x
  intro h_left
  cases h_left with
  | inl h_3 =>
    obtain ⟨a, h_3⟩ := h_3
    intro h_contra
    obtain ⟨b, h_mod6⟩ := h_contra
    sorry
  | inr h_2 =>
    obtain ⟨a, h_2⟩ := h_2
    intro h_contra
    obtain ⟨b, h_mod6⟩ := h_contra
    sorry
