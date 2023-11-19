import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

def Injective (f : X → Y) : Prop := ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2

def Surjective (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y

-- 8.1.13, Exercise 15 (Prove or disprove)
-- Going to disprove: can no longer map to odd numbers

theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  dsimp [Surjective]
  push_neg
  use fun x ↦ x
  constructor
  · intro y
    use y
    extra
  · use 1
    intro x
    simp
    push_neg
    have h_1_odd : Int.Odd 1 := by
      dsimp [Int.Odd]
      use 0
      numbers
    have h_1_parity_rule := Int.odd_iff_not_even 1
    obtain ⟨h_1_not_even', _⟩ := h_1_parity_rule
    have h_1_not_even : ¬ Int.Even 1 := by
      apply h_1_not_even'
      apply h_1_odd
    dsimp [Int.Even] at h_1_not_even
    push_neg at h_1_not_even
    have h_1_not_even_for_x := h_1_not_even x
    simp at *
    -- i am not sure why,
    -- but lean refuses to recognize that ¬1 = 2 * x closes the goal
    -- so i will painstakingly flip it around in the following manner
    have h := ne_or_eq (2 * x) 1
    cases h with
    | inl l =>
      simp at l
      apply l
    | inr r =>
      have r' : 1 = 2 * x := by rw [r]
      contradiction

-- 8.1.13, Exercise 16 (Prove or disprove)
-- Going to disprove: does not work for c = 0

theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  dsimp [Surjective]
  push_neg
  use 0
  use 1
  intro x
  ring
  numbers

-- 8.1.13, Exercise 17
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  dsimp [Injective]
  intro x
  intro y
  intro h_eq
  have h_cases := lt_trichotomy x y
  cases h_cases with
  | inl x_l_y =>
    have fx_l_fy : f x < f y := by
      apply hf
      apply x_l_y
    have h_contra := ne_of_lt fx_l_fy
    contradiction
  | inr r =>
    cases r with
    | inl x_e_y =>
      apply x_e_y
    | inr y_l_x =>
      have fy_l_fx : f y < f x := by
        apply hf
        apply y_l_x
      have h_contra := ne_of_gt fy_l_fx
      contradiction

-- 8.1.13, Exercise 18
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro y
  simple_induction y with k IH
  · use x0
    apply h0
  · obtain ⟨x_prev, h_prev⟩ := IH
    use i x_prev
    rw [hi]
    rw [h_prev]

def Bijective (f : X → Y) : Prop := Injective f ∧ Surjective f

-- 8.2.8, Exercise 1
-- Going to prove positive version
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  dsimp [Bijective, Injective, Surjective]
  constructor
  · intro x
    intro y
    intro h
    have h_eq : 3 * x = 3 * y := by addarith [h]
    cancel 3 at h_eq
  · intro y
    use (4 - y) / 3
    ring

-- 8.2.8, Exercise 2
-- Going to disprove: quadratics are not invertible

theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective, Injective, Surjective]
  push_neg
  intro h
  use -2
  intro x
  apply ne_of_gt
  have x2_nn : x ^ 2 + 2 * x + 1 ≥ 0 := by
    calc
      x ^ 2 + 2 * x + 1 = (x + 1) ^ 2 := by ring
      (x + 1) ^ 2 ≥ 0 := by extra
  have lower_bound : x ^ 2 + 2 * x ≥ -1 := by addarith [x2_nn]
  calc
    -2 < -1 := by numbers
    _ ≤ x ^ 2 + 2 * x := by rel [lower_bound]

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

-- 8.3.10, Exercise 2
def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

theorem problem5c : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    calc
      (v ∘ u) x = v (u x) := by rfl
      _ = (5 * x + 1 - 1) / 5 := by rfl
      _ = x := by ring
  · ext x
    calc
      (u ∘ v) x = u (v x) := by rfl
      _ = 5 * ((x - 1) / 5) + 1 := by rfl
      _ = x := by ring

-- 8.3.10, Exercise 3
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at *
  intro a
  intro b
  intro h
  have h_f_eq : f a = f b := by
    apply hg
    apply h
  apply hf
  apply h_f_eq
