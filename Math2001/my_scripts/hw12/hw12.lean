import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Library.Theory.InjectiveSurjective
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
import Library.Tactic.Product

set_option push_neg.use_distrib true
open Function

/- 3 points -/
theorem problem4a {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
    dsimp [Surjective] at *
    intro b
    have ⟨g_a, g_s⟩ := hg b
    have ⟨f_a, f_s⟩ := hf g_a
    use f_a
    rw [f_s]
    rw [g_s]

/- 2 points -/
theorem problem4b {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at *
  choose g hg using hf
  use g
  ext x
  have hg_x := hg x
  calc
    (f ∘ g) x = f (g x) := by rfl
    _ = x := by rw [hg_x]

/- 2 points -/
theorem problem4c {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at *
  obtain ⟨fg, gf⟩ := h
  constructor
  · apply gf
  · apply fg

/- 3 points -/
theorem problem4d {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
    dsimp [Inverse] at *
    ext x
    obtain ⟨g1f, fg1⟩ := h1
    obtain ⟨g2f, fg2⟩ := h2
    dsimp [id] at *
    have fg1_x : (f ∘ g1) x = x := by rw [fg1]
    have fg2_x : (f ∘ g2) x = x := by rw [fg2]

    have f_eq : (f ∘ g1) x = (f ∘ g2) x := by rw [fg1_x, fg2_x]
    have gf_eq : g1 ((f ∘ g1) x) = g1 ((f ∘ g2) x) := by rw [f_eq]

    have g_undo_f_1 :  g1 ((f ∘ g1) x) = (g1 x) := by
      calc
        g1 ((f ∘ g1) x) = (g1 ∘ f ∘ g1) x := by rfl
        _ = (g1 ∘ f) (g1 x) := by rfl
        _ = g1 x := by rw [g1f]
    have g_undo_f_2 :  g1 ((f ∘ g2) x) = (g2 x) := by
      calc
        g1 ((f ∘ g2) x) = (g1 ∘ f ∘ g2) x := by rfl
        _ = (g1 ∘ f) (g2 x) := by rfl
        _ = g2 x := by rw [g1f]

    rw [g_undo_f_1, g_undo_f_2] at gf_eq
    apply gf_eq

/- 1 points -/
theorem problem5a1 : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective] at *
  push_neg
  use (2, 1), (4, 2)
  numbers
  simp

/- 1 points -/
theorem problem5a2 : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective] at *
  intro b
  use (b + 3, 1)
  numbers
  ring

/- 2 points -/
theorem problem5b : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro xy
  apply ne_of_gt
  have h_nn : xy.fst ^ 2 + xy.snd ^ 2 ≥ 0 := by extra
  calc
    -1 < 0 := by numbers
    _ ≤ xy.fst ^ 2 + xy.snd ^ 2 := by rel [h_nn]

/- 3 points -/
theorem problem5c : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective] at *
  push_neg
  use (0,0,0), (1,-2,1)
  numbers
  simp

/- 3 points -/
theorem problem5d : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  dsimp [Injective] at *
  intro xy1
  intro xy2
  set a := xy1.fst
  set b := xy1.snd
  set c := xy2.fst
  set d := xy2.snd
  intro h
  obtain ⟨eq1, eq2, eq3⟩ := h
  have bd' : c + d + b = c + d + d := by
    calc
      c + d + b = a + b + b := by rw [eq1]
      _ = a + 2 * b := by ring
      _ = c + 2 * d := by rw [eq2]
      _ = c + d + d := by ring
  have bd : b = d := by addarith [bd']
  rw [bd] at eq1
  have ac : a = c := by addarith [eq1]
  constructor
  · apply ac
  · apply bd
