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

-- 3.1.10 Ex. 14

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  · obtain hb | hb := Int.even_or_odd b
    · left
      obtain ⟨k, hk⟩ := ha
      obtain ⟨k2, hk2⟩ := hb
      use k - k2
      calc
        a - b = 2 * k - b := by rw [hk]
        _ = 2 * k - 2 * k2 := by rw [hk2]
        _ = (k - k2) + (k - k2) := by ring
    · obtain hc | hc := Int.even_or_odd c
      · right
        left
        obtain ⟨k, hk⟩ := ha
        obtain ⟨k2, hk2⟩ := hc
        use k + k2
        calc
          a + c = 2 * k + c := by rw [hk]
          _ = 2 * k + 2 * k2 := by rw [hk2]
          _ = (k + k2) + (k + k2) := by ring
      · right
        right
        obtain ⟨k, hk⟩ := hb
        obtain ⟨k2, hk2⟩ := hc
        use k - k2
        calc
          b - c = 2 * k + 1 - c := by rw [hk]
          _ = 2 * k + 1 - (2 * k2 + 1) := by rw [hk2]
          _ = (k - k2) + (k - k2) := by ring
  · obtain hb | hb := Int.even_or_odd b
    · obtain hc | hc := Int.even_or_odd c
      · right
        right
        obtain ⟨k, hk⟩ := hb
        obtain ⟨k2, hk2⟩ := hc
        use k - k2
        calc
          b - c = 2 * k - c := by rw [hk]
          _ = 2 * k - (2 * k2) := by rw [hk2]
          _ = (k - k2) + (k - k2) := by ring
      · right
        left
        obtain ⟨k, hk⟩ := ha
        obtain ⟨k2, hk2⟩ := hc
        use k + k2 + 1
        calc
          a + c = 2 * k + 1 + c := by rw [hk]
          _ = 2 * k + 1 + (2 * k2 + 1) := by rw [hk2]
          _ = (k + k2 + 1) + (k + k2 + 1) := by ring

    · left
      obtain ⟨k, hk⟩ := ha
      obtain ⟨k2, hk2⟩ := hb
      use k - k2
      calc
        a - b = 2 * k + 1 - b := by rw [hk]
        _ = 2 * k + 1 - (2 * k2 + 1) := by rw [hk2]
        _ = (k - k2) + (k - k2) := by ring
