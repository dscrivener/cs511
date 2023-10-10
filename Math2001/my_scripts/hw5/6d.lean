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
namespace Nat

-- 4.4.6 Exercise 5

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at h
  obtain ⟨p_ge_2, p_facs⟩ := h
  obtain p_le_2 | p_ge_3 := le_or_succ_le p 2
  · left
    apply le_antisymm p_le_2 p_ge_2
  · right
    -- if p were even, 2 would divide p
    -- p would then have to be 2, but it isn't leading to a contradiction
    have h_even_or_odd := even_or_odd p
    dsimp [Even] at h_even_or_odd
    cases h_even_or_odd with
    | inl h_even => 
      have h_2_div_p : 2 ∣ p := by apply h_even
      have h_2_not_fac_p := p_facs 2
      have h_contra : 2 = p := by
        simp at h_2_not_fac_p
        apply h_2_not_fac_p
        apply h_2_div_p
      have h_plt3 : p < 3 := by
        calc
          p = 2 := by rw [h_contra]
          _ < 3 := by numbers
      have h_contra_2 : ¬p < 3 := by apply not_lt_of_ge p_ge_3
      contradiction
    | inr h_odd => apply h_odd
      

