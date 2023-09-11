import Mathlib.Data.Real.Basic

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring