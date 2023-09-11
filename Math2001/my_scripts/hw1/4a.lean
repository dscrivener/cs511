import Mathlib.Data.Real.Basic

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * 3 + 5 := by rw [h1, h2]
    _ = 11 := by ring