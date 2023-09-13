import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

example {p q r : Prop} (h1 : p ∧ ¬q → r) (h2 : ¬r) (h3 : p) : q := by
  have h_contra : ¬q → ⊥ := by
    intro h_nq
    have h_pnq : p ∧ ¬q := And.intro h3 h_nq
    have h_r : r := by apply h1 h_pnq
    contradiction
  have h_nnq : ¬¬q := by apply h_contra
  apply notnotE h_nnq
  
