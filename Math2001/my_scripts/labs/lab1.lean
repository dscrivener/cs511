example {p q : Prop} (h: (p ∨ (q → p)) ∧ q) : p := by
  have h_pqp : p ∨ (q → p) := And.left h
  have h_q : q := And.right h
  cases h_pqp with
    | inl l => apply l
    | inr r => apply r h_q

example {p q : Prop} (h1: p → q) (h2: ¬q): ¬p  := by
  intro h_p
  have h_q : q := by apply h1 h_p
  apply h2 h_q
  -- contradiction

example {p q : Prop} (h1: p) : ¬¬p := by
  intro h_np
  apply h_np h1
  -- contradiction