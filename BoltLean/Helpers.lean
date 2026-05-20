open Classical

theorem my_contra (a b: Prop): (a → b) ↔ (¬b → ¬a) := by
  constructor
  . intro himp hnb ha
    apply hnb
    apply himp
    exact ha
  . intro himp ha
    apply byContradiction
    intro hnb
    apply absurd
    . exact ha
    . apply himp
      assumption
