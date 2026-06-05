import BoltLean.Boolean.Basic

namespace BoolFormula
  /-- Aux Lemma: `True` -/
  theorem true_replace_accepts (f1 f2: BoolFormula n):
    f1.dominates f2 -> ∀ (v: Valuation n), (True.replace f2 f1).accepts v := by
      intro h v
      simp [replace]
      split
      . next heq =>
          rw [←heq] at h
          simp [dominates] at h
          apply h
      . next hne => simp

  /-- Aux Lemma: `False` -/
  theorem false_replace_not_accepts (f1 f2: BoolFormula n):
    f1.dominates f2 -> ∀ (v: Valuation n), ¬ (False.replace f2 f1).accepts v := by
      intro h v
      simp [replace]
      split
      . next heq =>
          rw [←heq] at h
          simp [dominates] at h
          apply h
      . next hne => simp

  /-- Aux Lemma: `Var` -/
  theorem var_replace_accepts (f1 f2: BoolFormula n) (i: Fin n) (neg: Bool):
    f1.dominates f2 ->
      ∀ (v: Valuation n) (b: Bool),
        (Var i neg).satisfies v b -> ((Var i neg).replace f2 f1).satisfies v b := by
      intro h v b hv
      simp [replace]
      split
      . next heq =>
          rw [←heq] at h
          apply h
          exact hv
      . next hne => assumption

  /-- Theorem: if f1 dominates f2, then in any formula f,
  replacing f2 by f1 yields a dominating formula.-/
  theorem domin_replace (f1 f2: BoolFormula n):
    f1.dominates f2 →
      ∀ (f: BoolFormula n), (f.replace f2 f1).dominates f := by
      intro hd f v b ha
      induction f with
      | True =>
        cases b with
        | false => simp at ha
        | true => simp; exact true_replace_accepts f1 f2 hd v
      | False =>
        cases b with
        | false => simp [replace]; exact false_replace_not_accepts f1 f2 hd v
        | true => simp at ha
      | Var i neg =>
        apply var_replace_accepts
          <;> assumption
      | And g1 g2 ih1 ih2 =>
        simp [replace]
        split
        . next heq =>
          apply hd
          rw [heq] at ha
          exact ha
        . next hne =>
          cases b with
          | false =>
            simp at *
            intro h
            by_cases hx: g1.accepts v
            . exact ih2 (ha hx)
            . have hc:= ih1 hx
              contradiction
          | true =>
            simp at *
            exact ⟨ih1 ha.left, ih2 ha.right⟩
      | Or g1 g2 ih1 ih2 =>
        simp [replace]
        split
        . next heq =>
          apply hd
          rw [heq] at ha
          assumption
        . next hne =>
          cases b with
          | false =>
            simp at *
            exact ⟨ih1 ha.left, ih2 ha.right⟩
          | true =>
            simp at *
            match ha with
            | .inl h1 => left; exact ih1 h1
            | .inr h2 => right; exact ih2 h2

end BoolFormula
