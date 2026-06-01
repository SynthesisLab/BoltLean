import BoltLean.Boolean.Basic

namespace BoolFormula
  theorem true_replace_accepts (f1 f2: BoolFormula n_var):
    f1.dominates f2 -> ∀ (v: Valuation n_var), (True.replace f2 f1).accepts v := by
      intro h v
      simp [replace]
      split
      . next heq =>
          rw [←heq] at h
          simp [dominates] at h
          apply h v
      . next hne => simp


  theorem var_replace_accepts (f1 f2: BoolFormula n_var) (i: Fin n_var) (neg: Bool):
    f1.dominates f2 -> ∀ (v: Valuation n_var), (Var i neg).accepts v -> ((Var i neg).replace f2 f1).accepts v := by
      intro h v
      simp [replace]
      split
      . next heq =>
          rw [←heq] at h
          simp [dominates] at h
          apply h v
      . next hne => simp

  theorem domin_replace (f1 f2: BoolFormula n_var):
    f1.dominates f2 →
      ∀ (f: BoolFormula n_var), (f.replace f2 f1).dominates f := by
      intro hd f v ha
      induction f with
      | True => apply true_replace_accepts; assumption
      | False => contradiction
      | Var i neg =>
        apply var_replace_accepts
          <;> assumption
      | And g1 g2 ih1 ih2 =>
        unfold replace
        simp
        split
        . next heq =>
          rw [←heq] at hd
          apply hd v
          assumption
        . next hne =>
          simp
          simp at ha
          constructor
          . exact ih1 ha.left
          . exact ih2 ha.right
      | Or g1 g2 ih1 ih2 =>
        unfold replace
        simp
        split
        . next heq =>
          rw [←heq] at hd
          apply hd v
          assumption
        . next hne =>
          simp
          simp at ha
          match ha with
          | .inl h1 => left; exact ih1 h1
          | .inr h2 => right; exact ih2 h2

end BoolFormula
