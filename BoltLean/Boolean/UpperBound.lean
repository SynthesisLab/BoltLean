import BoltLean.Boolean.Basic

namespace Valuation
  @[simp]
  def exact_at_indices  (v: Valuation n_var) (indices: List (Fin n_var)): BoolFormula n_var :=
    let vars := indices.map (fun i => BoolFormula.Var i (¬v[i]))
    vars.foldr BoolFormula.And BoolFormula.True

  def exact (v: Valuation n_var): BoolFormula n_var :=
    v.exact_at_indices (List.finRange n_var)

  -- Completeness of Exact
  theorem exact_at_indices_accepts (v: Valuation n_var) (indices: List (Fin n_var)):
    (v.exact_at_indices indices).accepts v := by
      induction indices with
      | nil => simp
      | cons hd tl ih =>
        simp
        simp at ih
        exact ih

  theorem exact_accepts (v: Valuation n_var):
    v.exact.accepts v := by
    unfold exact
    apply exact_at_indices_accepts

  -- Soundness of Exact
  theorem exact_at_indices_accepts_exact (v v': Valuation n_var) (indices: List (Fin n_var)):
    (v.exact_at_indices indices).accepts v' → ∀ i ∈ indices, v[i.val] = v'[i.val] := by
    intro h i hi
    induction indices with
    | nil => simp at hi
    | cons hd tl ih =>
      simp at h
      simp [exact_at_indices] at ih
      by_cases hyp: i ∈ tl
      . exact ih h.right hyp
      . simp [hyp] at hi
        rw [hi]
        rw [eq_comm]
        exact h.left

  theorem exact_accepts_only (v v': Valuation n_var):
    v.exact.accepts v' → v = v' := by
    intro hex
    ext i hi
    unfold exact at hex
    apply exact_at_indices_accepts_exact v v' (List.finRange n_var) hex ⟨i, hi⟩
    simp

end Valuation
