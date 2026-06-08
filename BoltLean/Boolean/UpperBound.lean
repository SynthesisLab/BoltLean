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

  /-- Correctness and soundness of `v.exact` -/
  theorem exact_correct (v v': Valuation n_var):
    v.exact.accepts v' ↔ v = v' := by
      constructor
      · exact exact_accepts_only v v'
      · intro h; rw [h]; exact exact_accepts v'

  theorem exists_accept_only (v: Valuation n_var) :
    ∃ (phi: BoolFormula n_var), phi.accepts v ∧
      ∀ (v': Valuation n_var), v ≠ v' → ¬ phi.accepts v' := by
      exists v.exact
      constructor
      · exact v.exact_accepts
      · intro v' hne he
        apply hne
        exact exact_accepts_only v v' he

end Valuation

/-- Given a list of valuations, construct a formula that accepts exactly these valuations. -/
def UpperBoundFormula (vs: List (Valuation n_var)) : BoolFormula n_var :=
  let fs := vs.map Valuation.exact
  fs.foldr BoolFormula.Or BoolFormula.False

/-- If some formula in a list accepts `v`, then the `Or` of the list also accepts `v`. -/
theorem foldr_or_aux (l: List (BoolFormula n)) (v: Valuation n):
  ∀ f ∈ l, f.accepts v → (l.foldr BoolFormula.Or BoolFormula.False).accepts v := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro f hm he
      cases hm
      · simp; left; exact he
      · next h_in =>
        simp; right
        apply ih f h_in he

/-- If the `Or` of a list of formulas accepts `v`, then some formula in the list accepts `v`. -/
theorem foldr_or_aux_rev (l: List (BoolFormula n)) (v: Valuation n):
  (l.foldr BoolFormula.Or BoolFormula.False).accepts v → ∃ f ∈ l, f.accepts v := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro h
      simp at h
      match h with
      | .inl h1 => exact ⟨hd, .head tl, h1⟩
      | .inr h1 =>
        obtain ⟨f, hf, hfa⟩ := ih h1
        exact ⟨f, .tail hd hf, hfa⟩

theorem list_map_contains (l: List α) (f: α → β):
  (∀ b, b ∈ l.map f → ∃ a ∈ l, b = f a) := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro b hb
      unfold List.map at hb
      rw [List.mem_cons] at hb
      match hb with
      | .inl h1 => exact ⟨hd, .head tl, h1⟩
      | .inr h1 =>
        obtain ⟨a, ha, hba⟩ := ih b h1
        exact ⟨a, .tail hd ha, hba⟩

/-- For any disjoint set of positive and negative valuations, there exists a Boolean formula
that accepts all positive valuations and rejects all negative valuations. -/
theorem UpperBound (pos: List (Valuation n_var)) (neg: List (Valuation n_var))
    (h: ∀ v ∈ pos, ∀ v' ∈ neg, v ≠ v') :
    ∃ (phi: BoolFormula n_var), (∀ v ∈ pos, phi.accepts v) ∧ (∀ v ∈ neg, ¬ phi.accepts v) := by
  exists UpperBoundFormula pos
  constructor
  · intro v hv
    unfold UpperBoundFormula
    simp
    apply foldr_or_aux (List.map Valuation.exact pos) v (v.exact)
    · induction pos with
      | nil => simp at hv
      | cons hd tl ih =>
        cases hv
        · simp
        · next hm =>
          simp
          right
          simp at h
          have hr := h.right
          have h2 := ih hr
          exact ⟨v, hm, rfl⟩
    · exact Valuation.exact_accepts v
  · intro v hv he
    unfold UpperBoundFormula at he
    simp at he
    have h1 := foldr_or_aux_rev (List.map Valuation.exact pos) v he
    match h1 with
    | ⟨f, hf⟩ =>
      have hf2 : ∃ v' ∈ pos, f = v'.exact := by
        apply list_map_contains
        exact hf.left
      match hf2 with
      | ⟨v', hv'⟩ =>
        have hf3 := hf.right
        rw [hv'.right] at hf3
        rw [Valuation.exact_correct] at hf3
        apply h v' hv'.left v hv
        exact hf3
