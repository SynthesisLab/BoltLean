import BoltLean.Ltl.Basic

namespace Trace
  /-- Returns a formula that accepts the value of predicate number `v`,
  at the given position,
  i.e. it returns the variable x_v if x_v is true,
  and ¬x_v otherwise. -/
  def get_exact_var (pos: Vector Bool n) (v: Fin n): Formula n :=
    Formula.Var v (not pos[v])

  /-- Construct a formula that accepts the value of all predicates listed in `l`
  at the given position.
  To build the `exact` function, this function is called with `List.finRange n`,
  but having `l` as a free parameter makes proofs easier.-/
  def exact_at_pos (pos: Vector Bool n) (l: List (Fin n)): Formula n :=
    let all_var := l.map (get_exact_var pos)
    all_var.foldr Formula.And Formula.True

  /-- Return a formula that accepts `t` and rejects all other traces.-/
  def exact (t: Trace n) : Formula n :=
    match t with
    | .nil => Formula.False.Globally
    | head :: tail => (exact_at_pos head (List.finRange n)).And (exact tail).Next

  -- We now prove that the `exact` construction works:
  -- - it is true on `t`
  -- - it is only true on `t`

  /-- Helper Lemma for correctness -/
  theorem exact_at_pos_accepts (pos: Vector Bool n) (t: Trace n):
    (exact_at_pos pos (List.finRange n)).accepts (pos :: t) := by
      unfold exact_at_pos
      simp
      -- Below says: We're going to show it for an arbitrary list `l` instead.
      generalize List.finRange n = l
      induction l with
      | nil => simp [Formula.accepts]
      | cons v vs ih => simp [Formula.accepts, ih, get_exact_var]

  /-- Correctness: `t.exact` evaluates to true on `t` -/
  theorem exact_accepts (t: Trace n):
    (t.exact).accepts t := by
    induction t with
    | nil => simp [exact, Formula.accepts]
    | cons hd tl ih =>
      simp [Formula.accepts, exact]
      constructor
      . exact exact_at_pos_accepts hd tl
      . exact ih

  -- Soundness
  /-- Lemma: Taking the `And` of a list of formulas and evaluating is the same as
  evaluating and taking the Boolean `And`.-/
  theorem foldr_and_aux (l: List (Formula n)) (t: Trace n):
    (l.foldr Formula.And Formula.True).accepts t
      → ∀ f ∈ l, f.accepts t := by
        induction l with
        | nil => simp
        | cons hd tl ih =>
          intro he f hm
          cases hm
          . unfold List.foldr at he
            unfold Formula.accepts at he
            simp [*] at he
            cases t <;> simp at he <;> exact he.left
          . next h_in =>
            unfold List.foldr at he
            unfold Formula.accepts at he
            simp [*] at he
            cases t <;> simp at he <;> apply ih he.right f h_in

  /-- Lemma: If `exact_at_pos pos l` accepts, then `get_exact_var pos v` also accepts for all `v ∈ l`-/
  theorem exact_at_pos_accepts_all (pos pos': Vector Bool n) (t: Trace n) (l: List (Fin n)) :
    (exact_at_pos pos l).accepts (pos' :: t) → ∀ v ∈ l, (get_exact_var pos v).accepts (pos' :: t) := by
      intro h v hv
      have h1 : ∀ f ∈ (List.map (get_exact_var pos) l), f.accepts (pos'::t) := by
        unfold exact_at_pos at h
        simp at h
        apply foldr_and_aux (List.map (get_exact_var pos) l) (pos'::t)
        exact h
      have h2: (get_exact_var pos v) ∈ (List.map (get_exact_var pos) l) := by
        induction l with
        | nil => simp at hv
        | cons hd tl ih =>
          cases hv
          . simp
          . next hm =>
            simp
            right
            exists v
      apply h1
      exact h2

  /-- Lemma: If `exact t` accepts `t'`, then `t` and `t'` have the same head.-/
  theorem exact_accepts_head (h h': Vector Bool n) (t t': Trace n):
    (exact (h::t)).accepts (h'::t') → h = h' := by
      simp [exact, Formula.accepts]
      intro h_accepts h2
      ext i hi
      have h1 := exact_at_pos_accepts_all h h' t' (List.finRange n) h_accepts ⟨i, hi⟩ (List.mem_finRange ⟨i, hi⟩)
      unfold Formula.accepts at h1
      simp [get_exact_var] at h1
      rw [h1]

  /-- Lemma: If `exact t` accepts `t'`, then `t` and `t'` have the same tail.-/
  theorem exact_accepts_cons (h h': Vector Bool n) (t t': Trace n):
    (exact (h::t)).accepts (h'::t') → (exact t).accepts t' := by
      intro hyp
      unfold exact at hyp
      unfold Formula.accepts at hyp
      simp at hyp
      have h2 := hyp.right
      unfold Formula.accepts at h2
      simp at h2
      exact h2

  /-- Lemma: `exact` of the empty trace does not accept non-empty traces.-/
  theorem exact_nil_not_accepts_cons (h: Vector Bool n) (t: Trace n):
    ¬ (exact []).accepts (h :: t) := by
    intro h1
    unfold exact at h1
    unfold Formula.accepts at h1
    simp at h1
    have h2 := h1 0
    simp [List.drop] at h2
    simp [Formula.accepts] at h2

  open Classical
  /-- Soundness: `t.exact` only accepts `t`-/
  theorem exact_accepts_only (t t': Trace n):
    (t.exact).accepts t' → t = t' := by
      intro h
      induction t generalizing t' with
      | nil =>
        induction t' with
        | nil => simp
        | cons hd' tl' ih' =>
          simp
          apply exact_nil_not_accepts_cons hd' tl'
          exact h
      | cons hd tl ih =>
        induction t' with
        | nil => simp [exact, Formula.accepts] at h
        | cons hd' tl' ih' =>
          simp
          constructor
          . exact exact_accepts_head hd hd' tl tl' h
          . apply ih
            apply exact_accepts_cons hd hd'
            assumption


  /-- Correctness and soundness of `t.exact` -/
  theorem exact_correct (t t': Trace n):
    t.exact.accepts t' ↔ t = t' := by
      constructor
      . exact exact_accepts_only t t'
      . intro h
        rw [h]
        exact exact_accepts t'

  theorem exists_accept_only (t: Trace n) :
    exists (phi: Formula n), phi.accepts t ∧
      forall (t': Trace n), t ≠ t' → ¬phi.accepts t' := by
      exists t.exact
      constructor
      . exact t.exact_accepts
      . intro t'
        intro hne
        intro he
        apply hne
        exact exact_accepts_only t t' he

end Trace

/-- Given a list of traces, construct a formula that accepts
exactly these traces, and no other. -/
def UpperBoundFormula (ts: List (Trace n)) : Formula n :=
  let fs := ts.map Trace.exact
  fs.foldr Formula.Or Formula.False

/-- Lemma: If all formulas in a list accept `t`,
then the `Or` of this list also accepts `t`.-/
theorem foldr_or_aux (l: List (Formula n)) (t: Trace n):
  ∀ f ∈ l, f.accepts t → (l.foldr Formula.Or Formula.False).accepts t := by
      induction l with
      | nil => simp
      | cons hd tl ih =>
        intro f hm he
        cases hm
        . unfold List.foldr
          unfold Formula.accepts
          simp
          cases t <;> simp <;> left <;> exact he
        . next h_in =>
          unfold List.foldr
          unfold Formula.accepts
          simp
          cases t <;> simp <;> right <;> apply ih f h_in he



/-- Lemma: If the `Or` of a list of formulas accepts `t`,
then some formula in the list accepts `t`.-/
theorem foldr_or_aux_rev (l: List (Formula n)) (t: Trace n):
  (l.foldr Formula.Or Formula.False).accepts t → ∃ f ∈ l, f.accepts t := by
      intro h
      induction l with
      | nil =>
        unfold Formula.accepts at h
        cases t <;> simp at h
      | cons hd tl ih =>
        unfold List.foldr at h
        unfold Formula.accepts at h
        simp at h
        cases t
          <;> simp at h
          <;> simp
          <;> match h with
            | .inl h1 => left; exact h1
            | .inr h1 => right; apply ih; exact h1

theorem list_map_contains (l: List α) (f: α → β):
  (∀b, b ∈ l.map f → ∃ a ∈ l, b = f a) := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro b hb
      unfold List.map at hb
      rw [List.mem_cons] at hb
      match hb with
      | .inl h1 => exists hd; simp; assumption
      | .inr h1 =>
        have h2 := ih b h1
        simp [List.mem_cons]
        right
        exact h2


/-- Theorem:
For any disjoint set of positive and negative examples,
there exists a formula that accepts all the positive and rejects the negatives.
-/
theorem UpperBound (pos: List (Trace n)) (neg: List (Trace n)) (h: ∀ t ∈ pos, ∀ t'∈ neg, t ≠ t') :
  exists (phi: Formula n), (∀ t ∈ pos, phi.accepts t) ∧ (∀t ∈ neg, ¬ phi.accepts t):= by
    exists UpperBoundFormula pos
    constructor
    . intro t ht
      unfold UpperBoundFormula
      simp
      apply foldr_or_aux (List.map Trace.exact pos) t (t.exact)
      . induction pos with
        | nil => simp at ht
        | cons hd tl ih =>
          cases ht
          . simp
          . next hm =>
              simp
              right
              simp at h
              have hr := h.right
              have h2 := ih hr
              exists t
      . exact t.exact_accepts
    . intro t ht he
      unfold UpperBoundFormula at he
      simp at he
      have ⟨f, hf⟩ := foldr_or_aux_rev (List.map Trace.exact pos) t he
      have ⟨t', ht'⟩ : ∃ t ∈ pos, f = t.exact := by
        apply list_map_contains
        exact hf.left
      have hf3 := hf.right
      rw [ht'.right] at hf3
      rw [Trace.exact_correct] at hf3
      apply h t' ht'.left t ht
      exact hf3
