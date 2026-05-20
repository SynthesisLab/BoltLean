import BoltLean.Ltl
import BoltLean.Helpers

namespace Trace
  def get_exact_var (t: Trace n) (i: Fin t.length) (v: Fin n): Formula n :=
    Formula.Var v (not t.predicates[v][i])

  /-- Auxiliary functions for constructing a formula that is true on t and only on t-/
  def exact_at_pos (t: Trace n) (i: Fin t.length): Formula n :=
    let all_indices := List.finRange n
    let all_var := all_indices.map (t.get_exact_var i)
    all_var.foldr (fun phi psi => phi.And psi) Formula.True


  def subrange (start: Nat) : List (Fin n) :=
    if h: start < n then
      ⟨start, by omega⟩ :: subrange (start + 1)
    else
      []

  def exact (t: Trace n) : Formula n :=
    let all_indices := subrange 0
    let all_exact := all_indices.map t.exact_at_pos
    -- Ensure that the trace has the right length
    -- by checking WeakNext False at the end
    all_exact.foldr (fun phi psi => phi.And psi.WeakNext) Formula.False

  -- Scaffolding for proving that the `exact` construction works:
  -- - it is true on `t`
  -- - it is only true on `t`
  /-- Helper lemma: Proves that the folded AND formula is true for ANY list of variables -/
  theorem exact_at_pos_eval_aux_list (t: Trace n) (i: Fin t.length) (vars : List (Fin n)):
    ((vars.map (t.get_exact_var i)).foldr (fun phi psi => phi.And psi) Formula.True).eval_aux t i := by
    induction vars with
    | nil => simp [Formula.eval_aux]
    | cons hd tl ih =>
      simp [Formula.eval_aux, get_exact_var]
      exact ih

  /-- Correctness: `t.exact_at_pos i` evaluates to true on `t` at `i` -/
  theorem exact_at_pos_eval_aux (t: Trace n) (i: Fin t.length):
    (t.exact_at_pos i).eval_aux t i := by
    unfold exact_at_pos
    apply exact_at_pos_eval_aux_list

  /-- Helper lemma: Evaluates the formula suffix starting from an arbitrary time `i` -/
  theorem exact_eval_suffix (t: Trace n) (rem: Nat) (i: Fin t.length) (h_rem: t.length - i.val = rem) :
    (((subrange i
      ).map t.exact_at_pos
     ).foldr
        (fun phi psi => phi.And psi.WeakNext)
        Formula.False
    ).eval_aux t i := by
    -- We do induction on the number of remaining steps in the trace
    induction rem generalizing i with
    | zero => omega
    | succ k ih =>
      unfold subrange
      by_cases hi: i < t.length
      . simp [hi]
        unfold Formula.eval_aux
        constructor
        . exact exact_at_pos_eval_aux t i
        . unfold Formula.eval_aux
          intro hi
          apply ih ⟨i.val+1, by omega⟩
          have hik : t.length - (i.val+1) = k := by omega
          omega
      . have he: i.val = t.length -1 := by
          omega
        simp [he]
        omega

  /-- Correctness: `t.exact` evaluates to true on `t` -/
  theorem exact_eval (t: Trace n) : (t.exact).eval t := by
    unfold exact
    unfold Formula.eval
    have h_rem : t.length - 0 = t.length := by omega
    have h := exact_eval_suffix t (t.length) ⟨0, t.pos_length⟩ h_rem
    simp
    exact h

  -- Soundness
  theorem diff_exist_diff_var (t t': Trace n) (h: t ≠ t'):
    t.length ≠ t'.length
      ∨ exists (i: Fin t.length) (v: Fin n) (h': i < t'.length),
        t.predicates[v][i] ≠ t'.predicates[v][i] := by
      by_cases hl: t.length = t'.length
      . right
        apply Classical.byContradiction
        intro h_contra
        apply h
        cases t
        cases t'
        simp at hl
        subst hl
        simp at *
        apply Vector.ext
        intro v hv
        apply Vector.ext
        intro i hi
        exact h_contra ⟨i, hi⟩ ⟨v, hv⟩
      . left
        exact hl

  theorem exact_at_pos_eval_iff
    (t t': Trace n) (i: Fin t.length) (i': Fin t'.length) :
      (t.exact_at_pos i).eval_aux t' i'
        ↔ (∀ (v : Fin n), t.predicates[v][i] = t'.predicates[v][i']) := by
    -- Proof by induction or well-founded recursion on (n - v)
    constructor
    . intro h v
      unfold exact_at_pos at h
      unfold Formula.eval_aux at h
      simp at h
    . sorry

  theorem not_eval_aux_exact_at_pos_if_diff_pred (t t': Trace n)
      (i: Fin t.length) (v: Fin n)
      (hi: i < t'.length) (h: t.predicates[v][i] ≠ t'.predicates[v][i]) :
    ¬(t.exact_at_pos i v).eval_aux t' ⟨i.val, hi⟩ := by
   unfold exact_at_pos
   simp
   split
   . next hif =>
                 simp [Formula.eval_aux]
                 intro he
                 simp at h
                 rw [eq_comm] at he
                 exact absurd he h
   . next hnif => simp [Formula.eval_aux]
                  simp at h
                  rw [eq_comm] at h
                  exact h

  theorem not_eval_aux_exact_at_pos_if_diff_pred_lt (t t': Trace n)
      (i: Fin t.length) (v v': Fin n) (hv: v' ≤ v)
      (hi: i < t'.length) (h: t.predicates[v][i] ≠ t'.predicates[v][i]) :
    ¬(t.exact_at_pos i v').eval_aux t' ⟨i.val, hi⟩ := by
    by_cases he: v' = v
    . rw [he]
      apply not_eval_aux_exact_at_pos_if_diff_pred <;> assumption
    . unfold exact_at_pos
      have hv': v' < n-1 := by omega
      simp [hv']
      simp [Formula.eval_aux]
      intro hp
      let v'' := v'.val+1
      have hv'': v'' ≤ v := by omega
      apply not_eval_aux_exact_at_pos_if_diff_pred_lt t t' i v ⟨v'', by omega⟩ hv'' hi h

  theorem not_eval_aux_exact_aux_if_diff_pred (t t': Trace n)
      (i: Fin t.length) (v: Fin n)
      (hi: i < t'.length) (h: t.predicates[v][i] ≠ t'.predicates[v][i]) :
    ¬(t.exact_aux i).eval_aux t' ⟨i.val, hi⟩ := by
    unfold exact_aux
    split
    . next hif => simp
                  unfold Formula.eval_aux
                  rw [Classical.not_and_iff_not_or_not]
                  left
                  apply not_eval_aux_exact_at_pos_if_diff_pred_lt
                  all_goals try assumption
                  apply Nat.zero_le
    . next hnif => simp
                   apply not_eval_aux_exact_at_pos_if_diff_pred_lt
                   all_goals try assumption
                   apply Nat.zero_le


  theorem not_eval_aux_exact_aux_if_diff_pred_lt (t t': Trace n)
      (i i': Fin t.length) (hi': i' ≤ i) (v: Fin n)
      (hi: i < t'.length) (h: t.predicates[v][i] ≠ t'.predicates[v][i]) :
    ¬(t.exact_aux i').eval_aux t' ⟨i'.val,by omega⟩ := by
    by_cases he: i = i'
    . subst he
      apply not_eval_aux_exact_aux_if_diff_pred <;> assumption
    . unfold exact_aux
      simp
      have h1: i' < t.length - 1 := by omega
      simp [h1]
      unfold Formula.eval_aux
      simp
      intro h2
      simp [Formula.eval_aux]
      intro
      apply not_eval_aux_exact_aux_if_diff_pred_lt
      all_goals try assumption
      rw [Nat.ne_iff_lt_or_gt] at he
      sorry

  open Classical
  /-- Soundness: `t.exact` only accepts `t`-/
  theorem exact_eval_only (t t': Trace n):
    (t.exact).eval t' → t = t' := by
      rw [my_contra]
      intro hne
      sorry
end Trace

-- theorem exact_eval (t: Trace n) :
--   exists (phi: Formula n), phi.eval t ∧
--     forall (t': Trace n), t ≠ t' → ¬phi.eval t' := by
--     sorry
