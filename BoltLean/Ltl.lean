structure Trace (n_pred: Nat) where
  length: Nat
  predicates : Vector (Vector Bool length) n_pred
deriving Repr

/-- LTL Formulas in NNF -/
inductive Formula n_pred
  | Var : Fin n_pred -> (neg: Bool) -> Formula n_pred -- neg: Whether the variable is negated
  | Next : Formula n_pred -> Formula n_pred
  | WeakNext : Formula n_pred -> Formula n_pred
  | Globally : Formula n_pred -> Formula n_pred
  | Finally : Formula n_pred -> Formula n_pred
  | Or : Formula n_pred -> Formula n_pred -> Formula n_pred
  | And : Formula n_pred -> Formula n_pred -> Formula n_pred
  | Until : Formula n_pred -> Formula n_pred -> Formula n_pred
deriving DecidableEq

namespace Formula

  def eval_aux (phi: Formula n) (t: Trace n) (i: Fin t.length): Prop :=
    match phi with
    | Var v neg => xor t.predicates[v][i] neg
    | Next psi => if h: i < t.length - 1 then eval_aux psi t ⟨i.val + 1, by omega⟩ else False
    | WeakNext psi => (h: i < t.length - 1) → eval_aux psi t ⟨i.val + 1, by omega⟩
    | Globally psi => ∀ j, j ≥ i  → eval_aux psi t j
    | Finally psi => ∃ j, j ≥ i ∧ eval_aux psi t j
    | Or psi1 psi2 => (eval_aux psi1 t i) ∨ (eval_aux psi2 t i)
    | And psi1 psi2 => (eval_aux psi1 t i) ∧ (eval_aux psi2 t i)
    | Until psi1 psi2 => ∃ j, j ≥ i ∧
                              (eval_aux psi2 t j) ∧
                              (∀ k, i ≤ k → k < j → eval_aux psi1 t k)

  def eval (phi : Formula n) (t : Trace n) : Prop :=
    if h : t.length > 0 then
      eval_aux phi t ⟨0, h⟩
    else
      match phi with
      -- I guess technically, WeakNext and Globally
      -- are both true on empty traces, and are the only ones.
      | WeakNext _ | Globally _ => True
      | Or psi1 psi2 => eval psi1 t ∨ eval psi2 t
      | And psi1 psi2 => eval psi1 t ∧ eval psi2 t
      | _ => False


  theorem or_eval (phi psi: Formula n) (t: Trace n):
    (phi.Or psi).eval t ↔ phi.eval t ∨ psi.eval t  := by
      constructor
      . intro h
        simp [eval, eval_aux] at h
        by_cases htl: 0 < t.length
        . simp [htl] at h
          unfold eval
          simp [htl]
          exact h
        . simp [htl] at h
          assumption
      . intro h
        rw [eval]
        by_cases htl: 0 < t.length
        all_goals simp [htl]
        . unfold eval at h
          simp [htl] at h
          rw [eval_aux]
          assumption
        . exact h


  theorem and_eval (phi psi: Formula n) (t: Trace n):
    (phi.And psi).eval t ↔ phi.eval t ∧ psi.eval t  := by
      constructor
      . intro h
        simp [eval, eval_aux] at h
        by_cases htl: 0 < t.length
        . simp [htl] at h
          unfold eval
          simp [htl]
          exact h
        . simp [htl] at h
          assumption
      . intro h
        rw [eval]
        by_cases htl: 0 < t.length
        all_goals simp [htl]
        . unfold eval at h
          simp [htl] at h
          rw [eval_aux]
          assumption
        . exact h


end Formula
