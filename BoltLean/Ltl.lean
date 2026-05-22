import BoltLean.Helpers

abbrev Trace (n_pred: Nat): Type := List (Vector Bool n_pred)

/-- LTL Formulas in NNF -/
inductive Formula n_pred
  | True : Formula n_pred
  | False : Formula n_pred
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

  def eval (phi: Formula n) (t: Trace n): Prop :=
  match t with
    | .nil => match phi with
      | True | WeakNext _ | Globally _ => _root_.True
      | False | Finally _ | Var _ _ | Next _ |  Until _ _ => _root_.False
      | Or psi1 psi2 => (eval psi1 t) ∨ (eval psi2 t)
      | And psi1 psi2 => (eval psi1 t) ∧ (eval psi2 t)
    | head::tail => match phi with
      | True => _root_.True
      | False => _root_.False
      | Var v neg => xor head[v] neg
      | Next psi => eval psi tail
      | WeakNext psi => tail = List.nil ∨ eval psi tail
      | Globally psi => ∀ j, j < t.length → eval psi (t.drop j)
      | Finally psi => ∃ j, j < t.length ∧ eval psi (t.drop j)
      | Or psi1 psi2 => (eval psi1 t) ∨ (eval psi2 t)
      | And psi1 psi2 => (eval psi1 t) ∧ (eval psi2 t)
      | Until psi1 psi2 => ∃ j, j < t.length ∧
                                (eval psi2 (t.drop j)) ∧
                                (∀ k, k < j → eval psi1 (t.drop k))

  def equivalence (phi psi : Formula n) : Prop := ∀ (t : Trace n), eval phi t ↔ eval psi t

  theorem congruence_finally (phi1 phi2 : Formula n) :
  (equivalence phi1 phi2) → equivalence (Finally phi1) (Finally phi2) := by
  intro h1 h2
  unfold eval
  simp
  match h2 with
    | List.nil => simp
    | head::tail => simp
                    constructor
                      <;> intro h
                      <;> have ⟨j, hj⟩ := h
                      <;> exists j
                      <;> first | rw [h1] | rw [←h1]
                      <;> exact hj
                    exact hj


  theorem congruence_globally (phi1 phi2 : Formula n) :
  (equivalence phi1 phi2) → equivalence (Globally phi1) (Globally phi2) := by
  intro h1 h2
  unfold eval
  simp
  match h2 with
    | List.nil => simp
    | head::tail => simp
                    constructor
                      <;> (
                        intro h j
                        first | rw [h1] | rw [←h1]
                        apply h
                      )




  theorem congruence (phi1 psi1 phi2 psi2 : Formula n) :
    (equivalence phi1 phi2) → (equivalence psi1 psi2) → equivalence (Until phi1 psi1) (Until phi2 psi2) := by
      unfold equivalence
      intro h1 h2
      sorry



  theorem simplification_rule (phi : Formula n) : equivalence (Finally (Finally phi)) (Finally phi) := by sorry


  -- theorem or_eval (phi psi: Formula n) (t: Trace n):
  --   (phi.Or psi).eval t ↔ phi.eval t ∨ psi.eval t  := by
  --     constructor
  --     . intro h
  --       simp [eval, eval_aux] at h
  --       by_cases htl: 0 < t.length
  --       . simp [htl] at h
  --         unfold eval
  --         simp [htl]
  --         exact h
  --       . simp [htl] at h
  --         assumption
  --     . intro h
  --       rw [eval]
  --       by_cases htl: 0 < t.length
  --       all_goals simp [htl]
  --       . unfold eval at h
  --         simp [htl] at h
  --         rw [eval_aux]
  --         assumption
  --       . exact h


  -- theorem and_eval (phi psi: Formula n) (t: Trace n):
  --   (phi.And psi).eval t ↔ phi.eval t ∧ psi.eval t  := by
  --     constructor
  --     . intro h
  --       simp [eval, eval_aux] at h
  --       by_cases htl: 0 < t.length
  --       . simp [htl] at h
  --         unfold eval
  --         simp [htl]
  --         exact h
  --       . simp [htl] at h
  --         assumption
  --     . intro h
  --       rw [eval]
  --       by_cases htl: 0 < t.length
  --       all_goals simp [htl]
  --       . unfold eval at h
  --         simp [htl] at h
  --         rw [eval_aux]
  --         assumption
  --       . exact h


end Formula
