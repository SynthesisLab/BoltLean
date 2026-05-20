import BoltLean.Helpers

structure Trace (n_pred : Nat) where
  pos_n_pred : n_pred > 0
  predicates : List (Vector Bool n_pred)
deriving Repr

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

  def eval_aux (phi: Formula n) (predicates: List (Vector Bool n)): Prop :=
  match predicates with
    | .nil => match phi with
      | True | Globally _ => _root_.True
      | False | Finally _ | Var _ _ | Next _ | WeakNext _ | Until _ _ => _root_.False
      | Or psi1 psi2 => (eval_aux psi1 predicates) ∨ (eval_aux psi2 predicates)
      | And psi1 psi2 => (eval_aux psi1 predicates) ∧ (eval_aux psi2 predicates)
    | head::tail => match phi with
      | True => _root_.True
      | False => _root_.False
      | Var v neg => xor head[v] neg
      | Next psi => eval_aux psi tail
      | WeakNext psi => tail = List.nil ∨ eval_aux psi tail
      | Globally psi => ∀ j, j < predicates.length → eval_aux psi (predicates.drop j)
      | Finally psi => ∃ j, j < predicates.length ∧ eval_aux psi (predicates.drop j)
      | Or psi1 psi2 => (eval_aux psi1 predicates) ∨ (eval_aux psi2 predicates)
      | And psi1 psi2 => (eval_aux psi1 predicates) ∧ (eval_aux psi2 predicates)
      | Until psi1 psi2 => ∃ j, j < predicates.length ∧
                                (eval_aux psi2 (predicates.drop j)) ∧
                                (∀ k, k < j → eval_aux psi1 (predicates.drop k))

  def eval (phi : Formula n) (t : Trace n) : Prop :=
    eval_aux phi t.predicates

  def equivalence (phi psi : Formula n) : Prop := ∀ (t : Trace n), eval phi t ↔ eval psi t

  theorem eval2eval_aux (phi1 phi2 : Formula n) (hn : n > 0): (equivalence phi1 phi2) ↔ ∀ l : List (Vector Bool n), (eval_aux phi1 l) ↔ (eval_aux phi2 l) := by
  constructor
  . intro h
    intro l
    unfold equivalence at h
    have h1 := h ⟨hn, l⟩
    unfold eval at h1
    simp at h1
    exact h1
  . intro h
    unfold equivalence
    intro t
    unfold eval
    exact h t.predicates

  theorem congruence_finally (phi1 phi2 : Formula n) :
  (equivalence phi1 phi2) → equivalence (Finally phi1) (Finally phi2) := by
  intro h1 h2
  rw [eval2eval_aux] at h1
  . unfold eval
    unfold eval_aux
    simp
    match h2.predicates with
      | List.nil => simp
      | head::tail => simp
                      constructor
                        <;> intro h
                        <;> have ⟨j, hj⟩ := h
                        <;> exists j
                        <;> first | rw [h1] | rw [←h1]
                        <;> exact hj
                      exact hj
  . exact h2.pos_n_pred


  theorem congruence_globally (phi1 phi2 : Formula n) :
  (equivalence phi1 phi2) → equivalence (Globally phi1) (Globally phi2) := by
  intro h1 h2
  rw [eval2eval_aux] at h1
  . unfold eval
    unfold eval_aux
    simp
    match h2.predicates with
      | List.nil => simp
      | head::tail => simp
                      constructor
                        <;> (
                          intro h j
                          first | rw [h1] | rw [←h1]
                          apply h
                        )
  . exact h2.pos_n_pred




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
