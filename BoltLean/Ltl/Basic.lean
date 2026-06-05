/-- `Trace n_pred` is an alias for `List (Vector Bool n_pred)`.
At position `i` in the list, the vector contains the truth value of the `n_pred` predicates at time `i`.-/
abbrev Trace (n_pred: Nat): Type := List (Vector Bool n_pred)

/-- LTL Formulas in NNF -/
inductive Formula n_pred
  | True : Formula n_pred
  | False : Formula n_pred
  /-- neg: Whether the variable is negated -- negations are only allowed at variables. -/
  | Var : Fin n_pred -> (neg: Bool) -> Formula n_pred
  | Next : Formula n_pred -> Formula n_pred
  | WeakNext : Formula n_pred -> Formula n_pred
  | Globally : Formula n_pred -> Formula n_pred
  | Finally : Formula n_pred -> Formula n_pred
  | Or : Formula n_pred -> Formula n_pred -> Formula n_pred
  | And : Formula n_pred -> Formula n_pred -> Formula n_pred
  | Until : Formula n_pred -> Formula n_pred -> Formula n_pred
deriving DecidableEq

namespace Formula
  /-- Whether the formula is satisfied by the Trace.-/
  def accepts (phi: Formula n) (t: Trace n): Prop :=
  match t with
    -- Special case of the empty Trace: it is only accepted by True and Globally,
    -- or their boolean combinations.
    | .nil => match phi with
      | True | Globally _ => _root_.True
      | False | Finally _ | Var _ _ | Next _ | WeakNext _ | Until _ _ => _root_.False
      | Or psi1 psi2 => (accepts psi1 t) ∨ (accepts psi2 t)
      | And psi1 psi2 => (accepts psi1 t) ∧ (accepts psi2 t)
    | head::tail => match phi with
      | True => _root_.True
      | False => _root_.False
      | Var v neg => xor head[v] neg
      | Next psi => accepts psi tail
      | WeakNext psi => tail = List.nil ∨ accepts psi tail
      | Globally psi => ∀ j, j < t.length → accepts psi (t.drop j)
      | Finally psi => ∃ j, j < t.length ∧ accepts psi (t.drop j)
      | Or psi1 psi2 => (accepts psi1 t) ∨ (accepts psi2 t)
      | And psi1 psi2 => (accepts psi1 t) ∧ (accepts psi2 t)
      | Until psi1 psi2 => ∃ j, j < t.length ∧
                                (accepts psi2 (t.drop j)) ∧
                                (∀ k, k < j → accepts psi1 (t.drop k))

end Formula
