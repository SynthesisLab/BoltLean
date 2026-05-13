structure Trace where
  n_pred: Nat
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

namespace Formula

  def fin_range (s e: Fin n) : List (Fin n) :=
    if h : s < e then
      s :: fin_range ⟨s.val + 1, by omega⟩ e
    else
      List.nil
    termination_by n - s

  def eval_aux (t: Trace) (phi: Formula t.n_pred) (i: Fin t.length): Bool :=
    match phi with
    | Var v neg => xor t.predicates[v][i] neg
    | Next psi => if h: i < t.length - 1 then
        eval_aux t psi ⟨i.val + 1, by omega⟩
      else
        false
    | WeakNext psi => if h: i < t.length - 1 then
        eval_aux t psi ⟨i.val + 1, by omega⟩
      else
        true
    | Globally psi => (List.finRange t.length).all (fun j => j < i  || eval_aux t psi j)
    | Finally psi => (List.finRange t.length).any (fun j => j >= i && eval_aux t psi j)
    | Or psi1 psi2 => (eval_aux t psi1 i) || (eval_aux t psi2 i)
    | And psi1 psi2 => (eval_aux t psi1 i) && (eval_aux t psi2 i)
    | Until psi1 psi2 => (List.finRange t.length).any (
        fun j =>
          j >= i
          && ((List.finRange t.length).all (fun k => k < i || k >= j || eval_aux t psi1 k))
          && (eval_aux t psi2 j)
       )

  -- def eval (t: Trace) (phi: Formula t.n_pred): Bool :=
  --   eval_aux t phi ⟨0, by rfl⟩


end Formula
