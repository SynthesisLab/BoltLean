abbrev Valuation (n_var: Nat): Type := Vector Bool n_var

/- Boolean formulas in NNF -/
inductive BoolFormula (n_var: Nat)
  | False: BoolFormula n_var
  | True : BoolFormula n_var
  | Var : Fin n_var -> (neg: Bool) -> BoolFormula n_var
  | And : BoolFormula n_var -> BoolFormula n_var -> BoolFormula n_var
  | Or : BoolFormula n_var -> BoolFormula n_var -> BoolFormula n_var
  deriving DecidableEq, Repr

namespace BoolFormula
  @[simp]
  def accepts (f: BoolFormula n_var) (v: Valuation n_var): Prop :=
    match f with
    | False => _root_.False
    | True => _root_.True
    | Var i neg => v[i] ^^ neg
    | And f1 f2 => f1.accepts v ∧ f2.accepts v
    | Or f1 f2 => f1.accepts v ∨ f2.accepts v

  def dominates (f1 f2: BoolFormula n_var): Prop :=
    ∀ (v: Valuation n_var), f2.accepts v → f1.accepts v

  def replace (f pat repl: BoolFormula n_var): BoolFormula n_var :=
    if f = pat then
      repl
    else match f with
    | And f1 f2 => And (f1.replace pat repl) (f2.replace pat repl)
    | Or f1 f2 => Or (f1.replace pat repl) (f2.replace pat repl)
    | x => x

end BoolFormula
