/-- A valuation represents the membership of a given element `x` of the universe
in each of the sets `S_1, ..., S_{n_sets}` of the instance.
It is an alias for `Vector Bool n_sets`,
and `v[i]` says whether `x` is in `S_i`.-/
abbrev Valuation (n_sets: Nat): Type := Vector Bool n_sets

/- Boolean formulas in NNF -/
inductive BoolFormula (n_sets: Nat)
  | False: BoolFormula n_sets
  | True : BoolFormula n_sets
  | Var : Fin n_sets -> (neg: Bool) -> BoolFormula n_sets
  | And : BoolFormula n_sets -> BoolFormula n_sets -> BoolFormula n_sets
  | Or : BoolFormula n_sets -> BoolFormula n_sets -> BoolFormula n_sets
  deriving DecidableEq, Repr

namespace BoolFormula
  @[simp]
  def accepts (f: BoolFormula n_sets) (v: Valuation n_sets): Prop :=
    match f with
    | False => _root_.False
    | True => _root_.True
    | Var i neg => v[i] ^^ neg
    | And f1 f2 => f1.accepts v ∧ f2.accepts v
    | Or f1 f2 => f1.accepts v ∨ f2.accepts v

  /-- A formula satisfies an examples if it is positive and the formula accepts,
  or if it is negative and the formula rejects.-/
  @[simp]
  def satisfies (f: BoolFormula n_sets) (v: Valuation n_sets) (positive: Bool) : Prop :=
    f.accepts v ↔ positive

  /-- A formula `f1` dominates `f2` another if `f1` satisfies a superset
  of the elements satisfied by `f2`.-/
  def dominates (f1 f2: BoolFormula n_sets): Prop :=
    ∀ (v: Valuation n_sets) (b: Bool), f2.satisfies v b → f1.satisfies v b

  /-- Replace all occurrence of the formula `pat` in `f` with the formula `repl`.-/
  def replace (f pat repl: BoolFormula n_sets): BoolFormula n_sets :=
    if f = pat then
      repl
    else match f with
    | And f1 f2 => And (f1.replace pat repl) (f2.replace pat repl)
    | Or f1 f2 => Or (f1.replace pat repl) (f2.replace pat repl)
    | x => x

end BoolFormula
