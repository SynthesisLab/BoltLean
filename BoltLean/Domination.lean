import BoltLean.Ltl

namespace Formula
def dominates (phi psi: Formula n): Prop :=
  ∀ (t: Trace n), psi.eval t → phi.eval t


theorem or_dominates (phi psi: Formula n) (f: Formula n):
  phi.dominates psi → (f.Or phi).dominates (f.Or psi) := by
    rw [dominates, dominates]
    apply forall_imp
    intro t h1 h2
    simp [eval, eval_aux] at h2
    simp [eval, eval_aux]
    match h2 with
    | ⟨hi, h_or⟩ => exists hi
                    match h_or with
                    | .inl hf => apply Or.inl; assumption
                    | .inr h_psi => apply Or.inr
                                    simp [eval, hi] at h1;
                                    apply h1; assumption


end Formula
