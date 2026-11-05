module

public import Mathlib.Tactic.FinCases
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedCanonicalModularForm
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

@[expose] public section

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem fixedIntegerBaseCanonical_mod_row_8 (k : Fin 48) :
    (fixedIntegerBaseCanonical (8 : Fin 49) k : ZMod 101) =
      fixedLiteralBaseMod (8 : Fin 49) k := by
  rw [fixedIntegerBaseCanonical_mod_coefficients]
  revert k
  decide +kernel

end InternalCatalan

end

end

end OAI
