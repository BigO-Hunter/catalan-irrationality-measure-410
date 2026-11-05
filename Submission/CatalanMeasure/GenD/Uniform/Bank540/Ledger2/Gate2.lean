module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger2.Instance2
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Gate

@[expose] public section
set_option Elab.async false

/-!
# The B = 540 gate for the refined partial ledger (lane G5e)

`gain2 = 7906089003959/392700000000 = 20.13264...`; the remaining families (MT(1), M, Theorem Z, ...)
must add area `>= 1.4757`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger2
open CatalanMeasure.GenD D58 CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

theorem gain2_ge : (201326 / 10000 : ℝ) ≤ gain2 := by unfold gain2; norm_num

theorem gate_of_remaining2 (extra : ℝ) (h : 14757 / 10000 ≤ extra) :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg (gain2 + extra) := by
  refine gate (gain2 + extra) ?_
  have := gain2_ge
  linarith

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger2
