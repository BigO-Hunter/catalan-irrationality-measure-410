module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger5.Merge5
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Decay.Providers540
public import Submission.CatalanMeasure.GenD.D58.C3.Cert
public import Submission.CatalanMeasure.GenD.D58.Final
public import Submission.CatalanMeasure.GenD.Final

@[expose] public section
set_option Elab.async false

/-!
# `μ(G) ≤ 540` (lane G5h)

`measure_of_design` for the design `(58,9,3,5,3)`: denominator side `partial_growth5` (ledger `wins5`, gain
`gain5 = 21.68676`), payments and decay by the gate `etaG = 29.596`, and the decay `delta_small` of `Providers540`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem gate5 :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg gain5 := gate gain5 gain5_ge

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger5
