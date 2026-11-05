module

public import Submission.CatalanMeasure.GenD.Signed.Data.S1.TrialEnd
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Decay.Providers540

@[expose] public section

/-!
# S1: the K590 trials in End form (final-build assembly; NOT built in lane D3)

Imports the 532/540 certificate data (`Providers540`, via `Bank.TrialFields`), so this module is
only checked by the final build.  The generic content (`secondEnd`, `firstEnd`, their budgets) is in
`TrialEnd`, which is built and imports no certificate.
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open CatalanMeasure.GenD.Uniform

noncomputable section

/-- Second-population K590 trial, factor-free: `SecondTrialBoundsEnd Odd.design 0 .. secondCost'`. -/
def second590 := secondEnd Bank540.second rfl rfl

/-- First-population K590 trial, factor-free: `FirstTrialBoundsEnd Odd.design .. firstCost'`. -/
def first590 := firstEnd Bank540.first rfl rfl rfl

end

end CatalanMeasure.GenD.Signed.Data.S1
