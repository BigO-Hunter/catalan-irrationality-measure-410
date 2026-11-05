module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMD

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

/-- `refBil` of trials (0,1) is at most U = 0.832340334. -/
def xU01 : ℚ := ((416170167 : ℚ) / 500000000)

theorem enc_x01_le : encUpper 7 (LF.sumL (planLits Rm0 Rm1)) xU01 = true := by decide +kernel

theorem refBil_T01_le {μ ν : SRef} (hμ : IsRefQ μ (ofTrial T0.trial)) (hν : IsRefQ ν (ofTrial T1.trial))
    (hR : (ofTrial T0.trial).OK) (hS : (ofTrial T1.trial).OK) : refBil μ ν ≤ (xU01 : ℝ) :=
  refBil_le_merged μ ν _ _ Rm0 Rm1 hμ hν hR hS merge0 merge1 7 _ enc_x01_le

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
