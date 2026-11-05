module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMD

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

/-- `refBil` of trials (1,2) is at most U = 0.804978809. -/
def xU12 : ℚ := ((804978809 : ℚ) / 1000000000)

theorem enc_x12_le : encUpper 7 (LF.sumL (planLits Rm1 Rm2)) xU12 = true := by decide +kernel

theorem refBil_T12_le {μ ν : SRef} (hμ : IsRefQ μ (ofTrial T1.trial)) (hν : IsRefQ ν (ofTrial T2.trial))
    (hR : (ofTrial T1.trial).OK) (hS : (ofTrial T2.trial).OK) : refBil μ ν ≤ (xU12 : ℝ) :=
  refBil_le_merged μ ν _ _ Rm1 Rm2 hμ hν hR hS merge1 merge2 7 _ enc_x12_le

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
