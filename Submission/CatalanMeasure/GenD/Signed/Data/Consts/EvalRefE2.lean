module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMD

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

/-- `refEnergy` of trial 2: [L, U] = [0.780985688, 0.780985691]. -/
def enU2 : ℚ := ((780985691 : ℚ) / 1000000000)
def enL2 : ℚ := ((97623211 : ℚ) / 125000000)

theorem enc_en2_le : encUpper 7 (LF.sumL (planLits Rm2 Rm2)) enU2 = true := by decide +kernel
theorem enc_en2_ge : encLower 7 (LF.sumL (planLits Rm2 Rm2)) enL2 = true := by decide +kernel

theorem refEnergy_T2_le {μ : SRef} (hμ : IsRefQ μ (ofTrial T2.trial)) (hR : (ofTrial T2.trial).OK) :
    refEnergy μ ≤ (enU2 : ℝ) := refEnergy_le_merged μ _ Rm2 hμ hR merge2 7 _ enc_en2_le

theorem refEnergy_T2_ge {μ : SRef} (hμ : IsRefQ μ (ofTrial T2.trial)) (hR : (ofTrial T2.trial).OK) :
    (enL2 : ℝ) ≤ refEnergy μ := refEnergy_ge_merged μ _ Rm2 hμ hR merge2 7 _ enc_en2_ge

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
