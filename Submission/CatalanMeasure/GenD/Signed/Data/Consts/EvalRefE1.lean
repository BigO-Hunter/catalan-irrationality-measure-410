module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMD

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

/-- `refEnergy` of trial 1: [L, U] = [0.830142088, 0.830142091]. -/
def enU1 : ℚ := ((830142091 : ℚ) / 1000000000)
def enL1 : ℚ := ((103767761 : ℚ) / 125000000)

theorem enc_en1_le : encUpper 7 (LF.sumL (planLits Rm1 Rm1)) enU1 = true := by decide +kernel
theorem enc_en1_ge : encLower 7 (LF.sumL (planLits Rm1 Rm1)) enL1 = true := by decide +kernel

theorem refEnergy_T1_le {μ : SRef} (hμ : IsRefQ μ (ofTrial T1.trial)) (hR : (ofTrial T1.trial).OK) :
    refEnergy μ ≤ (enU1 : ℝ) := refEnergy_le_merged μ _ Rm1 hμ hR merge1 7 _ enc_en1_le

theorem refEnergy_T1_ge {μ : SRef} (hμ : IsRefQ μ (ofTrial T1.trial)) (hR : (ofTrial T1.trial).OK) :
    (enL1 : ℝ) ≤ refEnergy μ := refEnergy_ge_merged μ _ Rm1 hμ hR merge1 7 _ enc_en1_ge

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
