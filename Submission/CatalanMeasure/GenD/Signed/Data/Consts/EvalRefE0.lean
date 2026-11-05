module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMD

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

/-- `refEnergy` of trial 0: [L, U] = [0.834545656, 0.834545659]. -/
def enU0 : ℚ := ((834545659 : ℚ) / 1000000000)
def enL0 : ℚ := ((104318207 : ℚ) / 125000000)

theorem enc_en0_le : encUpper 7 (LF.sumL (planLits Rm0 Rm0)) enU0 = true := by decide +kernel
theorem enc_en0_ge : encLower 7 (LF.sumL (planLits Rm0 Rm0)) enL0 = true := by decide +kernel

theorem refEnergy_T0_le {μ : SRef} (hμ : IsRefQ μ (ofTrial T0.trial)) (hR : (ofTrial T0.trial).OK) :
    refEnergy μ ≤ (enU0 : ℝ) := refEnergy_le_merged μ _ Rm0 hμ hR merge0 7 _ enc_en0_le

theorem refEnergy_T0_ge {μ : SRef} (hμ : IsRefQ μ (ofTrial T0.trial)) (hR : (ofTrial T0.trial).OK) :
    (enL0 : ℝ) ≤ refEnergy μ := refEnergy_ge_merged μ _ Rm0 hμ hR merge0 7 _ enc_en0_ge

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
