module

public import Submission.CatalanMeasure.GenD.D58.Cert590.NormP
public import Submission.CatalanMeasure.GenD.D58.Cert590.NormV

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
/-- The weighted norm of the two trials is below `2 NP + NV / 2`. -/
theorem weighted_norm_le :
    2 * barrierTrialNormSq (trialSeqS Pc P) + barrierTrialNormSq (trialSeqS Vc V) / 2 ≤
      ((2 * NP + NV / 2 : ℚ) : ℝ) := by
  have h1 := normP_le
  have h2 := normV_le
  push_cast
  linarith
end CatalanMeasure.GenD.D58.Cert590
