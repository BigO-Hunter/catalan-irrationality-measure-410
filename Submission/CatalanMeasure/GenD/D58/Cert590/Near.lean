module

public import Submission.CatalanMeasure.GenD.D58.Cert.Near
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

/-!
# D58, bank K590: the first coefficient `p_1 ≥ 9/50` of the K590 witness
(the near-field inequality itself is `Cert.near_residual_field_le_d58`, independent of the witness).
-/

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan Set
noncomputable section

theorem firstQ_data : (9 / 50 : ℚ) ≤ Cert.firstQ Pc P := by
  unfold Cert.firstQ; decide +kernel

theorem first_lower : (9 / 50 : ℝ) ≤ trialSeqS Pc P 1 := by
  rw [Cert.trialSeqS_one]
  have h : (((9 / 50 : ℚ)) : ℝ) ≤ ((Cert.firstQ Pc P : ℚ) : ℝ) := Rat.cast_le.mpr firstQ_data
  push_cast at h
  exact h

end
end CatalanMeasure.GenD.D58.Cert590
