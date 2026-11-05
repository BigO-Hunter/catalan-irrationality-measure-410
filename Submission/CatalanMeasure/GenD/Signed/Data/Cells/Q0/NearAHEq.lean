module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 0, corner ah) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0nearahTs_eq : q0nearahTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qFn)) := by decide +kernel
theorem q0nearahTsM_eq : q0nearahTsM = mergeL q0nearahTs := by decide +kernel
theorem q0nearahFq_poles : q0nearahFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.poles := by decide +kernel
theorem q0nearahFq_plog0 : q0nearahFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.plogs.take 1 := by decide +kernel
theorem q0nearahtFq_poles : q0nearahtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
