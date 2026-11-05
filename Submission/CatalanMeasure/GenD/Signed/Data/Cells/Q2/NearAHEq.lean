module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 2, corner ah) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2nearahTs_eq : q2nearahTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qFn)) := by decide +kernel
theorem q2nearahTsM_eq : q2nearahTsM = mergeL q2nearahTs := by decide +kernel
theorem q2nearahFq_poles : q2nearahFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel
theorem q2nearahFq_plog0 : q2nearahFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.plogs.take 1 := by decide +kernel
theorem q2nearahtFq_poles : q2nearahtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
