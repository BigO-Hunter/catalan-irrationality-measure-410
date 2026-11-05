module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 1, corner ah) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1nearahTs_eq : q1nearahTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qFn)) := by decide +kernel
theorem q1nearahTsM_eq : q1nearahTsM = mergeL q1nearahTs := by decide +kernel
theorem q1nearahFq_poles : q1nearahFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel
theorem q1nearahFq_plog0 : q1nearahFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 1 := by decide +kernel
theorem q1nearahtFq_poles : q1nearahtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel
theorem q1nearahFq_plogs : q1nearahFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs := by decide +kernel
theorem q1nearahtFq_plogs : q1nearahtFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 2 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
