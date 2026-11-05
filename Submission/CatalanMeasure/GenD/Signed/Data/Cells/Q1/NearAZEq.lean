module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 1, corner az) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1nearazTs_eq : q1nearazTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qFn)) := by decide +kernel
theorem q1nearazTsM_eq : q1nearazTsM = mergeL q1nearazTs := by decide +kernel
theorem q1nearazFq_poles : q1nearazFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel
theorem q1nearazFq_plog0 : q1nearazFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 1 := by decide +kernel
theorem q1nearaztFq_poles : q1nearaztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
