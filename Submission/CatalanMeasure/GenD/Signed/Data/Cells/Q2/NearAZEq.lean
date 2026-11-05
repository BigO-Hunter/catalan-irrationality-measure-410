module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 2, corner az) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2nearazTs_eq : q2nearazTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qFn)) := by decide +kernel
theorem q2nearazTsM_eq : q2nearazTsM = mergeL q2nearazTs := by decide +kernel
theorem q2nearazFq_poles : q2nearazFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel
theorem q2nearazFq_plog0 : q2nearazFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.plogs.take 1 := by decide +kernel
theorem q2nearaztFq_poles : q2nearaztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
