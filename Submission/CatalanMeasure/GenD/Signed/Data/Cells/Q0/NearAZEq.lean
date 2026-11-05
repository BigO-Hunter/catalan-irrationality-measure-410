module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 0, corner az) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0nearazTs_eq : q0nearazTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qFn)) := by decide +kernel
theorem q0nearazTsM_eq : q0nearazTsM = mergeL q0nearazTs := by decide +kernel
theorem q0nearazFq_poles : q0nearazFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.poles := by decide +kernel
theorem q0nearazFq_plog0 : q0nearazFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.plogs.take 1 := by decide +kernel
theorem q0nearaztFq_poles : q0nearaztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
