module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 0, corner zz) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0nearzzTs_eq : q0nearzzTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T0.trial.qFn)) := by decide +kernel
theorem q0nearzzTsM_eq : q0nearzzTsM = mergeL q0nearzzTs := by decide +kernel
theorem q0nearzzFq_poles : q0nearzzFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.poles := by decide +kernel
theorem q0nearzzFq_plog0 : q0nearzzFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.plogs.take 1 := by decide +kernel
theorem q0nearzztFq_poles : q0nearzztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.poles := by decide +kernel
theorem q0nearzzFq_plogs : q0nearzzFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.plogs := by decide +kernel
theorem q0nearzztFq_plogs : q0nearzztFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T0.nearFq.plogs.take 2 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
