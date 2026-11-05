module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 2, corner bz) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2nearbzTs_eq : q2nearbzTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qFn)) := by decide +kernel
theorem q2nearbzTsM_eq : q2nearbzTsM = mergeL q2nearbzTs := by decide +kernel
theorem q2nearbzFq_poles : q2nearbzFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel
theorem q2nearbzFq_plog0 : q2nearbzFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.plogs.take 1 := by decide +kernel
theorem q2nearbztFq_poles : q2nearbztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
