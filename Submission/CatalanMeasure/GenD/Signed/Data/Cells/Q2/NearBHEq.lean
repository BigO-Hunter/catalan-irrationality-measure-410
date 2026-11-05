module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 2, corner bh) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2nearbhTs_eq : q2nearbhTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qFn)) := by decide +kernel
theorem q2nearbhTsM_eq : q2nearbhTsM = mergeL q2nearbhTs := by decide +kernel
theorem q2nearbhFq_poles : q2nearbhFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel
theorem q2nearbhFq_plog0 : q2nearbhFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.plogs.take 1 := by decide +kernel
theorem q2nearbhtFq_poles : q2nearbhtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.poles := by decide +kernel
theorem q2nearbhFq_plogs : q2nearbhFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.plogs := by decide +kernel
theorem q2nearbhtFq_plogs : q2nearbhtFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.nearFq.plogs.take 2 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
