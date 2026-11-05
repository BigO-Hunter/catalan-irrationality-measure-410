module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 1, corner bh) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1nearbhTs_eq : q1nearbhTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qFn)) := by decide +kernel
theorem q1nearbhTsM_eq : q1nearbhTsM = mergeL q1nearbhTs := by decide +kernel
theorem q1nearbhFq_poles : q1nearbhFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel
theorem q1nearbhFq_plog0 : q1nearbhFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 1 := by decide +kernel
theorem q1nearbhtFq_poles : q1nearbhtFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
