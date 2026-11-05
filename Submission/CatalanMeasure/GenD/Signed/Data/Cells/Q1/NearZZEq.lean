module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 1, corner zz) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1nearzzTs_eq : q1nearzzTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qFn)) := by decide +kernel
theorem q1nearzzTsM_eq : q1nearzzTsM = mergeL q1nearzzTs := by decide +kernel
theorem q1nearzzFq_poles : q1nearzzFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel
theorem q1nearzzFq_plog0 : q1nearzzFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 1 := by decide +kernel
theorem q1nearzztFq_poles : q1nearzztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
