module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the NEAR data (trial 1, corner bz) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1nearbzTs_eq : q1nearbzTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qFn)) := by decide +kernel
theorem q1nearbzTsM_eq : q1nearbzTsM = mergeL q1nearbzTs := by decide +kernel
theorem q1nearbzFq_poles : q1nearbzFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel
theorem q1nearbzFq_plog0 : q1nearbzFq.plogs.take 1 = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 1 := by decide +kernel
theorem q1nearbztFq_poles : q1nearbztFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
