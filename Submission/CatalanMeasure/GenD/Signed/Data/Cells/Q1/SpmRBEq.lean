module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBGFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_R data (trial 1, corner b) with the trial literals; merge lemma. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spmrbTs_eq : q1spmrbTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qTn := by decide +kernel
theorem q1spmrbTsM_eq : q1spmrbTsM = mergeL q1spmrbTs := by decide +kernel
theorem q1spmrbFq_poles : q1spmrbFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.poles := by decide +kernel
theorem q1spmrbFq_plogs : q1spmrbFq.plogs.take 36 = CatalanMeasure.GenD.Signed.Data.Trial.T1.spmFq.plogs.take 36 := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
