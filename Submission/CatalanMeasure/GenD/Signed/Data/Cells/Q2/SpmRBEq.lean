module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBGFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SPM_R data (trial 2, corner b) with the trial literals; merge lemma. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q2spmrbTs_eq : q2spmrbTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T2.trial.qTn := by decide +kernel
theorem q2spmrbTsM_eq : q2spmrbTsM = mergeL q2spmrbTs := by decide +kernel
theorem q2spmrbFq_poles : q2spmrbFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.poles := by decide +kernel
theorem q2spmrbFq_plogs : q2spmrbFq.plogs.take 36 = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.plogs.take 36 := by decide +kernel
theorem q2spmrbFq_plogs_full : q2spmrbFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.spmFq.plogs := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
