module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! Shared-path identification of the SP data (trial 1) with the trial literals, and the merge lemma instance. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1spiTs_eq : q1spiTs = CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qTn := by decide +kernel
theorem q1spiTsM_eq : q1spiTsM = mergeL q1spiTs := by decide +kernel
theorem q1spiFq_poles : q1spiFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.poles := by decide +kernel
theorem q1spiFq_plogs : q1spiFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.spFq.plogs := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
