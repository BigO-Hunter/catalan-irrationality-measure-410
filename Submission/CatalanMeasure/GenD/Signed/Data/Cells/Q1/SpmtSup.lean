module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmtEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmtB000

@[expose] public section

/-! **SPM_TOP, trial 1: sup statements.** -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1spmtSupM : ∀ x ∈ Icc ((q1spmtBd.getD 0 0 : ℚ) : ℝ) ((q1spmtBd.getD 1 0 : ℚ) : ℝ), fieldTower q1spmtFq (poleF q1spmtFq.poles) 0 x + lfieldTower q1spmtTsM 0 x ≤ (q1spmtT : ℝ) :=
  q1spmtB000Bound
theorem q1spmtSup : ∀ x ∈ Icc ((q1spmtBd.getD 0 0 : ℚ) : ℝ) ((q1spmtBd.getD 1 0 : ℚ) : ℝ), fieldTower q1spmtFq (poleF q1spmtFq.poles) 0 x + lfieldTower q1spmtTs 0 x ≤ (q1spmtT : ℝ) := by
  intro x hx
  have h := q1spmtSupM x hx
  rw [q1spmtTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
