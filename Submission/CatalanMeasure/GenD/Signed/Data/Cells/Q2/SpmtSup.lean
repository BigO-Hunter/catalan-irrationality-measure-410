module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmtEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmtB000

@[expose] public section

/-! **SPM_TOP, trial 2: sup statements.** -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q2spmtSupM : ∀ x ∈ Icc ((q2spmtBd.getD 0 0 : ℚ) : ℝ) ((q2spmtBd.getD 1 0 : ℚ) : ℝ), fieldTower q2spmtFq (poleF q2spmtFq.poles) 0 x + lfieldTower q2spmtTsM 0 x ≤ (q2spmtT : ℝ) :=
  q2spmtB000Bound
theorem q2spmtSup : ∀ x ∈ Icc ((q2spmtBd.getD 0 0 : ℚ) : ℝ) ((q2spmtBd.getD 1 0 : ℚ) : ℝ), fieldTower q2spmtFq (poleF q2spmtFq.poles) 0 x + lfieldTower q2spmtTs 0 x ≤ (q2spmtT : ℝ) := by
  intro x hx
  have h := q2spmtSupM x hx
  rw [q2spmtTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
