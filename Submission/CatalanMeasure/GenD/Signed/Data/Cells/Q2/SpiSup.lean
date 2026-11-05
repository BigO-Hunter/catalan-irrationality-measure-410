module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiB007

@[expose] public section

/-! **SP, trial 2: sup statements.** -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q2spiSupM : ∀ x ∈ Icc ((q2spiBd.getD 0 0 : ℚ) : ℝ) ((q2spiBd.getD 19 0 : ℚ) : ℝ), fieldTower q2spiFq (poleF q2spiFq.poles) 0 x + lfieldTower q2spiTsM 0 x ≤ (q2spiT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2spiB000Bound) q2spiB001Bound) q2spiB002Bound) q2spiB003Bound) q2spiB004Bound) q2spiB005Bound) q2spiB006Bound) q2spiB007Bound) q2spiB008Bound) q2spiB009Bound) q2spiB010Bound) q2spiB011Bound) q2spiB012Bound) q2spiB013Bound) q2spiB014Bound) q2spiB015Bound) q2spiB016Bound) q2spiB017Bound) q2spiB018Bound
theorem q2spiSup : ∀ x ∈ Icc ((q2spiBd.getD 0 0 : ℚ) : ℝ) ((q2spiBd.getD 19 0 : ℚ) : ℝ), fieldTower q2spiFq (poleF q2spiFq.poles) 0 x + lfieldTower q2spiTs 0 x ≤ (q2spiT : ℝ) := by
  intro x hx
  have h := q2spiSupM x hx
  rw [q2spiTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
