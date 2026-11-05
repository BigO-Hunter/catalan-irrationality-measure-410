module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpiB011

@[expose] public section

/-! **SP, trial 1: sup statements.** -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1spiSupM : ∀ x ∈ Icc ((q1spiBd.getD 0 0 : ℚ) : ℝ) ((q1spiBd.getD 19 0 : ℚ) : ℝ), fieldTower q1spiFq (poleF q1spiFq.poles) 0 x + lfieldTower q1spiTsM 0 x ≤ (q1spiT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1spiB000Bound) q1spiB001Bound) q1spiB002Bound) q1spiB003Bound) q1spiB004Bound) q1spiB005Bound) q1spiB006Bound) q1spiB007Bound) q1spiB008Bound) q1spiB009Bound) q1spiB010Bound) q1spiB011Bound) q1spiB012Bound) q1spiB013Bound) q1spiB014Bound) q1spiB015Bound) q1spiB016Bound) q1spiB017Bound) q1spiB018Bound
theorem q1spiSup : ∀ x ∈ Icc ((q1spiBd.getD 0 0 : ℚ) : ℝ) ((q1spiBd.getD 19 0 : ℚ) : ℝ), fieldTower q1spiFq (poleF q1spiFq.poles) 0 x + lfieldTower q1spiTs 0 x ≤ (q1spiT : ℝ) := by
  intro x hx
  have h := q1spiSupM x hx
  rw [q1spiTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
