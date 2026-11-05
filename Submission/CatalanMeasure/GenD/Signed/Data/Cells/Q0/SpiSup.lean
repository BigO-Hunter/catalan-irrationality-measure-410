module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiB009

@[expose] public section

/-! **SP, trial 0: sup statements.** -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q0spiSupM : ∀ x ∈ Icc ((q0spiBd.getD 0 0 : ℚ) : ℝ) ((q0spiBd.getD 19 0 : ℚ) : ℝ), fieldTower q0spiFq (poleF q0spiFq.poles) 0 x + lfieldTower q0spiTsM 0 x ≤ (q0spiT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0spiB000Bound) q0spiB001Bound) q0spiB002Bound) q0spiB003Bound) q0spiB004Bound) q0spiB005Bound) q0spiB006Bound) q0spiB007Bound) q0spiB008Bound) q0spiB009Bound) q0spiB010Bound) q0spiB011Bound) q0spiB012Bound) q0spiB013Bound) q0spiB014Bound) q0spiB015Bound) q0spiB016Bound) q0spiB017Bound) q0spiB018Bound
theorem q0spiSup : ∀ x ∈ Icc ((q0spiBd.getD 0 0 : ℚ) : ℝ) ((q0spiBd.getD 19 0 : ℚ) : ℝ), fieldTower q0spiFq (poleF q0spiFq.poles) 0 x + lfieldTower q0spiTs 0 x ≤ (q0spiT : ℝ) := by
  intro x hx
  have h := q0spiSupM x hx
  rw [q0spiTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
