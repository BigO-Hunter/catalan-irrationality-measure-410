module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpmRBGB000

@[expose] public section

/-! **SPM_R, trial 2, corner 1/16: sup statement** (series window on [gs, 3/10], merged Laurent cells on [3/10, xc)). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


def q2spmrbgN : ℕ := 72
def q2spmrbgHi : ℚ := qmk (3) 5 0 1
def q2spmrbgDelta : ℚ := dy3 (1) 0 69
theorem q2spmrbg_laurent : l0OK q2spmrbTsM q2spmrbgHi q2spmrbgN = true := by decide +kernel
theorem q2spmrbg_cL : l0C q2spmrbTsM = 0 := by decide +kernel
theorem q2spmrbg_plogs : q2spmrbgFq.plogs = q2spmrbFq.plogs := by decide +kernel
theorem q2spmrbg_poles : q2spmrbgFq.poles = q2spmrbFq.poles := by decide +kernel
theorem q2spmrbg_hD : polyAB (vecAdd (vecAdd q2spmrbFq.poly (l0P q2spmrbTsM q2spmrbgN)) (q2spmrbgPoly.map (fun t => (-1 : ℚ) * t))) 0 q2spmrbgHi ≤ q2spmrbgDelta := by decide +kernel
theorem q2spmrbg_tot : q2spmrbgT + q2spmrbgDelta + l0Err q2spmrbgHi q2spmrbgN q2spmrbTsM ≤ q2spmrbT := by decide +kernel
theorem q2spmrbg_b0 : 0 < q2spmrbgBd.getD 0 0 := by decide +kernel
theorem q2spmrbg_bN : q2spmrbgBd.getD 4 0 ≤ q2spmrbgHi := by decide +kernel
theorem q2spmrbg_bmid : q2spmrbgBd.getD 4 0 = q2spmrbBd.getD 0 0 := by decide +kernel
theorem q2spmrbg_dom0 : q2spmrbgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q2spmrb_domN : q2spmrbBd.getD 12 0 = 999 / 1000 := by decide +kernel
theorem q2spmrbgCells : ∀ x ∈ Icc ((q2spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q2spmrbgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2spmrbgFq (poleF q2spmrbgFq.poles) 0 x ≤ (q2spmrbgT : ℝ) :=
  cover_union (cover_union (cover_union (q2spmrbgB000Bound) q2spmrbgB001Bound) q2spmrbgB002Bound) q2spmrbgB003Bound
theorem q2spmrbgSer : ∀ x ∈ Icc ((q2spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q2spmrbgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2spmrbFq (poleF q2spmrbFq.poles) 0 x + lfieldTower q2spmrbTsM 0 x ≤ (q2spmrbT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2spmrbgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2spmrbg_b0
  have hN : ((q2spmrbgBd.getD 4 0 : ℚ) : ℝ) ≤ (q2spmrbgHi : ℝ) := by exact_mod_cast q2spmrbg_bN
  have h := l0_series_sound q2spmrbFq q2spmrbgFq q2spmrbTsM q2spmrbgHi q2spmrbgN q2spmrbgDelta q2spmrbgT q2spmrbg_laurent q2spmrbg_cL q2spmrbg_plogs q2spmrbg_poles q2spmrbg_hD
    (Set.Icc ((q2spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q2spmrbgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2spmrbgCells y hy) x hx
  have hq : ((q2spmrbgT + q2spmrbgDelta + l0Err q2spmrbgHi q2spmrbgN q2spmrbTsM : ℚ) : ℝ) ≤ (q2spmrbT : ℝ) := by exact_mod_cast q2spmrbg_tot
  exact h.trans hq

theorem q2spmrbLaurentM : ∀ x ∈ Icc ((q2spmrbBd.getD 0 0 : ℚ) : ℝ) ((q2spmrbBd.getD 12 0 : ℚ) : ℝ), fieldTower q2spmrbFq (poleF q2spmrbFq.poles) 0 x + lfieldTower q2spmrbTsM 0 x ≤ (q2spmrbT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2spmrbB000Bound) q2spmrbB001Bound) q2spmrbB002Bound) q2spmrbB003Bound) q2spmrbB004Bound) q2spmrbB005Bound) q2spmrbB006Bound) q2spmrbB007Bound) q2spmrbB008Bound) q2spmrbB009Bound) q2spmrbB010Bound) q2spmrbB011Bound
/-- **SPM_R**, trial 2, corner 1/16: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q2spmrbSup : ∀ x ∈ Icc ((q2spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q2spmrbBd.getD 12 0 : ℚ) : ℝ), fieldTower q2spmrbFq (poleF q2spmrbFq.poles) 0 x + lfieldTower q2spmrbTs 0 x ≤ (q2spmrbT : ℝ) := by
  intro x hx
  have hb : ((q2spmrbgBd.getD 4 0 : ℚ) : ℝ) = ((q2spmrbBd.getD 0 0 : ℚ) : ℝ) := by rw [q2spmrbg_bmid]
  have h1 := q2spmrbgSer
  rw [hb] at h1
  have h := cover_union h1 q2spmrbLaurentM x hx
  rw [q2spmrbTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
