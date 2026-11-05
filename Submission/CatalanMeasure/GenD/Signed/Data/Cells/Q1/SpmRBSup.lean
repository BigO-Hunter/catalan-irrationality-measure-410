module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRBGB000

@[expose] public section

/-! **SPM_R, trial 1, corner 1/16: sup statement** (series window on [gs, 3/10], merged Laurent cells on [3/10, xc)). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


def q1spmrbgN : ℕ := 72
def q1spmrbgHi : ℚ := qmk (3) 5 0 1
def q1spmrbgDelta : ℚ := dy3 (1) 0 69
theorem q1spmrbg_laurent : l0OK q1spmrbTsM q1spmrbgHi q1spmrbgN = true := by decide +kernel
theorem q1spmrbg_cL : l0C q1spmrbTsM = 0 := by decide +kernel
theorem q1spmrbg_plogs : q1spmrbgFq.plogs = q1spmrbFq.plogs := by decide +kernel
theorem q1spmrbg_poles : q1spmrbgFq.poles = q1spmrbFq.poles := by decide +kernel
theorem q1spmrbg_hD : polyAB (vecAdd (vecAdd q1spmrbFq.poly (l0P q1spmrbTsM q1spmrbgN)) (q1spmrbgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1spmrbgHi ≤ q1spmrbgDelta := by decide +kernel
theorem q1spmrbg_tot : q1spmrbgT + q1spmrbgDelta + l0Err q1spmrbgHi q1spmrbgN q1spmrbTsM ≤ q1spmrbT := by decide +kernel
theorem q1spmrbg_b0 : 0 < q1spmrbgBd.getD 0 0 := by decide +kernel
theorem q1spmrbg_bN : q1spmrbgBd.getD 4 0 ≤ q1spmrbgHi := by decide +kernel
theorem q1spmrbg_bmid : q1spmrbgBd.getD 4 0 = q1spmrbBd.getD 0 0 := by decide +kernel
theorem q1spmrbg_dom0 : q1spmrbgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1spmrb_domN : q1spmrbBd.getD 12 0 = 999 / 1000 := by decide +kernel
theorem q1spmrbgCells : ∀ x ∈ Icc ((q1spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q1spmrbgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1spmrbgFq (poleF q1spmrbgFq.poles) 0 x ≤ (q1spmrbgT : ℝ) :=
  cover_union (cover_union (cover_union (q1spmrbgB000Bound) q1spmrbgB001Bound) q1spmrbgB002Bound) q1spmrbgB003Bound
theorem q1spmrbgSer : ∀ x ∈ Icc ((q1spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q1spmrbgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1spmrbFq (poleF q1spmrbFq.poles) 0 x + lfieldTower q1spmrbTsM 0 x ≤ (q1spmrbT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1spmrbgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1spmrbg_b0
  have hN : ((q1spmrbgBd.getD 4 0 : ℚ) : ℝ) ≤ (q1spmrbgHi : ℝ) := by exact_mod_cast q1spmrbg_bN
  have h := l0_series_sound q1spmrbFq q1spmrbgFq q1spmrbTsM q1spmrbgHi q1spmrbgN q1spmrbgDelta q1spmrbgT q1spmrbg_laurent q1spmrbg_cL q1spmrbg_plogs q1spmrbg_poles q1spmrbg_hD
    (Set.Icc ((q1spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q1spmrbgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1spmrbgCells y hy) x hx
  have hq : ((q1spmrbgT + q1spmrbgDelta + l0Err q1spmrbgHi q1spmrbgN q1spmrbTsM : ℚ) : ℝ) ≤ (q1spmrbT : ℝ) := by exact_mod_cast q1spmrbg_tot
  exact h.trans hq

theorem q1spmrbLaurentM : ∀ x ∈ Icc ((q1spmrbBd.getD 0 0 : ℚ) : ℝ) ((q1spmrbBd.getD 12 0 : ℚ) : ℝ), fieldTower q1spmrbFq (poleF q1spmrbFq.poles) 0 x + lfieldTower q1spmrbTsM 0 x ≤ (q1spmrbT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1spmrbB000Bound) q1spmrbB001Bound) q1spmrbB002Bound) q1spmrbB003Bound) q1spmrbB004Bound) q1spmrbB005Bound) q1spmrbB006Bound) q1spmrbB007Bound) q1spmrbB008Bound) q1spmrbB009Bound) q1spmrbB010Bound) q1spmrbB011Bound
/-- **SPM_R**, trial 1, corner 1/16: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1spmrbSup : ∀ x ∈ Icc ((q1spmrbgBd.getD 0 0 : ℚ) : ℝ) ((q1spmrbBd.getD 12 0 : ℚ) : ℝ), fieldTower q1spmrbFq (poleF q1spmrbFq.poles) 0 x + lfieldTower q1spmrbTs 0 x ≤ (q1spmrbT : ℝ) := by
  intro x hx
  have hb : ((q1spmrbgBd.getD 4 0 : ℚ) : ℝ) = ((q1spmrbBd.getD 0 0 : ℚ) : ℝ) := by rw [q1spmrbg_bmid]
  have h1 := q1spmrbgSer
  rw [hb] at h1
  have h := cover_union h1 q1spmrbLaurentM x hx
  rw [q1spmrbTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
