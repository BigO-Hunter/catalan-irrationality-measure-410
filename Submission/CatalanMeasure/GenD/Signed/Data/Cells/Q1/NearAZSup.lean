module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAZTB002

@[expose] public section

/-! **NEAR, trial 1, corner 1/200: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1nearaztSupM : ∀ x ∈ Icc ((q1nearaztBd.getD 0 0 : ℚ) : ℝ) ((q1nearaztBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearaztFq (poleF q1nearaztFq.poles) 0 x + lfieldTower q1nearazTsM 0 x ≤ (q1nearaztT : ℝ) :=
  q1nearaztB000Bound
theorem q1nearaztSup : ∀ x ∈ Icc ((q1nearaztBd.getD 0 0 : ℚ) : ℝ) ((q1nearaztBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearaztFq (poleF q1nearaztFq.poles) 0 x + lfieldTower q1nearazTs 0 x ≤ (q1nearaztT : ℝ) := by
  intro x hx
  have h := q1nearaztSupM x hx
  rw [q1nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q1nearaztSupJM : ∀ x ∈ Icc ((q1nearaztBd.getD 1 0 : ℚ) : ℝ) ((q1nearaztBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearaztFq (poleF q1nearaztFq.poles) 0 x + lfieldTower q1nearazTsM 0 x ≤ (q1nearaztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearaztB001Bound) q1nearaztB002Bound) q1nearaztB003Bound) q1nearaztB004Bound) q1nearaztB005Bound) q1nearaztB006Bound) q1nearaztB007Bound) q1nearaztB008Bound) q1nearaztB009Bound) q1nearaztB010Bound) q1nearaztB011Bound
theorem q1nearaztSupJ : ∀ x ∈ Icc ((q1nearaztBd.getD 1 0 : ℚ) : ℝ) ((q1nearaztBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearaztFq (poleF q1nearaztFq.poles) 0 x + lfieldTower q1nearazTs 0 x ≤ (q1nearaztTJ : ℝ) := by
  intro x hx
  have h := q1nearaztSupJM x hx
  rw [q1nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

def q1nearazgN : ℕ := 72
def q1nearazgHi : ℚ := qmk (3) 5 0 1
def q1nearazgDelta : ℚ := dy3 (1) 0 69
theorem q1nearazg_laurent : l0OK q1nearazTsM q1nearazgHi q1nearazgN = true := by decide +kernel
theorem q1nearazg_cL : l0C q1nearazTsM = 0 := by decide +kernel
theorem q1nearazg_plogs : q1nearazgFq.plogs = q1nearazFq.plogs := by decide +kernel
theorem q1nearazg_poles : q1nearazgFq.poles = q1nearazFq.poles := by decide +kernel
theorem q1nearazg_hD : polyAB (vecAdd (vecAdd q1nearazFq.poly (l0P q1nearazTsM q1nearazgN)) (q1nearazgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1nearazgHi ≤ q1nearazgDelta := by decide +kernel
theorem q1nearazg_tot : q1nearazgT + q1nearazgDelta + l0Err q1nearazgHi q1nearazgN q1nearazTsM ≤ q1nearazT := by decide +kernel
theorem q1nearazg_b0 : 0 < q1nearazgBd.getD 0 0 := by decide +kernel
theorem q1nearazg_bN : q1nearazgBd.getD 4 0 ≤ q1nearazgHi := by decide +kernel
theorem q1nearazg_bmid : q1nearazgBd.getD 4 0 = q1nearazBd.getD 0 0 := by decide +kernel
theorem q1nearazg_dom0 : q1nearazgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1nearaz_domN : q1nearazBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q1nearazgCells : ∀ x ∈ Icc ((q1nearazgBd.getD 0 0 : ℚ) : ℝ) ((q1nearazgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearazgFq (poleF q1nearazgFq.poles) 0 x ≤ (q1nearazgT : ℝ) :=
  cover_union (cover_union (cover_union (q1nearazgB000Bound) q1nearazgB001Bound) q1nearazgB002Bound) q1nearazgB003Bound
theorem q1nearazgSer : ∀ x ∈ Icc ((q1nearazgBd.getD 0 0 : ℚ) : ℝ) ((q1nearazgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearazFq (poleF q1nearazFq.poles) 0 x + lfieldTower q1nearazTsM 0 x ≤ (q1nearazT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1nearazgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1nearazg_b0
  have hN : ((q1nearazgBd.getD 4 0 : ℚ) : ℝ) ≤ (q1nearazgHi : ℝ) := by exact_mod_cast q1nearazg_bN
  have h := l0_series_sound q1nearazFq q1nearazgFq q1nearazTsM q1nearazgHi q1nearazgN q1nearazgDelta q1nearazgT q1nearazg_laurent q1nearazg_cL q1nearazg_plogs q1nearazg_poles q1nearazg_hD
    (Set.Icc ((q1nearazgBd.getD 0 0 : ℚ) : ℝ) ((q1nearazgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1nearazgCells y hy) x hx
  have hq : ((q1nearazgT + q1nearazgDelta + l0Err q1nearazgHi q1nearazgN q1nearazTsM : ℚ) : ℝ) ≤ (q1nearazT : ℝ) := by exact_mod_cast q1nearazg_tot
  exact h.trans hq

theorem q1nearazLaurentM : ∀ x ∈ Icc ((q1nearazBd.getD 0 0 : ℚ) : ℝ) ((q1nearazBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearazFq (poleF q1nearazFq.poles) 0 x + lfieldTower q1nearazTsM 0 x ≤ (q1nearazT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearazB000Bound) q1nearazB001Bound) q1nearazB002Bound) q1nearazB003Bound) q1nearazB004Bound) q1nearazB005Bound) q1nearazB006Bound) q1nearazB007Bound) q1nearazB008Bound) q1nearazB009Bound
/-- **NEAR**, trial 1, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1nearazSup : ∀ x ∈ Icc ((q1nearazgBd.getD 0 0 : ℚ) : ℝ) ((q1nearazBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearazFq (poleF q1nearazFq.poles) 0 x + lfieldTower q1nearazTs 0 x ≤ (q1nearazT : ℝ) := by
  intro x hx
  have hb : ((q1nearazgBd.getD 4 0 : ℚ) : ℝ) = ((q1nearazBd.getD 0 0 : ℚ) : ℝ) := by rw [q1nearazg_bmid]
  have h1 := q1nearazgSer
  rw [hb] at h1
  have h := cover_union h1 q1nearazLaurentM x hx
  rw [q1nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
