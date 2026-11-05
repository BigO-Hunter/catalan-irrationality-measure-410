module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAZTB002

@[expose] public section

/-! **NEAR, trial 0, corner 1/200: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q0nearaztSupM : ∀ x ∈ Icc ((q0nearaztBd.getD 0 0 : ℚ) : ℝ) ((q0nearaztBd.getD 1 0 : ℚ) : ℝ), fieldTower q0nearaztFq (poleF q0nearaztFq.poles) 0 x + lfieldTower q0nearazTsM 0 x ≤ (q0nearaztT : ℝ) :=
  q0nearaztB000Bound
theorem q0nearaztSup : ∀ x ∈ Icc ((q0nearaztBd.getD 0 0 : ℚ) : ℝ) ((q0nearaztBd.getD 1 0 : ℚ) : ℝ), fieldTower q0nearaztFq (poleF q0nearaztFq.poles) 0 x + lfieldTower q0nearazTs 0 x ≤ (q0nearaztT : ℝ) := by
  intro x hx
  have h := q0nearaztSupM x hx
  rw [q0nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q0nearaztSupJM : ∀ x ∈ Icc ((q0nearaztBd.getD 1 0 : ℚ) : ℝ) ((q0nearaztBd.getD 12 0 : ℚ) : ℝ), fieldTower q0nearaztFq (poleF q0nearaztFq.poles) 0 x + lfieldTower q0nearazTsM 0 x ≤ (q0nearaztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0nearaztB001Bound) q0nearaztB002Bound) q0nearaztB003Bound) q0nearaztB004Bound) q0nearaztB005Bound) q0nearaztB006Bound) q0nearaztB007Bound) q0nearaztB008Bound) q0nearaztB009Bound) q0nearaztB010Bound) q0nearaztB011Bound
theorem q0nearaztSupJ : ∀ x ∈ Icc ((q0nearaztBd.getD 1 0 : ℚ) : ℝ) ((q0nearaztBd.getD 12 0 : ℚ) : ℝ), fieldTower q0nearaztFq (poleF q0nearaztFq.poles) 0 x + lfieldTower q0nearazTs 0 x ≤ (q0nearaztTJ : ℝ) := by
  intro x hx
  have h := q0nearaztSupJM x hx
  rw [q0nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

def q0nearazgN : ℕ := 72
def q0nearazgHi : ℚ := qmk (3) 5 0 1
def q0nearazgDelta : ℚ := dy3 (1) 0 69
theorem q0nearazg_laurent : l0OK q0nearazTsM q0nearazgHi q0nearazgN = true := by decide +kernel
theorem q0nearazg_cL : l0C q0nearazTsM = 0 := by decide +kernel
theorem q0nearazg_plogs : q0nearazgFq.plogs = q0nearazFq.plogs := by decide +kernel
theorem q0nearazg_poles : q0nearazgFq.poles = q0nearazFq.poles := by decide +kernel
theorem q0nearazg_hD : polyAB (vecAdd (vecAdd q0nearazFq.poly (l0P q0nearazTsM q0nearazgN)) (q0nearazgPoly.map (fun t => (-1 : ℚ) * t))) 0 q0nearazgHi ≤ q0nearazgDelta := by decide +kernel
theorem q0nearazg_tot : q0nearazgT + q0nearazgDelta + l0Err q0nearazgHi q0nearazgN q0nearazTsM ≤ q0nearazT := by decide +kernel
theorem q0nearazg_b0 : 0 < q0nearazgBd.getD 0 0 := by decide +kernel
theorem q0nearazg_bN : q0nearazgBd.getD 4 0 ≤ q0nearazgHi := by decide +kernel
theorem q0nearazg_bmid : q0nearazgBd.getD 4 0 = q0nearazBd.getD 0 0 := by decide +kernel
theorem q0nearazg_dom0 : q0nearazgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q0nearaz_domN : q0nearazBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q0nearazgCells : ∀ x ∈ Icc ((q0nearazgBd.getD 0 0 : ℚ) : ℝ) ((q0nearazgBd.getD 4 0 : ℚ) : ℝ), fieldTower q0nearazgFq (poleF q0nearazgFq.poles) 0 x ≤ (q0nearazgT : ℝ) :=
  cover_union (cover_union (cover_union (q0nearazgB000Bound) q0nearazgB001Bound) q0nearazgB002Bound) q0nearazgB003Bound
theorem q0nearazgSer : ∀ x ∈ Icc ((q0nearazgBd.getD 0 0 : ℚ) : ℝ) ((q0nearazgBd.getD 4 0 : ℚ) : ℝ), fieldTower q0nearazFq (poleF q0nearazFq.poles) 0 x + lfieldTower q0nearazTsM 0 x ≤ (q0nearazT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q0nearazgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q0nearazg_b0
  have hN : ((q0nearazgBd.getD 4 0 : ℚ) : ℝ) ≤ (q0nearazgHi : ℝ) := by exact_mod_cast q0nearazg_bN
  have h := l0_series_sound q0nearazFq q0nearazgFq q0nearazTsM q0nearazgHi q0nearazgN q0nearazgDelta q0nearazgT q0nearazg_laurent q0nearazg_cL q0nearazg_plogs q0nearazg_poles q0nearazg_hD
    (Set.Icc ((q0nearazgBd.getD 0 0 : ℚ) : ℝ) ((q0nearazgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q0nearazgCells y hy) x hx
  have hq : ((q0nearazgT + q0nearazgDelta + l0Err q0nearazgHi q0nearazgN q0nearazTsM : ℚ) : ℝ) ≤ (q0nearazT : ℝ) := by exact_mod_cast q0nearazg_tot
  exact h.trans hq

theorem q0nearazLaurentM : ∀ x ∈ Icc ((q0nearazBd.getD 0 0 : ℚ) : ℝ) ((q0nearazBd.getD 10 0 : ℚ) : ℝ), fieldTower q0nearazFq (poleF q0nearazFq.poles) 0 x + lfieldTower q0nearazTsM 0 x ≤ (q0nearazT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0nearazB000Bound) q0nearazB001Bound) q0nearazB002Bound) q0nearazB003Bound) q0nearazB004Bound) q0nearazB005Bound) q0nearazB006Bound) q0nearazB007Bound) q0nearazB008Bound) q0nearazB009Bound
/-- **NEAR**, trial 0, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q0nearazSup : ∀ x ∈ Icc ((q0nearazgBd.getD 0 0 : ℚ) : ℝ) ((q0nearazBd.getD 10 0 : ℚ) : ℝ), fieldTower q0nearazFq (poleF q0nearazFq.poles) 0 x + lfieldTower q0nearazTs 0 x ≤ (q0nearazT : ℝ) := by
  intro x hx
  have hb : ((q0nearazgBd.getD 4 0 : ℚ) : ℝ) = ((q0nearazBd.getD 0 0 : ℚ) : ℝ) := by rw [q0nearazg_bmid]
  have h1 := q0nearazgSer
  rw [hb] at h1
  have h := cover_union h1 q0nearazLaurentM x hx
  rw [q0nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
