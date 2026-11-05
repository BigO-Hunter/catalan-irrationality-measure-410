module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAZTB002

@[expose] public section

/-! **NEAR, trial 2, corner 1/200: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q2nearaztSupM : ∀ x ∈ Icc ((q2nearaztBd.getD 0 0 : ℚ) : ℝ) ((q2nearaztBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearaztFq (poleF q2nearaztFq.poles) 0 x + lfieldTower q2nearazTsM 0 x ≤ (q2nearaztT : ℝ) :=
  q2nearaztB000Bound
theorem q2nearaztSup : ∀ x ∈ Icc ((q2nearaztBd.getD 0 0 : ℚ) : ℝ) ((q2nearaztBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearaztFq (poleF q2nearaztFq.poles) 0 x + lfieldTower q2nearazTs 0 x ≤ (q2nearaztT : ℝ) := by
  intro x hx
  have h := q2nearaztSupM x hx
  rw [q2nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q2nearaztSupJM : ∀ x ∈ Icc ((q2nearaztBd.getD 1 0 : ℚ) : ℝ) ((q2nearaztBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearaztFq (poleF q2nearaztFq.poles) 0 x + lfieldTower q2nearazTsM 0 x ≤ (q2nearaztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearaztB001Bound) q2nearaztB002Bound) q2nearaztB003Bound) q2nearaztB004Bound) q2nearaztB005Bound) q2nearaztB006Bound) q2nearaztB007Bound) q2nearaztB008Bound) q2nearaztB009Bound) q2nearaztB010Bound) q2nearaztB011Bound
theorem q2nearaztSupJ : ∀ x ∈ Icc ((q2nearaztBd.getD 1 0 : ℚ) : ℝ) ((q2nearaztBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearaztFq (poleF q2nearaztFq.poles) 0 x + lfieldTower q2nearazTs 0 x ≤ (q2nearaztTJ : ℝ) := by
  intro x hx
  have h := q2nearaztSupJM x hx
  rw [q2nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

def q2nearazgN : ℕ := 72
def q2nearazgHi : ℚ := qmk (3) 5 0 1
def q2nearazgDelta : ℚ := dy3 (1) 0 69
theorem q2nearazg_laurent : l0OK q2nearazTsM q2nearazgHi q2nearazgN = true := by decide +kernel
theorem q2nearazg_cL : l0C q2nearazTsM = 0 := by decide +kernel
theorem q2nearazg_plogs : q2nearazgFq.plogs = q2nearazFq.plogs := by decide +kernel
theorem q2nearazg_poles : q2nearazgFq.poles = q2nearazFq.poles := by decide +kernel
theorem q2nearazg_hD : polyAB (vecAdd (vecAdd q2nearazFq.poly (l0P q2nearazTsM q2nearazgN)) (q2nearazgPoly.map (fun t => (-1 : ℚ) * t))) 0 q2nearazgHi ≤ q2nearazgDelta := by decide +kernel
theorem q2nearazg_tot : q2nearazgT + q2nearazgDelta + l0Err q2nearazgHi q2nearazgN q2nearazTsM ≤ q2nearazT := by decide +kernel
theorem q2nearazg_b0 : 0 < q2nearazgBd.getD 0 0 := by decide +kernel
theorem q2nearazg_bN : q2nearazgBd.getD 4 0 ≤ q2nearazgHi := by decide +kernel
theorem q2nearazg_bmid : q2nearazgBd.getD 4 0 = q2nearazBd.getD 0 0 := by decide +kernel
theorem q2nearazg_dom0 : q2nearazgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q2nearaz_domN : q2nearazBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q2nearazgCells : ∀ x ∈ Icc ((q2nearazgBd.getD 0 0 : ℚ) : ℝ) ((q2nearazgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearazgFq (poleF q2nearazgFq.poles) 0 x ≤ (q2nearazgT : ℝ) :=
  cover_union (cover_union (cover_union (q2nearazgB000Bound) q2nearazgB001Bound) q2nearazgB002Bound) q2nearazgB003Bound
theorem q2nearazgSer : ∀ x ∈ Icc ((q2nearazgBd.getD 0 0 : ℚ) : ℝ) ((q2nearazgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearazFq (poleF q2nearazFq.poles) 0 x + lfieldTower q2nearazTsM 0 x ≤ (q2nearazT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2nearazgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2nearazg_b0
  have hN : ((q2nearazgBd.getD 4 0 : ℚ) : ℝ) ≤ (q2nearazgHi : ℝ) := by exact_mod_cast q2nearazg_bN
  have h := l0_series_sound q2nearazFq q2nearazgFq q2nearazTsM q2nearazgHi q2nearazgN q2nearazgDelta q2nearazgT q2nearazg_laurent q2nearazg_cL q2nearazg_plogs q2nearazg_poles q2nearazg_hD
    (Set.Icc ((q2nearazgBd.getD 0 0 : ℚ) : ℝ) ((q2nearazgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2nearazgCells y hy) x hx
  have hq : ((q2nearazgT + q2nearazgDelta + l0Err q2nearazgHi q2nearazgN q2nearazTsM : ℚ) : ℝ) ≤ (q2nearazT : ℝ) := by exact_mod_cast q2nearazg_tot
  exact h.trans hq

theorem q2nearazLaurentM : ∀ x ∈ Icc ((q2nearazBd.getD 0 0 : ℚ) : ℝ) ((q2nearazBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearazFq (poleF q2nearazFq.poles) 0 x + lfieldTower q2nearazTsM 0 x ≤ (q2nearazT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearazB000Bound) q2nearazB001Bound) q2nearazB002Bound) q2nearazB003Bound) q2nearazB004Bound) q2nearazB005Bound) q2nearazB006Bound) q2nearazB007Bound) q2nearazB008Bound) q2nearazB009Bound
/-- **NEAR**, trial 2, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q2nearazSup : ∀ x ∈ Icc ((q2nearazgBd.getD 0 0 : ℚ) : ℝ) ((q2nearazBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearazFq (poleF q2nearazFq.poles) 0 x + lfieldTower q2nearazTs 0 x ≤ (q2nearazT : ℝ) := by
  intro x hx
  have hb : ((q2nearazgBd.getD 4 0 : ℚ) : ℝ) = ((q2nearazBd.getD 0 0 : ℚ) : ℝ) := by rw [q2nearazg_bmid]
  have h1 := q2nearazgSer
  rw [hb] at h1
  have h := cover_union h1 q2nearazLaurentM x hx
  rw [q2nearazTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
