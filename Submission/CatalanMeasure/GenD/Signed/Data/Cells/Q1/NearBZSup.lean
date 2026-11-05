module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBZTB002

@[expose] public section

/-! **NEAR, trial 1, corner 1/16: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1nearbztSupM : ∀ x ∈ Icc ((q1nearbztBd.getD 0 0 : ℚ) : ℝ) ((q1nearbztBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearbztFq (poleF q1nearbztFq.poles) 0 x + lfieldTower q1nearbzTsM 0 x ≤ (q1nearbztT : ℝ) :=
  q1nearbztB000Bound
theorem q1nearbztSup : ∀ x ∈ Icc ((q1nearbztBd.getD 0 0 : ℚ) : ℝ) ((q1nearbztBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearbztFq (poleF q1nearbztFq.poles) 0 x + lfieldTower q1nearbzTs 0 x ≤ (q1nearbztT : ℝ) := by
  intro x hx
  have h := q1nearbztSupM x hx
  rw [q1nearbzTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q1nearbztSupJM : ∀ x ∈ Icc ((q1nearbztBd.getD 1 0 : ℚ) : ℝ) ((q1nearbztBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearbztFq (poleF q1nearbztFq.poles) 0 x + lfieldTower q1nearbzTsM 0 x ≤ (q1nearbztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearbztB001Bound) q1nearbztB002Bound) q1nearbztB003Bound) q1nearbztB004Bound) q1nearbztB005Bound) q1nearbztB006Bound) q1nearbztB007Bound) q1nearbztB008Bound) q1nearbztB009Bound) q1nearbztB010Bound) q1nearbztB011Bound
theorem q1nearbztSupJ : ∀ x ∈ Icc ((q1nearbztBd.getD 1 0 : ℚ) : ℝ) ((q1nearbztBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearbztFq (poleF q1nearbztFq.poles) 0 x + lfieldTower q1nearbzTs 0 x ≤ (q1nearbztTJ : ℝ) := by
  intro x hx
  have h := q1nearbztSupJM x hx
  rw [q1nearbzTsM_eq, lfieldTower_mergeL] at h
  exact h

def q1nearbzgN : ℕ := 72
def q1nearbzgHi : ℚ := qmk (3) 5 0 1
def q1nearbzgDelta : ℚ := dy3 (1) 0 69
theorem q1nearbzg_laurent : l0OK q1nearbzTsM q1nearbzgHi q1nearbzgN = true := by decide +kernel
theorem q1nearbzg_cL : l0C q1nearbzTsM = 0 := by decide +kernel
theorem q1nearbzg_plogs : q1nearbzgFq.plogs = q1nearbzFq.plogs := by decide +kernel
theorem q1nearbzg_poles : q1nearbzgFq.poles = q1nearbzFq.poles := by decide +kernel
theorem q1nearbzg_hD : polyAB (vecAdd (vecAdd q1nearbzFq.poly (l0P q1nearbzTsM q1nearbzgN)) (q1nearbzgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1nearbzgHi ≤ q1nearbzgDelta := by decide +kernel
theorem q1nearbzg_tot : q1nearbzgT + q1nearbzgDelta + l0Err q1nearbzgHi q1nearbzgN q1nearbzTsM ≤ q1nearbzT := by decide +kernel
theorem q1nearbzg_b0 : 0 < q1nearbzgBd.getD 0 0 := by decide +kernel
theorem q1nearbzg_bN : q1nearbzgBd.getD 4 0 ≤ q1nearbzgHi := by decide +kernel
theorem q1nearbzg_bmid : q1nearbzgBd.getD 4 0 = q1nearbzBd.getD 0 0 := by decide +kernel
theorem q1nearbzg_dom0 : q1nearbzgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1nearbz_domN : q1nearbzBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q1nearbzgCells : ∀ x ∈ Icc ((q1nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearbzgFq (poleF q1nearbzgFq.poles) 0 x ≤ (q1nearbzgT : ℝ) :=
  cover_union (cover_union (cover_union (q1nearbzgB000Bound) q1nearbzgB001Bound) q1nearbzgB002Bound) q1nearbzgB003Bound
theorem q1nearbzgSer : ∀ x ∈ Icc ((q1nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearbzFq (poleF q1nearbzFq.poles) 0 x + lfieldTower q1nearbzTsM 0 x ≤ (q1nearbzT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1nearbzgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1nearbzg_b0
  have hN : ((q1nearbzgBd.getD 4 0 : ℚ) : ℝ) ≤ (q1nearbzgHi : ℝ) := by exact_mod_cast q1nearbzg_bN
  have h := l0_series_sound q1nearbzFq q1nearbzgFq q1nearbzTsM q1nearbzgHi q1nearbzgN q1nearbzgDelta q1nearbzgT q1nearbzg_laurent q1nearbzg_cL q1nearbzg_plogs q1nearbzg_poles q1nearbzg_hD
    (Set.Icc ((q1nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbzgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1nearbzgCells y hy) x hx
  have hq : ((q1nearbzgT + q1nearbzgDelta + l0Err q1nearbzgHi q1nearbzgN q1nearbzTsM : ℚ) : ℝ) ≤ (q1nearbzT : ℝ) := by exact_mod_cast q1nearbzg_tot
  exact h.trans hq

theorem q1nearbzLaurentM : ∀ x ∈ Icc ((q1nearbzBd.getD 0 0 : ℚ) : ℝ) ((q1nearbzBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearbzFq (poleF q1nearbzFq.poles) 0 x + lfieldTower q1nearbzTsM 0 x ≤ (q1nearbzT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearbzB000Bound) q1nearbzB001Bound) q1nearbzB002Bound) q1nearbzB003Bound) q1nearbzB004Bound) q1nearbzB005Bound) q1nearbzB006Bound) q1nearbzB007Bound) q1nearbzB008Bound) q1nearbzB009Bound
/-- **NEAR**, trial 1, corner 1/16: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1nearbzSup : ∀ x ∈ Icc ((q1nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbzBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearbzFq (poleF q1nearbzFq.poles) 0 x + lfieldTower q1nearbzTs 0 x ≤ (q1nearbzT : ℝ) := by
  intro x hx
  have hb : ((q1nearbzgBd.getD 4 0 : ℚ) : ℝ) = ((q1nearbzBd.getD 0 0 : ℚ) : ℝ) := by rw [q1nearbzg_bmid]
  have h1 := q1nearbzgSer
  rw [hb] at h1
  have h := cover_union h1 q1nearbzLaurentM x hx
  rw [q1nearbzTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
