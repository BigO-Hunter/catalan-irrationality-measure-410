module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBZTB002

@[expose] public section

/-! **NEAR, trial 2, corner 1/16: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q2nearbztSupM : ∀ x ∈ Icc ((q2nearbztBd.getD 0 0 : ℚ) : ℝ) ((q2nearbztBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearbztFq (poleF q2nearbztFq.poles) 0 x + lfieldTower q2nearbzTsM 0 x ≤ (q2nearbztT : ℝ) :=
  q2nearbztB000Bound
theorem q2nearbztSup : ∀ x ∈ Icc ((q2nearbztBd.getD 0 0 : ℚ) : ℝ) ((q2nearbztBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearbztFq (poleF q2nearbztFq.poles) 0 x + lfieldTower q2nearbzTs 0 x ≤ (q2nearbztT : ℝ) := by
  intro x hx
  have h := q2nearbztSupM x hx
  rw [q2nearbzTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q2nearbztSupJM : ∀ x ∈ Icc ((q2nearbztBd.getD 1 0 : ℚ) : ℝ) ((q2nearbztBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearbztFq (poleF q2nearbztFq.poles) 0 x + lfieldTower q2nearbzTsM 0 x ≤ (q2nearbztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearbztB001Bound) q2nearbztB002Bound) q2nearbztB003Bound) q2nearbztB004Bound) q2nearbztB005Bound) q2nearbztB006Bound) q2nearbztB007Bound) q2nearbztB008Bound) q2nearbztB009Bound) q2nearbztB010Bound) q2nearbztB011Bound
theorem q2nearbztSupJ : ∀ x ∈ Icc ((q2nearbztBd.getD 1 0 : ℚ) : ℝ) ((q2nearbztBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearbztFq (poleF q2nearbztFq.poles) 0 x + lfieldTower q2nearbzTs 0 x ≤ (q2nearbztTJ : ℝ) := by
  intro x hx
  have h := q2nearbztSupJM x hx
  rw [q2nearbzTsM_eq, lfieldTower_mergeL] at h
  exact h

def q2nearbzgN : ℕ := 72
def q2nearbzgHi : ℚ := qmk (3) 5 0 1
def q2nearbzgDelta : ℚ := dy3 (1) 0 69
theorem q2nearbzg_laurent : l0OK q2nearbzTsM q2nearbzgHi q2nearbzgN = true := by decide +kernel
theorem q2nearbzg_cL : l0C q2nearbzTsM = 0 := by decide +kernel
theorem q2nearbzg_plogs : q2nearbzgFq.plogs = q2nearbzFq.plogs := by decide +kernel
theorem q2nearbzg_poles : q2nearbzgFq.poles = q2nearbzFq.poles := by decide +kernel
theorem q2nearbzg_hD : polyAB (vecAdd (vecAdd q2nearbzFq.poly (l0P q2nearbzTsM q2nearbzgN)) (q2nearbzgPoly.map (fun t => (-1 : ℚ) * t))) 0 q2nearbzgHi ≤ q2nearbzgDelta := by decide +kernel
theorem q2nearbzg_tot : q2nearbzgT + q2nearbzgDelta + l0Err q2nearbzgHi q2nearbzgN q2nearbzTsM ≤ q2nearbzT := by decide +kernel
theorem q2nearbzg_b0 : 0 < q2nearbzgBd.getD 0 0 := by decide +kernel
theorem q2nearbzg_bN : q2nearbzgBd.getD 4 0 ≤ q2nearbzgHi := by decide +kernel
theorem q2nearbzg_bmid : q2nearbzgBd.getD 4 0 = q2nearbzBd.getD 0 0 := by decide +kernel
theorem q2nearbzg_dom0 : q2nearbzgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q2nearbz_domN : q2nearbzBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q2nearbzgCells : ∀ x ∈ Icc ((q2nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearbzgFq (poleF q2nearbzgFq.poles) 0 x ≤ (q2nearbzgT : ℝ) :=
  cover_union (cover_union (cover_union (q2nearbzgB000Bound) q2nearbzgB001Bound) q2nearbzgB002Bound) q2nearbzgB003Bound
theorem q2nearbzgSer : ∀ x ∈ Icc ((q2nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearbzFq (poleF q2nearbzFq.poles) 0 x + lfieldTower q2nearbzTsM 0 x ≤ (q2nearbzT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2nearbzgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2nearbzg_b0
  have hN : ((q2nearbzgBd.getD 4 0 : ℚ) : ℝ) ≤ (q2nearbzgHi : ℝ) := by exact_mod_cast q2nearbzg_bN
  have h := l0_series_sound q2nearbzFq q2nearbzgFq q2nearbzTsM q2nearbzgHi q2nearbzgN q2nearbzgDelta q2nearbzgT q2nearbzg_laurent q2nearbzg_cL q2nearbzg_plogs q2nearbzg_poles q2nearbzg_hD
    (Set.Icc ((q2nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbzgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2nearbzgCells y hy) x hx
  have hq : ((q2nearbzgT + q2nearbzgDelta + l0Err q2nearbzgHi q2nearbzgN q2nearbzTsM : ℚ) : ℝ) ≤ (q2nearbzT : ℝ) := by exact_mod_cast q2nearbzg_tot
  exact h.trans hq

theorem q2nearbzLaurentM : ∀ x ∈ Icc ((q2nearbzBd.getD 0 0 : ℚ) : ℝ) ((q2nearbzBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearbzFq (poleF q2nearbzFq.poles) 0 x + lfieldTower q2nearbzTsM 0 x ≤ (q2nearbzT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearbzB000Bound) q2nearbzB001Bound) q2nearbzB002Bound) q2nearbzB003Bound) q2nearbzB004Bound) q2nearbzB005Bound) q2nearbzB006Bound) q2nearbzB007Bound) q2nearbzB008Bound) q2nearbzB009Bound
/-- **NEAR**, trial 2, corner 1/16: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q2nearbzSup : ∀ x ∈ Icc ((q2nearbzgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbzBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearbzFq (poleF q2nearbzFq.poles) 0 x + lfieldTower q2nearbzTs 0 x ≤ (q2nearbzT : ℝ) := by
  intro x hx
  have hb : ((q2nearbzgBd.getD 4 0 : ℚ) : ℝ) = ((q2nearbzBd.getD 0 0 : ℚ) : ℝ) := by rw [q2nearbzg_bmid]
  have h1 := q2nearbzgSer
  rw [hb] at h1
  have h := cover_union h1 q2nearbzLaurentM x hx
  rw [q2nearbzTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
