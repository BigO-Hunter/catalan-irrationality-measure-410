module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearBHTB002

@[expose] public section

/-! **NEAR, trial 1, corner 1/16: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1nearbhtSupM : ∀ x ∈ Icc ((q1nearbhtBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhtBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearbhtFq (poleF q1nearbhtFq.poles) 0 x + lfieldTower q1nearbhTsM 0 x ≤ (q1nearbhtT : ℝ) :=
  q1nearbhtB000Bound
theorem q1nearbhtSup : ∀ x ∈ Icc ((q1nearbhtBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhtBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearbhtFq (poleF q1nearbhtFq.poles) 0 x + lfieldTower q1nearbhTs 0 x ≤ (q1nearbhtT : ℝ) := by
  intro x hx
  have h := q1nearbhtSupM x hx
  rw [q1nearbhTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q1nearbhtSupJM : ∀ x ∈ Icc ((q1nearbhtBd.getD 1 0 : ℚ) : ℝ) ((q1nearbhtBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearbhtFq (poleF q1nearbhtFq.poles) 0 x + lfieldTower q1nearbhTsM 0 x ≤ (q1nearbhtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearbhtB001Bound) q1nearbhtB002Bound) q1nearbhtB003Bound) q1nearbhtB004Bound) q1nearbhtB005Bound) q1nearbhtB006Bound) q1nearbhtB007Bound) q1nearbhtB008Bound) q1nearbhtB009Bound) q1nearbhtB010Bound) q1nearbhtB011Bound
theorem q1nearbhtSupJ : ∀ x ∈ Icc ((q1nearbhtBd.getD 1 0 : ℚ) : ℝ) ((q1nearbhtBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearbhtFq (poleF q1nearbhtFq.poles) 0 x + lfieldTower q1nearbhTs 0 x ≤ (q1nearbhtTJ : ℝ) := by
  intro x hx
  have h := q1nearbhtSupJM x hx
  rw [q1nearbhTsM_eq, lfieldTower_mergeL] at h
  exact h

def q1nearbhgN : ℕ := 72
def q1nearbhgHi : ℚ := qmk (3) 5 0 1
def q1nearbhgDelta : ℚ := dy3 (1) 0 69
theorem q1nearbhg_laurent : l0OK q1nearbhTsM q1nearbhgHi q1nearbhgN = true := by decide +kernel
theorem q1nearbhg_cL : l0C q1nearbhTsM = 0 := by decide +kernel
theorem q1nearbhg_plogs : q1nearbhgFq.plogs = q1nearbhFq.plogs := by decide +kernel
theorem q1nearbhg_poles : q1nearbhgFq.poles = q1nearbhFq.poles := by decide +kernel
theorem q1nearbhg_hD : polyAB (vecAdd (vecAdd q1nearbhFq.poly (l0P q1nearbhTsM q1nearbhgN)) (q1nearbhgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1nearbhgHi ≤ q1nearbhgDelta := by decide +kernel
theorem q1nearbhg_tot : q1nearbhgT + q1nearbhgDelta + l0Err q1nearbhgHi q1nearbhgN q1nearbhTsM ≤ q1nearbhT := by decide +kernel
theorem q1nearbhg_b0 : 0 < q1nearbhgBd.getD 0 0 := by decide +kernel
theorem q1nearbhg_bN : q1nearbhgBd.getD 4 0 ≤ q1nearbhgHi := by decide +kernel
theorem q1nearbhg_bmid : q1nearbhgBd.getD 4 0 = q1nearbhBd.getD 0 0 := by decide +kernel
theorem q1nearbhg_dom0 : q1nearbhgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1nearbh_domN : q1nearbhBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q1nearbhgCells : ∀ x ∈ Icc ((q1nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearbhgFq (poleF q1nearbhgFq.poles) 0 x ≤ (q1nearbhgT : ℝ) :=
  cover_union (cover_union (cover_union (q1nearbhgB000Bound) q1nearbhgB001Bound) q1nearbhgB002Bound) q1nearbhgB003Bound
theorem q1nearbhgSer : ∀ x ∈ Icc ((q1nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearbhFq (poleF q1nearbhFq.poles) 0 x + lfieldTower q1nearbhTsM 0 x ≤ (q1nearbhT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1nearbhgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1nearbhg_b0
  have hN : ((q1nearbhgBd.getD 4 0 : ℚ) : ℝ) ≤ (q1nearbhgHi : ℝ) := by exact_mod_cast q1nearbhg_bN
  have h := l0_series_sound q1nearbhFq q1nearbhgFq q1nearbhTsM q1nearbhgHi q1nearbhgN q1nearbhgDelta q1nearbhgT q1nearbhg_laurent q1nearbhg_cL q1nearbhg_plogs q1nearbhg_poles q1nearbhg_hD
    (Set.Icc ((q1nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1nearbhgCells y hy) x hx
  have hq : ((q1nearbhgT + q1nearbhgDelta + l0Err q1nearbhgHi q1nearbhgN q1nearbhTsM : ℚ) : ℝ) ≤ (q1nearbhT : ℝ) := by exact_mod_cast q1nearbhg_tot
  exact h.trans hq

theorem q1nearbhLaurentM : ∀ x ∈ Icc ((q1nearbhBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearbhFq (poleF q1nearbhFq.poles) 0 x + lfieldTower q1nearbhTsM 0 x ≤ (q1nearbhT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearbhB000Bound) q1nearbhB001Bound) q1nearbhB002Bound) q1nearbhB003Bound) q1nearbhB004Bound) q1nearbhB005Bound) q1nearbhB006Bound) q1nearbhB007Bound) q1nearbhB008Bound) q1nearbhB009Bound
/-- **NEAR**, trial 1, corner 1/16: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1nearbhSup : ∀ x ∈ Icc ((q1nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q1nearbhBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearbhFq (poleF q1nearbhFq.poles) 0 x + lfieldTower q1nearbhTs 0 x ≤ (q1nearbhT : ℝ) := by
  intro x hx
  have hb : ((q1nearbhgBd.getD 4 0 : ℚ) : ℝ) = ((q1nearbhBd.getD 0 0 : ℚ) : ℝ) := by rw [q1nearbhg_bmid]
  have h1 := q1nearbhgSer
  rw [hb] at h1
  have h := cover_union h1 q1nearbhLaurentM x hx
  rw [q1nearbhTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
