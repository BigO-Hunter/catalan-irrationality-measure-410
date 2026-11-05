module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearBHTB002

@[expose] public section

/-! **NEAR, trial 2, corner 1/16: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q2nearbhtSupM : ∀ x ∈ Icc ((q2nearbhtBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhtBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearbhtFq (poleF q2nearbhtFq.poles) 0 x + lfieldTower q2nearbhTsM 0 x ≤ (q2nearbhtT : ℝ) :=
  q2nearbhtB000Bound
theorem q2nearbhtSup : ∀ x ∈ Icc ((q2nearbhtBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhtBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearbhtFq (poleF q2nearbhtFq.poles) 0 x + lfieldTower q2nearbhTs 0 x ≤ (q2nearbhtT : ℝ) := by
  intro x hx
  have h := q2nearbhtSupM x hx
  rw [q2nearbhTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q2nearbhtSupJM : ∀ x ∈ Icc ((q2nearbhtBd.getD 1 0 : ℚ) : ℝ) ((q2nearbhtBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearbhtFq (poleF q2nearbhtFq.poles) 0 x + lfieldTower q2nearbhTsM 0 x ≤ (q2nearbhtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearbhtB001Bound) q2nearbhtB002Bound) q2nearbhtB003Bound) q2nearbhtB004Bound) q2nearbhtB005Bound) q2nearbhtB006Bound) q2nearbhtB007Bound) q2nearbhtB008Bound) q2nearbhtB009Bound) q2nearbhtB010Bound) q2nearbhtB011Bound
theorem q2nearbhtSupJ : ∀ x ∈ Icc ((q2nearbhtBd.getD 1 0 : ℚ) : ℝ) ((q2nearbhtBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearbhtFq (poleF q2nearbhtFq.poles) 0 x + lfieldTower q2nearbhTs 0 x ≤ (q2nearbhtTJ : ℝ) := by
  intro x hx
  have h := q2nearbhtSupJM x hx
  rw [q2nearbhTsM_eq, lfieldTower_mergeL] at h
  exact h

def q2nearbhgN : ℕ := 72
def q2nearbhgHi : ℚ := qmk (3) 5 0 1
def q2nearbhgDelta : ℚ := dy3 (1) 0 69
theorem q2nearbhg_laurent : l0OK q2nearbhTsM q2nearbhgHi q2nearbhgN = true := by decide +kernel
theorem q2nearbhg_cL : l0C q2nearbhTsM = 0 := by decide +kernel
theorem q2nearbhg_plogs : q2nearbhgFq.plogs = q2nearbhFq.plogs := by decide +kernel
theorem q2nearbhg_poles : q2nearbhgFq.poles = q2nearbhFq.poles := by decide +kernel
theorem q2nearbhg_hD : polyAB (vecAdd (vecAdd q2nearbhFq.poly (l0P q2nearbhTsM q2nearbhgN)) (q2nearbhgPoly.map (fun t => (-1 : ℚ) * t))) 0 q2nearbhgHi ≤ q2nearbhgDelta := by decide +kernel
theorem q2nearbhg_tot : q2nearbhgT + q2nearbhgDelta + l0Err q2nearbhgHi q2nearbhgN q2nearbhTsM ≤ q2nearbhT := by decide +kernel
theorem q2nearbhg_b0 : 0 < q2nearbhgBd.getD 0 0 := by decide +kernel
theorem q2nearbhg_bN : q2nearbhgBd.getD 4 0 ≤ q2nearbhgHi := by decide +kernel
theorem q2nearbhg_bmid : q2nearbhgBd.getD 4 0 = q2nearbhBd.getD 0 0 := by decide +kernel
theorem q2nearbhg_dom0 : q2nearbhgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q2nearbh_domN : q2nearbhBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q2nearbhgCells : ∀ x ∈ Icc ((q2nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearbhgFq (poleF q2nearbhgFq.poles) 0 x ≤ (q2nearbhgT : ℝ) :=
  cover_union (cover_union (cover_union (q2nearbhgB000Bound) q2nearbhgB001Bound) q2nearbhgB002Bound) q2nearbhgB003Bound
theorem q2nearbhgSer : ∀ x ∈ Icc ((q2nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearbhFq (poleF q2nearbhFq.poles) 0 x + lfieldTower q2nearbhTsM 0 x ≤ (q2nearbhT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2nearbhgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2nearbhg_b0
  have hN : ((q2nearbhgBd.getD 4 0 : ℚ) : ℝ) ≤ (q2nearbhgHi : ℝ) := by exact_mod_cast q2nearbhg_bN
  have h := l0_series_sound q2nearbhFq q2nearbhgFq q2nearbhTsM q2nearbhgHi q2nearbhgN q2nearbhgDelta q2nearbhgT q2nearbhg_laurent q2nearbhg_cL q2nearbhg_plogs q2nearbhg_poles q2nearbhg_hD
    (Set.Icc ((q2nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2nearbhgCells y hy) x hx
  have hq : ((q2nearbhgT + q2nearbhgDelta + l0Err q2nearbhgHi q2nearbhgN q2nearbhTsM : ℚ) : ℝ) ≤ (q2nearbhT : ℝ) := by exact_mod_cast q2nearbhg_tot
  exact h.trans hq

theorem q2nearbhLaurentM : ∀ x ∈ Icc ((q2nearbhBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearbhFq (poleF q2nearbhFq.poles) 0 x + lfieldTower q2nearbhTsM 0 x ≤ (q2nearbhT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearbhB000Bound) q2nearbhB001Bound) q2nearbhB002Bound) q2nearbhB003Bound) q2nearbhB004Bound) q2nearbhB005Bound) q2nearbhB006Bound) q2nearbhB007Bound) q2nearbhB008Bound) q2nearbhB009Bound
/-- **NEAR**, trial 2, corner 1/16: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q2nearbhSup : ∀ x ∈ Icc ((q2nearbhgBd.getD 0 0 : ℚ) : ℝ) ((q2nearbhBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearbhFq (poleF q2nearbhFq.poles) 0 x + lfieldTower q2nearbhTs 0 x ≤ (q2nearbhT : ℝ) := by
  intro x hx
  have hb : ((q2nearbhgBd.getD 4 0 : ℚ) : ℝ) = ((q2nearbhBd.getD 0 0 : ℚ) : ℝ) := by rw [q2nearbhg_bmid]
  have h1 := q2nearbhgSer
  rw [hb] at h1
  have h := cover_union h1 q2nearbhLaurentM x hx
  rw [q2nearbhTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
