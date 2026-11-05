module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearAHTB002

@[expose] public section

/-! **NEAR, trial 1, corner 1/200: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1nearahtSupM : ∀ x ∈ Icc ((q1nearahtBd.getD 0 0 : ℚ) : ℝ) ((q1nearahtBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearahtFq (poleF q1nearahtFq.poles) 0 x + lfieldTower q1nearahTsM 0 x ≤ (q1nearahtT : ℝ) :=
  q1nearahtB000Bound
theorem q1nearahtSup : ∀ x ∈ Icc ((q1nearahtBd.getD 0 0 : ℚ) : ℝ) ((q1nearahtBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearahtFq (poleF q1nearahtFq.poles) 0 x + lfieldTower q1nearahTs 0 x ≤ (q1nearahtT : ℝ) := by
  intro x hx
  have h := q1nearahtSupM x hx
  rw [q1nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q1nearahtSupJM : ∀ x ∈ Icc ((q1nearahtBd.getD 1 0 : ℚ) : ℝ) ((q1nearahtBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearahtFq (poleF q1nearahtFq.poles) 0 x + lfieldTower q1nearahTsM 0 x ≤ (q1nearahtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearahtB001Bound) q1nearahtB002Bound) q1nearahtB003Bound) q1nearahtB004Bound) q1nearahtB005Bound) q1nearahtB006Bound) q1nearahtB007Bound) q1nearahtB008Bound) q1nearahtB009Bound) q1nearahtB010Bound) q1nearahtB011Bound
theorem q1nearahtSupJ : ∀ x ∈ Icc ((q1nearahtBd.getD 1 0 : ℚ) : ℝ) ((q1nearahtBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearahtFq (poleF q1nearahtFq.poles) 0 x + lfieldTower q1nearahTs 0 x ≤ (q1nearahtTJ : ℝ) := by
  intro x hx
  have h := q1nearahtSupJM x hx
  rw [q1nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

def q1nearahgN : ℕ := 72
def q1nearahgHi : ℚ := qmk (3) 5 0 1
def q1nearahgDelta : ℚ := dy3 (1) 0 69
theorem q1nearahg_laurent : l0OK q1nearahTsM q1nearahgHi q1nearahgN = true := by decide +kernel
theorem q1nearahg_cL : l0C q1nearahTsM = 0 := by decide +kernel
theorem q1nearahg_plogs : q1nearahgFq.plogs = q1nearahFq.plogs := by decide +kernel
theorem q1nearahg_poles : q1nearahgFq.poles = q1nearahFq.poles := by decide +kernel
theorem q1nearahg_hD : polyAB (vecAdd (vecAdd q1nearahFq.poly (l0P q1nearahTsM q1nearahgN)) (q1nearahgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1nearahgHi ≤ q1nearahgDelta := by decide +kernel
theorem q1nearahg_tot : q1nearahgT + q1nearahgDelta + l0Err q1nearahgHi q1nearahgN q1nearahTsM ≤ q1nearahT := by decide +kernel
theorem q1nearahg_b0 : 0 < q1nearahgBd.getD 0 0 := by decide +kernel
theorem q1nearahg_bN : q1nearahgBd.getD 4 0 ≤ q1nearahgHi := by decide +kernel
theorem q1nearahg_bmid : q1nearahgBd.getD 4 0 = q1nearahBd.getD 0 0 := by decide +kernel
theorem q1nearahg_dom0 : q1nearahgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1nearah_domN : q1nearahBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q1nearahgCells : ∀ x ∈ Icc ((q1nearahgBd.getD 0 0 : ℚ) : ℝ) ((q1nearahgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearahgFq (poleF q1nearahgFq.poles) 0 x ≤ (q1nearahgT : ℝ) :=
  cover_union (cover_union (cover_union (q1nearahgB000Bound) q1nearahgB001Bound) q1nearahgB002Bound) q1nearahgB003Bound
theorem q1nearahgSer : ∀ x ∈ Icc ((q1nearahgBd.getD 0 0 : ℚ) : ℝ) ((q1nearahgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearahFq (poleF q1nearahFq.poles) 0 x + lfieldTower q1nearahTsM 0 x ≤ (q1nearahT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1nearahgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1nearahg_b0
  have hN : ((q1nearahgBd.getD 4 0 : ℚ) : ℝ) ≤ (q1nearahgHi : ℝ) := by exact_mod_cast q1nearahg_bN
  have h := l0_series_sound q1nearahFq q1nearahgFq q1nearahTsM q1nearahgHi q1nearahgN q1nearahgDelta q1nearahgT q1nearahg_laurent q1nearahg_cL q1nearahg_plogs q1nearahg_poles q1nearahg_hD
    (Set.Icc ((q1nearahgBd.getD 0 0 : ℚ) : ℝ) ((q1nearahgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1nearahgCells y hy) x hx
  have hq : ((q1nearahgT + q1nearahgDelta + l0Err q1nearahgHi q1nearahgN q1nearahTsM : ℚ) : ℝ) ≤ (q1nearahT : ℝ) := by exact_mod_cast q1nearahg_tot
  exact h.trans hq

theorem q1nearahLaurentM : ∀ x ∈ Icc ((q1nearahBd.getD 0 0 : ℚ) : ℝ) ((q1nearahBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearahFq (poleF q1nearahFq.poles) 0 x + lfieldTower q1nearahTsM 0 x ≤ (q1nearahT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearahB000Bound) q1nearahB001Bound) q1nearahB002Bound) q1nearahB003Bound) q1nearahB004Bound) q1nearahB005Bound) q1nearahB006Bound) q1nearahB007Bound) q1nearahB008Bound) q1nearahB009Bound
/-- **NEAR**, trial 1, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1nearahSup : ∀ x ∈ Icc ((q1nearahgBd.getD 0 0 : ℚ) : ℝ) ((q1nearahBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearahFq (poleF q1nearahFq.poles) 0 x + lfieldTower q1nearahTs 0 x ≤ (q1nearahT : ℝ) := by
  intro x hx
  have hb : ((q1nearahgBd.getD 4 0 : ℚ) : ℝ) = ((q1nearahBd.getD 0 0 : ℚ) : ℝ) := by rw [q1nearahg_bmid]
  have h1 := q1nearahgSer
  rw [hb] at h1
  have h := cover_union h1 q1nearahLaurentM x hx
  rw [q1nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
