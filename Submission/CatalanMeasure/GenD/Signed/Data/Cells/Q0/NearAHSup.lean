module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearAHTB002

@[expose] public section

/-! **NEAR, trial 0, corner 1/200: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q0nearahtSupM : ∀ x ∈ Icc ((q0nearahtBd.getD 0 0 : ℚ) : ℝ) ((q0nearahtBd.getD 1 0 : ℚ) : ℝ), fieldTower q0nearahtFq (poleF q0nearahtFq.poles) 0 x + lfieldTower q0nearahTsM 0 x ≤ (q0nearahtT : ℝ) :=
  q0nearahtB000Bound
theorem q0nearahtSup : ∀ x ∈ Icc ((q0nearahtBd.getD 0 0 : ℚ) : ℝ) ((q0nearahtBd.getD 1 0 : ℚ) : ℝ), fieldTower q0nearahtFq (poleF q0nearahtFq.poles) 0 x + lfieldTower q0nearahTs 0 x ≤ (q0nearahtT : ℝ) := by
  intro x hx
  have h := q0nearahtSupM x hx
  rw [q0nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q0nearahtSupJM : ∀ x ∈ Icc ((q0nearahtBd.getD 1 0 : ℚ) : ℝ) ((q0nearahtBd.getD 12 0 : ℚ) : ℝ), fieldTower q0nearahtFq (poleF q0nearahtFq.poles) 0 x + lfieldTower q0nearahTsM 0 x ≤ (q0nearahtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0nearahtB001Bound) q0nearahtB002Bound) q0nearahtB003Bound) q0nearahtB004Bound) q0nearahtB005Bound) q0nearahtB006Bound) q0nearahtB007Bound) q0nearahtB008Bound) q0nearahtB009Bound) q0nearahtB010Bound) q0nearahtB011Bound
theorem q0nearahtSupJ : ∀ x ∈ Icc ((q0nearahtBd.getD 1 0 : ℚ) : ℝ) ((q0nearahtBd.getD 12 0 : ℚ) : ℝ), fieldTower q0nearahtFq (poleF q0nearahtFq.poles) 0 x + lfieldTower q0nearahTs 0 x ≤ (q0nearahtTJ : ℝ) := by
  intro x hx
  have h := q0nearahtSupJM x hx
  rw [q0nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

def q0nearahgN : ℕ := 72
def q0nearahgHi : ℚ := qmk (3) 5 0 1
def q0nearahgDelta : ℚ := dy3 (1) 0 69
theorem q0nearahg_laurent : l0OK q0nearahTsM q0nearahgHi q0nearahgN = true := by decide +kernel
theorem q0nearahg_cL : l0C q0nearahTsM = 0 := by decide +kernel
theorem q0nearahg_plogs : q0nearahgFq.plogs = q0nearahFq.plogs := by decide +kernel
theorem q0nearahg_poles : q0nearahgFq.poles = q0nearahFq.poles := by decide +kernel
theorem q0nearahg_hD : polyAB (vecAdd (vecAdd q0nearahFq.poly (l0P q0nearahTsM q0nearahgN)) (q0nearahgPoly.map (fun t => (-1 : ℚ) * t))) 0 q0nearahgHi ≤ q0nearahgDelta := by decide +kernel
theorem q0nearahg_tot : q0nearahgT + q0nearahgDelta + l0Err q0nearahgHi q0nearahgN q0nearahTsM ≤ q0nearahT := by decide +kernel
theorem q0nearahg_b0 : 0 < q0nearahgBd.getD 0 0 := by decide +kernel
theorem q0nearahg_bN : q0nearahgBd.getD 4 0 ≤ q0nearahgHi := by decide +kernel
theorem q0nearahg_bmid : q0nearahgBd.getD 4 0 = q0nearahBd.getD 0 0 := by decide +kernel
theorem q0nearahg_dom0 : q0nearahgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q0nearah_domN : q0nearahBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q0nearahgCells : ∀ x ∈ Icc ((q0nearahgBd.getD 0 0 : ℚ) : ℝ) ((q0nearahgBd.getD 4 0 : ℚ) : ℝ), fieldTower q0nearahgFq (poleF q0nearahgFq.poles) 0 x ≤ (q0nearahgT : ℝ) :=
  cover_union (cover_union (cover_union (q0nearahgB000Bound) q0nearahgB001Bound) q0nearahgB002Bound) q0nearahgB003Bound
theorem q0nearahgSer : ∀ x ∈ Icc ((q0nearahgBd.getD 0 0 : ℚ) : ℝ) ((q0nearahgBd.getD 4 0 : ℚ) : ℝ), fieldTower q0nearahFq (poleF q0nearahFq.poles) 0 x + lfieldTower q0nearahTsM 0 x ≤ (q0nearahT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q0nearahgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q0nearahg_b0
  have hN : ((q0nearahgBd.getD 4 0 : ℚ) : ℝ) ≤ (q0nearahgHi : ℝ) := by exact_mod_cast q0nearahg_bN
  have h := l0_series_sound q0nearahFq q0nearahgFq q0nearahTsM q0nearahgHi q0nearahgN q0nearahgDelta q0nearahgT q0nearahg_laurent q0nearahg_cL q0nearahg_plogs q0nearahg_poles q0nearahg_hD
    (Set.Icc ((q0nearahgBd.getD 0 0 : ℚ) : ℝ) ((q0nearahgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q0nearahgCells y hy) x hx
  have hq : ((q0nearahgT + q0nearahgDelta + l0Err q0nearahgHi q0nearahgN q0nearahTsM : ℚ) : ℝ) ≤ (q0nearahT : ℝ) := by exact_mod_cast q0nearahg_tot
  exact h.trans hq

theorem q0nearahLaurentM : ∀ x ∈ Icc ((q0nearahBd.getD 0 0 : ℚ) : ℝ) ((q0nearahBd.getD 10 0 : ℚ) : ℝ), fieldTower q0nearahFq (poleF q0nearahFq.poles) 0 x + lfieldTower q0nearahTsM 0 x ≤ (q0nearahT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0nearahB000Bound) q0nearahB001Bound) q0nearahB002Bound) q0nearahB003Bound) q0nearahB004Bound) q0nearahB005Bound) q0nearahB006Bound) q0nearahB007Bound) q0nearahB008Bound) q0nearahB009Bound
/-- **NEAR**, trial 0, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q0nearahSup : ∀ x ∈ Icc ((q0nearahgBd.getD 0 0 : ℚ) : ℝ) ((q0nearahBd.getD 10 0 : ℚ) : ℝ), fieldTower q0nearahFq (poleF q0nearahFq.poles) 0 x + lfieldTower q0nearahTs 0 x ≤ (q0nearahT : ℝ) := by
  intro x hx
  have hb : ((q0nearahgBd.getD 4 0 : ℚ) : ℝ) = ((q0nearahBd.getD 0 0 : ℚ) : ℝ) := by rw [q0nearahg_bmid]
  have h1 := q0nearahgSer
  rw [hb] at h1
  have h := cover_union h1 q0nearahLaurentM x hx
  rw [q0nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
