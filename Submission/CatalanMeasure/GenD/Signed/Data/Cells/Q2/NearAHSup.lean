module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.NearAHTB002

@[expose] public section

/-! **NEAR, trial 2, corner 1/200: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q2nearahtSupM : ∀ x ∈ Icc ((q2nearahtBd.getD 0 0 : ℚ) : ℝ) ((q2nearahtBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearahtFq (poleF q2nearahtFq.poles) 0 x + lfieldTower q2nearahTsM 0 x ≤ (q2nearahtT : ℝ) :=
  q2nearahtB000Bound
theorem q2nearahtSup : ∀ x ∈ Icc ((q2nearahtBd.getD 0 0 : ℚ) : ℝ) ((q2nearahtBd.getD 1 0 : ℚ) : ℝ), fieldTower q2nearahtFq (poleF q2nearahtFq.poles) 0 x + lfieldTower q2nearahTs 0 x ≤ (q2nearahtT : ℝ) := by
  intro x hx
  have h := q2nearahtSupM x hx
  rw [q2nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q2nearahtSupJM : ∀ x ∈ Icc ((q2nearahtBd.getD 1 0 : ℚ) : ℝ) ((q2nearahtBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearahtFq (poleF q2nearahtFq.poles) 0 x + lfieldTower q2nearahTsM 0 x ≤ (q2nearahtTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearahtB001Bound) q2nearahtB002Bound) q2nearahtB003Bound) q2nearahtB004Bound) q2nearahtB005Bound) q2nearahtB006Bound) q2nearahtB007Bound) q2nearahtB008Bound) q2nearahtB009Bound) q2nearahtB010Bound) q2nearahtB011Bound
theorem q2nearahtSupJ : ∀ x ∈ Icc ((q2nearahtBd.getD 1 0 : ℚ) : ℝ) ((q2nearahtBd.getD 12 0 : ℚ) : ℝ), fieldTower q2nearahtFq (poleF q2nearahtFq.poles) 0 x + lfieldTower q2nearahTs 0 x ≤ (q2nearahtTJ : ℝ) := by
  intro x hx
  have h := q2nearahtSupJM x hx
  rw [q2nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

def q2nearahgN : ℕ := 72
def q2nearahgHi : ℚ := qmk (3) 5 0 1
def q2nearahgDelta : ℚ := dy3 (1) 0 69
theorem q2nearahg_laurent : l0OK q2nearahTsM q2nearahgHi q2nearahgN = true := by decide +kernel
theorem q2nearahg_cL : l0C q2nearahTsM = 0 := by decide +kernel
theorem q2nearahg_plogs : q2nearahgFq.plogs = q2nearahFq.plogs := by decide +kernel
theorem q2nearahg_poles : q2nearahgFq.poles = q2nearahFq.poles := by decide +kernel
theorem q2nearahg_hD : polyAB (vecAdd (vecAdd q2nearahFq.poly (l0P q2nearahTsM q2nearahgN)) (q2nearahgPoly.map (fun t => (-1 : ℚ) * t))) 0 q2nearahgHi ≤ q2nearahgDelta := by decide +kernel
theorem q2nearahg_tot : q2nearahgT + q2nearahgDelta + l0Err q2nearahgHi q2nearahgN q2nearahTsM ≤ q2nearahT := by decide +kernel
theorem q2nearahg_b0 : 0 < q2nearahgBd.getD 0 0 := by decide +kernel
theorem q2nearahg_bN : q2nearahgBd.getD 4 0 ≤ q2nearahgHi := by decide +kernel
theorem q2nearahg_bmid : q2nearahgBd.getD 4 0 = q2nearahBd.getD 0 0 := by decide +kernel
theorem q2nearahg_dom0 : q2nearahgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q2nearah_domN : q2nearahBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q2nearahgCells : ∀ x ∈ Icc ((q2nearahgBd.getD 0 0 : ℚ) : ℝ) ((q2nearahgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearahgFq (poleF q2nearahgFq.poles) 0 x ≤ (q2nearahgT : ℝ) :=
  cover_union (cover_union (cover_union (q2nearahgB000Bound) q2nearahgB001Bound) q2nearahgB002Bound) q2nearahgB003Bound
theorem q2nearahgSer : ∀ x ∈ Icc ((q2nearahgBd.getD 0 0 : ℚ) : ℝ) ((q2nearahgBd.getD 4 0 : ℚ) : ℝ), fieldTower q2nearahFq (poleF q2nearahFq.poles) 0 x + lfieldTower q2nearahTsM 0 x ≤ (q2nearahT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2nearahgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2nearahg_b0
  have hN : ((q2nearahgBd.getD 4 0 : ℚ) : ℝ) ≤ (q2nearahgHi : ℝ) := by exact_mod_cast q2nearahg_bN
  have h := l0_series_sound q2nearahFq q2nearahgFq q2nearahTsM q2nearahgHi q2nearahgN q2nearahgDelta q2nearahgT q2nearahg_laurent q2nearahg_cL q2nearahg_plogs q2nearahg_poles q2nearahg_hD
    (Set.Icc ((q2nearahgBd.getD 0 0 : ℚ) : ℝ) ((q2nearahgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2nearahgCells y hy) x hx
  have hq : ((q2nearahgT + q2nearahgDelta + l0Err q2nearahgHi q2nearahgN q2nearahTsM : ℚ) : ℝ) ≤ (q2nearahT : ℝ) := by exact_mod_cast q2nearahg_tot
  exact h.trans hq

theorem q2nearahLaurentM : ∀ x ∈ Icc ((q2nearahBd.getD 0 0 : ℚ) : ℝ) ((q2nearahBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearahFq (poleF q2nearahFq.poles) 0 x + lfieldTower q2nearahTsM 0 x ≤ (q2nearahT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2nearahB000Bound) q2nearahB001Bound) q2nearahB002Bound) q2nearahB003Bound) q2nearahB004Bound) q2nearahB005Bound) q2nearahB006Bound) q2nearahB007Bound) q2nearahB008Bound) q2nearahB009Bound
/-- **NEAR**, trial 2, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q2nearahSup : ∀ x ∈ Icc ((q2nearahgBd.getD 0 0 : ℚ) : ℝ) ((q2nearahBd.getD 10 0 : ℚ) : ℝ), fieldTower q2nearahFq (poleF q2nearahFq.poles) 0 x + lfieldTower q2nearahTs 0 x ≤ (q2nearahT : ℝ) := by
  intro x hx
  have hb : ((q2nearahgBd.getD 4 0 : ℚ) : ℝ) = ((q2nearahBd.getD 0 0 : ℚ) : ℝ) := by rw [q2nearahg_bmid]
  have h1 := q2nearahgSer
  rw [hb] at h1
  have h := cover_union h1 q2nearahLaurentM x hx
  rw [q2nearahTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
