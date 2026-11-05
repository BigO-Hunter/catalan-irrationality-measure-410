module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.NearZZTB002

@[expose] public section

/-! **NEAR, trial 0, corner 0: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q0nearzztSupM : ∀ x ∈ Icc ((q0nearzztBd.getD 0 0 : ℚ) : ℝ) ((q0nearzztBd.getD 1 0 : ℚ) : ℝ), fieldTower q0nearzztFq (poleF q0nearzztFq.poles) 0 x + lfieldTower q0nearzzTsM 0 x ≤ (q0nearzztT : ℝ) :=
  q0nearzztB000Bound
theorem q0nearzztSup : ∀ x ∈ Icc ((q0nearzztBd.getD 0 0 : ℚ) : ℝ) ((q0nearzztBd.getD 1 0 : ℚ) : ℝ), fieldTower q0nearzztFq (poleF q0nearzztFq.poles) 0 x + lfieldTower q0nearzzTs 0 x ≤ (q0nearzztT : ℝ) := by
  intro x hx
  have h := q0nearzztSupM x hx
  rw [q0nearzzTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q0nearzztSupJM : ∀ x ∈ Icc ((q0nearzztBd.getD 1 0 : ℚ) : ℝ) ((q0nearzztBd.getD 12 0 : ℚ) : ℝ), fieldTower q0nearzztFq (poleF q0nearzztFq.poles) 0 x + lfieldTower q0nearzzTsM 0 x ≤ (q0nearzztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0nearzztB001Bound) q0nearzztB002Bound) q0nearzztB003Bound) q0nearzztB004Bound) q0nearzztB005Bound) q0nearzztB006Bound) q0nearzztB007Bound) q0nearzztB008Bound) q0nearzztB009Bound) q0nearzztB010Bound) q0nearzztB011Bound
theorem q0nearzztSupJ : ∀ x ∈ Icc ((q0nearzztBd.getD 1 0 : ℚ) : ℝ) ((q0nearzztBd.getD 12 0 : ℚ) : ℝ), fieldTower q0nearzztFq (poleF q0nearzztFq.poles) 0 x + lfieldTower q0nearzzTs 0 x ≤ (q0nearzztTJ : ℝ) := by
  intro x hx
  have h := q0nearzztSupJM x hx
  rw [q0nearzzTsM_eq, lfieldTower_mergeL] at h
  exact h

def q0nearzzgN : ℕ := 72
def q0nearzzgHi : ℚ := qmk (3) 5 0 1
def q0nearzzgDelta : ℚ := dy3 (1) 0 69
theorem q0nearzzg_laurent : l0OK q0nearzzTsM q0nearzzgHi q0nearzzgN = true := by decide +kernel
theorem q0nearzzg_cL : l0C q0nearzzTsM = 0 := by decide +kernel
theorem q0nearzzg_plogs : q0nearzzgFq.plogs = q0nearzzFq.plogs := by decide +kernel
theorem q0nearzzg_poles : q0nearzzgFq.poles = q0nearzzFq.poles := by decide +kernel
theorem q0nearzzg_hD : polyAB (vecAdd (vecAdd q0nearzzFq.poly (l0P q0nearzzTsM q0nearzzgN)) (q0nearzzgPoly.map (fun t => (-1 : ℚ) * t))) 0 q0nearzzgHi ≤ q0nearzzgDelta := by decide +kernel
theorem q0nearzzg_tot : q0nearzzgT + q0nearzzgDelta + l0Err q0nearzzgHi q0nearzzgN q0nearzzTsM ≤ q0nearzzT := by decide +kernel
theorem q0nearzzg_b0 : 0 < q0nearzzgBd.getD 0 0 := by decide +kernel
theorem q0nearzzg_bN : q0nearzzgBd.getD 4 0 ≤ q0nearzzgHi := by decide +kernel
theorem q0nearzzg_bmid : q0nearzzgBd.getD 4 0 = q0nearzzBd.getD 0 0 := by decide +kernel
theorem q0nearzzg_dom0 : q0nearzzgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q0nearzz_domN : q0nearzzBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q0nearzzgCells : ∀ x ∈ Icc ((q0nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q0nearzzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q0nearzzgFq (poleF q0nearzzgFq.poles) 0 x ≤ (q0nearzzgT : ℝ) :=
  cover_union (cover_union (cover_union (q0nearzzgB000Bound) q0nearzzgB001Bound) q0nearzzgB002Bound) q0nearzzgB003Bound
theorem q0nearzzgSer : ∀ x ∈ Icc ((q0nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q0nearzzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q0nearzzFq (poleF q0nearzzFq.poles) 0 x + lfieldTower q0nearzzTsM 0 x ≤ (q0nearzzT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q0nearzzgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q0nearzzg_b0
  have hN : ((q0nearzzgBd.getD 4 0 : ℚ) : ℝ) ≤ (q0nearzzgHi : ℝ) := by exact_mod_cast q0nearzzg_bN
  have h := l0_series_sound q0nearzzFq q0nearzzgFq q0nearzzTsM q0nearzzgHi q0nearzzgN q0nearzzgDelta q0nearzzgT q0nearzzg_laurent q0nearzzg_cL q0nearzzg_plogs q0nearzzg_poles q0nearzzg_hD
    (Set.Icc ((q0nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q0nearzzgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q0nearzzgCells y hy) x hx
  have hq : ((q0nearzzgT + q0nearzzgDelta + l0Err q0nearzzgHi q0nearzzgN q0nearzzTsM : ℚ) : ℝ) ≤ (q0nearzzT : ℝ) := by exact_mod_cast q0nearzzg_tot
  exact h.trans hq

theorem q0nearzzLaurentM : ∀ x ∈ Icc ((q0nearzzBd.getD 0 0 : ℚ) : ℝ) ((q0nearzzBd.getD 10 0 : ℚ) : ℝ), fieldTower q0nearzzFq (poleF q0nearzzFq.poles) 0 x + lfieldTower q0nearzzTsM 0 x ≤ (q0nearzzT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0nearzzB000Bound) q0nearzzB001Bound) q0nearzzB002Bound) q0nearzzB003Bound) q0nearzzB004Bound) q0nearzzB005Bound) q0nearzzB006Bound) q0nearzzB007Bound) q0nearzzB008Bound) q0nearzzB009Bound
/-- **NEAR**, trial 0, corner 0: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q0nearzzSup : ∀ x ∈ Icc ((q0nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q0nearzzBd.getD 10 0 : ℚ) : ℝ), fieldTower q0nearzzFq (poleF q0nearzzFq.poles) 0 x + lfieldTower q0nearzzTs 0 x ≤ (q0nearzzT : ℝ) := by
  intro x hx
  have hb : ((q0nearzzgBd.getD 4 0 : ℚ) : ℝ) = ((q0nearzzBd.getD 0 0 : ℚ) : ℝ) := by rw [q0nearzzg_bmid]
  have h1 := q0nearzzgSer
  rw [hb] at h1
  have h := cover_union h1 q0nearzzLaurentM x hx
  rw [q0nearzzTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
