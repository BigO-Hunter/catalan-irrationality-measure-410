module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZGB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZTFq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZTB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZTB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearZZTB002

@[expose] public section

/-! **NEAR, trial 1, corner 0: sup statements** (T = S_Lean - kappa_up of thresholds410.json). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


theorem q1nearzztSupM : ∀ x ∈ Icc ((q1nearzztBd.getD 0 0 : ℚ) : ℝ) ((q1nearzztBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearzztFq (poleF q1nearzztFq.poles) 0 x + lfieldTower q1nearzzTsM 0 x ≤ (q1nearzztT : ℝ) :=
  q1nearzztB000Bound
theorem q1nearzztSup : ∀ x ∈ Icc ((q1nearzztBd.getD 0 0 : ℚ) : ℝ) ((q1nearzztBd.getD 1 0 : ℚ) : ℝ), fieldTower q1nearzztFq (poleF q1nearzztFq.poles) 0 x + lfieldTower q1nearzzTs 0 x ≤ (q1nearzztT : ℝ) := by
  intro x hx
  have h := q1nearzztSupM x hx
  rw [q1nearzzTsM_eq, lfieldTower_mergeL] at h
  exact h

theorem q1nearzztSupJM : ∀ x ∈ Icc ((q1nearzztBd.getD 1 0 : ℚ) : ℝ) ((q1nearzztBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearzztFq (poleF q1nearzztFq.poles) 0 x + lfieldTower q1nearzzTsM 0 x ≤ (q1nearzztTJ : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearzztB001Bound) q1nearzztB002Bound) q1nearzztB003Bound) q1nearzztB004Bound) q1nearzztB005Bound) q1nearzztB006Bound) q1nearzztB007Bound) q1nearzztB008Bound) q1nearzztB009Bound) q1nearzztB010Bound) q1nearzztB011Bound
theorem q1nearzztSupJ : ∀ x ∈ Icc ((q1nearzztBd.getD 1 0 : ℚ) : ℝ) ((q1nearzztBd.getD 12 0 : ℚ) : ℝ), fieldTower q1nearzztFq (poleF q1nearzztFq.poles) 0 x + lfieldTower q1nearzzTs 0 x ≤ (q1nearzztTJ : ℝ) := by
  intro x hx
  have h := q1nearzztSupJM x hx
  rw [q1nearzzTsM_eq, lfieldTower_mergeL] at h
  exact h

def q1nearzzgN : ℕ := 72
def q1nearzzgHi : ℚ := qmk (3) 5 0 1
def q1nearzzgDelta : ℚ := dy3 (1) 0 69
theorem q1nearzzg_laurent : l0OK q1nearzzTsM q1nearzzgHi q1nearzzgN = true := by decide +kernel
theorem q1nearzzg_cL : l0C q1nearzzTsM = 0 := by decide +kernel
theorem q1nearzzg_plogs : q1nearzzgFq.plogs = q1nearzzFq.plogs := by decide +kernel
theorem q1nearzzg_poles : q1nearzzgFq.poles = q1nearzzFq.poles := by decide +kernel
theorem q1nearzzg_hD : polyAB (vecAdd (vecAdd q1nearzzFq.poly (l0P q1nearzzTsM q1nearzzgN)) (q1nearzzgPoly.map (fun t => (-1 : ℚ) * t))) 0 q1nearzzgHi ≤ q1nearzzgDelta := by decide +kernel
theorem q1nearzzg_tot : q1nearzzgT + q1nearzzgDelta + l0Err q1nearzzgHi q1nearzzgN q1nearzzTsM ≤ q1nearzzT := by decide +kernel
theorem q1nearzzg_b0 : 0 < q1nearzzgBd.getD 0 0 := by decide +kernel
theorem q1nearzzg_bN : q1nearzzgBd.getD 4 0 ≤ q1nearzzgHi := by decide +kernel
theorem q1nearzzg_bmid : q1nearzzgBd.getD 4 0 = q1nearzzBd.getD 0 0 := by decide +kernel
theorem q1nearzzg_dom0 : q1nearzzgBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1nearzz_domN : q1nearzzBd.getD 10 0 = 999 / 1000 := by decide +kernel
theorem q1nearzzgCells : ∀ x ∈ Icc ((q1nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearzzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearzzgFq (poleF q1nearzzgFq.poles) 0 x ≤ (q1nearzzgT : ℝ) :=
  cover_union (cover_union (cover_union (q1nearzzgB000Bound) q1nearzzgB001Bound) q1nearzzgB002Bound) q1nearzzgB003Bound
theorem q1nearzzgSer : ∀ x ∈ Icc ((q1nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearzzgBd.getD 4 0 : ℚ) : ℝ), fieldTower q1nearzzFq (poleF q1nearzzFq.poles) 0 x + lfieldTower q1nearzzTsM 0 x ≤ (q1nearzzT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1nearzzgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1nearzzg_b0
  have hN : ((q1nearzzgBd.getD 4 0 : ℚ) : ℝ) ≤ (q1nearzzgHi : ℝ) := by exact_mod_cast q1nearzzg_bN
  have h := l0_series_sound q1nearzzFq q1nearzzgFq q1nearzzTsM q1nearzzgHi q1nearzzgN q1nearzzgDelta q1nearzzgT q1nearzzg_laurent q1nearzzg_cL q1nearzzg_plogs q1nearzzg_poles q1nearzzg_hD
    (Set.Icc ((q1nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearzzgBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1nearzzgCells y hy) x hx
  have hq : ((q1nearzzgT + q1nearzzgDelta + l0Err q1nearzzgHi q1nearzzgN q1nearzzTsM : ℚ) : ℝ) ≤ (q1nearzzT : ℝ) := by exact_mod_cast q1nearzzg_tot
  exact h.trans hq

theorem q1nearzzLaurentM : ∀ x ∈ Icc ((q1nearzzBd.getD 0 0 : ℚ) : ℝ) ((q1nearzzBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearzzFq (poleF q1nearzzFq.poles) 0 x + lfieldTower q1nearzzTsM 0 x ≤ (q1nearzzT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1nearzzB000Bound) q1nearzzB001Bound) q1nearzzB002Bound) q1nearzzB003Bound) q1nearzzB004Bound) q1nearzzB005Bound) q1nearzzB006Bound) q1nearzzB007Bound) q1nearzzB008Bound) q1nearzzB009Bound
/-- **NEAR**, trial 1, corner 0: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1nearzzSup : ∀ x ∈ Icc ((q1nearzzgBd.getD 0 0 : ℚ) : ℝ) ((q1nearzzBd.getD 10 0 : ℚ) : ℝ), fieldTower q1nearzzFq (poleF q1nearzzFq.poles) 0 x + lfieldTower q1nearzzTs 0 x ≤ (q1nearzzT : ℝ) := by
  intro x hx
  have hb : ((q1nearzzgBd.getD 4 0 : ℚ) : ℝ) = ((q1nearzzBd.getD 0 0 : ℚ) : ℝ) := by rw [q1nearzzg_bmid]
  have h1 := q1nearzzgSer
  rw [hb] at h1
  have h := cover_union h1 q1nearzzLaurentM x hx
  rw [q1nearzzTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
