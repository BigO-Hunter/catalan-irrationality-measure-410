module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpgSup
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpiEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SpGE0
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP gap (0, 3/10), trial 2: the series window `l0_series_sound` turns the Laurent-free cover `q2spgSup` of fq' into the bound for the true SP field plus the merged Laurent terms. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q2spgN : ℕ := 72
def q2spgHi : ℚ := qmk (3) 5 0 1
def q2spgDelta : ℚ := dy3 (1) 0 69
theorem q2spg_laurent : l0OK q2spiTsM q2spgHi q2spgN = true := by decide +kernel
theorem q2spg_cL : l0C q2spiTsM = 0 := by decide +kernel
theorem q2spg_plogs : q2spgFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.plogs := by decide +kernel
theorem q2spg_poles : q2spgFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.poles := by decide +kernel
theorem q2spg_hD : polyAB (vecAdd (vecAdd CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.poly (l0P q2spiTsM q2spgN)) (q2spgPoly.map (fun t => (-1 : ℚ) * t))) 0 q2spgHi ≤ q2spgDelta := by decide +kernel
theorem q2spg_tot : q2spgT + q2spgDelta + l0Err q2spgHi q2spgN q2spiTsM ≤ q2spiT := by decide +kernel
theorem q2spg_b0 : 0 < q2spgBd.getD 0 0 := by decide +kernel
theorem q2spg_b0E : q2spgBd.getD 0 0 = q2spe0Hi := by decide +kernel
theorem q2spg_bN : q2spgBd.getD 71 0 ≤ q2spgHi := by decide +kernel
theorem q2spg_bNeq : q2spgBd.getD 71 0 = 3 / 10 := by decide +kernel
theorem q2spgGapM : ∀ x ∈ Ioo ((q2spgBd.getD 0 0 : ℚ) : ℝ) ((q2spgBd.getD 71 0 : ℚ) : ℝ), fieldTower CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.poles) 0 x + lfieldTower q2spiTsM 0 x ≤ (q2spiT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q2spgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q2spg_b0
  have hN : ((q2spgBd.getD 71 0 : ℚ) : ℝ) ≤ (q2spgHi : ℝ) := by exact_mod_cast q2spg_bN
  have h := l0_series_sound CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq q2spgFq q2spiTsM q2spgHi q2spgN q2spgDelta q2spgT q2spg_laurent q2spg_cL q2spg_plogs q2spg_poles q2spg_hD
    (Set.Ioo ((q2spgBd.getD 0 0 : ℚ) : ℝ) ((q2spgBd.getD 71 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q2spgSup y hy) x hx
  have hq : ((q2spgT + q2spgDelta + l0Err q2spgHi q2spgN q2spiTsM : ℚ) : ℝ) ≤ (q2spiT : ℝ) := by exact_mod_cast q2spg_tot
  exact h.trans hq

/-- **SP gap (0, 3/10)**, trial 2: the true SP field plus the exact Laurent terms. -/
theorem q2spiGapSup : ∀ x ∈ Ioo ((q2spgBd.getD 0 0 : ℚ) : ℝ) ((q2spgBd.getD 71 0 : ℚ) : ℝ), fieldTower CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial.T2.spFq.poles) 0 x + lfieldTower q2spiTs 0 x ≤ (q2spiT : ℝ) := by
  intro x hx
  have h := q2spgGapM x hx
  rw [q2spiTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
