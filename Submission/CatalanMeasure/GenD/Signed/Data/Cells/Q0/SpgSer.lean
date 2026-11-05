module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpgSup
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpiEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Fields
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpGE0
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.PolySplit

@[expose] public section

/-! SP gap (0, 3/10), trial 0: the series window `l0_series_sound` turns the Laurent-free cover `q0spgSup` of fq' into the bound for the true SP field plus the merged Laurent terms. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q0spgN : ℕ := 72
def q0spgHi : ℚ := qmk (3) 5 0 1
def q0spgDelta : ℚ := dy3 (1) 0 69
theorem q0spg_laurent : l0OK q0spiTsM q0spgHi q0spgN = true := by decide +kernel
theorem q0spg_cL : l0C q0spiTsM = 0 := by decide +kernel
theorem q0spg_plogs : q0spgFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.plogs := by decide +kernel
theorem q0spg_poles : q0spgFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.poles := by decide +kernel
theorem q0spg_hD : polyAB (vecAdd (vecAdd CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.poly (l0P q0spiTsM q0spgN)) (q0spgPoly.map (fun t => (-1 : ℚ) * t))) 0 q0spgHi ≤ q0spgDelta := by decide +kernel
theorem q0spg_tot : q0spgT + q0spgDelta + l0Err q0spgHi q0spgN q0spiTsM ≤ q0spiT := by decide +kernel
theorem q0spg_b0 : 0 < q0spgBd.getD 0 0 := by decide +kernel
theorem q0spg_b0E : q0spgBd.getD 0 0 = q0spe0Hi := by decide +kernel
theorem q0spg_bN : q0spgBd.getD 71 0 ≤ q0spgHi := by decide +kernel
theorem q0spg_bNeq : q0spgBd.getD 71 0 = 3 / 10 := by decide +kernel
theorem q0spgGapM : ∀ x ∈ Ioo ((q0spgBd.getD 0 0 : ℚ) : ℝ) ((q0spgBd.getD 71 0 : ℚ) : ℝ), fieldTower CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.poles) 0 x + lfieldTower q0spiTsM 0 x ≤ (q0spiT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q0spgBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q0spg_b0
  have hN : ((q0spgBd.getD 71 0 : ℚ) : ℝ) ≤ (q0spgHi : ℝ) := by exact_mod_cast q0spg_bN
  have h := l0_series_sound CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq q0spgFq q0spiTsM q0spgHi q0spgN q0spgDelta q0spgT q0spg_laurent q0spg_cL q0spg_plogs q0spg_poles q0spg_hD
    (Set.Ioo ((q0spgBd.getD 0 0 : ℚ) : ℝ) ((q0spgBd.getD 71 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q0spgSup y hy) x hx
  have hq : ((q0spgT + q0spgDelta + l0Err q0spgHi q0spgN q0spiTsM : ℚ) : ℝ) ≤ (q0spiT : ℝ) := by exact_mod_cast q0spg_tot
  exact h.trans hq

/-- **SP gap (0, 3/10)**, trial 0: the true SP field plus the exact Laurent terms. -/
theorem q0spiGapSup : ∀ x ∈ Ioo ((q0spgBd.getD 0 0 : ℚ) : ℝ) ((q0spgBd.getD 71 0 : ℚ) : ℝ), fieldTower CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial.T0.spFq.poles) 0 x + lfieldTower q0spiTs 0 x ≤ (q0spiT : ℝ) := by
  intro x hx
  have h := q0spgGapM x hx
  rw [q0spiTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
