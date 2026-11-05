module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SpmRAGB000

@[expose] public section

/-! **SPM_R, trial 1, corner 1/200: sup statement** (series window on [gs, 3/10], merged Laurent cells on [3/10, xc)). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


def q1spmragN : ℕ := 72
def q1spmragHi : ℚ := qmk (3) 5 0 1
def q1spmragDelta : ℚ := dy3 (1) 0 69
theorem q1spmrag_laurent : l0OK q1spmraTsM q1spmragHi q1spmragN = true := by decide +kernel
theorem q1spmrag_cL : l0C q1spmraTsM = 0 := by decide +kernel
theorem q1spmrag_plogs : q1spmragFq.plogs = q1spmraFq.plogs := by decide +kernel
theorem q1spmrag_poles : q1spmragFq.poles = q1spmraFq.poles := by decide +kernel
theorem q1spmrag_hD : polyAB (vecAdd (vecAdd q1spmraFq.poly (l0P q1spmraTsM q1spmragN)) (q1spmragPoly.map (fun t => (-1 : ℚ) * t))) 0 q1spmragHi ≤ q1spmragDelta := by decide +kernel
theorem q1spmrag_tot : q1spmragT + q1spmragDelta + l0Err q1spmragHi q1spmragN q1spmraTsM ≤ q1spmraT := by decide +kernel
theorem q1spmrag_b0 : 0 < q1spmragBd.getD 0 0 := by decide +kernel
theorem q1spmrag_bN : q1spmragBd.getD 4 0 ≤ q1spmragHi := by decide +kernel
theorem q1spmrag_bmid : q1spmragBd.getD 4 0 = q1spmraBd.getD 0 0 := by decide +kernel
theorem q1spmrag_dom0 : q1spmragBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q1spmra_domN : q1spmraBd.getD 12 0 = 999 / 1000 := by decide +kernel
theorem q1spmragCells : ∀ x ∈ Icc ((q1spmragBd.getD 0 0 : ℚ) : ℝ) ((q1spmragBd.getD 4 0 : ℚ) : ℝ), fieldTower q1spmragFq (poleF q1spmragFq.poles) 0 x ≤ (q1spmragT : ℝ) :=
  cover_union (cover_union (cover_union (q1spmragB000Bound) q1spmragB001Bound) q1spmragB002Bound) q1spmragB003Bound
theorem q1spmragSer : ∀ x ∈ Icc ((q1spmragBd.getD 0 0 : ℚ) : ℝ) ((q1spmragBd.getD 4 0 : ℚ) : ℝ), fieldTower q1spmraFq (poleF q1spmraFq.poles) 0 x + lfieldTower q1spmraTsM 0 x ≤ (q1spmraT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q1spmragBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q1spmrag_b0
  have hN : ((q1spmragBd.getD 4 0 : ℚ) : ℝ) ≤ (q1spmragHi : ℝ) := by exact_mod_cast q1spmrag_bN
  have h := l0_series_sound q1spmraFq q1spmragFq q1spmraTsM q1spmragHi q1spmragN q1spmragDelta q1spmragT q1spmrag_laurent q1spmrag_cL q1spmrag_plogs q1spmrag_poles q1spmrag_hD
    (Set.Icc ((q1spmragBd.getD 0 0 : ℚ) : ℝ) ((q1spmragBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q1spmragCells y hy) x hx
  have hq : ((q1spmragT + q1spmragDelta + l0Err q1spmragHi q1spmragN q1spmraTsM : ℚ) : ℝ) ≤ (q1spmraT : ℝ) := by exact_mod_cast q1spmrag_tot
  exact h.trans hq

theorem q1spmraLaurentM : ∀ x ∈ Icc ((q1spmraBd.getD 0 0 : ℚ) : ℝ) ((q1spmraBd.getD 12 0 : ℚ) : ℝ), fieldTower q1spmraFq (poleF q1spmraFq.poles) 0 x + lfieldTower q1spmraTsM 0 x ≤ (q1spmraT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1spmraB000Bound) q1spmraB001Bound) q1spmraB002Bound) q1spmraB003Bound) q1spmraB004Bound) q1spmraB005Bound) q1spmraB006Bound) q1spmraB007Bound) q1spmraB008Bound) q1spmraB009Bound) q1spmraB010Bound) q1spmraB011Bound
/-- **SPM_R**, trial 1, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q1spmraSup : ∀ x ∈ Icc ((q1spmragBd.getD 0 0 : ℚ) : ℝ) ((q1spmraBd.getD 12 0 : ℚ) : ℝ), fieldTower q1spmraFq (poleF q1spmraFq.poles) 0 x + lfieldTower q1spmraTs 0 x ≤ (q1spmraT : ℝ) := by
  intro x hx
  have hb : ((q1spmragBd.getD 4 0 : ℚ) : ℝ) = ((q1spmraBd.getD 0 0 : ℚ) : ℝ) := by rw [q1spmrag_bmid]
  have h1 := q1spmragSer
  rw [hb] at h1
  have h := cover_union h1 q1spmraLaurentM x hx
  rw [q1spmraTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
