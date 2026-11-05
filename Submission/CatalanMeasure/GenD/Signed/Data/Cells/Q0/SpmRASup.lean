module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAEq
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpmRAGB000

@[expose] public section

/-! **SPM_R, trial 0, corner 1/200: sup statement** (series window on [gs, 3/10], merged Laurent cells on [3/10, xc)). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval


def q0spmragN : ℕ := 72
def q0spmragHi : ℚ := qmk (3) 5 0 1
def q0spmragDelta : ℚ := dy3 (1) 0 69
theorem q0spmrag_laurent : l0OK q0spmraTsM q0spmragHi q0spmragN = true := by decide +kernel
theorem q0spmrag_cL : l0C q0spmraTsM = 0 := by decide +kernel
theorem q0spmrag_plogs : q0spmragFq.plogs = q0spmraFq.plogs := by decide +kernel
theorem q0spmrag_poles : q0spmragFq.poles = q0spmraFq.poles := by decide +kernel
theorem q0spmrag_hD : polyAB (vecAdd (vecAdd q0spmraFq.poly (l0P q0spmraTsM q0spmragN)) (q0spmragPoly.map (fun t => (-1 : ℚ) * t))) 0 q0spmragHi ≤ q0spmragDelta := by decide +kernel
theorem q0spmrag_tot : q0spmragT + q0spmragDelta + l0Err q0spmragHi q0spmragN q0spmraTsM ≤ q0spmraT := by decide +kernel
theorem q0spmrag_b0 : 0 < q0spmragBd.getD 0 0 := by decide +kernel
theorem q0spmrag_bN : q0spmragBd.getD 4 0 ≤ q0spmragHi := by decide +kernel
theorem q0spmrag_bmid : q0spmragBd.getD 4 0 = q0spmraBd.getD 0 0 := by decide +kernel
theorem q0spmrag_dom0 : q0spmragBd.getD 0 0 = 401 / 2500 := by decide +kernel
theorem q0spmra_domN : q0spmraBd.getD 12 0 = 999 / 1000 := by decide +kernel
theorem q0spmragCells : ∀ x ∈ Icc ((q0spmragBd.getD 0 0 : ℚ) : ℝ) ((q0spmragBd.getD 4 0 : ℚ) : ℝ), fieldTower q0spmragFq (poleF q0spmragFq.poles) 0 x ≤ (q0spmragT : ℝ) :=
  cover_union (cover_union (cover_union (q0spmragB000Bound) q0spmragB001Bound) q0spmragB002Bound) q0spmragB003Bound
theorem q0spmragSer : ∀ x ∈ Icc ((q0spmragBd.getD 0 0 : ℚ) : ℝ) ((q0spmragBd.getD 4 0 : ℚ) : ℝ), fieldTower q0spmraFq (poleF q0spmraFq.poles) 0 x + lfieldTower q0spmraTsM 0 x ≤ (q0spmraT : ℝ) := by
  intro x hx
  have h0 : (0 : ℝ) < ((q0spmragBd.getD 0 0 : ℚ) : ℝ) := by exact_mod_cast q0spmrag_b0
  have hN : ((q0spmragBd.getD 4 0 : ℚ) : ℝ) ≤ (q0spmragHi : ℝ) := by exact_mod_cast q0spmrag_bN
  have h := l0_series_sound q0spmraFq q0spmragFq q0spmraTsM q0spmragHi q0spmragN q0spmragDelta q0spmragT q0spmrag_laurent q0spmrag_cL q0spmrag_plogs q0spmrag_poles q0spmrag_hD
    (Set.Icc ((q0spmragBd.getD 0 0 : ℚ) : ℝ) ((q0spmragBd.getD 4 0 : ℚ) : ℝ)) (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩) (fun y hy => q0spmragCells y hy) x hx
  have hq : ((q0spmragT + q0spmragDelta + l0Err q0spmragHi q0spmragN q0spmraTsM : ℚ) : ℝ) ≤ (q0spmraT : ℝ) := by exact_mod_cast q0spmrag_tot
  exact h.trans hq

theorem q0spmraLaurentM : ∀ x ∈ Icc ((q0spmraBd.getD 0 0 : ℚ) : ℝ) ((q0spmraBd.getD 12 0 : ℚ) : ℝ), fieldTower q0spmraFq (poleF q0spmraFq.poles) 0 x + lfieldTower q0spmraTsM 0 x ≤ (q0spmraT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0spmraB000Bound) q0spmraB001Bound) q0spmraB002Bound) q0spmraB003Bound) q0spmraB004Bound) q0spmraB005Bound) q0spmraB006Bound) q0spmraB007Bound) q0spmraB008Bound) q0spmraB009Bound) q0spmraB010Bound) q0spmraB011Bound
/-- **SPM_R**, trial 0, corner 1/200: the field plus the exact Laurent terms on [401/2500, 999/1000]. -/
theorem q0spmraSup : ∀ x ∈ Icc ((q0spmragBd.getD 0 0 : ℚ) : ℝ) ((q0spmraBd.getD 12 0 : ℚ) : ℝ), fieldTower q0spmraFq (poleF q0spmraFq.poles) 0 x + lfieldTower q0spmraTs 0 x ≤ (q0spmraT : ℝ) := by
  intro x hx
  have hb : ((q0spmragBd.getD 4 0 : ℚ) : ℝ) = ((q0spmraBd.getD 0 0 : ℚ) : ℝ) := by rw [q0spmrag_bmid]
  have h1 := q0spmragSer
  rw [hb] at h1
  have h := cover_union h1 q0spmraLaurentM x hx
  rw [q0spmraTsM_eq, lfieldTower_mergeL] at h
  exact h

end CatalanMeasure.GenD.Signed.Data.Cells
