module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWinD58

@[expose] public section
set_option Elab.async false

/-!
# Certified windows for Theorem Z, Law_L (4) (lane G5h)

`FzL` is the concave piecewise-linear Law_L (4) profile; on `[13.64, 14.22]` it has three affine pieces
(slopes `11/2`, `1/2`, `-9/2`), each used as one window via `zL_winCert`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

/-- The three Z_L windows. -/
def zLWins : List KapWindow :=
  [cw (1364 / 100 : ℝ) (138 / 10 : ℝ) (-75 : ℝ) (11 / 2 : ℝ),
   cw (138 / 10 : ℝ) (14 : ℝ) (-6 : ℝ) (1 / 2 : ℝ),
   cw (14 : ℝ) (1422 / 100 : ℝ) (64 : ℝ) (-9 / 2 : ℝ)]

theorem zLWins_cert : ∀ w ∈ zLWins, WinCert (zLLB design D58.Odd.design_admissible) w := by
  intro w hw
  simp only [zLWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · refine zL_winCert (by norm_num) (by norm_num) ?_
    intro x h1 h2
    have e1 : min 0 (70 - 5 * x) = 0 := min_eq_left (by linarith)
    have e2 : min 0 (69 - 5 * x) = 0 := min_eq_left (by linarith)
    have e3 : min 0 (3 + x / 2 - (78 - 5 * x)) = 0 := min_eq_left (by linarith)
    simp only [FzL, e1, e2, e3]; linarith
  · refine zL_winCert (by norm_num) (by norm_num) ?_
    intro x h1 h2
    have e1 : min 0 (70 - 5 * x) = 0 := min_eq_left (by linarith)
    have e2 : min 0 (69 - 5 * x) = 69 - 5 * x := min_eq_right (by linarith)
    have e3 : min 0 (3 + x / 2 - (78 - 5 * x)) = 0 := min_eq_left (by linarith)
    simp only [FzL, e1, e2, e3]; linarith
  · refine zL_winCert (by norm_num) (by norm_num) ?_
    intro x h1 h2
    have e1 : min 0 (70 - 5 * x) = 70 - 5 * x := min_eq_right (by linarith)
    have e2 : min 0 (69 - 5 * x) = 69 - 5 * x := min_eq_right (by linarith)
    have e3 : min 0 (3 + x / 2 - (78 - 5 * x)) = 0 := min_eq_left (by linarith)
    simp only [FzL, e1, e2, e3]; linarith

theorem zLWins_pos : ∀ w ∈ zLWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [zLWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> simp only [cw] <;> norm_num

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger5
