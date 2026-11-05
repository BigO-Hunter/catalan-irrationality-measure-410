module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Cells

@[expose] public section
set_option Elab.async false

/-!
# `D_growth` for D58 from an arbitrary list of cells (lane G5c)

`ledger_growth`: for any nullity lower bound `lb` of the displaced design and any ordered list of
`KapWindow`s (certified against `lb.kap` and the pool minorant), the canonical normalizer
satisfies `log D_N <= (24733/4 + (2673/8) log 2 - gain + eps) N^2`, `gain` the exact area sum.
This is the shape consumed by `Bank540.Decay.Budget540.gD`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem gD_design (ws : List KapWindow) :
    gD design D58.Odd.f58 116 ws =
      2673 / 8 * Real.log 2 + 24733 / 4 - (ws.map (KapWindow.area 58)).sum := by
  have hH1 : ((design.H 1 : ℕ) : ℝ) = 78 := by
    rw [Odd.design_H]; norm_num
  have hint : D58.Odd.f58.area 1 78 = 24269 / 4 := by
    rw [← PL.Prof.integral_eval _ (by norm_num : (1 : ℝ) ≤ 78)]
    exact integral_f58
  have hA : Arithmetic.TwoAdic.A2 (design.n0 : ℝ) (78 : ℝ) (design.b0 : ℝ) = 2673 / 8 := by
    simp only [Arithmetic.TwoAdic.A2, design, D58.Odd.design, Uniform.Ledger.B2]
    norm_num
  unfold gD
  rw [hH1, hint, hA, design_n0]
  ring

theorem ledger_growth (lb : NullityLB design) (ws : List KapWindow) (gain : ℝ)
    (hsum : (ws.map (KapWindow.area 58)).sum = gain)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78)
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (hcert : ∀ w ∈ ws, ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → w.a * N < p →
      (p : ℝ) ≤ w.b * N →
        (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ (lb.kap N p : ℝ) ∧
        (N : ℝ) * w.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible lb 79
        (by rw [Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain + ε) * (N : ℝ) ^ 2 := by
  have hH78 : (design.H 1 : ℝ) = 78 := by
    have : design.H 1 = 78 := by rw [Odd.design_H]
    rw [this]; norm_num
  have h := D_growth_of_nullityLB design D58.Odd.design_admissible lb 79
    (by rw [Odd.design_H]; norm_num) D58.Odd.f58 116
    (fun N p hN hp => hloss_safe N p hN hp) (fun x hx => hf0_d58 x hx)
    (fun _ _ => 0) (fun _ => ∅) 0 0 le_rfl (by simp) (by simp) (by simp)
    ws 2 (by norm_num)
    (fun w hw => by obtain ⟨a, b, c⟩ := hpos w hw; exact ⟨a, b, by rw [hH78]; exact c⟩)
    hord hrec
    (fun w hw => by
      filter_upwards [hcert w hw] with N hN p hp h1 h2
      have := hN p hp h1 h2
      simpa using this)
    hε
  rw [gD_design, hsum] at h
  filter_upwards [h] with N hN
  convert hN using 2
  ring

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
