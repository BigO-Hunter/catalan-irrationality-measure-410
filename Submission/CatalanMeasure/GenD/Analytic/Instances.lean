module

public import Submission.CatalanMeasure.GenD.Analytic.Glue
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# Analytic layer: numerals of the generic constants at P20 and at the displaced design D58

Instance file (numerals only).  P20 = `⟨20, 3, 1, 2, 1⟩`, D58 = `Odd.design = ⟨58, 9, 3, 5, 3⟩`.

| constant                       | P20   | D58   |
|--------------------------------|-------|-------|
| `gRes`   `(n0-g0)/n0`          | 9/10  | 53/58 |
| `gKappa` `(b0+q0+g0)/n0`       | 3/10  | 17/58 |
| `gC0`                          | 1/5   | 6/29  |
| `gC1`                          | 8/5   | 47/29 |
| row weights `(A0, 2h0, H0)/n0` | (2/5, 1/10, 27/20) | (11/29, 3/29, 39/29) |
| column weights `(b0, q0)/n0`   | (3/20, 1/20) | (9/58, 3/58) |
| near weight `(n0-2g0-1)/n0`    | 3/4   | 47/58 |
| marked-first ratio `g0/n0`     | 1/10  | 5/58  |
-/

namespace CatalanMeasure.GenD
namespace Analytic
namespace Instances

open CatalanMeasure.Parametric

noncomputable section

/-- P20 as a literal (the old `twenty`; not imported). -/
def p20 : Parameters := ⟨20, 3, 1, 2, 1⟩

theorem p20_admissible : Admissible p20 := by norm_num [Admissible, p20]

theorem p20_gRes : gRes p20 = 9 / 10 := by unfold gRes p20; norm_num
theorem p20_gKappa : gKappa p20 = 3 / 10 := by unfold gKappa p20; norm_num
theorem p20_gC0 : gC0 p20 = 1 / 5 := by unfold gC0; rw [p20_gKappa]; norm_num
theorem p20_gC1 : gC1 p20 = 8 / 5 := by unfold gC1; rw [p20_gKappa, p20_gRes]; norm_num

theorem d58_gRes : gRes D58.Odd.design = 53 / 58 := by unfold gRes D58.Odd.design; norm_num
theorem d58_gKappa : gKappa D58.Odd.design = 17 / 58 := by unfold gKappa D58.Odd.design; norm_num
theorem d58_gC0 : gC0 D58.Odd.design = 6 / 29 := by unfold gC0; rw [d58_gKappa]; norm_num
theorem d58_gC1 : gC1 D58.Odd.design = 47 / 29 := by
  unfold gC1; rw [d58_gKappa, d58_gRes]; norm_num

theorem d58_row_weights :
    (((D58.Odd.design.b0 : ℝ) + D58.Odd.design.q0 + 2 * D58.Odd.design.g0) / D58.Odd.design.n0 =
        11 / 29) ∧
    (2 * (D58.Odd.design.h0 : ℝ) / D58.Odd.design.n0 = 3 / 29) ∧
    (((D58.Odd.design.n0 : ℝ) + D58.Odd.design.b0 + D58.Odd.design.q0 + D58.Odd.design.g0 +
        D58.Odd.design.h0) / D58.Odd.design.n0 = 39 / 29) := by
  unfold D58.Odd.design; norm_num

theorem d58_column_weights :
    ((D58.Odd.design.b0 : ℝ) / D58.Odd.design.n0 = 9 / 58) ∧
      ((D58.Odd.design.q0 : ℝ) / D58.Odd.design.n0 = 3 / 58) := by
  unfold D58.Odd.design; norm_num

theorem d58_near_weight :
    ((D58.Odd.design.n0 : ℝ) - 2 * D58.Odd.design.g0 - 1) / D58.Odd.design.n0 = 47 / 58 := by
  unfold D58.Odd.design; norm_num

theorem d58_g_ratio : (D58.Odd.design.g0 : ℝ) / D58.Odd.design.n0 = 5 / 58 := by
  unfold D58.Odd.design; norm_num

end
end Instances
end Analytic
end CatalanMeasure.GenD
