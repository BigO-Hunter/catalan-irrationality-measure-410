module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# D2 constants: the cap density `C1` of the actual gap nodes

`MarkedCap.nodeCap_gap` gives `C1 = J / (n 2 xc sqrt (1 - a^2))` with `J = 53 N`, `n = 58 N`,
`a = 2005000 / 6410801 = 2 g / (1 + g^2)` and `xc = 999/1000`; this is `0.481509...`.
`C1_bound`: it is at most `9631/20000 = 0.48155` (so any `C1 >= 9631/20000` is a legal `D.C1`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

theorem C1_bound :
    (53 : ℝ) / (58 * (2 * (999 / 1000) * Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2))) ≤
      9631 / 20000 := by
  have hs : (53 : ℝ) / (116 * (999 / 1000) * (9631 / 20000)) ≤
      Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hpos : 0 < Real.sqrt (1 - (2005000 / 6410801 : ℝ) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hs
  rw [div_le_iff₀ (by positivity)]
  have key : (9631 / 20000 : ℝ) * (116 * (999 / 1000)) *
      ((53 : ℝ) / (116 * (999 / 1000) * (9631 / 20000))) = 53 := by
    field_simp
  have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 9631 / 20000 * (116 * (999 / 1000)))
  nlinarith [this, key]

end CatalanMeasure.Signed.Consts
