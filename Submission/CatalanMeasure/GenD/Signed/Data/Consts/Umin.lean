module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# D2 constants: `hlogu` and `hn_top` of `Phase2Data` for the node scale `n = n0 N`

With `umin N = s / (A N + B)` (here `s = sqrt (1 - a^2)`, `A N + B = 2 (53 N + 1)`) and
`ncount N = n0 N`: `-log (umin N) / ncount N -> 0` and `ncount N -> infinity`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Filter Topology

theorem hn_top_lin {n0 : ℝ} (hn0 : 0 < n0) :
    Tendsto (fun N : ℕ => n0 * (N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.const_mul_atTop hn0

theorem hlogu_lin {s A B n0 : ℝ} (hs : 0 < s) (hA : 0 < A) (hB : 0 ≤ B) (hn0 : 0 < n0) :
    Tendsto (fun N : ℕ => -Real.log (s / (A * N + B)) / (n0 * N)) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => A * (N : ℝ) + B) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop hA)
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (n0 / A * x + (-(n0 * B / A)))) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop _ _ 1 (by positivity)
  have h2 := h1.comp hx
  have h3 : Tendsto (fun N : ℕ => -Real.log s / (n0 * (N : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (-Real.log s / n0))
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have h4 := h2.add h3
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < A * (N : ℝ) + B := by positivity
  simp only [Function.comp, pow_one]
  rw [Real.log_div hs.ne' hpos.ne']
  have hne : n0 / A * (A * (N : ℝ) + B) + -(n0 * B / A) = n0 * N := by
    field_simp; ring
  rw [hne]
  ring

end CatalanMeasure.Signed.Consts
