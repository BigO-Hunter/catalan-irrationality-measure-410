module

public import Submission.CatalanMeasure.GenD.Analytic.MarkedSheet

@[expose] public section

/-!
# Analytic layer, group 3: the sheet prefactor is `exp(o(N²))`

Generic version of `TwentyPrefactor`: for an arbitrary `P` with `0 < n0`,
`2^n · sheetPrefactor P N ≤ 2 (K N)^(n0 N)` with `K = 2 + 20 e^12 n0` (`2 + 400 e^12` at P20),
hence `≤ exp (ε (n0 N)²)` eventually.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Filter Real CatalanMeasure.Parametric
open scoped Topology

noncomputable section

/-- Linear growth constant of the prefactor (`2 + 20 e^12 n0`). -/
def prefactorK (P : Parameters) : ℝ := 2 + 20 * Real.exp 12 * (P.n0 : ℝ)

theorem prefactorK_pos (P : Parameters) : 0 < prefactorK P := by
  unfold prefactorK; positivity

theorem sheet_prefactor_le (P : Parameters) (hn0 : 0 < P.n0) {N : ℕ} (hN : 0 < N) :
    (2 : ℝ) ^ P.n N * sheetPrefactor P N ≤ 2 * (prefactorK P * (N : ℝ)) ^ (P.n0 * N) := by
  have hnN : P.n N = P.n0 * N := rfl
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc1 : (1 : ℝ) ≤ P.n0 := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ (P.n N : ℝ) := by
    rw [hnN]; push_cast; nlinarith only [hN1, hc1]
  have he : (1 : ℝ) ≤ Real.exp 12 := by rw [Real.one_le_exp_iff]; norm_num
  have hr := Real.rpow_le_rpow_of_exponent_le hn1
    (show (P.n N : ℝ) / 2 ≤ (P.n N : ℝ) by linarith only [hn1])
  rw [Real.rpow_natCast] at hr
  have hb : (3 / 2 : ℝ) * (P.n N : ℝ) ≤ 1 + 10 * Real.exp 12 * (P.n N : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_right he (show (0 : ℝ) ≤ (P.n N : ℝ) by positivity)]
  have hfirst : (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) ≤
      (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N := by
    calc
      _ ≤ (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ (P.n N) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = ((3 / 2 : ℝ) * (P.n N : ℝ)) ^ P.n N := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hb _
  have hS : sheetPrefactor P N ≤ 2 * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N := by
    unfold sheetPrefactor
    linarith only [hfirst]
  have hK : 2 * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ≤ prefactorK P * (N : ℝ) := by
    rw [hnN]
    unfold prefactorK
    push_cast
    nlinarith only [hN1]
  calc
    _ ≤ (2 : ℝ) ^ P.n N * (2 * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 2 * (2 * (1 + 10 * Real.exp 12 * (P.n N : ℝ))) ^ P.n N := by rw [mul_pow]; ring
    _ ≤ 2 * (prefactorK P * (N : ℝ)) ^ P.n N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hK _) (by norm_num)
    _ = _ := by rw [hnN]

theorem prefactor_error_tendsto (P : Parameters) (hn0 : 0 < P.n0) :
    Tendsto (fun N : ℕ =>
      (Real.log 2 + (P.n0 : ℝ) * (N : ℝ) * (Real.log (prefactorK P) + Real.log (N : ℝ))) /
        ((P.n0 : ℝ) * (N : ℝ)) ^ 2) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < P.n0 := by exact_mod_cast hn0
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hh := ((hi.pow 2).const_mul (Real.log 2 / (P.n0 : ℝ) ^ 2)).add
    (((hi.const_mul (Real.log (prefactorK P))).add hl).div_const (P.n0 : ℝ))
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc' : (P.n0 : ℝ) ≠ 0 := hc.ne'
  field_simp
  <;> ring

theorem sheet_prefactor_eventually (P : Parameters) (hn0 : 0 < P.n0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ P.n N * sheetPrefactor P N ≤
      Real.exp (ε * ((P.n0 : ℝ) * (N : ℝ)) ^ 2) := by
  have hh := (tendsto_order.mp (prefactor_error_tendsto P hn0)).2 ε hε
  have hc : (0 : ℝ) < P.n0 := by exact_mod_cast hn0
  filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hhN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := (div_lt_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < (P.n0 : ℝ) * N))).mp hhN
  have he : 2 * (prefactorK P * (N : ℝ)) ^ (P.n0 * N) =
      Real.exp (Real.log 2 + (P.n0 : ℝ) * (N : ℝ) *
        (Real.log (prefactorK P) + Real.log (N : ℝ))) := by
    rw [Real.exp_add, mul_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [show (P.n0 : ℝ) * (N : ℝ) = ((P.n0 * N : ℕ) : ℝ) by push_cast; rfl,
      Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (prefactorK_pos P), Real.exp_log hn,
      mul_pow]
  exact (sheet_prefactor_le P hn0 hN).trans
    (by rw [he]; exact Real.exp_le_exp.mpr hlog.le)

end

end Analytic
end CatalanMeasure.GenD
