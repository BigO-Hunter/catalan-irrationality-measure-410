module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeLog

/-!
# D2 constants: the scalar logarithm bounds `L` and `Sg` of `SpikeTrialCert`

For the damping `tau = 1 - e`, `0 <= e <= emax <= 1`, and the phantom point `r = 1 - theta`:
* `L_bound`: `log (2 / (1 + tau^2 r)) <= 2 / (1 + (1-emax)^2 r) - 1`;
* `Sg_bound`: `log (1 - tau^2 r^2) - log (1 - rho^2) <= 2 (Y - 1) / (Y + 1)` with
  `Y = (1 - (1-emax)^2 r^2) / (1 - rho^2) <= 1`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set

theorem L_bound {e emax θ : ℝ} (he0 : 0 ≤ e) (he : e ≤ emax) (hemax : emax ≤ 1) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) :
    Real.log (2 / (1 + (1 - e) ^ 2 * (1 - θ))) ≤ 2 / (1 + (1 - emax) ^ 2 * (1 - θ)) - 1 := by
  have h1 : (1 - emax) ^ 2 ≤ (1 - e) ^ 2 := by nlinarith
  have h0 : 0 ≤ (1 - emax) ^ 2 * (1 - θ) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have h2 : (1 - emax) ^ 2 * (1 - θ) ≤ (1 - e) ^ 2 * (1 - θ) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have hd : 0 < 1 + (1 - emax) ^ 2 * (1 - θ) := by linarith
  have hd2 : 0 < 1 + (1 - e) ^ 2 * (1 - θ) := by linarith
  have hx : 2 / (1 + (1 - e) ^ 2 * (1 - θ)) ≤ 2 / (1 + (1 - emax) ^ 2 * (1 - θ)) :=
    div_le_div_of_nonneg_left (by norm_num) hd (by linarith)
  have hxpos : 0 < 2 / (1 + (1 - e) ^ 2 * (1 - θ)) := by positivity
  have := Real.log_le_sub_one_of_pos hxpos
  linarith

theorem Sg_bound {e emax θ ρ : ℝ} (he0 : 0 ≤ e) (he : e ≤ emax) (hemax : emax ≤ 1) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hρ : |ρ| < 1)
    (hY : (1 - (1 - emax) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2) ≤ 1)
    (hY0 : 0 < (1 - (1 - emax) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2)) :
    Real.log (1 - (1 - e) ^ 2 * (1 - θ) ^ 2) - Real.log (1 - ρ ^ 2) ≤
      2 * ((1 - (1 - emax) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2) - 1) /
        ((1 - (1 - emax) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2) + 1) := by
  set Y := (1 - (1 - emax) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2) with hYdef
  have hρ2 : 0 < 1 - ρ ^ 2 := by
    have := abs_lt.mp hρ
    nlinarith [sq_abs ρ, abs_nonneg ρ]
  have h1 : (1 - emax) ^ 2 ≤ (1 - e) ^ 2 := by nlinarith
  have hr : 0 ≤ (1 - θ) ^ 2 := sq_nonneg _
  have h2 : (1 - emax) ^ 2 * (1 - θ) ^ 2 ≤ (1 - e) ^ 2 * (1 - θ) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 hr
  have hapos : 0 < 1 - (1 - e) ^ 2 * (1 - θ) ^ 2 := by
    have hτ : (1 - e) ^ 2 ≤ 1 := by nlinarith
    have hr1 : (1 - θ) ^ 2 < 1 := by nlinarith
    have : (1 - e) ^ 2 * (1 - θ) ^ 2 < 1 := by nlinarith [sq_nonneg (1 - e)]
    linarith
  have hlog : Real.log (1 - (1 - e) ^ 2 * (1 - θ) ^ 2) - Real.log (1 - ρ ^ 2) =
      Real.log ((1 - (1 - e) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2)) := by
    rw [Real.log_div hapos.ne' hρ2.ne']
  rw [hlog]
  have hq : (1 - (1 - e) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2) ≤ Y := by
    rw [hYdef]; exact div_le_div_of_nonneg_right (by linarith) hρ2.le
  have hqpos : 0 < (1 - (1 - e) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2) := by positivity
  calc Real.log ((1 - (1 - e) ^ 2 * (1 - θ) ^ 2) / (1 - ρ ^ 2)) ≤ Real.log Y :=
        Real.log_le_log hqpos hq
    _ ≤ 2 * (Y - 1) / (Y + 1) := log_le_pade hY0 hY

end CatalanMeasure.Signed.Consts
