module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Real.Basic

/-!
# D2 constants: the arithmetic inequality `hfin` of `SpikeTrialCert` from per-`nu` ratios

`hfin : 2 m (Kn L + 2 sp De2 + m Sg + 2 nu e A) + m K0 <= nu (2 m cs)` follows from the ratio
inequality `L + 2 sigma De2 + mu Sg + 2 emax A <= cs` (all per `nu`) when `Kn <= nu`,
`sp <= sigma nu`, `m >= mu nu`, `e <= emax`, `Sg <= 0`, `K0 <= 0`.  (For the data of `SpikeK`, every
`K0` is negative.)
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

theorem hfin_of_ratio {ν Kn sp m e emax A L De2 Sg K0 cs σ μ : ℝ} (hν : 0 < ν) (hm : 0 ≤ m)
    (hKn : Kn ≤ ν) (hL : 0 ≤ L) (hsp : sp ≤ σ * ν) (hDe : 0 ≤ De2) (hσ : 0 ≤ σ)
    (hmu : μ * ν ≤ m) (hSg : Sg ≤ 0) (hK0 : K0 ≤ 0) (he0 : 0 ≤ e) (he : e ≤ emax) (hA : 0 ≤ A)
    (hcs : L + 2 * σ * De2 + μ * Sg + 2 * emax * A ≤ cs) :
    2 * m * (Kn * L + 2 * sp * De2 + m * Sg + 2 * ν * e * A) + m * K0 ≤ ν * (2 * m * cs) := by
  have h1 : Kn * L ≤ ν * L := mul_le_mul_of_nonneg_right hKn hL
  have h2 : 2 * sp * De2 ≤ 2 * (σ * ν) * De2 := by nlinarith [mul_nonneg hDe (sub_nonneg.2 hsp)]
  have h3 : m * Sg ≤ μ * ν * Sg := by nlinarith [mul_nonneg (sub_nonneg.2 hmu) (neg_nonneg.2 hSg)]
  have h4 : 2 * ν * e * A ≤ 2 * ν * emax * A := by
    have := mul_le_mul_of_nonneg_right he hA
    nlinarith [mul_nonneg hν.le (sub_nonneg.2 this)]
  have key : Kn * L + 2 * sp * De2 + m * Sg + 2 * ν * e * A ≤ ν * cs := by
    have := mul_le_mul_of_nonneg_left hcs hν.le
    nlinarith [this]
  have h5 : 2 * m * (Kn * L + 2 * sp * De2 + m * Sg + 2 * ν * e * A) ≤ 2 * m * (ν * cs) :=
    mul_le_mul_of_nonneg_left key (by positivity)
  have h6 : m * K0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hK0
  nlinarith [h5, h6]

end CatalanMeasure.Signed.Consts
