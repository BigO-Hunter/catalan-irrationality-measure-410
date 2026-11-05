module

public import Submission.OAI.NumberTheory.Catalan.Analysis.RealEnergyKernelSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Norm

/-!
# Cross-kernel dilation and the negative cap (J3)

The cross kernel between a node `x ∈ (-1, 1)` and a particle `u = cos φ ∈ [-1, 1]` is
`l(x, u) = log (1 + 2 x u + x²) = 2 log ‖(-x) - e^{iφ}‖`, written `crossLog x u`.

* `crossLog_le_cap`: the one-sided negative cap.  For `c ∈ (0, 1)` and `-1 < x`,
  `l(x, u) ≤ l(max x (-(1 - c)), u) - log (1 - c)`, so a negative node costs at most
  `-log (1 - c) ≤ 2c` (for `c ≤ 1/2`) by being moved to `-(1 - c)`.
* `abs_crossLog_sub_dilate_le`: the two-sided dilation estimate.  For `|x| ≤ 1 - c'` and
  `D ∈ (0, 1]`, `|l(x, u) - l(D x, u)| ≤ 2 log (1 + (1 - D) / c')`.
* `crossLog_hasSum`: `l(τ² y, u)` as a Chebyshev series (reuse of `energy_hasSum_cross_kernel`).

All error terms are explicit functions of the cap parameters `c`, `c'` and the dilation `D`, so
the choice of rates (`e = o(c')`) is left to the consumer; see `abs_crossLog_sub_dilate_le_of_tau`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set

noncomputable section

/-- The cross kernel `l(x, u) = log (1 + 2 x u + x²)`. -/
def crossLog (x u : ℝ) : ℝ := Real.log (1 + 2 * x * u + x ^ 2)

/-- `f(x, u) ≥ (1 - |x|)²` for `|u| ≤ 1`. -/
theorem sq_one_sub_abs_le_cross {x u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1 - |x|) ^ 2 ≤ 1 + 2 * x * u + x ^ 2 := by
  have h1 : -|x| ≤ x * u := by
    have := abs_le.mp (show |x * u| ≤ |x| by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr hu))
    linarith [this.1]
  nlinarith [sq_abs x]

theorem cross_pos {x u : ℝ} (hx : |x| < 1) (hu : u ∈ Icc (-1 : ℝ) 1) :
    0 < 1 + 2 * x * u + x ^ 2 :=
  lt_of_lt_of_le (pow_pos (sub_pos.mpr hx) 2) (sq_one_sub_abs_le_cross hu)

/-- J3 (i), the negative cap, one-sided. -/
theorem crossLog_le_cap {c x u : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hx : -1 < x)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    crossLog x u ≤ crossLog (max x (-(1 - c))) u - Real.log (1 - c) := by
  have hc1 : 0 < 1 - c := sub_pos.mpr hc.2
  have hlog : Real.log (1 - c) ≤ 0 := Real.log_nonpos hc1.le (by linarith [hc.1])
  rcases le_or_gt (-(1 - c)) x with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h.le]
    have hxabs : |x| < 1 := by
      rw [abs_lt]; constructor <;> linarith [hc.1, hc.2]
    have hf := cross_pos hxabs hu
    have hcap : |-(1 - c)| < 1 := by
      rw [abs_neg, abs_of_pos hc1]; linarith [hc.1]
    have hf' := cross_pos hcap hu
    have hu1 := hu.1
    have hu2 := hu.2
    -- f(x,u) ≤ c² + 2(1-u) and (1-c)(c² + 2(1-u)) ≤ f(-(1-c),u)
    have hA : 1 + 2 * x * u + x ^ 2 ≤ c ^ 2 + 2 * (1 - u) := by
      have : 1 + 2 * x * u + x ^ 2 = (1 + x) ^ 2 + 2 * (-x) * (1 - u) := by ring
      have h1 : (1 + x) ^ 2 ≤ c ^ 2 := by nlinarith [hc.1, hc.2]
      have h2 : 2 * (-x) * (1 - u) ≤ 2 * (1 - u) := by nlinarith
      linarith
    have hB : (1 - c) * (1 + 2 * x * u + x ^ 2) ≤
        1 + 2 * (-(1 - c)) * u + (-(1 - c)) ^ 2 := by
      have h3 : (1 - c) * (1 + 2 * x * u + x ^ 2) ≤ (1 - c) * (c ^ 2 + 2 * (1 - u)) :=
        mul_le_mul_of_nonneg_left hA hc1.le
      nlinarith [mul_nonneg (mul_nonneg hc.1.le hc.1.le) hc.1.le]
    unfold crossLog
    have : Real.log (1 + 2 * x * u + x ^ 2) ≤
        Real.log ((1 + 2 * (-(1 - c)) * u + (-(1 - c)) ^ 2) / (1 - c)) := by
      apply Real.log_le_log hf
      rw [le_div_iff₀ hc1]
      linarith
    rwa [Real.log_div hf'.ne' hc1.ne'] at this

/-- Cost of the cap: `-log (1 - c) ≤ 2c` for `0 < c ≤ 1/2`. -/
theorem neg_log_one_sub_le {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 / 2)) : -Real.log (1 - c) ≤ 2 * c := by
  have h1 : 0 < 1 - c := by linarith [hc.1, hc.2]
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  have h2 : (1 - c)⁻¹ - 1 = c / (1 - c) := by field_simp; ring
  rw [h2] at h
  have h3 : c / (1 - c) ≤ 2 * c := by
    rw [div_le_iff₀ h1]; nlinarith [hc.1, hc.2]
  linarith

theorem crossLog_le_cap_two_mul {c x u : ℝ} (hc : c ∈ Ioc (0 : ℝ) (1 / 2)) (hx : -1 < x)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    crossLog x u ≤ crossLog (max x (-(1 - c))) u + 2 * c := by
  have := crossLog_le_cap ⟨hc.1, by linarith [hc.2]⟩ hx hu
  linarith [neg_log_one_sub_le hc]

/-- Euclidean (chord) length: `f(x, u) = (x + u)² + (1 - u²)`. -/
theorem cross_eq_sq_add (x u : ℝ) :
    1 + 2 * x * u + x ^ 2 = (x + u) ^ 2 + (1 - u ^ 2) := by ring

/-- `|√f(x,u) - √f(y,u)| ≤ |x - y|`: the chord length is 1-Lipschitz in the node. -/
theorem abs_sqrt_cross_sub_le {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (x y : ℝ) :
    |Real.sqrt (1 + 2 * x * u + x ^ 2) - Real.sqrt (1 + 2 * y * u + y ^ 2)| ≤ |x - y| := by
  have hv : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  let w : ℝ → ℂ := fun t => ⟨t + u, Real.sqrt (1 - u ^ 2)⟩
  have hn : ∀ t, ‖w t‖ = Real.sqrt (1 + 2 * t * u + t ^ 2) := by
    intro t
    rw [Complex.norm_def, Complex.normSq_apply, cross_eq_sq_add]
    congr 1
    have := Real.mul_self_sqrt hv
    simp only [w]
    nlinarith
  have hd : ‖w x - w y‖ = |x - y| := by
    have : w x - w y = ((x - y : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [w]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  calc _ = |‖w x‖ - ‖w y‖| := by rw [hn, hn]
    _ ≤ ‖w x - w y‖ := abs_norm_sub_norm_le _ _
    _ = _ := hd

theorem one_sub_abs_le_sqrt_cross {x u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    1 - |x| ≤ Real.sqrt (1 + 2 * x * u + x ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  exact sq_one_sub_abs_le_cross hu

/-- J3 (ii), the two-sided dilation estimate. -/
theorem abs_crossLog_sub_dilate_le {c' D x u : ℝ} (hc' : c' ∈ Ioc (0 : ℝ) 1)
    (hD : D ∈ Ioc (0 : ℝ) 1) (hx : |x| ≤ 1 - c') (hu : u ∈ Icc (-1 : ℝ) 1) :
    |crossLog x u - crossLog (D * x) u| ≤ 2 * Real.log (1 + (1 - D) / c') := by
  set δ : ℝ := (1 - D) / c' with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hD.2) hc'.1.le
  have hDx : |D * x| ≤ 1 - c' := by
    rw [abs_mul, abs_of_pos hD.1]
    calc D * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right hD.2 (abs_nonneg _)
      _ ≤ 1 - c' := by linarith
  set A := Real.sqrt (1 + 2 * x * u + x ^ 2) with hA
  set B := Real.sqrt (1 + 2 * (D * x) * u + (D * x) ^ 2) with hB
  have hA' : c' ≤ A := by linarith [one_sub_abs_le_sqrt_cross (x := x) hu]
  have hB' : c' ≤ B := by linarith [one_sub_abs_le_sqrt_cross (x := D * x) hu]
  have hApos : 0 < A := lt_of_lt_of_le hc'.1 hA'
  have hBpos : 0 < B := lt_of_lt_of_le hc'.1 hB'
  have hdiff : |A - B| ≤ 1 - D := by
    have h := abs_sqrt_cross_sub_le hu x (D * x)
    have h2 : |x - D * x| = (1 - D) * |x| := by
      rw [show x - D * x = (1 - D) * x by ring, abs_mul, abs_of_nonneg (sub_nonneg.mpr hD.2)]
    rw [h2] at h
    have hx1 : |x| ≤ 1 := by linarith [hc'.1]
    calc |A - B| ≤ (1 - D) * |x| := h
      _ ≤ (1 - D) * 1 := mul_le_mul_of_nonneg_left hx1 (sub_nonneg.mpr hD.2)
      _ = 1 - D := mul_one _
  have hδc : 1 - D = δ * c' := by rw [hδ, div_mul_cancel₀ _ hc'.1.ne']
  have hAB : A ≤ (1 + δ) * B := by
    have := (abs_le.mp hdiff).2
    nlinarith [mul_le_mul_of_nonneg_left hB' hδ0]
  have hBA : B ≤ (1 + δ) * A := by
    have := (abs_le.mp hdiff).1
    nlinarith [mul_le_mul_of_nonneg_left hA' hδ0]
  have hlogA : crossLog x u = 2 * Real.log A := by
    unfold crossLog
    rw [hA, Real.log_sqrt (cross_pos (by linarith [hc'.1]) hu).le]
    ring
  have hlogB : crossLog (D * x) u = 2 * Real.log B := by
    unfold crossLog
    rw [hB, Real.log_sqrt (cross_pos (by linarith [hc'.1]) hu).le]
    ring
  have h1 : Real.log A - Real.log B ≤ Real.log (1 + δ) := by
    rw [← Real.log_div hApos.ne' hBpos.ne']
    apply Real.log_le_log (div_pos hApos hBpos)
    rw [div_le_iff₀ hBpos]; exact hAB
  have h2 : Real.log B - Real.log A ≤ Real.log (1 + δ) := by
    rw [← Real.log_div hBpos.ne' hApos.ne']
    apply Real.log_le_log (div_pos hBpos hApos)
    rw [div_le_iff₀ hApos]; exact hBA
  rw [hlogA, hlogB, abs_le]
  constructor <;> linarith

/-- With the engine dilation `D = τ² = (1 - e)²`: error `≤ 4 e / c'`, so it is `o(1)` as soon as
`e = o(c')`. -/
theorem abs_crossLog_sub_dilate_le_of_tau {c' e x u : ℝ} (hc' : c' ∈ Ioc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : |x| ≤ 1 - c') (hu : u ∈ Icc (-1 : ℝ) 1) :
    |crossLog x u - crossLog ((1 - e) ^ 2 * x) u| ≤ 4 * e / c' := by
  have hD : (1 - e) ^ 2 ∈ Ioc (0 : ℝ) 1 :=
    ⟨by nlinarith [he.1, he.2], by nlinarith [he.1, he.2]⟩
  have h := abs_crossLog_sub_dilate_le hc' hD hx hu
  have h1 : 1 - (1 - e) ^ 2 ≤ 2 * e := by nlinarith [he.1, he.2]
  have h2 : Real.log (1 + (1 - (1 - e) ^ 2) / c') ≤ (1 - (1 - e) ^ 2) / c' := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (1 - (1 - e) ^ 2) / c' by
      have : 0 ≤ (1 - (1 - e) ^ 2) / c' :=
        div_nonneg (by nlinarith [he.1, he.2]) hc'.1.le
      linarith)
    linarith
  have h3 : (1 - (1 - e) ^ 2) / c' ≤ 2 * e / c' :=
    div_le_div_of_nonneg_right h1 hc'.1.le
  calc _ ≤ 2 * Real.log (1 + (1 - (1 - e) ^ 2) / c') := h
    _ ≤ 2 * (2 * e / c') := by linarith
    _ = 4 * e / c' := by ring

/-- Finite-configuration form: signed weights, all nodes in `[-(1 - c'), 1 - c']`. -/
theorem abs_cross_field_sub_dilate_le {n : ℕ} {c' e u : ℝ} (hc' : c' ∈ Ioc (0 : ℝ) 1)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (w y : Fin n → ℝ) (hy : ∀ l, |y l| ≤ 1 - c')
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    |∑ l, w l * crossLog (y l) u - ∑ l, w l * crossLog ((1 - e) ^ 2 * y l) u| ≤
      (∑ l, |w l|) * (4 * e / c') := by
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ l, |w l * crossLog (y l) u - w l * crossLog ((1 - e) ^ 2 * y l) u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |w l| * (4 * e / c') := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_crossLog_sub_dilate_le_of_tau hc' he (hy l) hu)
          (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- `l(x, u)` for `|x| < 1` as a Chebyshev series (reuse of `energy_hasSum_cross_kernel`). -/
theorem crossLog_hasSum {x u : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => -2 * (-x) ^ (k + 1) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u / ((k + 1 : ℕ) : ℝ))
      (crossLog x u) := by
  have hx' : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := OAI.InternalCatalan.energy_hasSum_cross_kernel hx' hu
  have h1 := (hasSum_nat_add_iff' (f := fun k : ℕ =>
    2 * (-x) ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u / (k : ℝ)) 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, sub_zero] at h1
  have h2 := h1.mul_left (-1 : ℝ)
  convert h2 using 1
  · ext k; ring
  · unfold crossLog
    have : 1 - 2 * (-x) * u + (-x) ^ 2 = 1 + 2 * x * u + x ^ 2 := by ring
    rw [this]; simp

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.crossLog_le_cap
#print axioms CatalanMeasure.Signed.crossLog_le_cap_two_mul
#print axioms CatalanMeasure.Signed.abs_crossLog_sub_dilate_le
#print axioms CatalanMeasure.Signed.abs_crossLog_sub_dilate_le_of_tau
#print axioms CatalanMeasure.Signed.abs_cross_field_sub_dilate_le
#print axioms CatalanMeasure.Signed.crossLog_hasSum
