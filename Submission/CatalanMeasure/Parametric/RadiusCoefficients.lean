module
public import Submission.CatalanMeasure.QuadCircle
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset
noncomputable section

theorem coeff_comp_scale (p : ℝ[X]) (r : ℝ) (m : ℕ) :
    (p.comp (C r * X)).coeff m = p.coeff m * r^m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, add_mul]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow,
      ← map_pow, ← mul_assoc, ← map_mul]
    simp only [coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst m; ring
    · simp

/-- The roots-of-unity coefficient estimate after rescaling the circle. -/
theorem abs_coeff_mul_radius_le (p : ℝ[X]) {r B : ℝ} (hr : 0 < r)
    (hB : ∀ z : ℂ, ‖z‖ = r → ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ≤ B) (m : ℕ) :
    |p.coeff m| * r^m ≤ B := by
  have h := CatalanMeasure.abs_coeff_le_of_circle (p.comp (C r * X))
    (C := B) (fun z hz => by
      rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        eval_comp, eval_mul, eval_C, eval_X]
      apply hB
      rw [norm_mul, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, hz, mul_one]) m
  rw [coeff_comp_scale, abs_mul, abs_pow, abs_of_pos hr] at h
  exact h

/-- For radius at least one, the same bound controls every unweighted coefficient. -/
theorem abs_coeff_le_radius (p : ℝ[X]) {r B : ℝ} (hr : 1 ≤ r)
    (hB : ∀ z : ℂ, ‖z‖ = r → ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ≤ B) (m : ℕ) :
    |p.coeff m| ≤ B := by
  have h := abs_coeff_mul_radius_le p (lt_of_lt_of_le zero_lt_one hr) hB m
  have hh := one_le_pow₀ hr (n := m)
  nlinarith [abs_nonneg (p.coeff m)]

/-- Removing the shared monomial and absorbing the filter into the other shared
factor preserves the circle coefficient bound, even below the monomial shift. -/
theorem common_factor_filtered_coeff_le (R : ℝ[X]) (A h q : ℕ) {r B : ℝ} (hr : 1 ≤ r)
    (hB : ∀ z : ℂ, ‖z‖ = r →
      ‖((R*(1-X)^(h+q)).map (algebraMap ℝ ℂ)).eval z‖ ≤ B) (m : ℕ) :
    |((X^A*(1-X)^h)*R*(X-1)^q).coeff m| ≤ B := by
  have hsign : (X-1:ℝ[X])^q = C ((-1:ℝ)^q)*(1-X)^q := by
    rw [show (X-1:ℝ[X]) = C (-1)*(1-X) by simp, mul_pow, ← map_pow]
  have he : (X^A*(1-X)^h)*R*(X-1)^q =
      X^A*(C ((-1:ℝ)^q)*(R*(1-X)^(h+q))) := by rw [hsign,pow_add]; ring
  rw [he,coeff_X_pow_mul']
  split_ifs with hm
  · rw [coeff_C_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact abs_coeff_le_radius _ hr hB _
  · simp only [abs_zero]
    exact (norm_nonneg _).trans (hB (r:ℂ) (by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_of_lt_of_le zero_lt_one hr)]))

/-- Finite coefficient sums cost only their number of terms after radial rescaling.
The integer shift may be negative, as it is after removing the common row factor. -/
theorem kernel_coeff_sum_le (p : ℝ[X]) {r B : ℝ} (hr : 1 ≤ r)
    (hB : ∀ z : ℂ, ‖z‖ = r → ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ≤ B)
    (H e : ℕ) (f : ℕ → ℕ) (hf : ∀ i ∈ range H, e ≤ f i) :
    |∑ i ∈ range H, (OAI.InternalCatalan.centralCoeffKernel (i : ℤ) : ℝ) *
      p.coeff (f i)| * r^e ≤ H * B := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (r : ℂ) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]))
  calc _ ≤ (∑ i ∈ range H, |(OAI.InternalCatalan.centralCoeffKernel (i : ℤ) : ℝ) *
      p.coeff (f i)|) * r^e := mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ i ∈ range H, |(OAI.InternalCatalan.centralCoeffKernel (i : ℤ) : ℝ)| *
        (|p.coeff (f i)| * r^e) := by simp_rw [sum_mul, abs_mul, mul_assoc]
    _ ≤ ∑ _i ∈ range H, B := by
      apply sum_le_sum
      intro i hi
      have he : |p.coeff (f i)| * r^e ≤ B :=
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (hf i hi)) (abs_nonneg _)).trans
          (abs_coeff_mul_radius_le p hr0 hB (f i))
      calc
        _ ≤ 1 * B := mul_le_mul (OAI.InternalCatalan.centralCoeffKernel_abs_le_one _)
          he (by positivity) zero_le_one
        _ = B := one_mul _
    _ = H * B := by simp

end
end CatalanMeasure.Parametric
