module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Bernstein–Szegő polynomials (strict case)

Let `h : ℝ[X]` with `h 0 = 1` and `natDegree h < 2 n`.  The polynomial
`bsPoly h n = ∑_r h_r T_{n-r}` has degree `n` and leading coefficient `2^(n-1)`
(R1), it is orthogonal to all polynomials of degree `< n` against `dθ / |h(e^{iθ})|²` in the angle
variable (R2), and at `t = -(x + 1/x)/2` it equals the explicit Laurent expression (R5).
-/

open Polynomial Polynomial.Chebyshev Finset Real

namespace CatalanMeasure.GenD.Signed

/-- `bsPoly h n = ∑_{r ≤ deg h} h_r T_{n-r}`. -/
noncomputable def bsPoly (h : ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∑ r ∈ range (h.natDegree + 1), C (h.coeff r) * T ℝ ((n : ℤ) - r)

/-! ### R5: Laurent evaluation -/

theorem T_eval_laurent (y : ℝ) (hy : y ≠ 0) (j : ℤ) :
    (T ℝ j).eval ((y + y⁻¹) / 2) = (y ^ j + y ^ (-j)) / 2 := by
  induction j using Polynomial.Chebyshev.induct' with
  | zero => simp
  | one => simp [T_one]
  | add_two n ih1 ih2 =>
    have e1 : ((n : ℤ) + 2) = ((n : ℤ) + 1) + 1 := by ring
    rw [T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, ih1, ih2]
    have h1 : y ^ ((n : ℤ) + 1) = y ^ (n : ℤ) * y := by rw [zpow_add_one₀ hy]
    have h2 : y ^ (-((n : ℤ) + 1)) = y ^ (-(n : ℤ)) * y⁻¹ := by
      rw [neg_add, zpow_add₀ hy, zpow_neg_one]
    have h3 : y ^ ((n : ℤ) + 2) = y ^ (n : ℤ) * y ^ 2 := by
      rw [zpow_add₀ hy]; norm_cast
    have h4 : y ^ (-((n : ℤ) + 2)) = y ^ (-(n : ℤ)) * (y⁻¹) ^ 2 := by
      rw [neg_add, zpow_add₀ hy]; simp [zpow_neg]
    rw [h1, h2, h3, h4]
    have : y ^ (n : ℤ) ≠ 0 := zpow_ne_zero _ hy
    field_simp
    ring
  | neg n ih =>
    rw [T_neg]
    rw [ih, neg_neg]
    ring

/-- Evaluation of `bsPoly` at `t = (y + y⁻¹)/2`. -/
theorem bsPoly_eval_laurent (h : ℝ[X]) (n : ℕ) (y : ℝ) (hy : y ≠ 0) :
    (bsPoly h n).eval ((y + y⁻¹) / 2) =
      (y ^ n * h.eval y⁻¹ + (y ^ n)⁻¹ * h.eval y) / 2 := by
  unfold bsPoly
  simp only [eval_finsetSum, eval_mul, eval_C, T_eval_laurent y hy]
  simp only [eval_eq_sum_range, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e1 : y ^ ((n : ℤ) - r) = y ^ n * (y ^ r)⁻¹ := by
    rw [zpow_sub₀ hy]; simp [div_eq_mul_inv]
  have e2 : y ^ (-((n : ℤ) - r)) = (y ^ n)⁻¹ * y ^ r := by
    rw [neg_sub, zpow_sub₀ hy]; simp [div_eq_mul_inv, mul_comm]
  rw [e1, e2, inv_pow]
  field_simp

/-! ### R1: degree and leading coefficient -/

theorem bsPoly_natDegree_and_lc (h : ℝ[X]) (h0 : h.coeff 0 = 1) (n : ℕ) (hn : 0 < n)
    (hd : h.natDegree < 2 * n) :
    (bsPoly h n).natDegree = n ∧ (bsPoly h n).leadingCoeff = 2 ^ (n - 1) := by
  have hsplit : bsPoly h n = (∑ r ∈ range h.natDegree,
      C (h.coeff (r + 1)) * T ℝ ((n : ℤ) - ((r + 1 : ℕ) : ℤ))) + T ℝ (n : ℤ) := by
    unfold bsPoly
    rw [Finset.sum_range_succ' _ h.natDegree]
    simp [h0]
  have hTn : (T ℝ (n : ℤ)).natDegree = n := by rw [natDegree_T]; simp
  have hR : (∑ r ∈ range h.natDegree,
      C (h.coeff (r + 1)) * T ℝ ((n : ℤ) - ((r + 1 : ℕ) : ℤ))).natDegree ≤ n - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro r hr
    have hr' := Finset.mem_range.mp hr
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_T]
    omega
  have hlt : (∑ r ∈ range h.natDegree,
      C (h.coeff (r + 1)) * T ℝ ((n : ℤ) - ((r + 1 : ℕ) : ℤ))).natDegree <
      (T ℝ (n : ℤ)).natDegree := by omega
  have hdeg := degree_lt_degree hlt
  rw [hsplit]
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt, hTn]
  · rw [leadingCoeff_add_of_degree_lt hdeg, leadingCoeff_T]; simp

/-! ### R2: orthogonality -/

open Complex in
/-- `|h(e^{iθ})|²`. -/
noncomputable def hAbs2 (h : ℝ[X]) (θ : ℝ) : ℝ :=
  ‖aeval (Complex.exp (θ * Complex.I)) h‖ ^ 2

open ComplexConjugate in
theorem bsPoly_eval_cos (h : ℝ[X]) (n : ℕ) (θ : ℝ) :
    (bsPoly h n).eval (Real.cos θ) =
      (Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
        conj (aeval (Complex.exp (θ * Complex.I)) h)).re := by
  rw [← Polynomial.aeval_conj, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  unfold bsPoly
  rw [eval_finsetSum, aeval_eq_sum_range, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eval_mul, eval_C, T_real_cos]
  have key : Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
      (Complex.exp (↑θ * -Complex.I)) ^ r =
      Complex.exp ((((n : ℝ) - r) * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Complex.real_smul, mul_left_comm, key, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  push_cast
  ring_nf

open ComplexConjugate in
theorem bsPoly_div_eq_re (h : ℝ[X]) (n : ℕ) (θ : ℝ)
    (hne : aeval (Complex.exp (θ * Complex.I)) h ≠ 0) :
    (bsPoly h n).eval (Real.cos θ) / hAbs2 h θ =
      (Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) /
        aeval (Complex.exp (θ * Complex.I)) h).re := by
  set a := aeval (Complex.exp (θ * Complex.I)) h with ha
  set z := Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)
  have hc : conj a ≠ 0 := by simpa using hne
  have : z / a = (z * conj a) / ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    have h2 : (((‖a‖ ^ 2 : ℝ)) : ℂ) = a * conj a := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [h2]; field_simp
  rw [this, Complex.div_ofReal_re, bsPoly_eval_cos]
  rfl

/-- Evenness: `|h(e^{i(2π-θ)})| = |h(e^{iθ})|`. -/
theorem hAbs2_two_pi_sub (h : ℝ[X]) (θ : ℝ) : hAbs2 h (2 * π - θ) = hAbs2 h θ := by
  unfold hAbs2
  have : Complex.exp (((2 * π - θ : ℝ) : ℂ) * Complex.I) =
      starRingEnd ℂ (Complex.exp (θ * Complex.I)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (((2 * π - θ : ℝ) : ℂ) * Complex.I) = (θ * -Complex.I) + (2 * π * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [this, Polynomial.aeval_conj, Complex.norm_conj]

theorem eval_cos_two_pi_sub (p : ℝ[X]) (θ : ℝ) :
    p.eval (Real.cos (2 * π - θ)) = p.eval (Real.cos θ) := by
  rw [Real.cos_two_pi_sub]

/-- The holomorphic kernel of the orthogonality proof. -/
noncomputable def orthoKernel (h : ℝ[X]) (i m : ℕ) (w : ℂ) : ℂ :=
  w ^ m * (w ^ 2 + 1) ^ i / (2 ^ i * aeval w h)

theorem differentiable_aeval_complex (h : ℝ[X]) : Differentiable ℂ fun w : ℂ => aeval w h :=
  Polynomial.differentiable_aeval (𝕜 := ℂ) h

theorem orthoKernel_diffContOnCl (h : ℝ[X])
    (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) (i m : ℕ) :
    DiffContOnCl ℂ (orthoKernel h i m) (Metric.ball (0 : ℂ) 1) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball _ one_ne_zero]
  unfold orthoKernel
  apply DifferentiableOn.div
  · fun_prop
  · exact ((differentiable_aeval_complex h).const_mul _ : Differentiable ℂ fun w : ℂ => (2 : ℂ) ^ i * aeval w h).differentiableOn
  · intro w hw
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
      (hnz w (by simpa using hw))

theorem integral_ortho_complex (h : ℝ[X])
    (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) (i m : ℕ) :
    ∫ θ in (0 : ℝ)..(2 * π),
      Complex.exp (θ * Complex.I) * orthoKernel h i m (Complex.exp (θ * Complex.I)) = 0 := by
  have h0 := (orthoKernel_diffContOnCl h hnz i m).circleIntegral_eq_zero zero_le_one
  rw [circleIntegral] at h0
  simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, Complex.ofReal_one, one_mul] at h0
  have : ∀ θ : ℝ, Complex.exp (θ * Complex.I) * orthoKernel h i m (Complex.exp (θ * Complex.I)) =
      Complex.I⁻¹ * (Complex.exp (θ * Complex.I) * Complex.I *
        orthoKernel h i m (Complex.exp (θ * Complex.I))) := by
    intro θ; field_simp
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, h0, mul_zero]

theorem orthoKernel_continuousOn (h : ℝ[X])
    (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) (i m : ℕ) :
    ContinuousOn (orthoKernel h i m) (Metric.closedBall (0 : ℂ) 1) := by
  have := (orthoKernel_diffContOnCl h hnz i m).continuousOn
  rwa [closure_ball _ one_ne_zero] at this

theorem psi_identity (z a : ℂ) (hz : z ≠ 0) (ha : a ≠ 0) (i m : ℕ) :
    z * (z ^ m * (z ^ 2 + 1) ^ i / (2 ^ i * a)) =
      ((z + z⁻¹) / 2) ^ i * (z ^ (i + m + 1) / a) := by
  have e : (z + z⁻¹) / 2 = (z ^ 2 + 1) / (2 * z) := by field_simp
  rw [e, div_pow, mul_pow]
  field_simp
  ring

/-- **R2.** For `i < n` the polynomial `bsPoly h n` is orthogonal to `cos^i` against `dθ/|h|²`
on `[0, π]`. -/
theorem bsPoly_orthogonal (h : ℝ[X]) (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0)
    (n i : ℕ) (hin : i < n) :
    ∫ θ in (0 : ℝ)..π, (bsPoly h n).eval (Real.cos θ) * Real.cos θ ^ i / hAbs2 h θ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = i + m + 1 := ⟨n - i - 1, by omega⟩
  set A : ℝ → ℝ := fun θ => (bsPoly h (i + m + 1)).eval (Real.cos θ) * Real.cos θ ^ i / hAbs2 h θ
    with hAdef
  set Ψ : ℝ → ℂ := fun θ => Complex.exp (θ * Complex.I) *
    orthoKernel h i m (Complex.exp (θ * Complex.I)) with hΨdef
  have hnorm : ∀ θ : ℝ, ‖Complex.exp (θ * Complex.I)‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
  have hA : ∀ θ, A θ = (Ψ θ).re := by
    intro θ
    have hzne : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hane : aeval (Complex.exp (θ * Complex.I)) h ≠ 0 := hnz _ (le_of_eq (hnorm θ))
    have hcos : (Real.cos θ : ℂ) = (Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos, ← Complex.exp_neg, neg_mul]
    have hexp : Complex.exp (((((i + m + 1 : ℕ) : ℝ)) * θ : ℝ) * Complex.I) =
        (Complex.exp (θ * Complex.I)) ^ (i + m + 1) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hΨ : Ψ θ = (Real.cos θ : ℂ) ^ i *
        (Complex.exp (((((i + m + 1 : ℕ) : ℝ)) * θ : ℝ) * Complex.I) /
          aeval (Complex.exp (θ * Complex.I)) h) := by
      simp only [hΨdef, orthoKernel]
      rw [hexp, hcos]
      exact psi_identity _ _ hzne hane i m
    have hre := bsPoly_div_eq_re h (i + m + 1) θ hane
    rw [hΨ, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← hre]
    simp only [hAdef]
    ring
  have hΨcont : Continuous Ψ := by
    have hc : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by fun_prop
    have hk : Continuous fun θ : ℝ => orthoKernel h i m (Complex.exp (θ * Complex.I)) :=
      (orthoKernel_continuousOn h hnz i m).comp_continuous hc
        (fun θ => by simp)
    exact hc.mul hk
  have hAcont : Continuous A := by
    have : A = fun θ => (Ψ θ).re := funext hA
    rw [this]; exact Complex.continuous_re.comp hΨcont
  have hAeven : ∀ θ, A (2 * π - θ) = A θ := by
    intro θ
    simp only [hAdef, hAbs2_two_pi_sub, Real.cos_two_pi_sub]
  have hint0 : ∫ θ in (0 : ℝ)..(2 * π), A θ = 0 := by
    have hΨint : IntervalIntegrable Ψ MeasureTheory.volume 0 (2 * π) :=
      hΨcont.intervalIntegrable _ _
    have := Complex.reCLM.intervalIntegral_comp_comm hΨint
    simp only [Complex.reCLM_apply] at this
    simp_rw [hA]
    rw [this, integral_ortho_complex h hnz i m]
    simp
  have hsplit : ∫ θ in (0 : ℝ)..(2 * π), A θ =
      (∫ θ in (0 : ℝ)..π, A θ) + ∫ θ in π..(2 * π), A θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hAcont.intervalIntegrable _ _)
      (hAcont.intervalIntegrable _ _)).symm
  have hrefl : ∫ θ in π..(2 * π), A θ = ∫ θ in (0 : ℝ)..π, A θ := by
    have := intervalIntegral.integral_comp_sub_left (a := π) (b := 2 * π) A (2 * π)
    simp only [hAeven] at this
    rw [this]
    congr 1 <;> ring
  rw [hsplit, hrefl] at hint0
  show ∫ θ in (0 : ℝ)..π, A θ = 0
  linarith

end CatalanMeasure.GenD.Signed

#print axioms CatalanMeasure.GenD.Signed.bsPoly_natDegree_and_lc
#print axioms CatalanMeasure.GenD.Signed.bsPoly_eval_laurent
#print axioms CatalanMeasure.GenD.Signed.bsPoly_orthogonal
