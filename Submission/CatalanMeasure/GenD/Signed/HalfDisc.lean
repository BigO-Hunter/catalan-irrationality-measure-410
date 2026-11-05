module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Half-disc contour integrals by primitives

The closed half-disc contour integral of a function holomorphic on a ball of radius `R > 1` vanishes.
The proof avoids the residue theorem: a holomorphic function on a ball has a primitive
(`DifferentiableOn.isExactOn_ball`), and each of the two pieces of the contour (a unit-circle arc and
a diameter) is evaluated by the fundamental theorem of calculus, so the four endpoint values cancel.

The "primitive" versions are stated for a function `f` with a primitive `G` on an arbitrary set `S`
containing the contour; they are used for the logarithm primitives of `1 / (z - a)`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Complex Set intervalIntegral Metric

/-! ### Derivatives of the parametrisations -/

theorem hasDerivAt_cexp_mul_I (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
  have := h1.cexp
  simpa [mul_comm] using this

theorem hasDerivAt_ofReal_mul_I (y : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I y := by
  simpa using (hasDerivAt_id y).ofReal_comp.mul_const Complex.I

/-! ### Fundamental theorem of calculus along the contour pieces -/

/-- Integrability of a continuous function along a unit-circle arc. -/
theorem intervalIntegrable_arc {f : ℂ → ℂ} {S : Set ℂ} (hf : ContinuousOn f S) {a b : ℝ}
    (hS : ∀ θ ∈ uIcc a b, Complex.exp ((θ : ℂ) * Complex.I) ∈ S) :
    IntervalIntegrable (fun θ : ℝ => f (Complex.exp ((θ : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hc : ContinuousOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (uIcc a b) := by
    fun_prop
  exact (hf.comp hc hS).mul (by fun_prop)

/-- Integrability of a continuous function along a segment of the imaginary axis. -/
theorem intervalIntegrable_imagSeg {f : ℂ → ℂ} {S : Set ℂ} (hf : ContinuousOn f S) {a b : ℝ}
    (hS : ∀ y ∈ uIcc a b, (y : ℂ) * Complex.I ∈ S) :
    IntervalIntegrable (fun y : ℝ => f ((y : ℂ) * Complex.I) * Complex.I)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hc : ContinuousOn (fun y : ℝ => (y : ℂ) * Complex.I) (uIcc a b) := by fun_prop
  exact (hf.comp hc hS).mul continuousOn_const

/-- FTC along a unit-circle arc. -/
theorem integral_arc_eq_sub {f G : ℂ → ℂ} {S : Set ℂ} (hG : ∀ z ∈ S, HasDerivAt G (f z) z)
    (hf : ContinuousOn f S) {a b : ℝ}
    (hS : ∀ θ ∈ uIcc a b, Complex.exp ((θ : ℂ) * Complex.I) ∈ S) :
    ∫ θ in a..b, f (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) =
      G (Complex.exp ((b : ℂ) * Complex.I)) - G (Complex.exp ((a : ℂ) * Complex.I)) := by
  apply integral_eq_sub_of_hasDerivAt (f := fun θ : ℝ => G (Complex.exp ((θ : ℂ) * Complex.I)))
  · intro θ hθ
    have h := (hG _ (hS θ hθ)).scomp θ (hasDerivAt_cexp_mul_I θ)
    rw [smul_eq_mul] at h
    exact h.congr_deriv (by ring)
  · apply ContinuousOn.intervalIntegrable
    have hc : ContinuousOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (uIcc a b) := by
      fun_prop
    exact (hf.comp hc hS).mul (by fun_prop)

/-- FTC along a vertical segment of the imaginary axis. -/
theorem integral_imagSeg_eq_sub {f G : ℂ → ℂ} {S : Set ℂ} (hG : ∀ z ∈ S, HasDerivAt G (f z) z)
    (hf : ContinuousOn f S) {a b : ℝ} (hS : ∀ y ∈ uIcc a b, (y : ℂ) * Complex.I ∈ S) :
    ∫ y in a..b, f ((y : ℂ) * Complex.I) * Complex.I =
      G ((b : ℂ) * Complex.I) - G ((a : ℂ) * Complex.I) := by
  apply integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => G ((y : ℂ) * Complex.I))
  · intro y hy
    have h := (hG _ (hS y hy)).scomp y (hasDerivAt_ofReal_mul_I y)
    rw [smul_eq_mul] at h
    exact h.congr_deriv (by ring)
  · apply ContinuousOn.intervalIntegrable
    have hc : ContinuousOn (fun y : ℝ => (y : ℂ) * Complex.I) (uIcc a b) := by fun_prop
    exact (hf.comp hc hS).mul continuousOn_const

/-- FTC along a segment of the real axis. -/
theorem integral_realSeg_eq_sub {f G : ℂ → ℂ} {S : Set ℂ} (hG : ∀ z ∈ S, HasDerivAt G (f z) z)
    (hf : ContinuousOn f S) {a b : ℝ} (hS : ∀ y ∈ uIcc a b, (y : ℂ) ∈ S) :
    ∫ y in a..b, f (y : ℂ) = G (b : ℂ) - G (a : ℂ) := by
  apply integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => G (y : ℂ))
  · intro y hy
    exact (hG _ (hS y hy)).comp_ofReal
  · apply ContinuousOn.intervalIntegrable
    have hc : ContinuousOn (fun y : ℝ => (y : ℂ)) (uIcc a b) := by fun_prop
    exact hf.comp hc hS

/-! ### Values of the exponential at the contour endpoints -/

theorem cexp_pi_div_two_mul_I :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

theorem cexp_neg_pi_div_two_mul_I :
    Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

theorem cexp_three_pi_div_two_mul_I :
    Complex.exp (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h1 : Real.cos (3 * Real.pi / 2) = 0 := by
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.cos_add_pi]; simp
  have h2 : Real.sin (3 * Real.pi / 2) = -1 := by
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.sin_add_pi]; simp
  rw [h1, h2]; simp

theorem cexp_pi_mul_I' : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-! ### Half-disc contour integrals -/

/-- The right half-disc contour (arc from `-i` to `i`, then the diameter from `i` to `-i`) for a
function with a primitive on a set `S` containing the contour. -/
theorem halfDisc_right_integral_eq_zero_of_primitive {f G : ℂ → ℂ} {S : Set ℂ}
    (hG : ∀ z ∈ S, HasDerivAt G (f z) z) (hf : ContinuousOn f S)
    (harc : ∀ θ ∈ uIcc (-(Real.pi / 2)) (Real.pi / 2), Complex.exp ((θ : ℂ) * Complex.I) ∈ S)
    (hseg : ∀ y ∈ uIcc (1 : ℝ) (-1), (y : ℂ) * Complex.I ∈ S) :
    (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), f (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) +
      (∫ y in (1 : ℝ)..(-1), f ((y : ℂ) * Complex.I) * Complex.I) = 0 := by
  rw [integral_arc_eq_sub hG hf harc, integral_imagSeg_eq_sub hG hf hseg,
    cexp_pi_div_two_mul_I, cexp_neg_pi_div_two_mul_I]
  simp

/-- The left half-disc contour (arc from `i` to `-i` through `-1`, then the diameter from `-i`
to `i`) for a function with a primitive on a set `S` containing the contour. -/
theorem halfDisc_left_integral_eq_zero_of_primitive {f G : ℂ → ℂ} {S : Set ℂ}
    (hG : ∀ z ∈ S, HasDerivAt G (f z) z) (hf : ContinuousOn f S)
    (harc : ∀ θ ∈ uIcc (Real.pi / 2) (3 * Real.pi / 2),
      Complex.exp ((θ : ℂ) * Complex.I) ∈ S)
    (hseg : ∀ y ∈ uIcc (-1 : ℝ) 1, (y : ℂ) * Complex.I ∈ S) :
    (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), f (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) +
      (∫ y in (-1 : ℝ)..1, f ((y : ℂ) * Complex.I) * Complex.I) = 0 := by
  rw [integral_arc_eq_sub hG hf harc, integral_imagSeg_eq_sub hG hf hseg,
    cexp_pi_div_two_mul_I, cexp_three_pi_div_two_mul_I]
  simp

/-- The upper half-disc contour (the diameter from `-1` to `1`, then the arc from `1` to `-1`)
for a function with a primitive on a set `S` containing the contour. -/
theorem halfDisc_upper_integral_eq_zero_of_primitive {f G : ℂ → ℂ} {S : Set ℂ}
    (hG : ∀ z ∈ S, HasDerivAt G (f z) z) (hf : ContinuousOn f S)
    (harc : ∀ θ ∈ uIcc (0 : ℝ) Real.pi, Complex.exp ((θ : ℂ) * Complex.I) ∈ S)
    (hseg : ∀ y ∈ uIcc (-1 : ℝ) 1, (y : ℂ) ∈ S) :
    (∫ y in (-1 : ℝ)..1, f (y : ℂ)) +
      (∫ θ in (0 : ℝ)..Real.pi, f (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) = 0 := by
  rw [integral_arc_eq_sub hG hf harc, integral_realSeg_eq_sub hG hf hseg, cexp_pi_mul_I']
  simp

/-! ### Holomorphic functions on a larger ball -/

/-- T3, right half-disc: the closed right half-disc contour integral of a function holomorphic on
`ball 0 R`, `R > 1`, is `0`. -/
theorem halfDisc_right_integral_eq_zero {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) :
    (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), f (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) +
      (∫ y in (1 : ℝ)..(-1), f ((y : ℂ) * Complex.I) * Complex.I) = 0 := by
  obtain ⟨G, hG⟩ := hf.isExactOn_ball
  refine halfDisc_right_integral_eq_zero_of_primitive hG hf.continuousOn ?_ ?_
  · intro θ _
    simp only [mem_ball, dist_zero_right, Complex.norm_exp_ofReal_mul_I]
    exact hR
  · intro y hy
    have hy' : |y| ≤ 1 := by
      rw [uIcc_of_ge (by norm_num)] at hy
      rw [abs_le]; exact ⟨hy.1, hy.2⟩
    simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    linarith

/-- T3, upper half-disc: the closed upper half-disc contour integral of a function holomorphic on
`ball 0 R`, `R > 1`, is `0`. -/
theorem halfDisc_upper_integral_eq_zero {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) :
    (∫ y in (-1 : ℝ)..1, f (y : ℂ)) +
      (∫ θ in (0 : ℝ)..Real.pi, f (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) = 0 := by
  obtain ⟨G, hG⟩ := hf.isExactOn_ball
  refine halfDisc_upper_integral_eq_zero_of_primitive hG hf.continuousOn ?_ ?_
  · intro θ _
    simp only [mem_ball, dist_zero_right, Complex.norm_exp_ofReal_mul_I]
    exact hR
  · intro y hy
    have hy' : |y| ≤ 1 := by
      rw [uIcc_of_le (by norm_num)] at hy
      rw [abs_le]; exact ⟨hy.1, hy.2⟩
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    linarith

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.halfDisc_right_integral_eq_zero
#print axioms CatalanMeasure.Signed.halfDisc_upper_integral_eq_zero

