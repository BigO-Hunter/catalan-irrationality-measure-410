module

public import Submission.CatalanMeasure.GenD.Signed.HalfDisc
public import Submission.OAI.NumberTheory.Catalan.Energy.FirstSheetReproducingKernel
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Lemma T (Loewner form)

Let `x : Fin n → ℝ` be injective with `0 < |x a| < 1`, `B(z) = ∏ (z - x a) / (1 - x a z)` and
`K a b = 1 / (1 - x a x b)`.  If `|y|^e ≤ M ‖B(i y)‖` on `[-1, 1]`, then for every real vector `c`
`|∑_{a, x a > 0} B'(x a) (x a)^e (c a)^2| ≤ (1 + M/2) ∑_{a,b} c a c b K a b`.

Proof (no residue theorem): the function `F(z) = z^e ψ(z)^2 / B(z)` with `ψ = B ∑ c_a/(z - x_a)` has
simple poles at the nodes; subtracting them with `dslope` leaves a function holomorphic on a ball of
radius `R > 1`, whose half-disc contour integral vanishes by `HalfDisc`.  The contour integral of
the pole terms is computed from logarithm primitives and the Cauchy integral on the circle.  The arc
is bounded by the Szegő reproducing identity, the diameter by a Fejér–Riesz argument that uses the
same half-disc lemma on the upper half-disc.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Complex Set intervalIntegral Metric Finset
open scoped ComplexConjugate

noncomputable section

section Algebra

variable {n : ℕ}

/-- The finite Blaschke product `B(z) = ∏ (z - x a) / (1 - x a z)`. -/
def blaschke (x : Fin n → ℝ) (z : ℂ) : ℂ := ∏ a, (z - (x a : ℂ)) / (1 - (x a : ℂ) * z)

/-- `B'(x a)` as an explicit product (see `hasDerivAt_blaschke`). -/
def bDeriv (x : Fin n → ℝ) (a : Fin n) : ℝ :=
  (∏ b ∈ univ.erase a, (x a - x b)) / ∏ b, (1 - x b * x a)

/-- Numerator `∏ (z - x a)` of `B`. -/
def bN (x : Fin n → ℝ) (z : ℂ) : ℂ := ∏ a, (z - (x a : ℂ))

/-- Denominator `∏ (1 - x a z)` of `B`. -/
def bD (x : Fin n → ℝ) (z : ℂ) : ℂ := ∏ a, (1 - (x a : ℂ) * z)

/-- `∏_{b ≠ a} (z - x b)`. -/
def bNe (x : Fin n → ℝ) (a : Fin n) (z : ℂ) : ℂ := ∏ b ∈ univ.erase a, (z - (x b : ℂ))

/-- Numerator `∑ c a ∏_{b ≠ a}(z - x b)` of `ψ`. -/
def bS (x c : Fin n → ℝ) (z : ℂ) : ℂ := ∑ a, (c a : ℂ) * bNe x a z

/-- `ψ(z) = B(z) ∑ c a / (z - x a)`, written without poles. -/
def psi (x c : Fin n → ℝ) (z : ℂ) : ℂ := bS x c z / bD x z

/-- `F(z) = z^e ψ(z)^2 / B(z)`, written as `z^e S^2 / (D N)`. -/
def Ffun (x c : Fin n → ℝ) (e : ℕ) (z : ℂ) : ℂ := z ^ e * bS x c z ^ 2 / (bD x z * bN x z)

variable (x c : Fin n → ℝ)

theorem blaschke_eq (z : ℂ) : blaschke x z = bN x z / bD x z := by
  simp [blaschke, bN, bD, Finset.prod_div_distrib]

theorem bN_eq_mul_bNe (a : Fin n) (z : ℂ) : bN x z = (z - (x a : ℂ)) * bNe x a z :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

theorem bNe_ne_zero (hx : Function.Injective x) (a : Fin n) :
    bNe x a (x a : ℂ) ≠ 0 := by
  unfold bNe
  rw [Finset.prod_ne_zero_iff]
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  intro h
  apply hba
  apply hx
  have := sub_eq_zero.mp h
  exact_mod_cast this.symm

theorem bNe_node_of_ne {a b : Fin n} (hab : b ≠ a) : bNe x a (x b : ℂ) = 0 := by
  unfold bNe
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ b⟩) (sub_self _)

theorem bS_node (a : Fin n) : bS x c (x a : ℂ) = (c a : ℂ) * bNe x a (x a : ℂ) := by
  unfold bS
  rw [Finset.sum_eq_single a]
  · intro b _ hba
    rw [bNe_node_of_ne x hba.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem bDeriv_eq (a : Fin n) :
    (bDeriv x a : ℂ) = bNe x a (x a : ℂ) / bD x (x a : ℂ) := by
  unfold bDeriv bNe bD
  push_cast
  simp

theorem exists_radius (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) :
    ∃ R : ℝ, 1 < R ∧ ∀ a, |x a| * R < 1 := by
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨a0, ha0⟩ := Finite.exists_max (fun a => |x a|)
    have hpos : 0 < |x a0| := abs_pos.mpr (hx0 a0)
    have hlt : |x a0| < 1 := hx1 a0
    refine ⟨(1 + |x a0|⁻¹) / 2, ?_, ?_⟩
    · have : 1 < |x a0|⁻¹ := by
        rw [lt_inv_comm₀ one_pos hpos]; simpa using hlt
      linarith
    · intro a
      have h1 : |x a| * ((1 + |x a0|⁻¹) / 2) ≤ |x a0| * ((1 + |x a0|⁻¹) / 2) :=
        mul_le_mul_of_nonneg_right (ha0 a) (by positivity)
      have h2 : |x a0| * ((1 + |x a0|⁻¹) / 2) = (|x a0| + 1) / 2 := by
        field_simp
      linarith
  · refine ⟨2, by norm_num, fun a => (hn ⟨a⟩).elim⟩

theorem bD_ne_zero {R : ℝ} (hR : ∀ a, |x a| * R < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    bD x z ≠ 0 := by
  unfold bD
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have h1 : (x a : ℂ) * z = 1 := by rw [sub_eq_zero] at h; exact h.symm
  have h2 : ‖(x a : ℂ) * z‖ = |x a| * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h3 : ‖z‖ < R := by simpa using hz
  have h4 : |x a| * ‖z‖ ≤ |x a| * R := mul_le_mul_of_nonneg_left h3.le (abs_nonneg _)
  rw [h1, norm_one] at h2
  have := hR a
  linarith

end Algebra

section Division

variable {n : ℕ}

theorem exists_eq_prod_mul {ι : Type*} [DecidableEq ι] {R : ℝ} (A : Finset ι) (p : ι → ℂ)
    (hp : ∀ i ∈ A, p i ∈ ball (0 : ℂ) R) (hinj : ∀ i ∈ A, ∀ j ∈ A, p i = p j → i = j)
    (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h (ball 0 R)) (h0 : ∀ i ∈ A, h (p i) = 0) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) R, h z = (∏ i ∈ A, (z - p i)) * q z := by
  induction A using Finset.induction_on generalizing h with
  | empty => exact ⟨h, hh, by simp⟩
  | insert i A hi ih =>
    have hpi := hp i (Finset.mem_insert_self i A)
    have hd : DifferentiableOn ℂ (dslope h (p i)) (ball 0 R) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hpi)).mpr hh
    obtain ⟨q, hq, hqe⟩ := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hinj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (dslope h (p i)) hd (by
        intro j hj
        have hne : p j ≠ p i := by
          intro hEq
          have := hinj j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i A) hEq
          exact hi (this ▸ hj)
        rw [dslope_of_ne _ hne, slope_def_field, h0 j (Finset.mem_insert_of_mem hj),
          h0 i (Finset.mem_insert_self i A)]
        simp)
    refine ⟨q, hq, fun z hz => ?_⟩
    have h1 : (z - p i) • dslope h (p i) z = h z - h (p i) := sub_smul_dslope h (p i) z
    rw [h0 i (Finset.mem_insert_self i A), sub_zero, smul_eq_mul] at h1
    rw [Finset.prod_insert hi, ← h1, hqe z hz]
    ring

variable (x c : Fin n → ℝ)

theorem real_mem_ball {R : ℝ} (hR1 : 1 < R) (hx1 : ∀ a, |x a| < 1) (a : Fin n) :
    (x a : ℂ) ∈ ball (0 : ℂ) R := by
  simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  linarith [hx1 a]

/-- The pole subtraction (T4): `F` minus its simple poles is holomorphic on `ball 0 R`. -/
theorem Ffun_decomp (hxi : Function.Injective x) (hx1 : ∀ a, |x a| < 1) {R : ℝ} (hR1 : 1 < R)
    (hR : ∀ a, |x a| * R < 1) (e : ℕ) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) R, (∀ a, z ≠ (x a : ℂ)) →
        Ffun x c e z = ∑ a, ((x a : ℂ) ^ e * (c a : ℂ) ^ 2 * (bDeriv x a : ℂ)) * (z - x a)⁻¹ +
          q z := by
  classical
  set g : ℂ → ℂ := fun z => z ^ e * bS x c z ^ 2 / bD x z with hg
  set r : Fin n → ℂ := fun a => g (x a) / bNe x a (x a) with hr
  set L : ℂ → ℂ := fun z => ∑ a, r a * bNe x a z with hL
  have hDne : ∀ z ∈ ball (0 : ℂ) R, bD x z ≠ 0 := fun z hz => bD_ne_zero x hR hz
  have hgd : DifferentiableOn ℂ g (ball 0 R) := by
    apply DifferentiableOn.div
    · unfold bS bNe; fun_prop
    · unfold bD; fun_prop
    · exact hDne
  have hLd : Differentiable ℂ L := by
    show Differentiable ℂ (fun z => ∑ a, r a * bNe x a z)
    unfold bNe; fun_prop
  have hhd : DifferentiableOn ℂ (fun z => g z - L z) (ball 0 R) := hgd.sub hLd.differentiableOn
  have h0 : ∀ b ∈ (Finset.univ : Finset (Fin n)), (fun z => g z - L z) (x b : ℂ) = 0 := by
    intro b _
    have hLb : L (x b : ℂ) = g (x b) := by
      simp only [hL]
      rw [Finset.sum_eq_single b]
      · simp only [hr]
        exact div_mul_cancel₀ _ (bNe_ne_zero x hxi b)
      · intro a _ hab
        rw [bNe_node_of_ne x (Ne.symm hab), mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    simp [hLb]
  obtain ⟨q, hq, hqe⟩ := exists_eq_prod_mul Finset.univ (fun a => (x a : ℂ))
    (fun a _ => real_mem_ball x hR1 hx1 a)
    (fun i _ j _ hij => hxi (by exact_mod_cast hij)) _ hhd h0
  refine ⟨q, hq, fun z hz hzn => ?_⟩
  have hN : bN x z ≠ 0 := by
    unfold bN; rw [Finset.prod_ne_zero_iff]; intro a _; exact sub_ne_zero.mpr (hzn a)
  have hqz : g z - L z = (∏ i ∈ Finset.univ, (z - (x i : ℂ))) * q z := hqe z hz
  have hgz : g z = L z + bN x z * q z := by
    have : bN x z = ∏ i ∈ Finset.univ, (z - (x i : ℂ)) := rfl
    rw [← this] at hqz
    linear_combination hqz
  have hF : Ffun x c e z = g z / bN x z := by
    simp only [Ffun, hg]; rw [div_div]
  rw [hF, hgz, add_div, mul_div_cancel_left₀ _ hN]
  congr 1
  simp only [hL, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hNe : bNe x a z ≠ 0 := by
    unfold bNe; rw [Finset.prod_ne_zero_iff]
    intro b hb; exact sub_ne_zero.mpr (hzn b)
  have hza : z - (x a : ℂ) ≠ 0 := sub_ne_zero.mpr (hzn a)
  -- residue
  have hNa : bNe x a (x a : ℂ) ≠ 0 := bNe_ne_zero x hxi a
  have hDa : bD x (x a : ℂ) ≠ 0 := hDne _ (real_mem_ball x hR1 hx1 a)
  have hra : r a = (x a : ℂ) ^ e * (c a : ℂ) ^ 2 * (bDeriv x a : ℂ) := by
    simp only [hr, hg, bS_node x c a, bDeriv_eq x a]
    field_simp
  rw [hra, bN_eq_mul_bNe x a z]
  field_simp

end Division

section PoleTerms

/-- The arc part of the right half-disc contour integral. -/
def arcInt (h : ℂ → ℂ) : ℂ :=
  ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
    h (Complex.exp ((θ : ℂ) * Complex.I)) * (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))

/-- The diameter part (from `i` to `-i`) of the right half-disc contour integral. -/
def segInt (h : ℂ → ℂ) : ℂ := ∫ y in (1 : ℝ)..(-1), h ((y : ℂ) * Complex.I) * Complex.I

/-- The right half-disc contour integral. -/
def contour (h : ℂ → ℂ) : ℂ := arcInt h + segInt h

theorem contour_pole_neg {x : ℝ} (hx : x < 0) :
    contour (fun z => (z - (x : ℂ))⁻¹) = 0 := by
  set S : Set ℂ := {z | 0 < z.re - x} with hS
  have hne : ∀ z ∈ S, z - (x : ℂ) ≠ 0 := by
    intro z hz h
    have h1 := congrArg Complex.re h
    have hz' : 0 < z.re - x := hz
    simp at h1
    linarith
  have hG : ∀ z ∈ S, HasDerivAt (fun z => Complex.log (z - (x : ℂ))) ((z - (x : ℂ))⁻¹) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => z - (x : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
    have hs : z - (x : ℂ) ∈ slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using (show 0 < z.re - x from hz)))
    simpa using h1.clog hs
  have hf : ContinuousOn (fun z : ℂ => (z - (x : ℂ))⁻¹) S :=
    ContinuousOn.inv₀ (by fun_prop) hne
  have key := halfDisc_right_integral_eq_zero_of_primitive hG hf ?_ ?_
  · exact key
  · intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    show 0 < (Complex.exp ((θ : ℂ) * Complex.I)).re - x
    rw [Complex.exp_ofReal_mul_I_re]
    have := Real.cos_nonneg_of_mem_Icc hθ
    linarith
  · intro y _
    show 0 < ((y : ℂ) * Complex.I).re - x
    simp
    linarith

theorem contour_pole_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    contour (fun z => (z - (x : ℂ))⁻¹) = 2 * Real.pi * Complex.I := by
  have hxn : ∀ z : ℂ, ‖z‖ = 1 → z - (x : ℂ) ≠ 0 := by
    intro z hz h
    have : z = (x : ℂ) := sub_eq_zero.mp h
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at hz
    linarith
  set Sx : Set ℂ := {z | z - (x : ℂ) ≠ 0} with hSx
  have hfc : ContinuousOn (fun z : ℂ => (z - (x : ℂ))⁻¹) Sx :=
    ContinuousOn.inv₀ (by fun_prop) (fun z hz => hz)
  have harcS : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ Sx := by
    intro θ
    exact hxn _ (Complex.norm_exp_ofReal_mul_I θ)
  -- left half-disc: logarithm primitive of `(z - x)⁻¹` is `log (x - z)`
  set S : Set ℂ := {z | 0 < x - z.re} with hS
  have hne : ∀ z ∈ S, (x : ℂ) - z ≠ 0 := by
    intro z hz h
    have h1 := congrArg Complex.re h
    have hz' : 0 < x - z.re := hz
    simp at h1
    linarith
  have hG : ∀ z ∈ S, HasDerivAt (fun z => Complex.log ((x : ℂ) - z)) ((z - (x : ℂ))⁻¹) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => (x : ℂ) - z) (-1) z := (hasDerivAt_id z).const_sub _
    have hs : (x : ℂ) - z ∈ slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using (show 0 < x - z.re from hz)))
    have h2 := h1.clog hs
    have h3 : (-1 : ℂ) / ((x : ℂ) - z) = (z - (x : ℂ))⁻¹ := by
      have h4 : z - (x : ℂ) = -((x : ℂ) - z) := by ring
      rw [h4, inv_neg, neg_div, one_div]
    rw [h3] at h2
    exact h2
  have hfS : ContinuousOn (fun z : ℂ => (z - (x : ℂ))⁻¹) S := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro z hz h
    exact hne z hz (by rw [← neg_sub, h, neg_zero])
  have hleft := halfDisc_left_integral_eq_zero_of_primitive hG hfS ?_ ?_
  swap
  · intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    show 0 < x - (Complex.exp ((θ : ℂ) * Complex.I)).re
    rw [Complex.exp_ofReal_mul_I_re]
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2, Real.pi_pos])
    linarith
  swap
  · intro y _
    show 0 < x - ((y : ℂ) * Complex.I).re
    simp
    linarith
  -- the full circle
  have hmem : (x : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp [abs_of_pos hx, hx1]
  have hcirc0 := circleIntegral.integral_sub_inv_of_mem_ball hmem
  unfold circleIntegral at hcirc0
  simp only [deriv_circleMap, circleMap_zero, Complex.ofReal_one, one_mul, smul_eq_mul] at hcirc0
  have hper : Function.Periodic (fun θ : ℝ => (Complex.exp ((θ : ℂ) * Complex.I) - (x : ℂ))⁻¹ *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) (2 * Real.pi) := by
    intro θ
    have : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    simp only [this]
  have hcirc : ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
      (Complex.exp ((θ : ℂ) * Complex.I) - (x : ℂ))⁻¹ *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) = 2 * Real.pi * Complex.I := by
    have h1 := hper.intervalIntegral_add_eq (-(Real.pi / 2)) 0
    have e1 : -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
    rw [e1, zero_add] at h1
    rw [h1, ← hcirc0]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    ring
  have hI1 := intervalIntegrable_arc hfc (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (fun θ _ => harcS θ)
  have hI2 := intervalIntegrable_arc hfc (a := Real.pi / 2) (b := 3 * Real.pi / 2)
    (fun θ _ => harcS θ)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  rw [hcirc] at hsplit
  have hs := intervalIntegral.integral_symm (μ := MeasureTheory.volume)
    (f := fun y : ℝ => ((y : ℂ) * Complex.I - (x : ℂ))⁻¹ * Complex.I) (1 : ℝ) (-1)
  unfold contour arcInt segInt
  beta_reduce
  linear_combination hsplit - hleft + hs

end PoleTerms

section ContourLinear

theorem contour_congr {f g : ℂ → ℂ} {S : Set ℂ} (h : ∀ z ∈ S, f z = g z)
    (harc : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ S)
    (hseg : ∀ y ∈ uIcc (1 : ℝ) (-1), (y : ℂ) * Complex.I ∈ S) : contour f = contour g := by
  unfold contour arcInt segInt
  congr 1
  · apply intervalIntegral.integral_congr
    intro θ _
    simp only [h _ (harc θ)]
  · apply intervalIntegral.integral_congr
    intro y hy
    simp only [h _ (hseg y hy)]

theorem contour_add {f g : ℂ → ℂ} {S : Set ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (harc : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ S)
    (hseg : ∀ y ∈ uIcc (1 : ℝ) (-1), (y : ℂ) * Complex.I ∈ S) :
    contour (fun z => f z + g z) = contour f + contour g := by
  unfold contour arcInt segInt
  have h1 := intervalIntegrable_arc hf (a := -(Real.pi / 2)) (b := Real.pi / 2) (fun θ _ => harc θ)
  have h2 := intervalIntegrable_arc hg (a := -(Real.pi / 2)) (b := Real.pi / 2) (fun θ _ => harc θ)
  have h3 := intervalIntegrable_imagSeg hf (a := 1) (b := -1) hseg
  have h4 := intervalIntegrable_imagSeg hg (a := 1) (b := -1) hseg
  simp only [add_mul]
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_add h3 h4]
  ring

theorem contour_const_mul (r : ℂ) (f : ℂ → ℂ) :
    contour (fun z => r * f z) = r * contour f := by
  unfold contour arcInt segInt
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  ring

theorem contour_zero : contour (fun _ => (0 : ℂ)) = 0 := by
  simp [contour, arcInt, segInt]

theorem contour_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {S : Set ℂ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) S)
    (harc : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ S)
    (hseg : ∀ y ∈ uIcc (1 : ℝ) (-1), (y : ℂ) * Complex.I ∈ S) :
    contour (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, contour (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contour_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [contour_add (hf i (Finset.mem_insert_self i s))
      (continuousOn_finsetSum _ (fun j hj => hf j (Finset.mem_insert_of_mem hj))) harc hseg,
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end ContourLinear

section ContourF

variable {n : ℕ} (x c : Fin n → ℝ)

/-- T4 + T5: the contour integral of `F` is `2πi` times the sum of the residues at positive nodes. -/
theorem contour_Ffun (hxi : Function.Injective x) (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0)
    (e : ℕ) :
    contour (Ffun x c e) = 2 * Real.pi * Complex.I *
      ((∑ a ∈ Finset.univ.filter (fun a => 0 < x a), bDeriv x a * x a ^ e * c a ^ 2 : ℝ) : ℂ) := by
  classical
  obtain ⟨R, hR1, hR⟩ := exists_radius x hx1 hx0
  obtain ⟨q, hq, hqe⟩ := Ffun_decomp x c hxi hx1 hR1 hR e
  set ρ : Fin n → ℂ := fun a => (x a : ℂ) ^ e * (c a : ℂ) ^ 2 * (bDeriv x a : ℂ) with hρ
  set S : Set ℂ := {z | z ∈ ball (0 : ℂ) R ∧ ∀ a, z ≠ (x a : ℂ)} with hS
  have harc : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ S := by
    intro θ
    refine ⟨?_, ?_⟩
    · simp [Complex.norm_exp_ofReal_mul_I]; linarith
    · intro a h
      have := congrArg norm h
      rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs] at this
      linarith [hx1 a]
  have hseg : ∀ y ∈ uIcc (1 : ℝ) (-1), (y : ℂ) * Complex.I ∈ S := by
    intro y hy
    rw [Set.uIcc_of_ge (by norm_num)] at hy
    refine ⟨?_, ?_⟩
    · simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
      have : |y| ≤ 1 := abs_le.mpr ⟨hy.1, hy.2⟩
      linarith
    · intro a h
      have h1 := congrArg Complex.im h
      have h2 := congrArg Complex.re h
      simp at h1 h2
      exact hx0 a (by rw [← h2])
  have hpole : ∀ a, ContinuousOn (fun z : ℂ => (z - (x a : ℂ))⁻¹) S := by
    intro a
    apply ContinuousOn.inv₀ (by fun_prop)
    intro z hz h
    exact hz.2 a (sub_eq_zero.mp h)
  have hTc : ∀ a ∈ (Finset.univ : Finset (Fin n)), ContinuousOn (fun z : ℂ => ρ a * (z - (x a : ℂ))⁻¹) S :=
    fun a _ => continuousOn_const.mul (hpole a)
  have hTsum : ContinuousOn (fun z : ℂ => ∑ a, ρ a * (z - (x a : ℂ))⁻¹) S :=
    continuousOn_finsetSum _ hTc
  have hqc : ContinuousOn q S := hq.continuousOn.mono (fun z hz => hz.1)
  have hFeq : contour (Ffun x c e) = contour (fun z => (∑ a, ρ a * (z - (x a : ℂ))⁻¹) + q z) := by
    apply contour_congr (S := S) _ harc hseg
    intro z hz
    exact hqe z hz.1 hz.2
  rw [hFeq, contour_add hTsum hqc harc hseg]
  have hq0 : contour q = 0 := halfDisc_right_integral_eq_zero hR1 hq
  rw [hq0, add_zero, contour_sum _ _ hTc harc hseg]
  simp only [contour_const_mul]
  have hP : ∀ a, contour (fun z : ℂ => (z - (x a : ℂ))⁻¹) =
      if 0 < x a then 2 * Real.pi * Complex.I else 0 := by
    intro a
    rcases lt_or_gt_of_ne (hx0 a) with h | h
    · rw [contour_pole_neg h]; simp [not_lt.mpr h.le]
    · rw [contour_pole_pos h (lt_of_le_of_lt (le_abs_self _) (hx1 a))]; simp [h]
  simp only [hP, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [hρ]
  ring

end ContourF

section Gram

open OAI.InternalCatalan

variable {n : ℕ} (x c : Fin n → ℝ)

/-- The Gram form `∑ c a c b / (1 - x a x b)`. -/
def Qform : ℝ := ∑ a, ∑ b, c a * c b / (1 - x a * x b)

/-- `∑ c a k_a(z)` with `k_a(z) = 1 / (1 - x a z)`. -/
def Uk (z : ℂ) : ℂ := ∑ a, (c a : ℂ) * firstSheetKernel (x a) z

theorem circleMap_zero_one_eq (θ : ℝ) :
    circleMap 0 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [circleMap]

theorem norm_circle_node {z : ℂ} (hz : ‖z‖ = 1) {a : Fin n} (h : |x a| < 1) :
    z - (x a : ℂ) ≠ 0 := by
  intro h0
  have : z = (x a : ℂ) := sub_eq_zero.mp h0
  rw [this, Complex.norm_real, Real.norm_eq_abs] at hz
  linarith

theorem bD_ne_zero_circle (hx1 : ∀ a, |x a| < 1) {z : ℂ} (hz : ‖z‖ = 1) : bD x z ≠ 0 := by
  unfold bD
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have h1 : (x a : ℂ) * z = 1 := by rw [sub_eq_zero] at h; exact h.symm
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, norm_one, mul_one] at h2
  linarith [hx1 a]

theorem norm_bN_eq_norm_bD {z : ℂ} (hz : ‖z‖ = 1) : ‖bN x z‖ = ‖bD x z‖ := by
  unfold bN bD
  rw [norm_prod, norm_prod]
  apply Finset.prod_congr rfl
  intro a _
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj', hz]; simp
  have : (1 : ℂ) - (x a : ℂ) * z = z * conj (z - (x a : ℂ)) := by
    rw [map_sub, Complex.conj_ofReal, mul_sub, hzz]; ring
  rw [this, norm_mul, hz, one_mul, RCLike.norm_conj]

theorem psi_circle (hx1 : ∀ a, |x a| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    psi x c z = blaschke x z * z⁻¹ * conj (Uk x c z) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hD := bD_ne_zero_circle x hx1 hz
  unfold psi bS Uk
  rw [map_sum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have hza := norm_circle_node x hz (hx1 a)
  rw [map_mul, Complex.conj_ofReal, conj_firstSheetKernel_on_circle (x a) hz, blaschke_eq,
    bN_eq_mul_bNe x a z]
  field_simp

theorem norm_psi_circle (hx1 : ∀ a, |x a| < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖psi x c z‖ = ‖Uk x c z‖ := by
  rw [psi_circle x c hx1 hz, norm_mul, norm_mul, blaschke_eq, norm_div,
    norm_bN_eq_norm_bD x hz, div_self (norm_ne_zero_iff.mpr (bD_ne_zero_circle x hx1 hz))]
  simp [norm_inv, hz]

theorem analyticOnNhd_firstSheetKernel (hx1 : ∀ a, |x a| < 1) (a : Fin n) :
    AnalyticOnNhd ℂ (firstSheetKernel (x a)) (closedBall (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hne := firstSheetKernel_denominator_ne_zero (hx1 a) hz'
  unfold firstSheetKernel
  exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv hne

theorem intervalIntegrable_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun θ => ∑ i ∈ s, f i θ) MeasureTheory.volume a b := by
  have := IntervalIntegrable.sum s h
  rwa [Finset.sum_fn] at this

theorem gram_integral (hx1 : ∀ a, |x a| < 1) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 =
      2 * Real.pi * Qform x c := by
  apply Complex.ofReal_injective
  have hpt : ∀ θ : ℝ, (((‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 : ℝ)) : ℂ) =
      ∑ b, ∑ a, ((c b * c a : ℝ) : ℂ) *
        (firstSheetKernel (x b) (circleMap 0 1 θ) * conj (firstSheetKernel (x a) (circleMap 0 1 θ))) := by
    intro θ
    have hz : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    rw [circleMap_zero_one_eq, norm_psi_circle x c hx1 hz]
    push_cast
    rw [← Complex.mul_conj']
    unfold Uk
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    rw [map_mul, Complex.conj_ofReal]
    ring
  have hOAI : ∀ b a : Fin n, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      firstSheetKernel (x b) (circleMap 0 1 θ) * conj (firstSheetKernel (x a) (circleMap 0 1 θ)) =
        2 * Real.pi * (1 - (x b : ℂ) * (x a : ℂ))⁻¹ := by
    intro b a
    have h := intervalIntegral_mul_conj_firstSheetKernel
      (analyticOnNhd_firstSheetKernel x hx1 b) (hx1 a)
    rw [Complex.real_smul] at h
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have := Real.pi_pos
      exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    have h' : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      firstSheetKernel (x b) (circleMap 0 1 θ) * conj (firstSheetKernel (x a) (circleMap 0 1 θ))) =
        (2 * (Real.pi : ℂ)) * firstSheetKernel (x b) (x a : ℂ) := by
      rw [← h]
      push_cast
      field_simp
    rw [h']
    simp [firstSheetKernel]
  have hint : ∀ b a : Fin n, IntervalIntegrable (fun θ : ℝ =>
      ((c b * c a : ℝ) : ℂ) * (firstSheetKernel (x b) (circleMap 0 1 θ) *
        conj (firstSheetKernel (x a) (circleMap 0 1 θ)))) MeasureTheory.volume 0 (2 * Real.pi) := by
    intro b a
    exact (circleIntegrable_mul_conj_firstSheetKernel (analyticOnNhd_firstSheetKernel x hx1 b)
      (hx1 a)).const_mul _
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum (fun b _ =>
    intervalIntegrable_sum' _ (fun a _ => hint b a))]
  simp_rw [intervalIntegral.integral_finsetSum (fun a _ => hint _ a)]
  simp_rw [intervalIntegral.integral_const_mul, hOAI]
  unfold Qform
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

end Gram

section Bounds

open OAI.InternalCatalan

variable {n : ℕ} (x c : Fin n → ℝ)

theorem psi_conj (z : ℂ) : conj (psi x c z) = psi x c (conj z) := by
  unfold psi bS bD bNe
  simp [map_sum, map_prod, map_div₀, map_mul, map_sub, Complex.conj_ofReal]

theorem psi_differentiableOn {R : ℝ} (hR : ∀ a, |x a| * R < 1) :
    DifferentiableOn ℂ (psi x c) (ball 0 R) := by
  unfold psi
  apply DifferentiableOn.div
  · unfold bS bNe; fun_prop
  · unfold bD; fun_prop
  · exact fun z hz => bD_ne_zero x hR hz

theorem cexp_add_two_pi (θ : ℝ) :
    Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem continuous_phi (hx1 : ∀ a, |x a| < 1) :
    Continuous (fun θ : ℝ => ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) := by
  have : Continuous (fun θ : ℝ => psi x c (Complex.exp ((θ : ℂ) * Complex.I))) := by
    unfold psi
    apply Continuous.div
    · unfold bS bNe; fun_prop
    · unfold bD; fun_prop
    · intro θ; exact bD_ne_zero_circle x hx1 (Complex.norm_exp_ofReal_mul_I θ)
  fun_prop

theorem periodic_phi :
    Function.Periodic (fun θ : ℝ => ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2)
      (2 * Real.pi) := by
  intro θ
  simp only [cexp_add_two_pi]

theorem phi_integral_shift (hx1 : ∀ a, |x a| < 1) :
    ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
      ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 = 2 * Real.pi * Qform x c := by
  have h1 := (periodic_phi x c).intervalIntegral_add_eq (-(Real.pi / 2)) 0
  have e1 : -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
  rw [e1, zero_add] at h1
  rw [h1]
  exact gram_integral x c hx1

theorem norm_Ffun_circle (hx1 : ∀ a, |x a| < 1) (e : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖Ffun x c e z‖ = ‖psi x c z‖ ^ 2 := by
  have hD : ‖bD x z‖ ≠ 0 := norm_ne_zero_iff.mpr (bD_ne_zero_circle x hx1 hz)
  unfold Ffun psi
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hz, norm_bN_eq_norm_bD x hz]
  field_simp
  simp

theorem arcInt_norm_le (hx1 : ∀ a, |x a| < 1) (e : ℕ) :
    ‖arcInt (Ffun x c e)‖ ≤ 2 * Real.pi * Qform x c := by
  unfold arcInt
  refine (intervalIntegral.norm_integral_le_integral_norm
    (by linarith [Real.pi_pos])).trans ?_
  have hpt : ∀ θ : ℝ, ‖Ffun x c e (Complex.exp ((θ : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ =
      ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 := by
    intro θ
    have hz : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    rw [norm_mul, norm_mul, norm_I, hz, mul_one, mul_one, norm_Ffun_circle x c hx1 e hz]
  simp_rw [hpt]
  calc ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2
      ≤ ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
        ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 := by
        apply intervalIntegral.integral_mono_interval (le_refl _)
          (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        · exact Filter.Eventually.of_forall (fun θ => sq_nonneg _)
        · exact (continuous_phi x c hx1).intervalIntegrable _ _
    _ = 2 * Real.pi * Qform x c := phi_integral_shift x c hx1

theorem fejer_riesz (hx1 : ∀ a, |x a| < 1) {R : ℝ} (hR1 : 1 < R) (hR : ∀ a, |x a| * R < 1) :
    ∫ y in (-1 : ℝ)..1, ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 ≤ Real.pi * Qform x c := by
  set g : ℂ → ℂ := fun z => psi x c (Complex.I * z) * psi x c (-(Complex.I * z)) with hg
  have hψ := psi_differentiableOn x c hR
  have hgd : DifferentiableOn ℂ g (ball 0 R) := by
    have m1 : Set.MapsTo (fun z : ℂ => Complex.I * z) (ball 0 R) (ball 0 R) := by
      intro z hz; simpa using hz
    have m2 : Set.MapsTo (fun z : ℂ => -(Complex.I * z)) (ball 0 R) (ball 0 R) := by
      intro z hz; simpa using hz
    exact (hψ.comp (by fun_prop) m1).mul (hψ.comp (by fun_prop) m2)
  have hup := halfDisc_upper_integral_eq_zero hR1 hgd
  have hgy : ∀ y : ℝ, g (y : ℂ) = ((‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    have h0 : Complex.I * (y : ℂ) = (y : ℂ) * Complex.I := mul_comm _ _
    have h1 : -((y : ℂ) * Complex.I) = conj ((y : ℂ) * Complex.I) := by
      simp [map_mul]
    simp only [hg, h0]
    rw [h1, ← psi_conj, Complex.mul_conj']
    push_cast
    ring
  have hAc : (∫ y in (-1 : ℝ)..1, g (y : ℂ)) =
      ((∫ y in (-1 : ℝ)..1, ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr (fun y _ => hgy y)
  rw [hAc] at hup
  set A : ℝ := ∫ y in (-1 : ℝ)..1, ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 with hA
  have hAle : A ≤ ‖∫ θ in (0 : ℝ)..Real.pi, g (Complex.exp ((θ : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ := by
    have : (A : ℂ) = -∫ θ in (0 : ℝ)..Real.pi, g (Complex.exp ((θ : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) := by
      linear_combination hup
    have h2 := congrArg norm this
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [← h2]
    exact le_abs_self A
  refine hAle.trans ?_
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  -- pointwise bound on the arc
  have hp1 : ∀ θ : ℝ, Complex.I * Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((((θ + Real.pi / 2 : ℝ)) : ℂ) * Complex.I) := by
    intro θ
    have := cexp_pi_div_two_mul_I
    push_cast at this ⊢
    rw [add_mul, Complex.exp_add, this]; ring
  have hp2 : ∀ θ : ℝ, -(Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp ((((θ + -(Real.pi / 2) : ℝ)) : ℂ) * Complex.I) := by
    intro θ
    have := cexp_neg_pi_div_two_mul_I
    push_cast at this ⊢
    rw [add_mul, Complex.exp_add, this]; ring
  have hpt : ∀ θ : ℝ, ‖g (Complex.exp ((θ : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      (‖psi x c (Complex.exp ((((θ + Real.pi / 2 : ℝ)) : ℂ) * Complex.I))‖ ^ 2 +
        ‖psi x c (Complex.exp ((((θ + -(Real.pi / 2) : ℝ)) : ℂ) * Complex.I))‖ ^ 2) / 2 := by
    intro θ
    have hn : ‖Complex.I * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      rw [norm_mul, norm_I, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [norm_mul, hn, mul_one]
    simp only [hg]
    rw [hp2 θ, hp1 θ, norm_mul]
    nlinarith [sq_nonneg (‖psi x c (Complex.exp ((((θ + Real.pi / 2 : ℝ)) : ℂ) * Complex.I))‖ -
      ‖psi x c (Complex.exp ((((θ + -(Real.pi / 2) : ℝ)) : ℂ) * Complex.I))‖)]
  have hcg : Continuous (fun θ : ℝ => ‖g (Complex.exp ((θ : ℂ) * Complex.I)) *
      (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖) := by
    have hgc : Continuous (fun θ : ℝ => g (Complex.exp ((θ : ℂ) * Complex.I))) := by
      have := hgd.continuousOn.comp_continuous (f := fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
        (by fun_prop) (fun θ => by
          simp only [mem_ball, dist_zero_right, Complex.norm_exp_ofReal_mul_I]; exact hR1)
      exact this
    exact (hgc.mul (by fun_prop)).norm
  have hphi := continuous_phi x c hx1
  have hc1 : Continuous (fun θ : ℝ => ‖psi x c (Complex.exp ((((θ + Real.pi / 2 : ℝ)) : ℂ) *
      Complex.I))‖ ^ 2) := hphi.comp (by fun_prop : Continuous fun θ : ℝ => θ + Real.pi / 2)
  have hc2 : Continuous (fun θ : ℝ => ‖psi x c (Complex.exp ((((θ + -(Real.pi / 2) : ℝ)) : ℂ) *
      Complex.I))‖ ^ 2) := hphi.comp (by fun_prop : Continuous fun θ : ℝ => θ + -(Real.pi / 2))
  calc ∫ θ in (0 : ℝ)..Real.pi, ‖g (Complex.exp ((θ : ℂ) * Complex.I)) *
        (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))‖
      ≤ ∫ θ in (0 : ℝ)..Real.pi,
        (‖psi x c (Complex.exp ((((θ + Real.pi / 2 : ℝ)) : ℂ) * Complex.I))‖ ^ 2 +
        ‖psi x c (Complex.exp ((((θ + -(Real.pi / 2) : ℝ)) : ℂ) * Complex.I))‖ ^ 2) / 2 := by
        apply intervalIntegral.integral_mono_on Real.pi_pos.le
          (hcg.intervalIntegrable _ _)
        · exact ((hc1.add hc2).div_const 2).intervalIntegrable _ _
        · intro θ _; exact hpt θ
    _ = Real.pi * Qform x c := by
        simp only [add_div]
        rw [intervalIntegral.integral_add ((hc1.div_const 2).intervalIntegrable _ _)
          ((hc2.div_const 2).intervalIntegrable _ _)]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_div]
        have e1 := intervalIntegral.integral_comp_add_right
          (fun θ : ℝ => ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) (a := 0) (b := Real.pi)
          (Real.pi / 2)
        have e2 := intervalIntegral.integral_comp_add_right
          (fun θ : ℝ => ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) (a := 0) (b := Real.pi)
          (-(Real.pi / 2))
        beta_reduce at e1 e2
        rw [e1, e2]
        have hs := intervalIntegral.integral_add_adjacent_intervals
          (hphi.intervalIntegrable (μ := MeasureTheory.volume) (-(Real.pi / 2)) (Real.pi / 2))
          (hphi.intervalIntegrable (μ := MeasureTheory.volume) (Real.pi / 2) (3 * Real.pi / 2))
        rw [phi_integral_shift x c hx1] at hs
        have e3 : (0 : ℝ) + Real.pi / 2 = Real.pi / 2 := by ring
        have e4 : Real.pi + Real.pi / 2 = 3 * Real.pi / 2 := by ring
        have e5 : (0 : ℝ) + -(Real.pi / 2) = -(Real.pi / 2) := by ring
        have e6 : Real.pi + -(Real.pi / 2) = Real.pi / 2 := by ring
        rw [e3, e4, e5, e6]
        linarith

end Bounds

section Main

open OAI.InternalCatalan

variable {n : ℕ} (x c : Fin n → ℝ)

theorem bD_ne_zero_imag (y : ℝ) : bD x ((y : ℂ) * Complex.I) ≠ 0 := by
  unfold bD
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have := congrArg Complex.re h
  simp at this

theorem bN_ne_zero_imag (hx0 : ∀ a, x a ≠ 0) (y : ℝ) : bN x ((y : ℂ) * Complex.I) ≠ 0 := by
  unfold bN
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have := congrArg Complex.re h
  simp at this
  exact hx0 a this

theorem segInt_norm_le (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) {M : ℝ} (hM0 : 0 ≤ M) (e : ℕ)
    (hM : ∀ y ∈ Icc (-1 : ℝ) 1, |y| ^ e ≤ M * ‖blaschke x ((y : ℂ) * Complex.I)‖)
    {R : ℝ} (hR1 : 1 < R) (hR : ∀ a, |x a| * R < 1) :
    ‖segInt (Ffun x c e)‖ ≤ M * (Real.pi * Qform x c) := by
  have hpt : ∀ y ∈ Icc (-1 : ℝ) 1, ‖Ffun x c e ((y : ℂ) * Complex.I)‖ ≤
      M * ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 := by
    intro y hy
    have hMy := hM y hy
    rw [blaschke_eq, norm_div] at hMy
    have hD : 0 < ‖bD x ((y : ℂ) * Complex.I)‖ := norm_pos_iff.mpr (bD_ne_zero_imag x y)
    have hN : 0 < ‖bN x ((y : ℂ) * Complex.I)‖ := norm_pos_iff.mpr (bN_ne_zero_imag x hx0 y)
    have hy1 : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
    unfold Ffun psi
    rw [norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hy1]
    have key : |y| ^ e * ‖bS x c ((y : ℂ) * Complex.I)‖ ^ 2 /
        (‖bD x ((y : ℂ) * Complex.I)‖ * ‖bN x ((y : ℂ) * Complex.I)‖) ≤
        (M * (‖bN x ((y : ℂ) * Complex.I)‖ / ‖bD x ((y : ℂ) * Complex.I)‖)) *
          ‖bS x c ((y : ℂ) * Complex.I)‖ ^ 2 /
        (‖bD x ((y : ℂ) * Complex.I)‖ * ‖bN x ((y : ℂ) * Complex.I)‖) := by
      gcongr
    refine key.trans (le_of_eq ?_)
    field_simp
  have hcF : Continuous (fun y : ℝ => Ffun x c e ((y : ℂ) * Complex.I)) := by
    unfold Ffun
    apply Continuous.div
    · unfold bS bNe; fun_prop
    · unfold bD bN; fun_prop
    · intro y
      exact mul_ne_zero (bD_ne_zero_imag x y) (bN_ne_zero_imag x hx0 y)
  have hcP : Continuous (fun y : ℝ => ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2) := by
    have : Continuous (fun y : ℝ => psi x c ((y : ℂ) * Complex.I)) := by
      unfold psi
      apply Continuous.div
      · unfold bS bNe; fun_prop
      · unfold bD; fun_prop
      · intro y; exact bD_ne_zero_imag x y
    fun_prop
  unfold segInt
  rw [intervalIntegral.integral_symm (-1 : ℝ) 1, norm_neg]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
  simp only [norm_mul, norm_I, mul_one]
  calc ∫ y in (-1 : ℝ)..1, ‖Ffun x c e ((y : ℂ) * Complex.I)‖
      ≤ ∫ y in (-1 : ℝ)..1, M * ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact hcF.norm.intervalIntegrable _ _
        · exact (hcP.const_mul M).intervalIntegrable _ _
        · exact hpt
    _ = M * ∫ y in (-1 : ℝ)..1, ‖psi x c ((y : ℂ) * Complex.I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ M * (Real.pi * Qform x c) :=
        mul_le_mul_of_nonneg_left (fejer_riesz x c hx1 hR1 hR) hM0

/-- **Lemma T** (Loewner form). With `B(z) = ∏ (z - x a) / (1 - x a z)`, `K a b = 1 / (1 - x a x b)`
and `M ≥ 0` such that `|y|^e ≤ M ‖B(i y)‖` on `[-1, 1]`, for every real vector `c`
`|∑_{x a > 0} B'(x a) (x a)^e (c a)^2| ≤ (1 + M/2) ∑_{a,b} c a c b K a b`.
(`bDeriv x a` is `B'(x a)`, see `hasDerivAt_blaschke`.) -/
theorem lemmaT {e : ℕ} (hx : Function.Injective x) (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ Icc (-1 : ℝ) 1, |y| ^ e ≤ M * ‖blaschke x ((y : ℂ) * Complex.I)‖) :
    |∑ a ∈ Finset.univ.filter (fun a => 0 < x a), bDeriv x a * x a ^ e * c a ^ 2| ≤
      (1 + M / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
  obtain ⟨R, hR1, hR⟩ := exists_radius x hx1 hx0
  have hc := contour_Ffun x c hx hx1 hx0 e
  set S0 : ℝ := ∑ a ∈ Finset.univ.filter (fun a => 0 < x a), bDeriv x a * x a ^ e * c a ^ 2
    with hS0
  have h1 : ‖contour (Ffun x c e)‖ = 2 * Real.pi * |S0| := by
    rw [hc, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I]
    simp [abs_of_pos Real.pi_pos]
  have h2 : ‖contour (Ffun x c e)‖ ≤ 2 * Real.pi * Qform x c + M * (Real.pi * Qform x c) := by
    refine (norm_add_le _ _).trans ?_
    exact add_le_add (arcInt_norm_le x c hx1 e) (segInt_norm_le x c hx1 hx0 hM0 e hM hR1 hR)
  rw [h1] at h2
  have hpi := Real.pi_pos
  unfold Qform at h2
  have : 2 * Real.pi * |S0| ≤ 2 * Real.pi * ((1 + M / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b)) := by
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

end Main

section Slope

variable {n : ℕ} (x : Fin n → ℝ)

theorem norm_sq_imag_sub (y t : ℝ) :
    ‖(y : ℂ) * Complex.I - (t : ℂ)‖ ^ 2 = y ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem norm_sq_one_sub (y t : ℝ) :
    ‖(1 : ℂ) - (t : ℂ) * ((y : ℂ) * Complex.I)‖ ^ 2 = 1 + t ^ 2 * y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- `‖B(i y)‖^2` as a real product. -/
def Bsq (y : ℝ) : ℝ := ∏ a, (y ^ 2 + x a ^ 2) / (1 + x a ^ 2 * y ^ 2)

theorem norm_blaschke_sq (y : ℝ) : ‖blaschke x ((y : ℂ) * Complex.I)‖ ^ 2 = Bsq x y := by
  unfold blaschke Bsq
  rw [norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro a _
  rw [norm_div, div_pow, norm_sq_imag_sub, norm_sq_one_sub]

theorem Bsq_pos (y : ℝ) (hy : 0 < y) : 0 < Bsq x y := by
  unfold Bsq
  apply Finset.prod_pos
  intro a _
  positivity

/-- T8 (core): on `(0, 1]` the function `y ↦ log (y^(2e) / B(iy)^2)` has positive derivative
`(2/y)(e - ∑ k_y(x a))`, hence `y^(2e) ≤ ‖B(iy)‖^2`. -/
theorem pow_le_Bsq {e : ℕ}
    (hslope : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2))) :
    ∀ y ∈ Ioc (0 : ℝ) 1, y ^ (2 * e) ≤ Bsq x y := by
  set f : ℝ → ℝ := fun y => 2 * e * Real.log y -
    ∑ a, (Real.log (y ^ 2 + x a ^ 2) - Real.log (1 + x a ^ 2 * y ^ 2)) with hf
  set D : ℝ → ℝ := fun y => 2 * e * y⁻¹ -
    ∑ a, (2 * y / (y ^ 2 + x a ^ 2) - x a ^ 2 * (2 * y) / (1 + x a ^ 2 * y ^ 2)) with hD
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt f (D y) y := by
    intro y hy
    have h1 : ∀ a : Fin n, HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + x a ^ 2))
        (2 * y / (y ^ 2 + x a ^ 2)) y := by
      intro a
      have hne : y ^ 2 + x a ^ 2 ≠ 0 := by positivity
      exact (((hasDerivAt_pow 2 y).add_const (x a ^ 2)).log hne).congr_deriv (by norm_num)
    have h2 : ∀ a : Fin n, HasDerivAt (fun y : ℝ => Real.log (1 + x a ^ 2 * y ^ 2))
        (x a ^ 2 * (2 * y) / (1 + x a ^ 2 * y ^ 2)) y := by
      intro a
      have hne : 1 + x a ^ 2 * y ^ 2 ≠ 0 := by positivity
      exact ((((hasDerivAt_pow 2 y).const_mul (x a ^ 2)).const_add 1).log hne).congr_deriv
        (by norm_num)
    have h4 : HasDerivAt (fun y : ℝ => ∑ a, (Real.log (y ^ 2 + x a ^ 2) -
        Real.log (1 + x a ^ 2 * y ^ 2)))
        (∑ a, (2 * y / (y ^ 2 + x a ^ 2) - x a ^ 2 * (2 * y) / (1 + x a ^ 2 * y ^ 2))) y :=
      HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun a y => Real.log (y ^ 2 + x a ^ 2) - Real.log (1 + x a ^ 2 * y ^ 2))
        (fun a _ => (h1 a).sub (h2 a))
    exact ((Real.hasDerivAt_log hy.ne').const_mul (2 * (e : ℝ))).sub h4
  have hDpos : ∀ y ∈ Ioc (0 : ℝ) 1, 0 < D y := by
    intro y hy
    have hy0 := hy.1
    have hk := hslope y hy
    have hsum : ∑ a, (2 * y / (y ^ 2 + x a ^ 2) - x a ^ 2 * (2 * y) / (1 + x a ^ 2 * y ^ 2)) =
        2 * y⁻¹ * ∑ a, (y ^ 2 / (y ^ 2 + x a ^ 2) - x a ^ 2 * y ^ 2 / (1 + x a ^ 2 * y ^ 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have h1 : y ^ 2 + x a ^ 2 ≠ 0 := by positivity
      have h2 : 1 + x a ^ 2 * y ^ 2 ≠ 0 := by positivity
      field_simp
    simp only [hD]
    rw [hsum]
    have : 2 * (e : ℝ) * y⁻¹ - 2 * y⁻¹ * ∑ a, (y ^ 2 / (y ^ 2 + x a ^ 2) -
        x a ^ 2 * y ^ 2 / (1 + x a ^ 2 * y ^ 2)) =
        2 * y⁻¹ * ((e : ℝ) - ∑ a, (y ^ 2 / (y ^ 2 + x a ^ 2) -
        x a ^ 2 * y ^ 2 / (1 + x a ^ 2 * y ^ 2))) := by ring
    rw [this]
    positivity
  have hmono : MonotoneOn f (Ioc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro y hy
      exact (hderiv y hy.1).continuousAt.continuousWithinAt
    · rw [interior_Ioc]
      intro y hy
      exact (hderiv y hy.1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro y hy
      rw [(hderiv y hy.1).deriv]
      exact (hDpos y ⟨hy.1, hy.2.le⟩).le
  intro y hy
  have h1 : f y ≤ f 1 := hmono hy ⟨one_pos, le_refl _⟩ hy.2
  have hf1 : f 1 = 0 := by simp [hf]
  rw [hf1] at h1
  have hy0 := hy.1
  have hBpos := Bsq_pos x y hy0
  have hlog : Real.log (Bsq x y) = ∑ a, (Real.log (y ^ 2 + x a ^ 2) -
      Real.log (1 + x a ^ 2 * y ^ 2)) := by
    unfold Bsq
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro a _
      have h1 : y ^ 2 + x a ^ 2 ≠ 0 := by positivity
      have h2 : 1 + x a ^ 2 * y ^ 2 ≠ 0 := by positivity
      rw [Real.log_div h1 h2]
    · intro a _
      have h1 : y ^ 2 + x a ^ 2 ≠ 0 := by positivity
      have h2 : 1 + x a ^ 2 * y ^ 2 ≠ 0 := by positivity
      exact div_ne_zero h1 h2
  rw [← Real.log_le_log_iff (by positivity) hBpos, Real.log_pow, hlog]
  simp only [hf] at h1
  push_cast
  linarith

/-- **Lemma T′ (slope criterion for `M* = 1`).**  If `e ≥ 1` and `e - ∑ k_t(x a) > 0` for all
`t ∈ (0, 1]`, with `k_t(x) = t^2/(t^2 + x^2) - x^2 t^2/(1 + x^2 t^2)`, then `M = 1` is admissible:
`|y|^e ≤ ‖B(i y)‖` on `[-1, 1]`. -/
theorem pow_le_norm_blaschke_of_slope {e : ℕ} (he : 1 ≤ e)
    (hslope : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2))) :
    ∀ y ∈ Icc (-1 : ℝ) 1, |y| ^ e ≤ 1 * ‖blaschke x ((y : ℂ) * Complex.I)‖ := by
  intro y hy
  rw [one_mul]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [zero_pow (by omega : e ≠ 0)]
  have hu : |y| ∈ Ioc (0 : ℝ) 1 := ⟨abs_pos.mpr hy0, abs_le.mpr ⟨hy.1, hy.2⟩⟩
  have h1 := pow_le_Bsq x hslope |y| hu
  have h2 : Bsq x |y| = Bsq x y := by
    unfold Bsq
    simp only [sq_abs]
  rw [h2, ← norm_blaschke_sq] at h1
  have h3 : (|y| ^ e) ^ 2 ≤ ‖blaschke x ((y : ℂ) * Complex.I)‖ ^ 2 := by
    rw [← pow_mul, mul_comm]; exact h1
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3

/-- **Lemma T with the slope criterion** (`M* = 1`, so `τ' ≤ 3/2`). -/
theorem lemmaT_of_slope {e : ℕ} (c : Fin n → ℝ) (hx : Function.Injective x)
    (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) (he : 1 ≤ e)
    (hslope : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2))) :
    |∑ a ∈ Finset.univ.filter (fun a => 0 < x a), bDeriv x a * x a ^ e * c a ^ 2| ≤
      (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
  have h := lemmaT x c (e := e) hx hx1 hx0 (M := 1) zero_le_one
    (pow_le_norm_blaschke_of_slope x he hslope)
  norm_num at h
  exact h

end Slope

section Derivative

variable {n : ℕ} (x : Fin n → ℝ)

/-- `bDeriv x a` is the derivative of the Blaschke product at the node `x a`. -/
theorem hasDerivAt_blaschke (_hxi : Function.Injective x) (hx1 : ∀ a, |x a| < 1) (a : Fin n) :
    HasDerivAt (blaschke x) (bDeriv x a : ℂ) (x a : ℂ) := by
  have hDne : bD x (x a : ℂ) ≠ 0 := by
    unfold bD
    rw [Finset.prod_ne_zero_iff]
    intro b _ h
    have h1 : (x b : ℂ) * (x a : ℂ) = 1 := by rw [sub_eq_zero] at h; exact h.symm
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      norm_one] at h2
    have := abs_nonneg (x b)
    have := abs_nonneg (x a)
    nlinarith [hx1 a, hx1 b]
  have hNe : DifferentiableAt ℂ (bNe x a) (x a : ℂ) := by
    unfold bNe; fun_prop
  have hDd : DifferentiableAt ℂ (bD x) (x a : ℂ) := by
    unfold bD; fun_prop
  have hN : HasDerivAt (bN x) (bNe x a (x a : ℂ)) (x a : ℂ) := by
    have : bN x = fun z => (z - (x a : ℂ)) * bNe x a z := funext (bN_eq_mul_bNe x a)
    rw [this]
    have h := ((hasDerivAt_id (x a : ℂ)).sub_const (x a : ℂ)).mul hNe.hasDerivAt
    exact h.congr_deriv (by simp)
  have hq := hN.div hDd.hasDerivAt hDne
  have hb : blaschke x = fun z => bN x z / bD x z := funext (blaschke_eq x)
  rw [hb, bDeriv_eq]
  convert hq using 1
  have hN0 : bN x (x a : ℂ) = 0 := by
    unfold bN
    exact Finset.prod_eq_zero (Finset.mem_univ a) (sub_self _)
  rw [hN0]
  field_simp
  ring

end Derivative

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.lemmaT
#print axioms CatalanMeasure.Signed.lemmaT_of_slope
#print axioms CatalanMeasure.Signed.pow_le_norm_blaschke_of_slope
#print axioms CatalanMeasure.Signed.hasDerivAt_blaschke
