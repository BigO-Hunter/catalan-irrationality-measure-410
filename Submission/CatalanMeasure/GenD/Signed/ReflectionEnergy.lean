module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The discrete reflection-energy inequality (D7.1)

This file proves a discrete form of the positivity theorem for the logarithmic energy of a signed
measure on `[-1,1]` of total mass `0` whose positive and negative parts live on `(0,1)` and
`(-1,0)`: the energy dominates the `L`-functionals of the two folded parts,
`I(δ) ≥ L(δ₊) + L(R δ₋)`, where `L(t) = ∑_k (∫ a^k dt)² / k`.

## Setting (folded coordinates)

A configuration consists of finitely many points `x_i ∈ (-1,1) ∖ {0}` with weights `w_i > 0`.  Write
`a_i = |x_i| ∈ (0,1)` and let `σ_i : Bool` record the sign of `x_i`.  The reference is a pair of
finite measures `μ_τ` (`τ : Bool`) on `(0,1)` (the folded species) with density `≤ C` with respect to
Lebesgue measure; their total mass equals `∑ w_i`.  In the coordinates `a = |x|`:

* the kernel is `-log |a - b|` between two points of the same species and `-log (a + b)` between
  points of opposite species (`Kt`);
* `Ioff` is the energy of `∑ w_i δ_{x_i} - μ` without the diagonal terms of the atoms:
  `∑_{i ≠ j} w_i w_j K + (-2) ∑_i w_i ∑_τ ∫ K(a_i, ·) dμ_τ + ∑_{τ,τ'} ∬ K dμ_τ dμ_τ'`.

## Main result

`CatalanMeasure.Signed.ReflectionEnergy.reflection_energy`: for every `ρ ∈ (0,1)`,

`Ioff ≥ ∑_τ Lpart τ - ∑_i w_i² (-log a_i + log (1/(1-ρ))) - E(ρ, C, W)`,

with `Lpart τ = L(D_{√ρ} p_τ)` the `L`-functional of the `√ρ`-dilation of the signed species measure
`p_τ = ∑_{σ_i = τ} w_i δ_{a_i} - μ_τ`, `W = ∑ w_i` and
`E = 8 W C (1-ρ)(1 + log (1/(1-ρ))) + 2 (1-ρ) (2W)²`.
The diagonal term `∑ w_i² (-log a_i + …)` is the per-atom cost of the damped self-interaction.

## Proof

Everything is written in the variable `a = |x|`.  The damped kernels
`K1d = -log max - log (1 - ρ min/max)` and `K2d = -log max - log (1 + ρ min/max)` are compared to the
true kernels (`D1`, `D2`; `D1 ≥ 0`, `-(1-ρ) ≤ D2 ≤ 0`, and `D1 ≤ log (1 + (1-ρ)/|a-b|)` whose
integral over `(0,1)` is at most `4 (1-ρ)(1 + log (1/(1-ρ)))`).  The damped quadratic form is
decomposed as `½ (K1d + K2d)(p+q) + ½ (K1d - K2d)(p-q)` and each part is shown to dominate the
`L`-functional by *rank-one expansions*: `K1d - ell` is an integral over `s ∈ (0,1)` of sums of
squares `1[a<s](a/s)^m 1[b<s](b/s)^m`; `K2d` is a Frullani integral of rank-one kernels; and
`K1d - K2d = ∑_{m odd} (2ρ^m/m) (min/max)^m` is a sum of rank-one kernels plus integrals of
rank-one kernels, to which a weighted Cauchy–Schwarz step (proved by the discriminant of a
quadratic in the tilt) is applied.  Positive definiteness is thus always "a square integrated is `≥ 0`":
no planar potential theory or Fourier transform is used.  The pairing of kernels with the signed
measure `(A - M)` is the generic `P2`, with Fubini lemmas `P2_integral`, `PP_tsum`, `PP_param`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

section Kit
variable {Y : Type*} [MeasurableSpace Y]

/-- The double integral against the signed measure `(A - M) ⊗ (A - M)`. -/
noncomputable def P2 (A M : Measure Y) (G : Y × Y → ℝ) : ℝ :=
  ∫ z, G z ∂(A.prod A) - ∫ z, G z ∂(A.prod M) - ∫ z, G z ∂(M.prod A) + ∫ z, G z ∂(M.prod M)

variable {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]

theorem integrable_AA {G : Y × Y → ℝ} (h : Integrable G ((A + M).prod (A + M))) :
    Integrable G (A.prod A) :=
  h.mono_measure (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_right le_rfl))
theorem integrable_AM {G : Y × Y → ℝ} (h : Integrable G ((A + M).prod (A + M))) :
    Integrable G (A.prod M) :=
  h.mono_measure (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl))
theorem integrable_MA {G : Y × Y → ℝ} (h : Integrable G ((A + M).prod (A + M))) :
    Integrable G (M.prod A) :=
  h.mono_measure (Measure.prod_mono (Measure.le_add_left le_rfl) (Measure.le_add_right le_rfl))
theorem integrable_MM {G : Y × Y → ℝ} (h : Integrable G ((A + M).prod (A + M))) :
    Integrable G (M.prod M) :=
  h.mono_measure (Measure.prod_mono (Measure.le_add_left le_rfl) (Measure.le_add_left le_rfl))

theorem P2_add {G H : Y × Y → ℝ} (hG : Integrable G ((A + M).prod (A + M)))
    (hH : Integrable H ((A + M).prod (A + M))) :
    P2 A M (fun z => G z + H z) = P2 A M G + P2 A M H := by
  unfold P2
  rw [integral_add (integrable_AA hG) (integrable_AA hH), integral_add (integrable_AM hG) (integrable_AM hH),
    integral_add (integrable_MA hG) (integrable_MA hH), integral_add (integrable_MM hG) (integrable_MM hH)]
  ring

theorem P2_sub {G H : Y × Y → ℝ} (hG : Integrable G ((A + M).prod (A + M)))
    (hH : Integrable H ((A + M).prod (A + M))) :
    P2 A M (fun z => G z - H z) = P2 A M G - P2 A M H := by
  unfold P2
  rw [integral_sub (integrable_AA hG) (integrable_AA hH), integral_sub (integrable_AM hG) (integrable_AM hH),
    integral_sub (integrable_MA hG) (integrable_MA hH), integral_sub (integrable_MM hG) (integrable_MM hH)]
  ring

theorem P2_smul (c : ℝ) (G : Y × Y → ℝ) : P2 A M (fun z => c * G z) = c * P2 A M G := by
  unfold P2
  simp only [integral_const_mul]
  ring

/-- Rank-one kernels give a square. -/
theorem P2_rankone (f : Y → ℝ) :
    P2 A M (fun z => f z.1 * f z.2) = (∫ y, f y ∂A - ∫ y, f y ∂M) ^ 2 := by
  unfold P2
  simp only [integral_prod_mul]
  ring

theorem P2_const (c : ℝ) :
    P2 A M (fun _ => c) = c * (A.real univ - M.real univ) ^ 2 := by
  have h := P2_rankone (A := A) (M := M) (fun _ => (1:ℝ))
  have h2 := P2_smul (A := A) (M := M) c (fun _ => (1:ℝ))
  simp only [mul_one, integral_const, smul_eq_mul] at h h2
  rw [h2, h]

theorem P2_integral {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SFinite ν]
    (F : Θ → Y × Y → ℝ)
    (hF : Integrable (Function.uncurry F) (ν.prod ((A + M).prod (A + M)))) :
    P2 A M (fun z => ∫ θ, F θ z ∂ν) = ∫ θ, P2 A M (F θ) ∂ν := by
  have h1 : Integrable (Function.uncurry F) (ν.prod (A.prod A)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_right le_rfl)))
  have h2 : Integrable (Function.uncurry F) (ν.prod (A.prod M)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl)))
  have h3 : Integrable (Function.uncurry F) (ν.prod (M.prod A)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_left le_rfl) (Measure.le_add_right le_rfl)))
  have h4 : Integrable (Function.uncurry F) (ν.prod (M.prod M)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_left le_rfl) (Measure.le_add_left le_rfl)))
  have i1 : Integrable (fun θ => ∫ z, F θ z ∂(A.prod A)) ν := h1.integral_prod_left
  have i2 : Integrable (fun θ => ∫ z, F θ z ∂(A.prod M)) ν := h2.integral_prod_left
  have i3 : Integrable (fun θ => ∫ z, F θ z ∂(M.prod A)) ν := h3.integral_prod_left
  have i4 : Integrable (fun θ => ∫ z, F θ z ∂(M.prod M)) ν := h4.integral_prod_left
  unfold P2
  rw [← integral_integral_swap h1, ← integral_integral_swap h2, ← integral_integral_swap h3,
    ← integral_integral_swap h4]
  have j12 : Integrable (fun θ => ∫ z, F θ z ∂(A.prod A) - ∫ z, F θ z ∂(A.prod M)) ν := i1.sub i2
  have j123 : Integrable (fun θ => ∫ z, F θ z ∂(A.prod A) - ∫ z, F θ z ∂(A.prod M)
      - ∫ z, F θ z ∂(M.prod A)) ν := j12.sub i3
  rw [← integral_sub i1 i2, ← integral_sub j12 i3, ← integral_add j123 i4]

end Kit

/-- `min / max`, the ratio `e^{-|u-v|}` in the variable `u = -log a`. -/
def rr (a b : ℝ) : ℝ := min a b / max a b
def K1d (ρ a b : ℝ) : ℝ := -log (max a b) - log (1 - ρ * rr a b)
def K2d (ρ a b : ℝ) : ℝ := -log (max a b) - log (1 + ρ * rr a b)
def ell (ρ a b : ℝ) : ℝ := -log (1 - ρ * (a * b))
/-- the `s`-section of the rank-one expansion of `K1d - ell`. -/
def Gs (ρ s a b : ℝ) : ℝ :=
  if max a b < s then s⁻¹ * ((1 + ρ * (a * b / s ^ 2)) / (1 - ρ * (a * b / s ^ 2))) else 0

section real
variable {ρ a b : ℝ}

theorem max_pos' (ha : 0 < a) : 0 < max a b := lt_max_of_lt_left ha

theorem rr_pos (ha : 0 < a) (hb : 0 < b) : 0 < rr a b := by
  have := max_pos' (b := b) ha
  have : 0 < min a b := lt_min ha hb
  unfold rr; positivity

theorem rr_le_one (ha : 0 < a) : rr a b ≤ 1 := by
  unfold rr
  rw [div_le_one (max_pos' ha)]
  exact min_le_max

theorem mul_eq_min_max (a b : ℝ) : a * b = min a b * max a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

theorem ab_div_max_sq (ha : 0 < a) : a * b / (max a b) ^ 2 = rr a b := by
  have hM : 0 < max a b := max_pos' ha
  rw [mul_eq_min_max, rr]; field_simp

theorem Gs_integral (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    ∫ s in Ioo (0:ℝ) 1, Gs ρ s a b = K1d ρ a b - ell ρ a b := by
  set M := max a b with hMdef
  have hM : 0 < M := max_pos' ha
  have hM1 : M < 1 := max_lt ha1 hb1
  have hMeas : MeasurableSet (Ioi M) := measurableSet_Ioi
  have h1 : ∀ s, Gs ρ s a b = (Ioi M).indicator (fun s => s⁻¹ * ((1 + ρ * (a * b / s ^ 2)) / (1 - ρ * (a * b / s ^ 2)))) s := by
    intro s; by_cases h : M < s
    · rw [Gs, if_pos h, indicator_of_mem (mem_Ioi.mpr h)]
    · rw [Gs, if_neg h, indicator_of_notMem (by simpa using h)]
  simp_rw [h1]
  rw [setIntegral_indicator hMeas]
  have : Ioo (0:ℝ) 1 ∩ Ioi M = Ioo M 1 := by
    ext s; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨hM.trans h3, h2⟩, h3⟩
  rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hM1.le]
  set c := ρ * (a * b) with hc
  have hcpos : 0 < c := by positivity
  have hcM : c < M ^ 2 := by
    have h1 : a * b ≤ M ^ 2 := by
      rw [mul_eq_min_max, sq]
      exact mul_le_mul_of_nonneg_right (min_le_max) hM.le
    have : ρ * (a * b) < a * b := by nlinarith [mul_pos ha hb]
    linarith
  have hder : ∀ x ∈ Set.uIcc M 1, HasDerivAt (fun s => Real.log (s ^ 2 - c) - Real.log s)
      (x⁻¹ * ((1 + ρ * (a * b / x ^ 2)) / (1 - ρ * (a * b / x ^ 2)))) x := by
    intro x hx
    rw [Set.uIcc_of_le hM1.le] at hx
    have hx0 : 0 < x := hM.trans_le hx.1
    have hxne : x ≠ 0 := hx0.ne'
    have hx2 : c < x ^ 2 := lt_of_lt_of_le hcM (pow_le_pow_left₀ hM.le hx.1 2)
    have hne : x ^ 2 - c ≠ 0 := by linarith
    have h := (((hasDerivAt_pow 2 x).sub_const c).log hne).sub (Real.hasDerivAt_log hxne)
    convert h using 1
    have : (1 - ρ * (a * b / x ^ 2)) = (x ^ 2 - c) / x ^ 2 := by rw [hc]; field_simp
    have h2 : (1 + ρ * (a * b / x ^ 2)) = (x ^ 2 + c) / x ^ 2 := by rw [hc]; field_simp
    rw [this, h2]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹ * ((1 + ρ * (a * b / x ^ 2)) / (1 - ρ * (a * b / x ^ 2)))) (Set.uIcc M 1) := by
    intro x hx
    rw [Set.uIcc_of_le hM1.le] at hx
    have hx0 : 0 < x := hM.trans_le hx.1
    have hx2 : c < x ^ 2 := lt_of_lt_of_le hcM (pow_le_pow_left₀ hM.le hx.1 2)
    have hden : 1 - ρ * (a * b / x ^ 2) ≠ 0 := by
      have : (1 - ρ * (a * b / x ^ 2)) = (x ^ 2 - c) / x ^ 2 := by rw [hc]; field_simp
      rw [this]; apply div_ne_zero (by linarith) (by positivity)
    apply ContinuousAt.continuousWithinAt
    have hx0' : x ≠ 0 := hx0.ne'
    have hx2ne : x ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable)]
  have hMM : M ^ 2 - c = M ^ 2 * (1 - ρ * rr a b) := by
    rw [hc, ← ab_div_max_sq ha (b := b), ← hMdef]; field_simp
  have hpos1 : 0 < 1 - c := by linarith [(by nlinarith [mul_pos ha hb] : ρ * (a * b) < 1)]
  have hpos2 : 0 < 1 - ρ * rr a b := by nlinarith [rr_le_one (b := b) ha, rr_pos ha hb]
  simp only [one_pow, Real.log_one]
  rw [hMM, Real.log_mul (by positivity) hpos2.ne', Real.log_pow]
  unfold K1d ell
  rw [← hMdef]
  have : (1 - c) = 1 - ρ * (a * b) := rfl
  rw [this]
  push_cast
  ring

/-- coefficients of `(1 + y)/(1 - y) = ∑ cc m y^m`-type expansion with ratio `ρ`. -/
def cc (ρ : ℝ) (m : ℕ) : ℝ := if m = 0 then 1 else 2 * ρ ^ m

/-- `ψ_{m,s}(a) = 1[a < s] (a/s)^m`. -/
def psi (m : ℕ) (s a : ℝ) : ℝ := if a < s then (a / s) ^ m else 0

theorem psi_nonneg (m : ℕ) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) : 0 ≤ psi m s a := by
  unfold psi; split_ifs
  · positivity
  · exact le_rfl

theorem psi_le_one (m : ℕ) {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) : psi m s a ≤ 1 := by
  unfold psi; split_ifs with h
  · exact pow_le_one₀ (by positivity) ((div_lt_one hs).2 h).le
  · exact zero_le_one

theorem cc_nonneg (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ cc ρ m := by
  unfold cc; split_ifs <;> positivity

theorem cc_le' (hρ : 0 ≤ ρ) (m : ℕ) : cc ρ m ≤ 2 * ρ ^ m := by
  unfold cc; split_ifs with h
  · subst h; norm_num
  · exact le_rfl

theorem summable_cc (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : Summable (cc ρ) :=
  Summable.of_nonneg_of_le (cc_nonneg hρ0) (cc_le' hρ0)
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left 2)

theorem cc_hasSum (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun m => cc ρ m * x ^ m) ((1 + ρ * x) / (1 - ρ * x)) := by
  have hy : ρ * x < 1 := by nlinarith
  have hy0 : 0 ≤ ρ * x := by positivity
  have h1 : HasSum (fun m : ℕ => 2 * (ρ * x) ^ m) (2 * (1 - ρ * x)⁻¹) :=
    (hasSum_geometric_of_lt_one hy0 hy).mul_left 2
  have h2 : HasSum (fun m : ℕ => if m = 0 then (1:ℝ) else 0) 1 := by
    simpa using hasSum_ite_eq (0:ℕ) (1:ℝ)
  have h3 := h1.sub h2
  have hfun : (fun m : ℕ => cc ρ m * x ^ m) = fun m => 2 * (ρ * x) ^ m - (if m = 0 then (1:ℝ) else 0) := by
    funext m; unfold cc; split_ifs with h
    · subst h; simp; ring
    · rw [mul_pow]; ring
  rw [hfun]
  convert h3 using 1
  have : (1 - ρ * x) ≠ 0 := by linarith
  field_simp; ring

theorem Gs_hasSum (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) {s : ℝ} (hs : 0 < s) :
    HasSum (fun m => s⁻¹ * cc ρ m * (psi m s a * psi m s b)) (Gs ρ s a b) := by
  by_cases h : max a b < s
  · have ha' : a < s := lt_of_le_of_lt (le_max_left _ _) h
    have hb' : b < s := lt_of_le_of_lt (le_max_right _ _) h
    have hx0 : 0 ≤ a / s * (b / s) := by positivity
    have hx1 : a / s * (b / s) < 1 := by
      have := (div_lt_one hs).2 ha'; have := (div_lt_one hs).2 hb'
      nlinarith [div_pos ha hs, div_pos hb hs]
    have := (cc_hasSum hρ0 hρ1 hx0 hx1).mul_left s⁻¹
    have hG : Gs ρ s a b = s⁻¹ * ((1 + ρ * (a / s * (b / s))) / (1 - ρ * (a / s * (b / s)))) := by
      unfold Gs; rw [if_pos h]; congr 3 <;> field_simp
    rw [hG]
    convert this using 1
    funext m
    unfold psi; rw [if_pos ha', if_pos hb', ← mul_pow]; ring
  · have : Gs ρ s a b = 0 := by unfold Gs; rw [if_neg h]
    rw [this]
    have h0 : ∀ m, s⁻¹ * cc ρ m * (psi m s a * psi m s b) = 0 := by
      intro m
      have : psi m s a = 0 ∨ psi m s b = 0 := by
        by_contra hc; push_neg at hc
        unfold psi at hc
        have h1 : a < s := by by_contra h'; exact hc.1 (by simp [h'])
        have h2 : b < s := by by_contra h'; exact hc.2 (by simp [h'])
        exact h (max_lt h1 h2)
      rcases this with h | h <;> simp [h]
    simp only [h0]; exact hasSum_zero


theorem Hs_integral (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) {m : ℕ} (hm : 0 < m) :
    ∫ s in Ioo (0:ℝ) 1, s⁻¹ * (psi m s a * psi m s b) = (rr a b ^ m - (a * b) ^ m) / (2 * m) := by
  set M := max a b with hMdef
  have hM : 0 < M := max_pos' ha
  have hM1 : M < 1 := max_lt ha1 hb1
  have hMeas : MeasurableSet (Ioi M) := measurableSet_Ioi
  have h1 : ∀ s, s⁻¹ * (psi m s a * psi m s b) =
      (Ioi M).indicator (fun s => s⁻¹ * ((a / s) ^ m * (b / s) ^ m)) s := by
    intro s
    by_cases h : M < s
    · have ha' : a < s := lt_of_le_of_lt (le_max_left _ _) h
      have hb' : b < s := lt_of_le_of_lt (le_max_right _ _) h
      rw [indicator_of_mem (mem_Ioi.mpr h)]; unfold psi; rw [if_pos ha', if_pos hb']
    · rw [indicator_of_notMem (by simpa using h)]
      have : ¬ (a < s ∧ b < s) := fun hh => h (max_lt hh.1 hh.2)
      unfold psi
      by_cases h2 : a < s
      · have h3 : ¬ b < s := fun h3 => this ⟨h2, h3⟩
        simp [h3]
      · simp [h2]
  simp_rw [h1]
  rw [setIntegral_indicator hMeas]
  have : Ioo (0:ℝ) 1 ∩ Ioi M = Ioo M 1 := by
    ext s; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨hM.trans h3, h2⟩, h3⟩
  rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hM1.le]
  set c := (a * b) ^ m with hc
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hder : ∀ x ∈ Set.uIcc M 1, HasDerivAt (fun s : ℝ => -(c / (2 * m)) * (s ^ (2 * m))⁻¹)
      (x⁻¹ * ((a / x) ^ m * (b / x) ^ m)) x := by
    intro x hx
    rw [Set.uIcc_of_le hM1.le] at hx
    have hx0 : 0 < x := hM.trans_le hx.1
    have hxne : x ≠ 0 := hx0.ne'
    have hp : HasDerivAt (fun s : ℝ => s ^ (2 * m)) (((2 * m : ℕ) : ℝ) * x ^ (2 * m - 1)) x :=
      hasDerivAt_pow (2 * m) x
    have h := (hp.inv (pow_ne_zero _ hxne)).const_mul (-(c / (2 * m)))
    convert h using 1
    have e1 : (a / x) ^ m * (b / x) ^ m = (a * b) ^ m / x ^ (2 * m) := by
      rw [← mul_pow, div_mul_div_comm, div_pow, ← pow_two, ← pow_mul, mul_comm 2 m]
    have hx2 : x ^ (2 * m) = x ^ (2 * m - 1) * x := by
      rw [← pow_succ]; congr 1; omega
    have hP : x ^ (2 * m - 1) ≠ 0 := pow_ne_zero _ hxne
    rw [e1, ← hc]
    push_cast
    rw [hx2]
    field_simp
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹ * ((a / x) ^ m * (b / x) ^ m)) (Set.uIcc M 1) := by
    intro x hx
    rw [Set.uIcc_of_le hM1.le] at hx
    have hx0 : 0 < x := hM.trans_le hx.1
    apply ContinuousAt.continuousWithinAt
    have hx0' : x ≠ 0 := hx0.ne'
    fun_prop (disch := assumption)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable)]
  have hrr : c * (M ^ (2 * m))⁻¹ = rr a b ^ m := by
    rw [hc, ← ab_div_max_sq ha (b := b), ← hMdef, div_pow, ← pow_mul, div_eq_mul_inv]
  simp only [one_pow, inv_one]
  rw [mul_one]
  have : (-(c / (2 * m)) - -(c / (2 * m)) * (M ^ (2 * m))⁻¹) = (c * (M ^ (2 * m))⁻¹ - c) / (2 * m) := by
    field_simp; ring
  rw [this, hrr]
theorem ell_hasSum (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    HasSum (fun k : ℕ => ρ ^ (k + 1) / (k + 1) * (a * b) ^ (k + 1)) (ell ρ a b) := by
  have h : |ρ * (a * b)| < 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith [mul_pos ha hb]
  have := hasSum_pow_div_log_of_abs_lt_one h
  unfold ell
  convert this using 1
  funext k
  rw [mul_pow]; ring

theorem H_hasSum (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun n : ℕ => (2 * ρ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) * rr a b ^ (2 * n + 1))
      (K1d ρ a b - K2d ρ a b) := by
  have hr0 := rr_pos ha hb
  have hr1 := rr_le_one (b := b) ha
  have h : |ρ * rr a b| < 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith
  have := hasSum_log_sub_log_of_abs_lt_one h
  have e : K1d ρ a b - K2d ρ a b = Real.log (1 + ρ * rr a b) - Real.log (1 - ρ * rr a b) := by
    unfold K1d K2d; ring
  rw [e]
  convert this using 1
  funext n
  push_cast
  rw [mul_pow]; field_simp


/-! ### Bounds -/

theorem log_max_le (ha : 0 < a) (ha1 : a < 1) : -Real.log (max a b) ≤ |Real.log a| := by
  have := Real.log_le_log ha (le_max_left a b)
  rw [abs_of_neg (Real.log_neg ha ha1)]; linarith

theorem log_max_nonneg (ha : 0 < a) (hb1 : b < 1) (ha1 : a < 1) : 0 ≤ -Real.log (max a b) := by
  have := Real.log_neg (max_pos' (b := b) ha) (max_lt ha1 hb1)
  linarith

theorem K1d_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    0 ≤ K1d ρ a b := by
  have h1 := log_max_nonneg ha hb1 ha1
  have h2 : Real.log (1 - ρ * rr a b) ≤ 0 :=
    Real.log_nonpos (by nlinarith [rr_pos ha hb, rr_le_one (b := b) ha]) (by nlinarith [rr_pos ha hb])
  unfold K1d; linarith

theorem K1d_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    K1d ρ a b ≤ |Real.log a| + |Real.log (1 - ρ)| := by
  have h1 := log_max_le (b := b) ha ha1
  have hr := rr_le_one (b := b) ha
  have hr0 := rr_pos ha hb
  have h2 : -Real.log (1 - ρ * rr a b) ≤ -Real.log (1 - ρ) := by
    have := Real.log_le_log (by linarith) (by nlinarith : 1 - ρ ≤ 1 - ρ * rr a b)
    linarith
  have h3 : -Real.log (1 - ρ) ≤ |Real.log (1 - ρ)| := neg_le_abs _
  unfold K1d; linarith

theorem K2d_abs_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    |K2d ρ a b| ≤ |Real.log a| + 1 := by
  have h1 := log_max_le (b := b) ha ha1
  have h1' := log_max_nonneg ha hb1 ha1
  have hr := rr_le_one (b := b) ha
  have hr0 := rr_pos ha hb
  have h2 : Real.log (1 + ρ * rr a b) ≤ Real.log 2 :=
    Real.log_le_log (by nlinarith) (by nlinarith)
  have h2' : 0 ≤ Real.log (1 + ρ * rr a b) := Real.log_nonneg (by nlinarith)
  have h3 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  unfold K2d
  rw [abs_le]; constructor <;> linarith

theorem ell_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    0 ≤ ell ρ a b := by
  have : Real.log (1 - ρ * (a * b)) ≤ 0 :=
    Real.log_nonpos (by nlinarith [mul_pos ha hb]) (by nlinarith [mul_pos ha hb])
  unfold ell; linarith

theorem ell_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    ell ρ a b ≤ |Real.log (1 - ρ)| := by
  have h2 : -Real.log (1 - ρ * (a * b)) ≤ -Real.log (1 - ρ) := by
    have hab : a * b ≤ 1 := by nlinarith
    have := Real.log_le_log (by nlinarith [mul_pos ha hb]) (by nlinarith [mul_le_mul_of_nonneg_left hab hρ0.le] : 1 - ρ ≤ 1 - ρ * (a * b))
    linarith
  have h3 : -Real.log (1 - ρ) ≤ |Real.log (1 - ρ)| := neg_le_abs _
  unfold ell; linarith

/-! ### Frullani kernel -/

def cX (ρ a b : ℝ) : ℝ := (max a b + ρ * min a b) / 2
def Fl (ρ lam a b : ℝ) : ℝ := lam⁻¹ * (Real.exp (-(lam * cX ρ a b)) - Real.exp (-lam))

theorem cX_pos (hρ0 : 0 < ρ) (ha : 0 < a) (hb : 0 < b) : 0 < cX ρ a b := by
  have : 0 < max a b := max_pos' ha
  have : 0 < min a b := lt_min ha hb
  unfold cX; positivity

theorem cX_lt_one (hρ1 : ρ < 1) (ha1 : a < 1) (hb1 : b < 1) (ha : 0 < a) (hb : 0 < b) : cX ρ a b < 1 := by
  have h1 : max a b < 1 := max_lt ha1 hb1
  have h2 : min a b ≤ max a b := min_le_max
  have : 0 < min a b := lt_min ha hb
  unfold cX; nlinarith

theorem K2d_eq_cX (hρ0 : 0 < ρ) (ha : 0 < a) (hb : 0 < b) :
    K2d ρ a b = -Real.log 2 + -Real.log (cX ρ a b) := by
  have hM := max_pos' (b := b) ha
  have hm : 0 < min a b := lt_min ha hb
  have hr := rr_pos ha hb
  have : cX ρ a b = max a b * (1 + ρ * rr a b) / 2 := by
    unfold cX rr; field_simp
  rw [this]
  unfold K2d
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hM.ne' (by positivity)]
  ring

theorem Fl_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) (hb1 : b < 1)
    {lam : ℝ} (hl : 0 < lam) : 0 ≤ Fl ρ lam a b := by
  have h1 := cX_lt_one hρ1 ha1 hb1 ha hb
  unfold Fl
  apply mul_nonneg (inv_nonneg.2 hl.le)
  rw [sub_nonneg, Real.exp_le_exp]
  nlinarith

theorem Fl_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) (hb1 : b < 1)
    {lam : ℝ} (hl : 0 < lam) : Fl ρ lam a b ≤ (1 - cX ρ a b) * Real.exp (-(cX ρ a b * lam)) := by
  have h1 := cX_lt_one hρ1 ha1 hb1 ha hb
  have h0 := cX_pos hρ0 ha hb
  unfold Fl
  set c := cX ρ a b
  have e : Real.exp (-lam) = Real.exp (-(lam * c)) * Real.exp (-(lam * (1 - c))) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : 1 - lam * (1 - c) ≤ Real.exp (-(lam * (1 - c))) := by
    have := Real.add_one_le_exp (-(lam * (1 - c))); linarith
  have hexp : 0 < Real.exp (-(lam * c)) := Real.exp_pos _
  rw [e, mul_comm c lam, inv_mul_le_iff₀ hl]
  nlinarith [mul_le_mul_of_nonneg_left h2 hexp.le]

theorem Fl_integral (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) (hb1 : b < 1) :
    ∫ lam in Ioi (0:ℝ), Fl ρ lam a b = -Real.log (cX ρ a b) := by
  have h1 := cX_lt_one hρ1 ha1 hb1 ha hb
  have h0 := cX_pos hρ0 ha hb
  set c := cX ρ a b with hcdef
  have hint : IntegrableOn (fun x : ℝ => x⁻¹ • (Real.exp (-(c * x)) - Real.exp (-(1 * x)))) (Ioi 0) := by
    have hI : IntegrableOn (fun x : ℝ => (1 - c) * Real.exp (-c * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul (1 - c)
    refine hI.mono' ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have := Fl_nonneg hρ0 hρ1 ha hb ha1 hb1 hx
      have h2 := Fl_le hρ0 hρ1 ha hb ha1 hb1 hx
      have e : x⁻¹ • (Real.exp (-(c * x)) - Real.exp (-(1 * x))) = Fl ρ x a b := by
        unfold Fl; rw [← hcdef, smul_eq_mul, one_mul, mul_comm c x]
      rw [e, Real.norm_of_nonneg this, neg_mul]; exact h2
  have hmain := Frullani.integral_Ioi_eq (f := fun x : ℝ => Real.exp (-x)) (a := c) (b := 1)
    (L := 1) (R := 0) ?_ h0 one_pos ?_ ?_ hint
  · simp only [smul_eq_mul, one_mul, div_div_eq_mul_div, one_mul, sub_zero, mul_one, one_div,
      Real.log_inv] at hmain
    have e : ∀ x, x⁻¹ * (Real.exp (-(c * x)) - Real.exp (-x)) = Fl ρ x a b := by
      intro x; unfold Fl; rw [← hcdef, mul_comm c x]
    simp only [e] at hmain
    exact hmain
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
  · have : Filter.Tendsto (fun x : ℝ => Real.exp (-x)) (nhds 0) (nhds 1) := by
      have hc : Continuous (fun x : ℝ => Real.exp (-x)) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  · exact Real.tendsto_exp_comp_nhds_zero.mpr Filter.tendsto_neg_atTop_atBot

end real

/-! ### Weighted kernels on a measurable space -/
section Glue
variable {Y : Type*} [MeasurableSpace Y]

/-- The kernel `e(y) e(y') k(pr y, pr y')` on `Y × Y`. -/
def Wk (pr e : Y → ℝ) (k : ℝ → ℝ → ℝ) : Y × Y → ℝ := fun z => e z.1 * e z.2 * k (pr z.1) (pr z.2)

/-- The signed measure `(A - M)` paired with a function. -/
def S1 (A M : Measure Y) (f : Y → ℝ) : ℝ := ∫ y, f y ∂A - ∫ y, f y ∂M

theorem integrable_param {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SFinite ν]
    {m : Measure Y} [IsFiniteMeasure m] {pr : Y → ℝ} (hpr : Measurable pr)
    (hloc : ∀ᵐ y ∂m, pr y ∈ Ioo (0:ℝ) 1) (hlog : Integrable (fun y => Real.log (pr y)) m)
    {e : Y → ℝ} (he : Measurable e) (heb : ∀ y, |e y| ≤ 1)
    {F : Θ → ℝ → ℝ → ℝ} (hFm : Measurable (fun p : Θ × ℝ × ℝ => F p.1 p.2.1 p.2.2))
    (hF0 : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → ∀ᵐ θ ∂ν, 0 ≤ F θ a b)
    (hint : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → Integrable (fun θ => F θ a b) ν)
    {c : ℝ} (hbd : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 →
      ∫ θ, F θ a b ∂ν ≤ c + |Real.log a| + |Real.log b|) :
    Integrable (Function.uncurry fun θ (z : Y × Y) => Wk pr e (F θ) z) (ν.prod (m.prod m)) := by
  set f : Θ × (Y × Y) → ℝ := Function.uncurry fun θ (z : Y × Y) => Wk pr e (F θ) z with hf
  have hfm : Measurable f := by
    have h1 : Measurable (fun p : Θ × (Y × Y) => e p.2.1) := he.comp (measurable_fst.comp measurable_snd)
    have h2 : Measurable (fun p : Θ × (Y × Y) => e p.2.2) := he.comp (measurable_snd.comp measurable_snd)
    have h3 : Measurable (fun p : Θ × (Y × Y) => F p.1 (pr p.2.1) (pr p.2.2)) :=
      hFm.comp (measurable_fst.prodMk ((hpr.comp (measurable_fst.comp measurable_snd)).prodMk
        (hpr.comp (measurable_snd.comp measurable_snd))))
    exact (h1.mul h2).mul h3
  rw [integrable_prod_iff' hfm.aestronglyMeasurable]
  have hae : ∀ᵐ z ∂(m.prod m), pr z.1 ∈ Ioo (0:ℝ) 1 ∧ pr z.2 ∈ Ioo (0:ℝ) 1 := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := m) (ν := m)).ae hloc
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := m) (ν := m)).ae hloc
    filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩
  constructor
  · filter_upwards [hae] with z hz
    have := (hint _ _ hz.1 hz.2).const_mul (e z.1 * e z.2)
    refine this.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp [hf, Wk]
  · have hg : Integrable (fun z : Y × Y => c + |Real.log (pr z.1)| + |Real.log (pr z.2)|) (m.prod m) := by
      have h1 : Integrable (fun z : Y × Y => |Real.log (pr z.1)|) (m.prod m) := hlog.abs.comp_fst m
      have h2 : Integrable (fun z : Y × Y => |Real.log (pr z.2)|) (m.prod m) := hlog.abs.comp_snd m
      exact ((integrable_const c).add h1).add h2
    refine hg.mono' ?_ ?_
    · exact (hfm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    · filter_upwards [hae] with z hz
      have hi := (hint _ _ hz.1 hz.2)
      have hnn : 0 ≤ ∫ θ, ‖f (θ, z)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      calc ∫ θ, ‖f (θ, z)‖ ∂ν ≤ ∫ θ, F θ (pr z.1) (pr z.2) ∂ν := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
              ((hF0 _ _ hz.1 hz.2).mono fun θ h0 => ?_)
            simp only [hf, Function.uncurry, Wk, norm_mul]
            have h1 := heb z.1; have h2 := heb z.2

            rw [Real.norm_of_nonneg h0]
            calc ‖e z.1‖ * ‖e z.2‖ * F θ (pr z.1) (pr z.2) ≤ 1 * 1 * F θ (pr z.1) (pr z.2) := by
                  apply mul_le_mul_of_nonneg_right _ h0
                  rw [Real.norm_eq_abs, Real.norm_eq_abs]
                  exact mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
              _ = _ := by ring
        _ ≤ _ := hbd _ _ hz.1 hz.2

theorem adm_of_bound {m : Measure Y} [IsFiniteMeasure m] {pr : Y → ℝ} (hpr : Measurable pr)
    (hloc : ∀ᵐ y ∂m, pr y ∈ Ioo (0:ℝ) 1) (hlog : Integrable (fun y => Real.log (pr y)) m)
    {e : Y → ℝ} (he : Measurable e) (heb : ∀ y, |e y| ≤ 1)
    {k : ℝ → ℝ → ℝ} (hk : Measurable (fun p : ℝ × ℝ => k p.1 p.2))
    {c : ℝ} (hb : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → |k a b| ≤ c + |Real.log a| + |Real.log b|) :
    Integrable (Wk pr e k) (m.prod m) := by
  have hkm : Measurable (Wk pr e k) := by
    have h1 : Measurable (fun z : Y × Y => e z.1) := he.comp measurable_fst
    have h2 : Measurable (fun z : Y × Y => e z.2) := he.comp measurable_snd
    have h3 : Measurable (fun z : Y × Y => k (pr z.1) (pr z.2)) :=
      hk.comp ((hpr.comp measurable_fst).prodMk (hpr.comp measurable_snd))
    exact (h1.mul h2).mul h3
  have hae : ∀ᵐ z ∂(m.prod m), pr z.1 ∈ Ioo (0:ℝ) 1 ∧ pr z.2 ∈ Ioo (0:ℝ) 1 := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := m) (ν := m)).ae hloc
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := m) (ν := m)).ae hloc
    filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩
  have hg : Integrable (fun z : Y × Y => c + |Real.log (pr z.1)| + |Real.log (pr z.2)|) (m.prod m) := by
    have h1 : Integrable (fun z : Y × Y => |Real.log (pr z.1)|) (m.prod m) := hlog.abs.comp_fst m
    have h2 : Integrable (fun z : Y × Y => |Real.log (pr z.2)|) (m.prod m) := hlog.abs.comp_snd m
    exact ((integrable_const c).add h1).add h2
  refine hg.mono' hkm.aestronglyMeasurable ?_
  filter_upwards [hae] with z hz
  simp only [Wk, norm_mul, Real.norm_eq_abs]
  have h1 := heb z.1; have h2 := heb z.2
  have h3 := hb _ _ hz.1 hz.2
  calc |e z.1| * |e z.2| * |k (pr z.1) (pr z.2)| ≤ 1 * 1 * |k (pr z.1) (pr z.2)| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ ≤ _ := by linarith

end Glue

section PPsec
variable {Y : Type*} [MeasurableSpace Y]

theorem P2_param_integrable {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SFinite ν]
    (F : Θ → Y × Y → ℝ)
    (hF : Integrable (Function.uncurry F) (ν.prod ((A + M).prod (A + M)))) :
    Integrable (fun θ => P2 A M (F θ)) ν := by
  have h1 : Integrable (Function.uncurry F) (ν.prod (A.prod A)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_right le_rfl)))
  have h2 : Integrable (Function.uncurry F) (ν.prod (A.prod M)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl)))
  have h3 : Integrable (Function.uncurry F) (ν.prod (M.prod A)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_left le_rfl) (Measure.le_add_right le_rfl)))
  have h4 : Integrable (Function.uncurry F) (ν.prod (M.prod M)) :=
    hF.mono_measure (Measure.prod_mono le_rfl (Measure.prod_mono (Measure.le_add_left le_rfl) (Measure.le_add_left le_rfl)))
  unfold P2
  exact (((h1.integral_prod_left.sub h2.integral_prod_left).sub h3.integral_prod_left).add
    h4.integral_prod_left)

/-- The standing hypotheses: positions in `(0,1)`, log-integrable, bounded measurable weight. -/
structure Ctx (A M : Measure Y) (pr e : Y → ℝ) : Prop where
  meas : Measurable pr
  loc : ∀ᵐ y ∂(A + M), pr y ∈ Ioo (0:ℝ) 1
  logint : Integrable (fun y => Real.log (pr y)) (A + M)
  emeas : Measurable e
  ebd : ∀ y, |e y| ≤ 1

/-- The paired double integral of a kernel. -/
def PP (A M : Measure Y) (pr e : Y → ℝ) (k : ℝ → ℝ → ℝ) : ℝ := P2 A M (Wk pr e k)

variable {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M] {pr e : Y → ℝ}

theorem Ctx.ae_pair (C : Ctx A M pr e) {μ μ' : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure μ'] (h : μ ≤ A + M) (h' : μ' ≤ A + M) :
    ∀ᵐ z ∂(μ.prod μ'), pr z.1 ∈ Ioo (0:ℝ) 1 ∧ pr z.2 ∈ Ioo (0:ℝ) 1 := by
  have l1 : ∀ᵐ y ∂μ, pr y ∈ Ioo (0:ℝ) 1 :=
    C.loc.filter_mono (Measure.absolutelyContinuous_of_le h).ae_le
  have l2 : ∀ᵐ y ∂μ', pr y ∈ Ioo (0:ℝ) 1 :=
    C.loc.filter_mono (Measure.absolutelyContinuous_of_le h').ae_le
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ')).ae l1
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ')).ae l2
  filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩

theorem PP_congr (C : Ctx A M pr e) {k k' : ℝ → ℝ → ℝ}
    (h : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → k a b = k' a b) :
    PP A M pr e k = PP A M pr e k' := by
  have hA : A ≤ A + M := Measure.le_add_right le_rfl
  have hM : M ≤ A + M := Measure.le_add_left le_rfl
  unfold PP P2
  have e1 : ∀ {μ μ' : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure μ'], μ ≤ A + M → μ' ≤ A + M →
      ∫ z, Wk pr e k z ∂(μ.prod μ') = ∫ z, Wk pr e k' z ∂(μ.prod μ') := by
    intro μ μ' _ _ h1 h2
    apply integral_congr_ae
    filter_upwards [C.ae_pair h1 h2] with z hz
    simp only [Wk, h _ _ hz.1 hz.2]
  rw [e1 hA hA, e1 hA hM, e1 hM hA, e1 hM hM]

theorem PP_add (C : Ctx A M pr e) {k₁ k₂ : ℝ → ℝ → ℝ}
    (h₁ : Integrable (Wk pr e k₁) ((A + M).prod (A + M)))
    (h₂ : Integrable (Wk pr e k₂) ((A + M).prod (A + M))) :
    PP A M pr e (fun a b => k₁ a b + k₂ a b) = PP A M pr e k₁ + PP A M pr e k₂ := by
  unfold PP
  rw [← P2_add h₁ h₂]
  congr 1; funext z; simp only [Wk]; ring

theorem PP_sub (C : Ctx A M pr e) {k₁ k₂ : ℝ → ℝ → ℝ}
    (h₁ : Integrable (Wk pr e k₁) ((A + M).prod (A + M)))
    (h₂ : Integrable (Wk pr e k₂) ((A + M).prod (A + M))) :
    PP A M pr e (fun a b => k₁ a b - k₂ a b) = PP A M pr e k₁ - PP A M pr e k₂ := by
  unfold PP
  rw [← P2_sub h₁ h₂]
  congr 1; funext z; simp only [Wk]; ring

theorem PP_smul (c : ℝ) (k : ℝ → ℝ → ℝ) :
    PP A M pr e (fun a b => c * k a b) = c * PP A M pr e k := by
  unfold PP
  rw [← P2_smul]
  congr 1; funext z; simp only [Wk]; ring

theorem PP_rankone (φ : ℝ → ℝ) :
    PP A M pr e (fun a b => φ a * φ b) = (S1 A M (fun y => e y * φ (pr y))) ^ 2 := by
  unfold PP S1
  rw [← P2_rankone]
  congr 1; funext z; simp only [Wk]; ring

theorem PP_const_eq (c : ℝ) (he : ∀ y, e y = 1) :
    PP A M pr e (fun _ _ => c) = c * (A.real univ - M.real univ) ^ 2 := by
  unfold PP
  have : Wk pr e (fun _ _ => c) = fun _ => c := by funext z; simp [Wk, he]
  rw [this, P2_const]

theorem PP_param {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [SFinite ν]
    (C : Ctx A M pr e)
    {F : Θ → ℝ → ℝ → ℝ} (hFm : Measurable (fun p : Θ × ℝ × ℝ => F p.1 p.2.1 p.2.2))
    (hF0 : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → ∀ᵐ θ ∂ν, 0 ≤ F θ a b)
    (hint : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → Integrable (fun θ => F θ a b) ν)
    {c : ℝ} (hbd : ∀ a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 →
      ∫ θ, F θ a b ∂ν ≤ c + |Real.log a| + |Real.log b|) :
    PP A M pr e (fun a b => ∫ θ, F θ a b ∂ν) = ∫ θ, PP A M pr e (F θ) ∂ν ∧
      Integrable (fun θ => PP A M pr e (F θ)) ν := by
  have hI := integrable_param ν (m := A + M) C.meas C.loc C.logint C.emeas C.ebd hFm hF0 hint hbd
  constructor
  · unfold PP
    have : Wk pr e (fun a b => ∫ θ, F θ a b ∂ν) = fun z => ∫ θ, Wk pr e (F θ) z ∂ν := by
      funext z; simp only [Wk, integral_const_mul]
    rw [this]
    exact P2_integral ν (fun θ => Wk pr e (F θ)) hI
  · exact P2_param_integrable ν (fun θ => Wk pr e (F θ)) hI

theorem PP_tsum (C : Ctx A M pr e) {K : ℕ → ℝ → ℝ → ℝ}
    (hKm : ∀ n, Measurable (fun p : ℝ × ℝ => K n p.1 p.2)) {c : ℕ → ℝ} (hc : Summable c)
    (hb : ∀ n a b, a ∈ Ioo (0:ℝ) 1 → b ∈ Ioo (0:ℝ) 1 → |K n a b| ≤ c n) :
    HasSum (fun n => PP A M pr e (K n)) (PP A M pr e (fun a b => ∑' n, K n a b)) := by
  have hA : A ≤ A + M := Measure.le_add_right le_rfl
  have hM : M ≤ A + M := Measure.le_add_left le_rfl
  have key : ∀ {μ μ' : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure μ'], μ ≤ A + M → μ' ≤ A + M →
      HasSum (fun n => ∫ z, Wk pr e (K n) z ∂(μ.prod μ')) (∫ z, Wk pr e (fun a b => ∑' n, K n a b) z ∂(μ.prod μ')) := by
    intro μ μ' _ _ h1 h2
    have hae := C.ae_pair h1 h2
    have hmeas : ∀ n, Measurable (Wk pr e (K n)) := by
      intro n
      have h1 : Measurable (fun z : Y × Y => e z.1) := C.emeas.comp measurable_fst
      have h2 : Measurable (fun z : Y × Y => e z.2) := C.emeas.comp measurable_snd
      have h3 : Measurable (fun z : Y × Y => K n (pr z.1) (pr z.2)) :=
        (hKm n).comp ((C.meas.comp measurable_fst).prodMk (C.meas.comp measurable_snd))
      exact (h1.mul h2).mul h3
    refine hasSum_integral_of_dominated_convergence (fun n _ => c n) (fun n => (hmeas n).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · intro n
      filter_upwards [hae] with z hz
      simp only [Wk, norm_mul, Real.norm_eq_abs]
      have h1 := C.ebd z.1; have h2 := C.ebd z.2
      have h3 := hb n _ _ hz.1 hz.2
      calc |e z.1| * |e z.2| * |K n (pr z.1) (pr z.2)| ≤ 1 * 1 * c n := by
            apply mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3 (abs_nonneg _) (by norm_num)
        _ = c n := by ring
    · exact Filter.Eventually.of_forall fun _ => hc
    · simpa using integrable_const (∑' n, c n)
    · filter_upwards [hae] with z hz
      have hs : Summable (fun n => K n (pr z.1) (pr z.2)) :=
        Summable.of_norm_bounded hc (fun n => by simpa using hb n _ _ hz.1 hz.2)
      have := (hs.hasSum).mul_left (e z.1 * e z.2)
      simpa [Wk, tsum_mul_left] using this
  unfold PP P2
  have := ((key hA hA).sub (key hA hM)).sub (key hM hA) |>.add (key hM hM)
  exact this

end PPsec

/-! ### Positive definiteness of the pieces -/
section PDsec

theorem measurable_psi (m : ℕ) (s : ℝ) : Measurable (fun a : ℝ => psi m s a) := by
  unfold psi
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem measurable_Gs (ρ : ℝ) : Measurable (fun p : ℝ × ℝ × ℝ => Gs ρ p.1 p.2.1 p.2.2) := by
  unfold Gs
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem Gs_nonneg {ρ a b s : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    0 ≤ Gs ρ s a b := by
  unfold Gs
  split_ifs with h
  · have ha' : a < s := lt_of_le_of_lt (le_max_left _ _) h
    have hb' : b < s := lt_of_le_of_lt (le_max_right _ _) h
    have hx : a * b / s ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    have hx0 : 0 < a * b / s ^ 2 := by positivity
    apply mul_nonneg (inv_nonneg.2 hs.le)
    apply div_nonneg (by positivity) (by nlinarith)
  · exact le_rfl

theorem Gs_le {ρ a b s : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    Gs ρ s a b ≤ (max a b)⁻¹ * ((1 + ρ) / (1 - ρ)) := by
  have hM := max_pos' (b := b) ha
  unfold Gs
  split_ifs with h
  · have ha' : a < s := lt_of_le_of_lt (le_max_left _ _) h
    have hb' : b < s := lt_of_le_of_lt (le_max_right _ _) h
    have hx : a * b / s ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    have hx0 : 0 < a * b / s ^ 2 := by positivity
    have h1 : (1 + ρ * (a * b / s ^ 2)) / (1 - ρ * (a * b / s ^ 2)) ≤ (1 + ρ) / (1 - ρ) := by
      rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith
    have h2 : s⁻¹ ≤ (max a b)⁻¹ := inv_anti₀ hM h.le
    have h3 : 0 ≤ (1 + ρ * (a * b / s ^ 2)) / (1 - ρ * (a * b / s ^ 2)) :=
      div_nonneg (by positivity) (by nlinarith)
    calc s⁻¹ * ((1 + ρ * (a * b / s ^ 2)) / (1 - ρ * (a * b / s ^ 2)))
        ≤ (max a b)⁻¹ * ((1 + ρ * (a * b / s ^ 2)) / (1 - ρ * (a * b / s ^ 2))) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hM.le)
  · positivity

variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem PP_Gs_nonneg (C : Ctx A M pr e) {ρ s : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) :
    0 ≤ PP A M pr e (Gs ρ s) := by
  have hsum := PP_tsum (A := A) (M := M) (pr := pr) (e := e) C
    (K := fun m a b => (s⁻¹ * cc ρ m) * (psi m s a * psi m s b))
    (fun m => by
      have := measurable_psi m s
      fun_prop)
    (c := fun m => s⁻¹ * cc ρ m)
    ((summable_cc hρ0.le hρ1).mul_left _)
    (by
      intro m a b ha hb
      have h0 := psi_nonneg m hs ha.1.le
      have h1 := psi_nonneg m hs hb.1.le
      have h2 := psi_le_one m hs ha.1.le
      have h3 := psi_le_one m hs hb.1.le
      have hc := cc_nonneg hρ0.le m
      rw [abs_of_nonneg (by positivity)]
      calc s⁻¹ * cc ρ m * (psi m s a * psi m s b) ≤ s⁻¹ * cc ρ m * (1 * 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul h2 h3 h1 zero_le_one
        _ = _ := by ring)
  have hk : PP A M pr e (Gs ρ s) = PP A M pr e (fun a b => ∑' m, (s⁻¹ * cc ρ m) * (psi m s a * psi m s b)) := by
    apply PP_congr C
    intro a b ha hb
    exact (Gs_hasSum hρ0.le hρ1 ha.1 hb.1 hs).tsum_eq.symm
  rw [hk]
  refine hsum.nonneg (fun m => ?_)
  rw [PP_smul, PP_rankone (A := A) (M := M) (pr := pr) (e := e) (fun a => psi m s a)]
  have := cc_nonneg hρ0.le m
  positivity


theorem measurable_K1d (ρ : ℝ) : Measurable (fun p : ℝ × ℝ => K1d ρ p.1 p.2) := by
  unfold K1d rr; fun_prop
theorem measurable_K2d (ρ : ℝ) : Measurable (fun p : ℝ × ℝ => K2d ρ p.1 p.2) := by
  unfold K2d rr; fun_prop
theorem measurable_ell (ρ : ℝ) : Measurable (fun p : ℝ × ℝ => ell ρ p.1 p.2) := by
  unfold ell; fun_prop

theorem adm_K1d (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (Wk pr e (K1d ρ)) ((A + M).prod (A + M)) :=
  adm_of_bound C.meas C.loc C.logint C.emeas C.ebd (measurable_K1d ρ) (c := |Real.log (1 - ρ)|)
    (fun a b ha hb => by
      rw [abs_of_nonneg (K1d_nonneg hρ0 hρ1 ha.1 ha.2 hb.1 hb.2)]
      have := K1d_le hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      linarith [abs_nonneg (Real.log b)])

theorem adm_K2d (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (Wk pr e (K2d ρ)) ((A + M).prod (A + M)) :=
  adm_of_bound C.meas C.loc C.logint C.emeas C.ebd (measurable_K2d ρ) (c := 1)
    (fun a b ha hb => by
      have := K2d_abs_le hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      linarith [abs_nonneg (Real.log b)])

theorem adm_ell (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (Wk pr e (ell ρ)) ((A + M).prod (A + M)) :=
  adm_of_bound C.meas C.loc C.logint C.emeas C.ebd (measurable_ell ρ) (c := |Real.log (1 - ρ)|)
    (fun a b ha hb => by
      rw [abs_of_nonneg (ell_nonneg hρ0 hρ1 ha.1 ha.2 hb.1 hb.2)]
      have := ell_le hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      linarith [abs_nonneg (Real.log b), abs_nonneg (Real.log a)])

theorem adm_G (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (Wk pr e (fun a b => K1d ρ a b - ell ρ a b)) ((A + M).prod (A + M)) :=
  adm_of_bound C.meas C.loc C.logint C.emeas C.ebd
    ((measurable_K1d ρ).sub (measurable_ell ρ)) (c := |Real.log (1 - ρ)|)
    (fun a b ha hb => by
      have h1 := K1d_nonneg hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      have h2 := K1d_le hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      have h3 := ell_nonneg hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      have h4 := ell_le hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      rw [abs_le]; constructor <;> linarith [abs_nonneg (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log (1-ρ))])

theorem PP_G_nonneg (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 ≤ PP A M pr e (fun a b => K1d ρ a b - ell ρ a b) := by
  set ν : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hν
  have hc : PP A M pr e (fun a b => K1d ρ a b - ell ρ a b) = PP A M pr e (fun a b => ∫ s, Gs ρ s a b ∂ν) :=
    PP_congr C (fun a b ha hb => (Gs_integral hρ0 hρ1 ha.1 ha.2 hb.1 hb.2).symm)
  have hmeas : ∀ a b : ℝ, Measurable (fun s : ℝ => Gs ρ s a b) := fun a b =>
    (measurable_Gs ρ).comp (by fun_prop : Measurable fun s : ℝ => (s, a, b))
  obtain ⟨h1, h2⟩ := PP_param ν C (F := Gs ρ) (measurable_Gs ρ)
    (fun a b ha hb => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact Gs_nonneg hρ0 hρ1 ha.1 hb.1 hs.1)
    (fun a b ha hb => by
      refine Integrable.of_bound (hmeas a b).aestronglyMeasurable ((max a b)⁻¹ * ((1 + ρ) / (1 - ρ))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_of_nonneg (Gs_nonneg hρ0 hρ1 ha.1 hb.1 hs.1)]
      exact Gs_le hρ0 hρ1 ha.1 hb.1 hs.1)
    (c := |Real.log (1 - ρ)|)
    (fun a b ha hb => by
      rw [hν, Gs_integral hρ0 hρ1 ha.1 ha.2 hb.1 hb.2]
      have h1 := K1d_le hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      have h3 := ell_nonneg hρ0 hρ1 ha.1 ha.2 hb.1 hb.2
      linarith [abs_nonneg (Real.log b)])
  rw [hc, h1]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact PP_Gs_nonneg C hρ0 hρ1 hs.1

end PDsec

/-! ### The Frullani part -/
section Frull

/-- the rank-one factor of `exp(-λ cX)` at level `τ`. -/
def pf (ρ lam τ a : ℝ) : ℝ :=
  Real.exp (-(lam * ρ * a / 2)) * (if τ < Real.exp (-(lam * (1 - ρ) * a / 2)) then 1 else 0)

theorem integral_ind2 {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    ∫ τ in Ioo (0:ℝ) 1, (if τ < u then (1:ℝ) else 0) * (if τ < v then (1:ℝ) else 0) = min u v := by
  have h1 : ∀ τ : ℝ, (if τ < u then (1:ℝ) else 0) * (if τ < v then (1:ℝ) else 0) =
      (Iio (min u v)).indicator (fun _ => (1:ℝ)) τ := by
    intro τ
    by_cases h : τ < min u v
    · rw [indicator_of_mem (mem_Iio.mpr h), if_pos (lt_of_lt_of_le h (min_le_left _ _)),
        if_pos (lt_of_lt_of_le h (min_le_right _ _))]; ring
    · rw [indicator_of_notMem (by simpa using h)]
      rcases lt_min_iff.not.mp h |> not_and_or.mp with h' | h'
      · rw [if_neg h']; ring
      · rw [if_neg h']; ring
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Iio]
  have : Ioo (0:ℝ) 1 ∩ Iio (min u v) = Ioo 0 (min u v) := by
    ext τ; simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, lt_of_lt_of_le h3 (le_trans (min_le_left _ _) hu1)⟩, h3⟩
  rw [this]
  simp [Real.volume_real_Ioo, le_min hu hv]

theorem E_eq {ρ a b lam : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hl : 0 < lam) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.exp (-(lam * cX ρ a b)) = ∫ τ in Ioo (0:ℝ) 1, pf ρ lam τ a * pf ρ lam τ b := by
  set u := Real.exp (-(lam * (1 - ρ) * a / 2)) with hu
  set v := Real.exp (-(lam * (1 - ρ) * b / 2)) with hv
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hv0 : 0 ≤ v := (Real.exp_pos _).le
  have hu1 : u ≤ 1 := by
    rw [hu, Real.exp_le_one_iff]; have : 0 ≤ lam * (1 - ρ) * a / 2 := by
      have : 0 < 1 - ρ := by linarith
      positivity
    linarith
  have hv1 : v ≤ 1 := by
    rw [hv, Real.exp_le_one_iff]; have : 0 ≤ lam * (1 - ρ) * b / 2 := by
      have : 0 < 1 - ρ := by linarith
      positivity
    linarith
  have h1 : ∀ τ : ℝ, pf ρ lam τ a * pf ρ lam τ b =
      (Real.exp (-(lam * ρ * a / 2)) * Real.exp (-(lam * ρ * b / 2))) *
        ((if τ < u then (1:ℝ) else 0) * (if τ < v then (1:ℝ) else 0)) := by
    intro τ; unfold pf; ring
  simp_rw [h1]
  rw [integral_const_mul, integral_ind2 hu0 hv0 hu1 hv1]
  rw [← Real.exp_add]
  have hmin : min u v = Real.exp (-(lam * (1 - ρ) * max a b / 2)) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      apply min_eq_right
      rw [hu, hv, Real.exp_le_exp]
      have : 0 < 1 - ρ := by linarith
      nlinarith [mul_pos hl this]
    · rw [max_eq_left h]
      apply min_eq_left
      rw [hu, hv, Real.exp_le_exp]
      have : 0 < 1 - ρ := by linarith
      nlinarith [mul_pos hl this]
  rw [hmin, ← Real.exp_add]
  congr 1
  unfold cX
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]; ring

end Frull

section Frull2
variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem measurable_pf (ρ lam : ℝ) : Measurable (fun p : ℝ × ℝ => pf ρ lam p.1 p.2) := by
  unfold pf
  refine (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-(lam * ρ * p.2 / 2))).mul ?_
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const measurable_const

theorem measurable_Fl (ρ : ℝ) : Measurable (fun p : ℝ × ℝ × ℝ => Fl ρ p.1 p.2.1 p.2.2) := by
  unfold Fl cX; fun_prop

theorem measurable_E (ρ : ℝ) (lam : ℝ) :
    Measurable (fun p : ℝ × ℝ => Real.exp (-(lam * cX ρ p.1 p.2))) := by
  unfold cX; fun_prop

theorem adm_const (C : Ctx A M pr e) (c : ℝ) :
    Integrable (Wk pr e (fun _ _ => c)) ((A + M).prod (A + M)) :=
  adm_of_bound C.meas C.loc C.logint C.emeas C.ebd measurable_const (c := |c|)
    (fun a b _ _ => by linarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)])

theorem pf_nonneg {ρ lam τ a : ℝ} : 0 ≤ pf ρ lam τ a := by
  unfold pf; split_ifs <;> positivity

theorem pf_le_one {ρ lam τ a : ℝ} (hρ : 0 ≤ ρ) (hl : 0 ≤ lam) (ha : 0 ≤ a) : pf ρ lam τ a ≤ 1 := by
  unfold pf
  have : Real.exp (-(lam * ρ * a / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ lam * ρ * a / 2 := by positivity
    linarith
  split_ifs <;> linarith

theorem PP_E_nonneg (C : Ctx A M pr e) {ρ lam : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hl : 0 < lam) :
    0 ≤ PP A M pr e (fun a b => Real.exp (-(lam * cX ρ a b))) := by
  set ν : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hν
  have hc : PP A M pr e (fun a b => Real.exp (-(lam * cX ρ a b))) =
      PP A M pr e (fun a b => ∫ τ, pf ρ lam τ a * pf ρ lam τ b ∂ν) :=
    PP_congr C (fun a b ha hb => E_eq hρ0 hρ1 hl ha.1.le hb.1.le)
  have hFm : Measurable (fun p : ℝ × ℝ × ℝ => pf ρ lam p.1 p.2.1 * pf ρ lam p.1 p.2.2) := by
    have h1 : Measurable (fun p : ℝ × ℝ × ℝ => pf ρ lam p.1 p.2.1) :=
      (measurable_pf ρ lam).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : Measurable (fun p : ℝ × ℝ × ℝ => pf ρ lam p.1 p.2.2) :=
      (measurable_pf ρ lam).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact h1.mul h2
  obtain ⟨h1, h2⟩ := PP_param ν C (F := fun τ a b => pf ρ lam τ a * pf ρ lam τ b) hFm
    (fun a b ha hb => Filter.Eventually.of_forall fun τ => mul_nonneg pf_nonneg pf_nonneg)
    (fun a b ha hb => by
      refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun τ => ?_)
      · have h1 := (measurable_pf ρ lam).comp (measurable_id.prodMk (measurable_const (a := a)))
        have h2 := (measurable_pf ρ lam).comp (measurable_id.prodMk (measurable_const (a := b)))
        exact (h1.mul h2).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (mul_nonneg pf_nonneg pf_nonneg)]
        have := pf_le_one (τ := τ) hρ0.le hl.le ha.1.le
        have := pf_le_one (τ := τ) hρ0.le hl.le hb.1.le
        have := pf_nonneg (ρ := ρ) (lam := lam) (τ := τ) (a := a)
        have := pf_nonneg (ρ := ρ) (lam := lam) (τ := τ) (a := b)
        nlinarith)
    (c := 1)
    (fun a b ha hb => by
      rw [hν, ← E_eq hρ0 hρ1 hl ha.1.le hb.1.le]
      have : Real.exp (-(lam * cX ρ a b)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := cX_pos hρ0 ha.1 hb.1
        have : 0 ≤ lam * cX ρ a b := by positivity
        linarith
      linarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)])
  rw [hc, h1]
  apply integral_nonneg
  intro τ
  show 0 ≤ PP A M pr e (fun a b => pf ρ lam τ a * pf ρ lam τ b)
  rw [PP_rankone (A := A) (M := M) (pr := pr) (e := e) (fun a => pf ρ lam τ a)]
  positivity

theorem PP_Fl_nonneg (C : Ctx A M pr e) (hmass : A.real univ = M.real univ) (he1 : ∀ y, e y = 1)
    {ρ lam : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hl : 0 < lam) :
    0 ≤ PP A M pr e (Fl ρ lam) := by
  have hE : Integrable (Wk pr e (fun a b => Real.exp (-(lam * cX ρ a b)))) ((A + M).prod (A + M)) :=
    adm_of_bound C.meas C.loc C.logint C.emeas C.ebd
      ((measurable_E ρ lam)) (c := 1)
      (fun a b ha hb => by
        have : Real.exp (-(lam * cX ρ a b)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := cX_pos hρ0 ha.1 hb.1
          have : 0 ≤ lam * cX ρ a b := by positivity
          linarith
        rw [abs_of_pos (Real.exp_pos _)]
        linarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)])
  have h0 : PP A M pr e (fun _ _ => Real.exp (-lam)) = 0 := by
    rw [PP_const_eq _ he1, hmass]; ring
  have hfl : PP A M pr e (Fl ρ lam) = PP A M pr e (fun a b => lam⁻¹ * (Real.exp (-(lam * cX ρ a b)) - Real.exp (-lam))) := rfl
  rw [hfl, PP_smul, PP_sub C hE (adm_const C _), h0]
  have := PP_E_nonneg C hρ0 hρ1 hl
  have : 0 ≤ lam⁻¹ := inv_nonneg.2 hl.le
  positivity

end Frull2

section K2sec
variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem Fl_integrable {ρ a b : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b)
    (ha1 : a < 1) (hb1 : b < 1) :
    Integrable (fun lam => Fl ρ lam a b) (volume.restrict (Ioi (0:ℝ))) := by
  have h1 := cX_lt_one hρ1 ha1 hb1 ha hb
  have h0 := cX_pos hρ0 ha hb
  set c := cX ρ a b with hcdef
  have hI : IntegrableOn (fun x : ℝ => (1 - c) * Real.exp (-c * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul (1 - c)
  refine hI.mono' ?_ ?_
  · exact ((measurable_Fl ρ).comp (by fun_prop : Measurable fun lam : ℝ => (lam, a, b))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have := Fl_nonneg hρ0 hρ1 ha hb ha1 hb1 hx
    have h2 := Fl_le hρ0 hρ1 ha hb ha1 hb1 hx
    rw [Real.norm_of_nonneg this, neg_mul]; exact h2

theorem neg_log_cX_le {ρ a b : ℝ} (hρ0 : 0 < ρ) (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) :
    -Real.log (cX ρ a b) ≤ 1 + |Real.log a| := by
  have hM := max_pos' (b := b) ha
  have hm : 0 < min a b := lt_min ha hb
  have h1 : max a b / 2 ≤ cX ρ a b := by unfold cX; nlinarith
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_div hM.ne' (by norm_num)] at h2
  have h3 := log_max_le (b := b) ha ha1
  have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

theorem PP_K2d_nonneg (C : Ctx A M pr e) (hmass : A.real univ = M.real univ) (he1 : ∀ y, e y = 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 ≤ PP A M pr e (K2d ρ) := by
  set ν : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hν
  have hcongr : PP A M pr e (fun a b => K2d ρ a b - (-Real.log 2)) =
      PP A M pr e (fun a b => ∫ lam, Fl ρ lam a b ∂ν) :=
    PP_congr C (fun a b ha hb => by
      rw [K2d_eq_cX hρ0 ha.1 hb.1, hν, Fl_integral hρ0 hρ1 ha.1 hb.1 ha.2 hb.2]; ring)
  obtain ⟨h1, h2⟩ := PP_param ν C (F := Fl ρ) (measurable_Fl ρ)
    (fun a b ha hb => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lam hl
      exact Fl_nonneg hρ0 hρ1 ha.1 hb.1 ha.2 hb.2 hl)
    (fun a b ha hb => Fl_integrable hρ0 hρ1 ha.1 hb.1 ha.2 hb.2)
    (c := 1)
    (fun a b ha hb => by
      rw [hν, Fl_integral hρ0 hρ1 ha.1 hb.1 ha.2 hb.2]
      have := neg_log_cX_le hρ0 ha.1 hb.1 ha.2
      linarith [abs_nonneg (Real.log b)])
  have hnn : 0 ≤ ∫ lam, PP A M pr e (Fl ρ lam) ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with lam hl
    exact PP_Fl_nonneg C hmass he1 hρ0 hρ1 hl
  have hsub : PP A M pr e (fun a b => K2d ρ a b - (-Real.log 2)) =
      PP A M pr e (K2d ρ) - PP A M pr e (fun _ _ => -Real.log 2) :=
    PP_sub C (adm_K2d C hρ0 hρ1) (adm_const C (-Real.log 2))
  have hc0 : PP A M pr e (fun _ _ => -Real.log 2) = 0 := by
    rw [PP_const_eq _ he1, hmass]; ring
  rw [hsub, hc0, sub_zero] at hcongr
  rw [hcongr, h1]; exact hnn

end K2sec

/-! ### The series for `ell` and for `K1d - K2d` -/
section Hsec

/-- `(rr^m - (ab)^m)/(2m)`, the value of `∫ σ⁻¹ ψ_{m,σ}(a) ψ_{m,σ}(b)`. -/
def Rm (m : ℕ) (a b : ℝ) : ℝ := (rr a b ^ m - (a * b) ^ m) / (2 * m)
/-- the `σ`-density of `Rm`. -/
def Hs (m : ℕ) (σ a b : ℝ) : ℝ := σ⁻¹ * (psi m σ a * psi m σ b)

theorem measurable_Hs (m : ℕ) : Measurable (fun p : ℝ × ℝ × ℝ => Hs m p.1 p.2.1 p.2.2) := by
  unfold Hs psi
  refine (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ => p.1⁻¹).mul ?_
  refine Measurable.mul ?_ ?_
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) measurable_const
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) measurable_const

theorem measurable_Rm (m : ℕ) : Measurable (fun p : ℝ × ℝ => Rm m p.1 p.2) := by
  unfold Rm rr; fun_prop

theorem Hs_nonneg {m : ℕ} {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Hs m σ a b := by
  unfold Hs
  have := psi_nonneg m hσ ha; have := psi_nonneg m hσ hb
  positivity

theorem Hs_le {m : ℕ} {σ a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : 0 < σ) :
    Hs m σ a b ≤ (max a b)⁻¹ := by
  have hM := max_pos' (b := b) ha
  unfold Hs
  by_cases h : max a b < σ
  · have h2 : σ⁻¹ ≤ (max a b)⁻¹ := inv_anti₀ hM h.le
    have h3 := psi_le_one m hσ ha.le; have h4 := psi_le_one m hσ hb.le
    have h5 := psi_nonneg m hσ ha.le; have h6 := psi_nonneg m hσ hb.le
    calc σ⁻¹ * (psi m σ a * psi m σ b) ≤ σ⁻¹ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hσ.le)
          nlinarith
      _ ≤ _ := by linarith
  · have : psi m σ a * psi m σ b = 0 := by
      have : ¬ (a < σ ∧ b < σ) := fun hh => h (max_lt hh.1 hh.2)
      unfold psi
      by_cases h2 : a < σ
      · have h3 : ¬ b < σ := fun h3 => this ⟨h2, h3⟩
        simp [h3]
      · simp [h2]
    rw [this, mul_zero]; exact inv_nonneg.2 hM.le

theorem Rm_nonneg {m : ℕ} (hm : 0 < m) {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    0 ≤ Rm m a b := by
  unfold Rm
  have h1 : (a * b) ≤ rr a b := by
    have := ab_div_max_sq ha (b := b)
    have hM := max_pos' (b := b) ha
    have hr := rr_le_one (b := b) ha
    have hM1 : max a b ^ 2 ≤ 1 := by have := max_lt ha1 hb1; nlinarith
    rw [← this, le_div_iff₀ (by positivity)]
    have : a * b ≤ max a b ^ 2 := by
      rw [mul_eq_min_max, sq]; exact mul_le_mul_of_nonneg_right min_le_max hM.le
    nlinarith [mul_pos ha hb, mul_le_mul_of_nonneg_left hM1 (mul_pos ha hb).le]
  have h2 : (a * b) ^ m ≤ rr a b ^ m := pow_le_pow_left₀ (by positivity) h1 m
  have : (0:ℝ) < 2 * m := by positivity
  exact div_nonneg (by linarith) this.le

theorem Rm_le_one {m : ℕ} (hm : 0 < m) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Rm m a b ≤ 1 := by
  unfold Rm
  have hr := rr_le_one (b := b) ha
  have hr0 := rr_pos ha hb
  have h2 : rr a b ^ m ≤ 1 := pow_le_one₀ hr0.le hr
  have h3 : 0 ≤ (a * b) ^ m := by positivity
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  rw [div_le_one (by positivity)]
  linarith

theorem psi_integral {m : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∫ σ in Ioo (0:ℝ) 1, σ ^ m * psi m σ a = a ^ m * (1 - a) := by
  have h1 : ∀ σ : ℝ, σ ^ m * psi m σ a = (Ioi a).indicator (fun _ => a ^ m) σ := by
    intro σ
    by_cases h : a < σ
    · have hσ : 0 < σ := ha.trans h
      rw [indicator_of_mem (mem_Ioi.mpr h)]; unfold psi; rw [if_pos h, div_pow]
      field_simp
    · rw [indicator_of_notMem (by simpa using h)]; unfold psi; rw [if_neg h]; simp
  simp_rw [h1]
  rw [setIntegral_indicator measurableSet_Ioi]
  have : Ioo (0:ℝ) 1 ∩ Ioi a = Ioo a 1 := by
    ext σ; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨ha.trans h3, h2⟩, h3⟩
  rw [this, setIntegral_const]
  simp [Real.volume_real_Ioo, ha1.le]
  ring

variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

/-- moments. -/
def mom (A M : Measure Y) (pr e : Y → ℝ) (k : ℕ) : ℝ := S1 A M (fun y => e y * pr y ^ k)
/-- sections. -/
def Gf (A M : Measure Y) (pr e : Y → ℝ) (m : ℕ) (σ : ℝ) : ℝ :=
  S1 A M (fun y => e y * psi m σ (pr y))

theorem PP_ell (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    HasSum (fun k : ℕ => ρ ^ (k + 1) / (k + 1) * (mom A M pr e (k + 1)) ^ 2) (PP A M pr e (ell ρ)) := by
  have h := PP_tsum (A := A) (M := M) (pr := pr) (e := e) C
    (K := fun k a b => ρ ^ (k + 1) / (k + 1) * (a ^ (k + 1) * b ^ (k + 1)))
    (fun k => by fun_prop) (c := fun k => ρ ^ (k + 1))
    ((summable_geometric_of_lt_one hρ0.le hρ1).comp_injective (add_left_injective 1) |>.congr (fun k => rfl))
    (by
      intro k a b ha hb
      have ha0 := ha.1; have hb0 := hb.1
      have h1 : 0 < a ^ (k + 1) * b ^ (k + 1) := by have := ha.1; have := hb.1; positivity
      have h2 : a ^ (k + 1) * b ^ (k + 1) ≤ 1 :=
        mul_le_one₀ (pow_le_one₀ ha.1.le ha.2.le) (by positivity) (pow_le_one₀ hb.1.le hb.2.le)
      rw [abs_of_nonneg (by positivity)]
      have h3 : ρ ^ (k + 1) / (k + 1) ≤ ρ ^ (k + 1) :=
        div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
      calc ρ ^ (k + 1) / (k + 1) * (a ^ (k + 1) * b ^ (k + 1)) ≤ ρ ^ (k + 1) / (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ _ := by linarith)
  have hk : PP A M pr e (ell ρ) = PP A M pr e (fun a b => ∑' k : ℕ, ρ ^ (k + 1) / (k + 1) * (a ^ (k + 1) * b ^ (k + 1))) := by
    apply PP_congr C
    intro a b ha hb
    have := (ell_hasSum hρ0 hρ1 ha.1 ha.2 hb.1 hb.2).tsum_eq
    rw [← this]
    congr 1; funext k; rw [mul_pow]
  rw [hk]
  have hfun : (fun k : ℕ => ρ ^ (k + 1) / (k + 1) * (mom A M pr e (k + 1)) ^ 2) =
      fun k : ℕ => PP A M pr e (fun a b => ρ ^ (k + 1) / (k + 1) * (a ^ (k + 1) * b ^ (k + 1))) := by
    funext k
    rw [PP_smul, PP_rankone (A := A) (M := M) (pr := pr) (e := e) (fun a => a ^ (k + 1))]
    rfl
  rw [hfun]; exact h

end Hsec

section Hsec2
variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem PP_Rm (C : Ctx A M pr e) {m : ℕ} (hm : 0 < m) :
    PP A M pr e (Rm m) = ∫ σ in Ioo (0:ℝ) 1, σ⁻¹ * (Gf A M pr e m σ) ^ 2 ∧
      Integrable (fun σ => σ⁻¹ * (Gf A M pr e m σ) ^ 2) (volume.restrict (Ioo (0:ℝ) 1)) := by
  set ν : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hν
  have hcongr : PP A M pr e (Rm m) = PP A M pr e (fun a b => ∫ σ, Hs m σ a b ∂ν) :=
    PP_congr C (fun a b ha hb => by
      rw [hν]; unfold Hs; rw [Hs_integral ha.1 ha.2 hb.1 hb.2 hm]; rfl)
  have hmeas : ∀ a b : ℝ, Measurable (fun σ : ℝ => Hs m σ a b) := fun a b =>
    (measurable_Hs m).comp (by fun_prop : Measurable fun σ : ℝ => (σ, a, b))
  obtain ⟨h1, h2⟩ := PP_param ν C (F := Hs m) (measurable_Hs m)
    (fun a b ha hb => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
      exact Hs_nonneg hσ.1 ha.1.le hb.1.le)
    (fun a b ha hb => by
      refine Integrable.of_bound (hmeas a b).aestronglyMeasurable ((max a b)⁻¹) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
      rw [Real.norm_of_nonneg (Hs_nonneg hσ.1 ha.1.le hb.1.le)]
      exact Hs_le ha.1 hb.1 hσ.1)
    (c := 1)
    (fun a b ha hb => by
      have : ∫ σ, Hs m σ a b ∂ν = Rm m a b := by
        rw [hν]; unfold Hs; rw [Hs_integral ha.1 ha.2 hb.1 hb.2 hm]; rfl
      rw [this]
      linarith [Rm_le_one hm ha.1 hb.1, abs_nonneg (Real.log a), abs_nonneg (Real.log b)])
  have hpt : ∀ σ : ℝ, PP A M pr e (Hs m σ) = σ⁻¹ * (Gf A M pr e m σ) ^ 2 := by
    intro σ
    have : Hs m σ = fun a b => σ⁻¹ * (psi m σ a * psi m σ b) := rfl
    rw [this, PP_smul, PP_rankone (A := A) (M := M) (pr := pr) (e := e) (fun a => psi m σ a)]
    rfl
  constructor
  · rw [hcongr, h1]; exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  · exact h2.congr (Filter.Eventually.of_forall hpt)

/-- the series terms for `K1d - K2d` -/
def Tn (ρ : ℝ) (n : ℕ) (a b : ℝ) : ℝ :=
  (2 * ρ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) * rr a b ^ (2 * n + 1)

theorem measurable_Tn (ρ : ℝ) (n : ℕ) : Measurable (fun p : ℝ × ℝ => Tn ρ n p.1 p.2) := by
  unfold Tn rr; fun_prop

theorem PP_Tm (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {m : ℕ} (hm0 : 0 < m) :
    PP A M pr e (fun a b => (2 * ρ ^ m / (m : ℝ)) * rr a b ^ m) =
      (2 * ρ ^ m / (m : ℝ)) * (mom A M pr e m) ^ 2
      + 4 * ρ ^ m * ∫ σ in Ioo (0:ℝ) 1, σ⁻¹ * (Gf A M pr e m σ) ^ 2 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm0
  have hk : PP A M pr e (fun a b => (2 * ρ ^ m / (m : ℝ)) * rr a b ^ m) =
      PP A M pr e (fun a b => (2 * ρ ^ m / (m : ℝ)) * (a ^ m * b ^ m) + (4 * ρ ^ m) * Rm m a b) := by
    apply PP_congr C
    intro a b ha hb
    unfold Rm
    rw [mul_pow]
    field_simp
    ring
  have hA1 : Integrable (Wk pr e (fun a b => (2 * ρ ^ m / (m : ℝ)) * (a ^ m * b ^ m))) ((A + M).prod (A + M)) :=
    adm_of_bound C.meas C.loc C.logint C.emeas C.ebd (by fun_prop) (c := 2 * ρ ^ m / (m : ℝ))
      (fun a b ha hb => by
        have h2 : a ^ m * b ^ m ≤ 1 :=
          mul_le_one₀ (pow_le_one₀ ha.1.le ha.2.le) (by have := hb.1; positivity) (pow_le_one₀ hb.1.le hb.2.le)
        have h3 : 0 ≤ a ^ m * b ^ m := by have := ha.1; have := hb.1; positivity
        have h4 : 0 ≤ 2 * ρ ^ m / (m : ℝ) := by positivity
        rw [abs_of_nonneg (by positivity)]
        nlinarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)])
  have hA2 : Integrable (Wk pr e (fun a b => (4 * ρ ^ m) * Rm m a b)) ((A + M).prod (A + M)) :=
    adm_of_bound C.meas C.loc C.logint C.emeas C.ebd ((measurable_Rm m).const_mul _) (c := 4 * ρ ^ m)
      (fun a b ha hb => by
        have h1 := Rm_nonneg hm0 ha.1 ha.2 hb.1 hb.2
        have h2 := Rm_le_one hm0 ha.1 hb.1
        have h4 : 0 ≤ 4 * ρ ^ m := by positivity
        rw [abs_of_nonneg (by positivity)]
        nlinarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)])
  rw [hk, PP_add C hA1 hA2, PP_smul, PP_smul,
    PP_rankone (A := A) (M := M) (pr := pr) (e := e) (fun a => a ^ m), (PP_Rm C hm0).1]
  rfl

theorem PP_Tn (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n : ℕ) :
    PP A M pr e (Tn ρ n) = (2 * ρ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) * (mom A M pr e (2 * n + 1)) ^ 2
      + 4 * ρ ^ (2 * n + 1) * ∫ σ in Ioo (0:ℝ) 1, σ⁻¹ * (Gf A M pr e (2 * n + 1) σ) ^ 2 :=
  PP_Tm C hρ0 hρ1 (by omega)

theorem PP_H_hasSum (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    HasSum (fun n : ℕ => PP A M pr e (Tn ρ n)) (PP A M pr e (fun a b => K1d ρ a b - K2d ρ a b)) := by
  have hc0 : Summable (fun n : ℕ => ρ ^ (2 * n + 1)) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).comp_injective (i := fun n : ℕ => 2 * n + 1)
      (fun x y h => by simpa using h)
  have hc : Summable (fun n : ℕ => 2 * ρ ^ (2 * n + 1)) := hc0.mul_left 2
  have h := PP_tsum (A := A) (M := M) (pr := pr) (e := e) C (K := Tn ρ) (measurable_Tn ρ)
    hc (by
      intro n a b ha hb
      unfold Tn
      have hr := rr_le_one (b := b) ha.1
      have hr0 := rr_pos ha.1 hb.1
      have h1 : rr a b ^ (2 * n + 1) ≤ 1 := pow_le_one₀ hr0.le hr
      have h2 : (1:ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
      have h3 : 2 * ρ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * ρ ^ (2 * n + 1) :=
        div_le_self (by positivity) h2
      rw [abs_of_nonneg (by positivity)]
      calc 2 * ρ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) * rr a b ^ (2 * n + 1)
          ≤ 2 * ρ ^ (2 * n + 1) * 1 := mul_le_mul h3 h1 (by positivity) (by positivity)
        _ = _ := by ring)
  have hk : PP A M pr e (fun a b => K1d ρ a b - K2d ρ a b) = PP A M pr e (fun a b => ∑' n, Tn ρ n a b) := by
    apply PP_congr C
    intro a b ha hb
    exact ((H_hasSum hρ0 hρ1 ha.1 hb.1).tsum_eq).symm
  rw [hk]; exact h

end Hsec2

section F12
variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem measurable_psi_joint (m : ℕ) : Measurable (fun p : ℝ × ℝ => psi m p.1 p.2) := by
  unfold psi
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) measurable_const

theorem ineq_pair {p q x y I : ℝ} {m : ℕ} (hm : 1 ≤ m) (hp : 0 ≤ p) (hqp : q ≤ p)
    (hy : (2 * m + 2) * y ^ 2 ≤ I) (hI : 0 ≤ I) :
    p / m * x ^ 2 + q / (m + 1) * (x - y) ^ 2 ≤ 2 * p / m * x ^ 2 + 4 * p * I := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have h1 : (x - y) ^ 2 ≤ (1 + 1 / m) * x ^ 2 + (1 + m) * y ^ 2 := by
    have : 0 ≤ (x + m * y) ^ 2 := sq_nonneg _
    have e : (1 + 1 / (m:ℝ)) * x ^ 2 + (1 + m) * y ^ 2 - (x - y) ^ 2 = (x + m * y) ^ 2 / m := by
      field_simp; ring
    have : 0 ≤ (x + m * y) ^ 2 / m := by positivity
    linarith
  have h2 : q / (m + 1) * (x - y) ^ 2 ≤ p / (m + 1) * ((1 + 1 / m) * x ^ 2 + (1 + m) * y ^ 2) := by
    apply mul_le_mul (div_le_div_of_nonneg_right hqp (by positivity)) h1 (sq_nonneg _) (by positivity)
  have h3 : p / (m + 1) * ((1 + 1 / m) * x ^ 2 + (1 + m) * y ^ 2) = p / m * x ^ 2 + p * y ^ 2 := by
    field_simp
    ring
  have h4 : p * y ^ 2 ≤ 4 * p * I := by
    have : y ^ 2 ≤ I := by nlinarith [sq_nonneg y]
    nlinarith [mul_le_mul_of_nonneg_left this hp]
  have h5 : 2 * p / m * x ^ 2 = 2 * (p / m * x ^ 2) := by ring
  linarith

theorem integrable_pow_mul (C : Ctx A M pr e) {μ : Measure Y} [IsFiniteMeasure μ] (hμ : μ ≤ A + M) (k : ℕ)
    (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ a ∈ Ioo (0:ℝ) 1, |g a| ≤ 1) :
    Integrable (fun y => e y * pr y ^ k * g (pr y)) μ := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact ((C.emeas.mul (C.meas.pow_const k)).mul (hg.comp C.meas)).aestronglyMeasurable
  · filter_upwards [C.loc.filter_mono (Measure.absolutelyContinuous_of_le hμ).ae_le] with y hy
    simp only [norm_mul, Real.norm_eq_abs, abs_pow]
    have h1 := C.ebd y
    have h2 : |pr y| ^ k ≤ 1 := by
      rw [abs_of_pos hy.1]; exact pow_le_one₀ hy.1.le hy.2.le
    have h3 := hgb _ hy
    calc |e y| * |pr y| ^ k * |g (pr y)| ≤ 1 * 1 * 1 := by
          apply mul_le_mul (mul_le_mul h1 h2 (by positivity) zero_le_one) h3 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- Fubini swap for the sections of `ψ`. -/
theorem swap_psi (C : Ctx A M pr e) {μ : Measure Y} [IsFiniteMeasure μ] (hμ : μ ≤ A + M) (m : ℕ) :
    Integrable (fun σ => σ ^ m * ∫ y, e y * psi m σ (pr y) ∂μ) (volume.restrict (Ioo (0:ℝ) 1)) ∧
    ∫ σ in Ioo (0:ℝ) 1, σ ^ m * ∫ y, e y * psi m σ (pr y) ∂μ = ∫ y, e y * pr y ^ m * (1 - pr y) ∂μ := by
  set ν : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hν
  set Φ : ℝ → Y → ℝ := fun σ y => σ ^ m * (e y * psi m σ (pr y)) with hΦ
  have hmeas : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable (fun p : ℝ × Y => p.1 ^ m) := (measurable_fst).pow_const m
    have h2 : Measurable (fun p : ℝ × Y => e p.2) := C.emeas.comp measurable_snd
    have h3 : Measurable (fun p : ℝ × Y => psi m p.1 (pr p.2)) :=
      (measurable_psi_joint m).comp (measurable_fst.prodMk (C.meas.comp measurable_snd))
    exact h1.mul (h2.mul h3)
  have hint : Integrable (Function.uncurry Φ) (ν.prod μ) := by
    refine Integrable.of_bound (C := 1) hmeas.aestronglyMeasurable ?_
    have hae1 : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ Ioo (0:ℝ) 1 :=
      (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae (ae_restrict_mem measurableSet_Ioo)
    have hae2 : ∀ᵐ p ∂(ν.prod μ), pr p.2 ∈ Ioo (0:ℝ) 1 :=
      (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae
        (C.loc.filter_mono (Measure.absolutelyContinuous_of_le hμ).ae_le)
    filter_upwards [hae1, hae2] with p hp hq
    simp only [Function.uncurry, hΦ, norm_mul, Real.norm_eq_abs, abs_pow]
    have h1 := C.ebd p.2
    have h2 : |p.1| ^ m ≤ 1 := by rw [abs_of_pos hp.1]; exact pow_le_one₀ hp.1.le hp.2.le
    have h3 : |psi m p.1 (pr p.2)| ≤ 1 := by
      rw [abs_of_nonneg (psi_nonneg m hp.1 hq.1.le)]
      exact psi_le_one m hp.1 hq.1.le
    calc |p.1| ^ m * (|e p.2| * |psi m p.1 (pr p.2)|) ≤ 1 * (1 * 1) := by
          apply mul_le_mul h2 (mul_le_mul h1 h3 (abs_nonneg _) zero_le_one) (by positivity) zero_le_one
      _ = 1 := by norm_num
  have hfun : (fun σ => σ ^ m * ∫ y, e y * psi m σ (pr y) ∂μ) = fun σ => ∫ y, Φ σ y ∂μ := by
    funext σ; simp only [hΦ]; rw [integral_const_mul]
  rw [hfun]
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards [C.loc.filter_mono (Measure.absolutelyContinuous_of_le hμ).ae_le] with y hy
  simp only [hΦ]
  have : ∫ σ, σ ^ m * (e y * psi m σ (pr y)) ∂ν = e y * ∫ σ in Ioo (0:ℝ) 1, σ ^ m * psi m σ (pr y) := by
    rw [← integral_const_mul]; congr 1; funext σ; ring
  rw [this, psi_integral hy.1 hy.2]; ring

end F12

section F12b
variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem S1_def (f : Y → ℝ) : S1 A M f = ∫ y, f y ∂A - ∫ y, f y ∂M := rfl

theorem Ym_eq (C : Ctx A M pr e) (m : ℕ) :
    Integrable (fun σ => σ ^ m * Gf A M pr e m σ) (volume.restrict (Ioo (0:ℝ) 1)) ∧
    ∫ σ in Ioo (0:ℝ) 1, σ ^ m * Gf A M pr e m σ = S1 A M (fun y => e y * pr y ^ m * (1 - pr y)) := by
  have hA : A ≤ A + M := Measure.le_add_right le_rfl
  have hM : M ≤ A + M := Measure.le_add_left le_rfl
  obtain ⟨hA1, hA2⟩ := swap_psi C hA m
  obtain ⟨hM1, hM2⟩ := swap_psi C hM m
  have hfun : (fun σ => σ ^ m * Gf A M pr e m σ) =
      fun σ => σ ^ m * (∫ y, e y * psi m σ (pr y) ∂A) - σ ^ m * (∫ y, e y * psi m σ (pr y) ∂M) := by
    funext σ; unfold Gf S1; ring
  rw [hfun]
  refine ⟨hA1.sub hM1, ?_⟩
  rw [integral_sub hA1 hM1, hA2, hM2]; rfl

theorem mom_succ (C : Ctx A M pr e) (m : ℕ) :
    mom A M pr e (m + 1) = mom A M pr e m - S1 A M (fun y => e y * pr y ^ m * (1 - pr y)) := by
  have hA : A ≤ A + M := Measure.le_add_right le_rfl
  have hM : M ≤ A + M := Measure.le_add_left le_rfl
  have i1 := fun {μ : Measure Y} [IsFiniteMeasure μ] (h : μ ≤ A + M) =>
    integrable_pow_mul C h m (fun _ => 1) measurable_const (fun a _ => by simp)
  have i2 := fun {μ : Measure Y} [IsFiniteMeasure μ] (h : μ ≤ A + M) =>
    integrable_pow_mul C h m (fun a => 1 - a) (by fun_prop) (fun a ha => by
      rw [abs_le]; constructor <;> linarith [ha.1, ha.2])
  unfold mom S1
  have key : ∀ {μ : Measure Y} [IsFiniteMeasure μ], μ ≤ A + M →
      ∫ y, e y * pr y ^ (m + 1) ∂μ = ∫ y, e y * pr y ^ m ∂μ - ∫ y, e y * pr y ^ m * (1 - pr y) ∂μ := by
    intro μ _ h
    rw [← integral_sub (by simpa using i1 h) (i2 h)]
    congr 1; funext y; ring
  rw [key hA, key hM]; ring

theorem Ysq_le (C : Ctx A M pr e) {m : ℕ} (hm : 0 < m) :
    (2 * (m:ℝ) + 2) * (∫ σ in Ioo (0:ℝ) 1, σ ^ m * Gf A M pr e m σ) ^ 2 ≤
      ∫ σ in Ioo (0:ℝ) 1, σ⁻¹ * (Gf A M pr e m σ) ^ 2 := by
  set ν : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hν
  obtain ⟨hY1, -⟩ := Ym_eq C m
  have hI := (PP_Rm C hm).2
  set Y := ∫ σ in Ioo (0:ℝ) 1, σ ^ m * Gf A M pr e m σ with hY
  set I := ∫ σ in Ioo (0:ℝ) 1, σ⁻¹ * (Gf A M pr e m σ) ^ 2 with hIdef
  have hc : ∫ σ in Ioo (0:ℝ) 1, σ ^ (2 * m + 1) = 1 / (2 * m + 2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    push_cast
    field_simp
    ring
  have hP : Integrable (fun σ : ℝ => σ ^ (2 * m + 1)) ν :=
    ((continuous_id.pow _).integrableOn_Icc (a := 0) (b := 1) (μ := volume)).mono_set Ioo_subset_Icc_self
  set t : ℝ := (2 * (m:ℝ) + 2) * Y with ht
  have hnn : 0 ≤ ∫ σ, σ⁻¹ * (Gf A M pr e m σ - t * σ ^ (m + 1)) ^ 2 ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
    have := hσ.1
    positivity
  have hexp : ∫ σ, σ⁻¹ * (Gf A M pr e m σ - t * σ ^ (m + 1)) ^ 2 ∂ν =
      ∫ σ, (σ⁻¹ * (Gf A M pr e m σ) ^ 2 - 2 * t * (σ ^ m * Gf A M pr e m σ) + t ^ 2 * σ ^ (2 * m + 1)) ∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
    have h0 : σ ≠ 0 := hσ.1.ne'
    field_simp
    ring
  have j2 : Integrable (fun σ => 2 * t * (σ ^ m * Gf A M pr e m σ)) ν := hY1.const_mul (2 * t)
  have j1 : Integrable (fun σ => σ⁻¹ * (Gf A M pr e m σ) ^ 2 - 2 * t * (σ ^ m * Gf A M pr e m σ)) ν :=
    hI.sub j2
  have j3 : Integrable (fun σ => t ^ 2 * σ ^ (2 * m + 1)) ν := hP.const_mul (t ^ 2)
  rw [hexp, integral_add j1 j3, integral_sub hI j2, integral_const_mul, integral_const_mul] at hnn
  have e1 : ∫ σ, σ⁻¹ * (Gf A M pr e m σ) ^ 2 ∂ν = I := rfl
  have e2 : ∫ σ, σ ^ m * Gf A M pr e m σ ∂ν = Y := rfl
  rw [e2] at hnn
  have e3 : ∫ σ, σ ^ (2 * m + 1) ∂ν = 1 / (2 * m + 2) := hc
  rw [e3] at hnn
  have hpos : (0:ℝ) < 2 * m + 2 := by positivity
  rw [ht] at hnn
  have : I - 2 * ((2 * (m:ℝ) + 2) * Y) * Y + ((2 * (m:ℝ) + 2) * Y) ^ 2 * (1 / (2 * m + 2)) =
      I - (2 * (m:ℝ) + 2) * Y ^ 2 := by field_simp; ring
  rw [e1] at hnn
  linarith

end F12b

section Core
variable {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} [IsFiniteMeasure A] [IsFiniteMeasure M]
  {pr e : Y → ℝ}

theorem PP_H_ge_ell (C : Ctx A M pr e) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    PP A M pr e (ell ρ) ≤ PP A M pr e (fun a b => K1d ρ a b - K2d ρ a b) := by
  have hell := PP_ell C hρ0 hρ1
  have hH := PP_H_hasSum C hρ0 hρ1
  set f : ℕ → ℝ := fun k => ρ ^ (k + 1) / (k + 1) * (mom A M pr e (k + 1)) ^ 2 with hf
  have hs : Summable f := hell.summable
  have he : Summable (fun n : ℕ => f (2 * n)) :=
    hs.comp_injective (i := fun n : ℕ => 2 * n) (fun x y h => by simpa using h)
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hs.comp_injective (i := fun n : ℕ => 2 * n + 1) (fun x y h => by simpa using h)
  have hsum : HasSum (fun n : ℕ => f (2 * n) + f (2 * n + 1)) (PP A M pr e (ell ρ)) := by
    have hs2 : Summable (fun n : ℕ => f (2 * n) + f (2 * n + 1)) := he.add ho
    have : ∑' n : ℕ, (f (2 * n) + f (2 * n + 1)) = PP A M pr e (ell ρ) := by
      rw [he.tsum_add ho, tsum_even_add_odd he ho, hell.tsum_eq]
    rw [← this]; exact hs2.hasSum
  refine hasSum_le (fun n => ?_) hsum hH
  rw [PP_Tn C hρ0 hρ1 n]
  set m := 2 * n + 1 with hm
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hY1, hY2⟩ := Ym_eq C m
  have hI0 : 0 ≤ ∫ σ in Ioo (0:ℝ) 1, σ⁻¹ * (Gf A M pr e m σ) ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
    have := hσ.1
    positivity
  have hY := Ysq_le C (by omega : 0 < m)
  rw [hY2] at hY
  have hsucc := mom_succ C m
  have e1 : f (2 * n) = ρ ^ m / (m : ℝ) * (mom A M pr e m) ^ 2 := by
    simp only [hf, hm]; (try push_cast); (try ring)
  have e2 : f (2 * n + 1) = ρ ^ (m + 1) / ((m : ℝ) + 1) * (mom A M pr e (m + 1)) ^ 2 := by
    simp only [hf, hm]; (try push_cast); (try ring)
  rw [e1, e2, hsucc]
  have hp : 0 ≤ ρ ^ m := by positivity
  have hqp : ρ ^ (m + 1) ≤ ρ ^ m := pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.le_succ m)
  exact ineq_pair (m := m) hm1 hp hqp hY hI0

theorem PP_sum_ge_ell (C : Ctx A M pr e) (hmass : A.real univ = M.real univ) (he1 : ∀ y, e y = 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    PP A M pr e (ell ρ) ≤ PP A M pr e (fun a b => K1d ρ a b + K2d ρ a b) := by
  have hdec : PP A M pr e (fun a b => K1d ρ a b + K2d ρ a b) =
      PP A M pr e (ell ρ) + PP A M pr e (fun a b => K1d ρ a b - ell ρ a b) + PP A M pr e (K2d ρ) := by
    have h1 : PP A M pr e (fun a b => K1d ρ a b + K2d ρ a b) =
        PP A M pr e (fun a b => (ell ρ a b + (K1d ρ a b - ell ρ a b)) + K2d ρ a b) :=
      PP_congr C (fun a b _ _ => by ring)
    have hsum : Integrable (Wk pr e (fun a b => ell ρ a b + (K1d ρ a b - ell ρ a b))) ((A + M).prod (A + M)) := by
      have := (adm_ell C hρ0 hρ1).add (adm_G C hρ0 hρ1)
      convert this using 1
      funext z; simp only [Wk, Pi.add_apply]; ring
    rw [h1, PP_add C hsum (adm_K2d C hρ0 hρ1), PP_add C (adm_ell C hρ0 hρ1) (adm_G C hρ0 hρ1)]
  rw [hdec]
  have := PP_G_nonneg C hρ0 hρ1
  have := PP_K2d_nonneg C hmass he1 hρ0 hρ1
  linarith

end Core

/-! ### Bridge from the damped to the true kernels -/
section Bridge

def D1 (ρ x y : ℝ) : ℝ := -Real.log |x - y| - K1d ρ x y
def D2 (ρ x y : ℝ) : ℝ := -Real.log (x + y) - K2d ρ x y

variable {ρ a b : ℝ}

theorem abs_sub_eq (ha : 0 < a) (hb : 0 < b) : |a - b| = max a b * (1 - rr a b) := by
  have hM := max_pos' (b := b) ha
  unfold rr
  rw [mul_sub, mul_one, mul_div_cancel₀ _ hM.ne']
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_right h, min_eq_left h]; ring
  · rw [abs_of_nonneg (by linarith), max_eq_left h, min_eq_right h]

theorem one_sub_rr_pos (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : 0 < 1 - rr a b := by
  have h1 := rr_le_one (b := b) ha
  have hM := max_pos' (b := b) ha
  have : rr a b ≠ 1 := by
    intro h
    unfold rr at h
    rw [div_eq_one_iff_eq hM.ne'] at h
    rcases le_total a b with hh | hh
    · rw [max_eq_right hh, min_eq_left hh] at h; exact hab h
    · rw [max_eq_left hh, min_eq_right hh] at h; exact hab h.symm
  exact sub_pos.2 (lt_of_le_of_ne h1 this)

theorem D1_eq (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    D1 ρ a b = Real.log (1 - ρ * rr a b) - Real.log (1 - rr a b) := by
  have hM := max_pos' (b := b) ha
  have h1 := one_sub_rr_pos ha hb hab
  unfold D1 K1d
  rw [abs_sub_eq ha hb, Real.log_mul hM.ne' h1.ne']
  ring

theorem D1_nonneg (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 ≤ D1 ρ a b := by
  have h1 := one_sub_rr_pos ha hb hab
  have hr0 := rr_pos ha hb
  rw [D1_eq ha hb hab, sub_nonneg]
  exact Real.log_le_log h1 (by nlinarith)

theorem D1_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hab : a ≠ b) : D1 ρ a b ≤ Real.log (1 + (1 - ρ) / |a - b|) := by
  have h1 := one_sub_rr_pos ha hb hab
  have hr0 := rr_pos ha hb
  have hM := max_pos' (b := b) ha
  have hM1 : max a b < 1 := max_lt ha1 hb1
  have habpos : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
  rw [D1_eq ha hb hab, ← Real.log_div (by nlinarith) h1.ne']
  apply Real.log_le_log (div_pos (by nlinarith) h1)
  rw [div_le_iff₀ h1]
  have hq : rr a b ≤ (1 - rr a b) / |a - b| := by
    rw [abs_sub_eq ha hb, le_div_iff₀ (by positivity)]
    have : rr a b * (max a b * (1 - rr a b)) ≤ (1 - rr a b) := by
      have : rr a b * max a b = min a b := by unfold rr; field_simp
      have hm : min a b < 1 := lt_of_le_of_lt min_le_max hM1
      calc rr a b * (max a b * (1 - rr a b)) = (rr a b * max a b) * (1 - rr a b) := by ring
        _ = min a b * (1 - rr a b) := by rw [this]
        _ ≤ 1 * (1 - rr a b) := by nlinarith
        _ = _ := by ring
    exact this
  have : (1 - ρ) * rr a b ≤ (1 - ρ) * ((1 - rr a b) / |a - b|) := mul_le_mul_of_nonneg_left hq (by linarith)
  have e : (1 + (1 - ρ) / |a - b|) * (1 - rr a b) = (1 - rr a b) + (1 - ρ) * ((1 - rr a b) / |a - b|) := by
    field_simp
  rw [e]; nlinarith

theorem K2d_eq_log (hρ0 : 0 < ρ) (ha : 0 < a) (hb : 0 < b) :
    K2d ρ a b = -Real.log (max a b + ρ * min a b) := by
  have hM := max_pos' (b := b) ha
  have hr := rr_pos ha hb
  unfold K2d
  have : max a b + ρ * min a b = max a b * (1 + ρ * rr a b) := by unfold rr; field_simp
  rw [this, Real.log_mul hM.ne' (by positivity)]; ring

theorem D2_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) : D2 ρ a b ≤ 0 := by
  have hM := max_pos' (b := b) ha
  have hm : 0 < min a b := lt_min ha hb
  unfold D2
  rw [K2d_eq_log hρ0 ha hb]
  have hs : a + b = max a b + min a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, min_eq_left h]; try ring
    · rw [max_eq_left h, min_eq_right h]; try ring
  rw [hs]
  have := Real.log_le_log (by positivity : 0 < max a b + ρ * min a b)
    (by nlinarith : max a b + ρ * min a b ≤ max a b + min a b)
  linarith

theorem D2_ge (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hb : 0 < b) : -(1 - ρ) ≤ D2 ρ a b := by
  have hM := max_pos' (b := b) ha
  have hm : 0 < min a b := lt_min ha hb
  have hmM : min a b ≤ max a b := min_le_max
  unfold D2
  rw [K2d_eq_log hρ0 ha hb]
  have hs : a + b = max a b + min a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, min_eq_left h]; try ring
    · rw [max_eq_left h, min_eq_right h]; try ring
  rw [hs]
  set u := max a b + ρ * min a b with hu
  set v := max a b + min a b with hv
  have hu0 : 0 < u := by positivity
  have hv0 : 0 < v := by positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
  rw [Real.log_div hv0.ne' hu0.ne'] at h1
  have h2 : v / u - 1 = (1 - ρ) * min a b / u := by
    rw [hu, hv]; field_simp; ring
  have h3 : (1 - ρ) * min a b / u ≤ (1 - ρ) := by
    rw [div_le_iff₀ hu0]; rw [hu]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ρ) (by nlinarith : 0 ≤ max a b + ρ * min a b - min a b)]
  linarith

end Bridge

section Sbound

/-- `s ↦ log (1 + ε/s)` -/
def gl (ε s : ℝ) : ℝ := Real.log (1 + ε / s)

theorem gl_eq {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) : gl ε s = Real.log (s + ε) - Real.log s := by
  unfold gl
  rw [← Real.log_div (by positivity) hs.ne']; congr 1; field_simp

theorem gl_nonneg {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) : 0 ≤ gl ε s :=
  Real.log_nonneg (by have : 0 < ε / s := by positivity
                      linarith)

theorem gl_intervalIntegrable {ε : ℝ} (hε : 0 < ε) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (gl ε) volume 0 b := by
  have h1 : IntervalIntegrable (fun s => Real.log (s + ε)) volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.log (by fun_prop) (fun s hs => ?_)
    rw [Set.uIcc_of_le hb] at hs
    exact (by linarith [hs.1] : 0 < s + ε).ne'
  have h2 : IntervalIntegrable Real.log volume 0 b := intervalIntegral.intervalIntegrable_log'
  have := h1.sub h2
  refine this.congr (fun s hs => ?_)
  rw [Set.uIoc_of_le hb] at hs
  rw [gl_eq hε hs.1]

theorem J_eps {ε : ℝ} (hε0 : 0 < ε) :
    ∫ s in (0:ℝ)..1, gl ε s = (1 + ε) * Real.log (1 + ε) - ε * Real.log ε := by
  have hcont : ContinuousOn (fun s : ℝ => (s + ε) * Real.log (s + ε) - s * Real.log s) (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    exact ((Real.continuous_mul_log.comp (continuous_id.add continuous_const)).sub Real.continuous_mul_log)
  have hder : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun s : ℝ => (s + ε) * Real.log (s + ε) - s * Real.log s) (gl ε s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => (s + ε) * Real.log (s + ε)) (Real.log (s + ε) + 1) s := by
      have := (Real.hasDerivAt_mul_log (by linarith [hs.1] : s + ε ≠ 0)).comp_add_const s ε
      exact this
    have h2 := Real.hasDerivAt_mul_log hs.1.ne'
    have := h1.sub h2
    convert this using 1
    rw [gl_eq hε0 hs.1]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hder (gl_intervalIntegrable hε0 zero_le_one)]
  simp

theorem J_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∫ s in (0:ℝ)..1, gl ε s ≤ 2 * ε + ε * Real.log (1 / ε) := by
  rw [J_eps hε0, one_div, Real.log_inv]
  have h1 : Real.log (1 + ε) ≤ ε := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε); linarith
  have h2 : (1 + ε) * Real.log (1 + ε) ≤ 2 * ε := by
    have h0 : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
    nlinarith
  linarith


theorem S_bound {ε x : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hx : x ∈ Ioo (0:ℝ) 1) :
    IntegrableOn (fun y => gl ε |x - y|) (Ioo (0:ℝ) 1) ∧
    ∫ y in Ioo (0:ℝ) 1, gl ε |x - y| ≤ 4 * ε * (1 + Real.log (1 / ε)) := by
  have hx0 := hx.1.le
  have hx1 := hx.2.le
  have hJ : IntervalIntegrable (gl ε) volume 0 1 := gl_intervalIntegrable hε0 zero_le_one
  have hI1 : IntervalIntegrable (fun y => gl ε |x - y|) volume 0 x := by
    have := (gl_intervalIntegrable hε0 hx0).comp_sub_left x
    simp only [sub_self, sub_zero] at this
    replace this := this.symm
    refine this.congr (fun y hy => ?_)
    rw [Set.uIoc_of_le hx0] at hy
    beta_reduce
    rw [abs_of_nonneg (by linarith [hy.2])]
  have hI2 : IntervalIntegrable (fun y => gl ε |x - y|) volume x 1 := by
    have := (gl_intervalIntegrable hε0 (by linarith : 0 ≤ 1 - x)).comp_sub_right x
    simp only [zero_add, sub_add_cancel] at this
    refine this.congr (fun y hy => ?_)
    rw [Set.uIoc_of_le hx1] at hy
    beta_reduce
    rw [abs_of_nonpos (by linarith [hy.1]), neg_sub]
  have hI : IntervalIntegrable (fun y => gl ε |x - y|) volume 0 1 := hI1.trans hI2
  have hnn : ∀ b, 0 ≤ b → b ≤ 1 → ∫ s in (0:ℝ)..b, gl ε s ≤ ∫ s in (0:ℝ)..1, gl ε s := by
    intro b hb0 hb1
    apply intervalIntegral.integral_mono_interval le_rfl hb0 hb1 _ hJ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact gl_nonneg hε0 hs.1
  have e1 : ∫ y in (0:ℝ)..x, gl ε |x - y| = ∫ s in (0:ℝ)..x, gl ε s := by
    have h := intervalIntegral.integral_comp_sub_left (fun s => gl ε s) (a := 0) (b := x) x
    simp only [sub_self, sub_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    beta_reduce
    rw [abs_of_nonneg (by linarith [hy.2])]
  have e2 : ∫ y in x..(1:ℝ), gl ε |x - y| = ∫ s in (0:ℝ)..(1 - x), gl ε s := by
    have h := intervalIntegral.integral_comp_sub_right (fun s => gl ε s) (a := x) (b := 1) x
    simp only [sub_self] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx1] at hy
    beta_reduce
    rw [abs_of_nonpos (by linarith [hy.1]), neg_sub]
  have hsum := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hL : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  constructor
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hI).mono_set Ioo_subset_Ioc_self
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, ← hsum, e1, e2]
    have a1 := hnn x hx0 hx1
    have a2 := hnn (1 - x) (by linarith) (by linarith)
    have a3 := J_le hε0 hε1
    nlinarith

end Sbound

/-! ### Reference measures with bounded density -/
section Ref

/-- The reference measure `m` has density `≤ C` with respect to Lebesgue measure on `(0,1)`. -/
def BD (m : Measure ℝ) (C : ℝ) : Prop := m ≤ ENNReal.ofReal C • volume.restrict (Ioo (0:ℝ) 1)

variable {m : Measure ℝ} {C : ℝ}

theorem BD.finite (h : BD m C) : IsFiniteMeasure m := by
  refine ⟨?_⟩
  have := Measure.le_iff'.1 h univ
  refine lt_of_le_of_lt this ?_
  simp [Measure.smul_apply]

theorem BD.ae_mem (h : BD m C) : ∀ᵐ y ∂m, y ∈ Ioo (0:ℝ) 1 :=
  (Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _).filter_mono
    (Measure.absolutelyContinuous_of_le h).ae_le

theorem BD.noatom (h : BD m C) (x : ℝ) : m {x} = 0 := by
  have h1 := Measure.le_iff'.1 h {x}
  have h2 : (volume.restrict (Ioo (0:ℝ) 1)) {x} = 0 :=
    le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self {x}).trans (by simp)) bot_le
  rw [Measure.smul_apply, h2, smul_zero] at h1
  exact le_antisymm h1 bot_le

theorem BD.logint (h : BD m C) : Integrable (fun y => Real.log y) m := by
  have h1 : Integrable (fun y : ℝ => Real.log y) (volume.restrict (Ioo (0:ℝ) 1)) := by
    have := (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := 1))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this).mono_set Ioo_subset_Ioc_self
  exact (h1.smul_measure ENNReal.ofReal_ne_top).mono_measure h

theorem BD.integral_le (h : BD m C) (hC : 0 ≤ C) {f : ℝ → ℝ}
    (hf0 : ∀ᵐ y ∂(volume.restrict (Ioo (0:ℝ) 1)), 0 ≤ f y)
    (hfi : Integrable f (volume.restrict (Ioo (0:ℝ) 1))) :
    ∫ y, f y ∂m ≤ C * ∫ y in Ioo (0:ℝ) 1, f y := by
  have := integral_mono_measure h (Measure.ae_smul_measure hf0 _) (hfi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul] at this
  exact this

end Ref

/-! ### Integrability of the difference kernels against reference measures -/
section RefInt

variable {m m' : Measure ℝ} {C : ℝ} {ρ : ℝ}

theorem measurable_D1 (ρ : ℝ) : Measurable (fun p : ℝ × ℝ => D1 ρ p.1 p.2) := by
  unfold D1 K1d rr; fun_prop
theorem measurable_D2 (ρ : ℝ) : Measurable (fun p : ℝ × ℝ => D2 ρ p.1 p.2) := by
  unfold D2 K2d rr; fun_prop

theorem ae_ne_of_BD (h : BD m C) (x : ℝ) : ∀ᵐ y ∂m, y ≠ x := by
  rw [ae_iff]
  have : {y : ℝ | ¬ y ≠ x} = {x} := by ext; simp
  rw [this]; exact h.noatom x

theorem D1_int_aux (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    Integrable (fun y => D1 ρ x y) (volume.restrict (Ioo (0:ℝ) 1)) ∧
    ∫ y in Ioo (0:ℝ) 1, D1 ρ x y ≤ 4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))) := by
  have hε0 : 0 < 1 - ρ := by linarith
  have hε1 : 1 - ρ < 1 := by linarith
  obtain ⟨hS1, hS2⟩ := S_bound hε0 hε1 hx
  have hmeas : Measurable (fun y => D1 ρ x y) :=
    (measurable_D1 ρ).comp (by fun_prop : Measurable fun y : ℝ => (x, y))
  have hae : ∀ᵐ y ∂(volume.restrict (Ioo (0:ℝ) 1)), 0 ≤ D1 ρ x y ∧ D1 ρ x y ≤ gl (1 - ρ) |x - y| := by
    have hne : ∀ᵐ y ∂(volume.restrict (Ioo (0:ℝ) 1)), y ≠ x := by
      rw [ae_iff]
      have : {y : ℝ | ¬ y ≠ x} = {x} := by ext; simp
      rw [this]
      exact le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self {x}).trans (by simp)) bot_le
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with y hy hyx
    refine ⟨D1_nonneg hρ0 hρ1 hx.1 hy.1 (Ne.symm hyx), ?_⟩
    have := D1_le hρ0 hρ1 hx.1 hx.2 hy.1 hy.2 (Ne.symm hyx)
    unfold gl; exact this
  have hint : Integrable (fun y => D1 ρ x y) (volume.restrict (Ioo (0:ℝ) 1)) := by
    refine hS1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with y hy
    rw [Real.norm_of_nonneg hy.1]; exact hy.2
  refine ⟨hint, ?_⟩
  refine le_trans (integral_mono_ae hint hS1 (by filter_upwards [hae] with y hy using hy.2)) hS2

theorem D1_int (h : BD m C) (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    Integrable (fun y => D1 ρ x y) m ∧ 0 ≤ ∫ y, D1 ρ x y ∂m ∧
      ∫ y, D1 ρ x y ∂m ≤ C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))) := by
  obtain ⟨h1, h2⟩ := D1_int_aux hρ0 hρ1 hx
  have hε0 : 0 < 1 - ρ := by linarith
  have hε1 : 1 - ρ < 1 := by linarith
  have hnn : ∀ᵐ y ∂(volume.restrict (Ioo (0:ℝ) 1)), 0 ≤ D1 ρ x y := by
    have hne : ∀ᵐ y ∂(volume.restrict (Ioo (0:ℝ) 1)), y ≠ x := by
      rw [ae_iff]
      have : {y : ℝ | ¬ y ≠ x} = {x} := by ext; simp
      rw [this]
      exact le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self {x}).trans (by simp)) bot_le
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with y hy hyx
    exact D1_nonneg hρ0 hρ1 hx.1 hy.1 (Ne.symm hyx)
  refine ⟨(h1.smul_measure ENNReal.ofReal_ne_top).mono_measure h, ?_, ?_⟩
  · apply integral_nonneg_of_ae
    filter_upwards [h.ae_mem, ae_ne_of_BD h x] with y hy hyx
    exact D1_nonneg hρ0 hρ1 hx.1 hy.1 (Ne.symm hyx)
  · exact (h.integral_le hC hnn h1).trans (mul_le_mul_of_nonneg_left h2 hC)

theorem D2_int (h : BD m C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    Integrable (fun y => D2 ρ x y) m ∧ ∫ y, D2 ρ x y ∂m ≤ 0 := by
  haveI := h.finite
  have hmeas : Measurable (fun y => D2 ρ x y) :=
    (measurable_D2 ρ).comp (by fun_prop : Measurable fun y : ℝ => (x, y))
  constructor
  · refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [h.ae_mem] with y hy
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [D2_ge hρ0 hρ1 hx.1 hy.1], by linarith [D2_le hρ0 hρ1 hx.1 hy.1]⟩
  · apply integral_nonpos_of_ae
    filter_upwards [h.ae_mem] with y hy
    exact D2_le hρ0 hρ1 hx.1 hy.1

end RefInt

section RefInt2
variable {m m' : Measure ℝ} {C : ℝ} {ρ : ℝ}

theorem D1_prod (h : BD m C) (h' : BD m' C) (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (fun p : ℝ × ℝ => D1 ρ p.1 p.2) (m.prod m') := by
  have := h.finite; have := h'.finite
  have hmeas := measurable_D1 ρ
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [h.ae_mem] with x hx
    exact (D1_int h' hC hρ0 hρ1 hx).1
  · refine Integrable.of_bound ?_ (C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))))) ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := m')).aestronglyMeasurable
    · filter_upwards [h.ae_mem] with x hx
      obtain ⟨-, h2, h3⟩ := D1_int h' hC hρ0 hρ1 hx
      have : ∫ y, ‖D1 ρ (x, y).1 (x, y).2‖ ∂m' = ∫ y, D1 ρ x y ∂m' := by
        apply integral_congr_ae
        filter_upwards [h'.ae_mem, ae_ne_of_BD h' x] with y hy hyx
        rw [Real.norm_of_nonneg (D1_nonneg hρ0 hρ1 hx.1 hy.1 (Ne.symm hyx))]
      rw [this, Real.norm_of_nonneg h2]; exact h3

theorem D2_prod (h : BD m C) (h' : BD m' C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (fun p : ℝ × ℝ => D2 ρ p.1 p.2) (m.prod m') := by
  have := h.finite; have := h'.finite
  refine Integrable.of_bound (measurable_D2 ρ).aestronglyMeasurable 1 ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := m) (ν := m')).ae h.ae_mem
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := m) (ν := m')).ae h'.ae_mem
  filter_upwards [h1, h2] with p hp1 hp2
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [D2_ge hρ0 hρ1 hp1.1 hp2.1], by linarith [D2_le hρ0 hρ1 hp1.1 hp2.1]⟩

theorem intK_single (h : BD m C) {k : ℝ → ℝ → ℝ} {c : ℝ} (hk : ∀ x, Measurable (k x))
    (hb : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → |k x y| ≤ c + |Real.log x| + |Real.log y|)
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : Integrable (k x) m := by
  have := h.finite
  refine Integrable.mono' (g := fun y => (c + |Real.log x|) + |Real.log y|)
    ((integrable_const _).add h.logint.abs) (hk x).aestronglyMeasurable ?_
  filter_upwards [h.ae_mem] with y hy
  rw [Real.norm_eq_abs]; have := hb x y hx hy; linarith

theorem intK_prod (h : BD m C) (h' : BD m' C) {k : ℝ → ℝ → ℝ}
    (hk : Measurable (fun p : ℝ × ℝ => k p.1 p.2)) {c : ℝ}
    (hb : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → |k x y| ≤ c + |Real.log x| + |Real.log y|) :
    Integrable (fun p : ℝ × ℝ => k p.1 p.2) (m.prod m') := by
  have := h.finite; have := h'.finite
  have hloc : ∀ᵐ y ∂(m + m'), id y ∈ Ioo (0:ℝ) 1 := by
    exact ae_add_measure_iff.2 ⟨h.ae_mem, h'.ae_mem⟩
  have hlog : Integrable (fun y => Real.log (id y)) (m + m') := h.logint.add_measure h'.logint
  have := adm_of_bound (m := m + m') (pr := id) (e := fun _ => (1:ℝ)) measurable_id hloc hlog
    measurable_const (fun _ => by simp) hk hb
  have h2 : Integrable (Wk id (fun _ => (1:ℝ)) k) (m.prod m') :=
    this.mono_measure (Measure.prod_mono (Measure.le_add_right le_rfl) (Measure.le_add_left le_rfl))
  refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [Wk]

end RefInt2

/-! ### The atomic-plus-density pair of measures on `Bool × ℝ`

The reference is a SIGNED measure `P - N` (both parts nonnegative, of bounded density on `(0,1)`;
the paper's Theorem 7.1 is for signed measures of total mass `0`).  The discrepancy
`∑ w_i δ_{a_i} - (P - N)` is written `(A + N) - P` with the atoms `A`: the configuration side is
`Amu + Mmu N`, the reference side is `Mmu P`. -/
section Inst

variable {ι : Type*} [Fintype ι]

/-- the atomic part `∑ w_i δ_{(σ_i, a_i)}` -/
def Amu (w a : ι → ℝ) (σ : ι → Bool) : Measure (Bool × ℝ) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac (σ i, a i)
/-- a reference part -/
def Mmu (μ : Bool → Measure ℝ) : Measure (Bool × ℝ) := ∑ τ : Bool, (μ τ).map (Prod.mk τ)
/-- species sign -/
def sgn (y : Bool × ℝ) : ℝ := if y.1 then 1 else -1

variable {w a : ι → ℝ} {σ : ι → Bool} {μ P N : Bool → Measure ℝ} {C : ℝ}

instance Amu_finite : IsFiniteMeasure (Amu w a σ) := by
  have : ∀ i, IsFiniteMeasure (ENNReal.ofReal (w i) • Measure.dirac (σ i, a i)) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  unfold Amu; infer_instance

theorem Mmu_finite (h : ∀ τ, BD (μ τ) C) : IsFiniteMeasure (Mmu μ) := by
  have : ∀ τ, IsFiniteMeasure (μ τ) := fun τ => (h τ).finite
  unfold Mmu
  infer_instance

theorem measurable_sgn : Measurable sgn :=
  (measurable_from_top (f := fun b : Bool => if b then (1:ℝ) else -1)).comp measurable_fst

theorem abs_sgn_le (y : Bool × ℝ) : |sgn y| ≤ 1 := by
  unfold sgn; split_ifs <;> simp

theorem ae_Amu (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) : ∀ᵐ y ∂(Amu w a σ), Prod.snd y ∈ Ioo (0:ℝ) 1 := by
  unfold Amu
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  intro i
  refine Measure.ae_smul_measure ?_ _
  rw [ae_dirac_eq]; exact Filter.eventually_pure.2 (ha i)

theorem ae_Mmu (h : ∀ τ, BD (μ τ) C) : ∀ᵐ y ∂(Mmu μ), Prod.snd y ∈ Ioo (0:ℝ) 1 := by
  unfold Mmu
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  intro τ
  rw [(measurableEmbedding_prodMk_left τ).ae_map_iff]
  exact (h τ).ae_mem

theorem integrable_Amu (f : Bool × ℝ → ℝ) : Integrable f (Amu w a σ) := by
  unfold Amu
  rw [integrable_finsetSum_measure]
  intro i _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integrable_Mmu (μ : Bool → Measure ℝ) {f : Bool × ℝ → ℝ}
    (hf : ∀ τ, Integrable (fun x => f (τ, x)) (μ τ)) : Integrable f (Mmu μ) := by
  unfold Mmu
  rw [integrable_finsetSum_measure]
  intro τ _
  rw [(measurableEmbedding_prodMk_left τ).integrable_map_iff]
  exact hf τ

theorem ctx_inst (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    {e : Bool × ℝ → ℝ} (he : Measurable e) (heb : ∀ y, |e y| ≤ 1) :
    Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd e := by
  have := Mmu_finite hP
  have := Mmu_finite hN
  refine ⟨measurable_snd, ?_, ?_, he, heb⟩
  · rw [ae_add_measure_iff, ae_add_measure_iff]
    exact ⟨⟨ae_Amu ha, ae_Mmu hN⟩, ae_Mmu hP⟩
  · refine ((integrable_Amu _).add_measure ?_).add_measure ?_
    · exact integrable_Mmu N (fun τ => (hN τ).logint)
    · exact integrable_Mmu P (fun τ => (hP τ).logint)

theorem intA (w a : ι → ℝ) (σ : ι → Bool) (hw : ∀ i, 0 < w i) (f : Bool × ℝ → ℝ) :
    ∫ y, f y ∂(Amu w a σ) = ∑ i, w i * f (σ i, a i) := by
  unfold Amu
  rw [integral_finset_sum_measure (fun i _ => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i).le, smul_eq_mul]

theorem intM (μ : Bool → Measure ℝ) (f : Bool × ℝ → ℝ) (hf : ∀ τ, Integrable (fun x => f (τ, x)) (μ τ)) :
    ∫ y, f y ∂(Mmu μ) = ∑ τ : Bool, ∫ x, f (τ, x) ∂(μ τ) := by
  unfold Mmu
  rw [integral_finset_sum_measure (fun τ _ => by
    rw [(measurableEmbedding_prodMk_left τ).integrable_map_iff]; exact hf τ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [(measurableEmbedding_prodMk_left τ).integral_map]

theorem intAN (hw : ∀ i, 0 < w i) (f : Bool × ℝ → ℝ) (hf : ∀ τ, Integrable (fun x => f (τ, x)) (N τ)) :
    ∫ y, f y ∂(Amu w a σ + Mmu N) = ∑ i, w i * f (σ i, a i) + ∑ τ : Bool, ∫ x, f (τ, x) ∂(N τ) := by
  rw [integral_add_measure (integrable_Amu f) (integrable_Mmu N hf), intA w a σ hw, intM N f hf]

end Inst

section Eval
variable {Y : Type*} [MeasurableSpace Y]

theorem integral_add_prod {U V W : Measure Y} [SFinite U] [SFinite V] [SFinite W] {G : Y × Y → ℝ}
    (h : Integrable G ((U + V).prod W)) :
    ∫ z, G z ∂((U + V).prod W) = ∫ z, G z ∂(U.prod W) + ∫ z, G z ∂(V.prod W) := by
  rw [Measure.add_prod] at h ⊢
  exact integral_add_measure (h.mono_measure (Measure.le_add_right le_rfl))
    (h.mono_measure (Measure.le_add_left le_rfl))

theorem integral_prod_add {U V W : Measure Y} [SFinite U] [SFinite V] [SFinite W] {G : Y × Y → ℝ}
    (h : Integrable G (U.prod (V + W))) :
    ∫ z, G z ∂(U.prod (V + W)) = ∫ z, G z ∂(U.prod V) + ∫ z, G z ∂(U.prod W) := by
  rw [Measure.prod_add] at h ⊢
  exact integral_add_measure (h.mono_measure (Measure.le_add_right le_rfl))
    (h.mono_measure (Measure.le_add_left le_rfl))

variable {ι : Type*} [Fintype ι] {w a : ι → ℝ} {σ : ι → Bool} {μ ν P N : Bool → Measure ℝ} {C : ℝ}

/-- `∑_i w_i ∑_τ ∫ κ(a_i, ·) dμ_τ`: the atoms against a reference part. -/
def rowI (w a : ι → ℝ) (σ : ι → Bool) (μ : Bool → Measure ℝ) (κ : Bool → Bool → ℝ → ℝ → ℝ) : ℝ :=
  ∑ i, w i * ∑ τ, ∫ y, κ (σ i) τ (a i) y ∂(μ τ)

/-- `∑_{τ,τ'} ∬ κ dν_τ' dμ_τ`: a reference part against another. -/
def pairI (μ ν : Bool → Measure ℝ) (κ : Bool → Bool → ℝ → ℝ → ℝ) : ℝ :=
  ∑ τ, ∑ τ', ∫ x, ∫ y, κ τ τ' x y ∂(ν τ') ∂(μ τ)

theorem blkAA (hw : ∀ i, 0 < w i) {κ : Bool → Bool → ℝ → ℝ → ℝ}
    (hint : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2)
      ((Amu w a σ).prod (Amu w a σ))) :
    ∫ z, κ z.1.1 z.2.1 z.1.2 z.2.2 ∂((Amu w a σ).prod (Amu w a σ)) =
      ∑ i, ∑ j, w i * w j * κ (σ i) (σ j) (a i) (a j) := by
  rw [integral_prod _ hint]
  dsimp only
  rw [intA w a σ hw]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only
  rw [intA w a σ hw, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem blkAM (hw : ∀ i, 0 < w i) (h : ∀ τ, BD (ν τ) C) {κ : Bool → Bool → ℝ → ℝ → ℝ}
    (hG1 : ∀ i τ, Integrable (κ (σ i) τ (a i)) (ν τ))
    (hint : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2)
      ((Amu w a σ).prod (Mmu ν))) :
    ∫ z, κ z.1.1 z.2.1 z.1.2 z.2.2 ∂((Amu w a σ).prod (Mmu ν)) = rowI w a σ ν κ := by
  have := Mmu_finite h
  rw [integral_prod _ hint]
  dsimp only
  rw [intA w a σ hw]
  unfold rowI
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only
  rw [intM ν (fun y => κ (σ i) y.1 (a i) y.2) (fun τ => hG1 i τ)]

theorem blkMA (hw : ∀ i, 0 < w i) (h : ∀ τ, BD (ν τ) C) {κ : Bool → Bool → ℝ → ℝ → ℝ}
    (hsymm : ∀ s t x y, κ s t x y = κ t s y x)
    (hG1 : ∀ i τ, Integrable (κ (σ i) τ (a i)) (ν τ))
    (hint : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2)
      ((Mmu ν).prod (Amu w a σ))) :
    ∫ z, κ z.1.1 z.2.1 z.1.2 z.2.2 ∂((Mmu ν).prod (Amu w a σ)) = rowI w a σ ν κ := by
  have := Mmu_finite h
  have hfin : ∀ τ, IsFiniteMeasure (ν τ) := fun τ => (h τ).finite
  rw [integral_prod _ hint]
  dsimp only
  have hinner : ∀ y : Bool × ℝ, ∫ y', κ y.1 y'.1 y.2 y'.2 ∂(Amu w a σ) =
      ∑ j, w j * κ y.1 (σ j) y.2 (a j) := by
    intro y; rw [intA w a σ hw]
  simp_rw [hinner]
  have hsw : ∀ j τ x, κ τ (σ j) x (a j) = κ (σ j) τ (a j) x := fun j τ x => hsymm τ (σ j) x (a j)
  have hint' : ∀ τ j, Integrable (fun x => w j * κ τ (σ j) x (a j)) (ν τ) := by
    intro τ j
    refine ((hG1 j τ).const_mul (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hsw]
  rw [intM ν (fun y => ∑ j, w j * κ y.1 (σ j) y.2 (a j))
    (fun τ => integrable_finsetSum _ (fun j _ => hint' τ j))]
  have hτ : ∀ τ, ∫ x, ∑ j, w j * κ τ (σ j) x (a j) ∂(ν τ) =
      ∑ j, w j * ∫ x, κ (σ j) τ (a j) x ∂(ν τ) := by
    intro τ
    rw [integral_finsetSum _ (fun j _ => hint' τ j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul]
    simp only [hsw]
  simp only [hτ]
  unfold rowI
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]

theorem blkMM (hμ : ∀ τ, BD (μ τ) C) (hν : ∀ τ, BD (ν τ) C) {κ : Bool → Bool → ℝ → ℝ → ℝ}
    (hG2 : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((μ τ).prod (ν τ')))
    (hint : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2)
      ((Mmu μ).prod (Mmu ν))) :
    ∫ z, κ z.1.1 z.2.1 z.1.2 z.2.2 ∂((Mmu μ).prod (Mmu ν)) = pairI μ ν κ := by
  have := Mmu_finite hμ
  have := Mmu_finite hν
  have hfμ : ∀ τ, IsFiniteMeasure (μ τ) := fun τ => (hμ τ).finite
  have hfν : ∀ τ, IsFiniteMeasure (ν τ) := fun τ => (hν τ).finite
  rw [integral_prod _ hint]
  dsimp only
  have hae : ∀ τ, ∀ᵐ x ∂(μ τ), ∀ τ', Integrable (fun y => κ τ τ' x y) (ν τ') := by
    intro τ
    rw [ae_all_iff]
    intro τ'
    exact (hG2 τ τ').prod_right_ae
  have hinner : ∀ τ, ∀ᵐ x ∂(μ τ), ∫ y', κ τ y'.1 x y'.2 ∂(Mmu ν) =
      ∑ τ', ∫ y, κ τ τ' x y ∂(ν τ') := by
    intro τ
    filter_upwards [hae τ] with x hx
    exact intM ν (fun y' => κ τ y'.1 x y'.2) hx
  have hint1 : ∀ τ, Integrable (fun x => ∑ τ', ∫ y, κ τ τ' x y ∂(ν τ')) (μ τ) := by
    intro τ
    exact integrable_finsetSum _ (fun τ' _ => (hG2 τ τ').integral_prod_left)
  have hint2 : ∀ τ, Integrable (fun x => ∫ y', κ τ y'.1 x y'.2 ∂(Mmu ν)) (μ τ) := by
    intro τ
    exact (hint1 τ).congr ((hinner τ).mono fun x hx => hx.symm)
  rw [intM μ (fun y => ∫ y', κ y.1 y'.1 y.2 y'.2 ∂(Mmu ν)) hint2]
  unfold pairI
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  dsimp only
  rw [integral_congr_ae (hinner τ),
    integral_finsetSum _ (fun τ' _ => (hG2 τ τ').integral_prod_left)]

/-- **The pairing of the signed discrepancy `(A + N) - P` with a symmetric kernel**, evaluated. -/
theorem P2_eval (hw : ∀ i, 0 < w i) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    {κ : Bool → Bool → ℝ → ℝ → ℝ} (hsymm : ∀ s t x y, κ s t x y = κ t s y x)
    (hP1 : ∀ i τ, Integrable (κ (σ i) τ (a i)) (P τ))
    (hN1 : ∀ i τ, Integrable (κ (σ i) τ (a i)) (N τ))
    (hPP : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((P τ).prod (P τ')))
    (hPN : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((P τ).prod (N τ')))
    (hNP : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((N τ).prod (P τ')))
    (hNN : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((N τ).prod (N τ')))
    (hF : Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2)
      ((Amu w a σ + Mmu N + Mmu P).prod (Amu w a σ + Mmu N + Mmu P))) :
    P2 (Amu w a σ + Mmu N) (Mmu P) (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2) =
      (∑ i, ∑ j, w i * w j * κ (σ i) (σ j) (a i) (a j))
        + 2 * rowI w a σ N κ - 2 * rowI w a σ P κ
        + pairI N N κ - pairI N P κ - pairI P N κ + pairI P P κ := by
  have := Mmu_finite hP
  have := Mmu_finite hN
  have lA : Amu w a σ ≤ Amu w a σ + Mmu N + Mmu P := Measure.le_add_right (Measure.le_add_right le_rfl)
  have lN : Mmu N ≤ Amu w a σ + Mmu N + Mmu P := Measure.le_add_right (Measure.le_add_left le_rfl)
  have lP : Mmu P ≤ Amu w a σ + Mmu N + Mmu P := Measure.le_add_left le_rfl
  have lAN : Amu w a σ + Mmu N ≤ Amu w a σ + Mmu N + Mmu P := Measure.le_add_right le_rfl
  have hI : ∀ {U V : Measure (Bool × ℝ)} [SFinite U] [SFinite V], U ≤ Amu w a σ + Mmu N + Mmu P →
      V ≤ Amu w a σ + Mmu N + Mmu P →
      Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => κ z.1.1 z.2.1 z.1.2 z.2.2) (U.prod V) :=
    fun hU hV => hF.mono_measure (Measure.prod_mono hU hV)
  have eAA := blkAA hw (hI lA lA)
  have eAN := blkAM hw hN hN1 (hI lA lN)
  have eAP := blkAM hw hP hP1 (hI lA lP)
  have eNA := blkMA hw hN hsymm hN1 (hI lN lA)
  have ePA := blkMA hw hP hsymm hP1 (hI lP lA)
  have eNN := blkMM hN hN hNN (hI lN lN)
  have eNP := blkMM hN hP hNP (hI lN lP)
  have ePN := blkMM hP hN hPN (hI lP lN)
  have ePP := blkMM hP hP hPP (hI lP lP)
  unfold P2
  rw [integral_add_prod (hI lAN lAN), integral_prod_add (hI lA lAN), integral_prod_add (hI lN lAN),
    integral_add_prod (hI lAN lP), integral_prod_add (hI lP lAN)]
  rw [eAA, eAN, eAP, eNA, ePA, eNN, eNP, ePN, ePP]
  ring

end Eval

/-! ### The species kernels and the energy functional -/
section Final

/-- the true kernel: `-log |x - y|` for equal labels, `-log (x + y)` for opposite labels -/
def Kt (s t : Bool) (x y : ℝ) : ℝ := if s = t then -Real.log |x - y| else -Real.log (x + y)
/-- damped kernel -/
def Ktil (ρ : ℝ) (s t : Bool) (x y : ℝ) : ℝ := if s = t then K1d ρ x y else K2d ρ x y
/-- difference kernel -/
def Dk (ρ : ℝ) (s t : Bool) (x y : ℝ) : ℝ := if s = t then D1 ρ x y else D2 ρ x y

theorem Kt_eq (ρ : ℝ) (s t : Bool) (x y : ℝ) : Kt s t x y = Ktil ρ s t x y + Dk ρ s t x y := by
  unfold Kt Ktil Dk D1 D2
  split_ifs <;> ring

theorem Ktil_symm (ρ : ℝ) (s t : Bool) (x y : ℝ) : Ktil ρ s t x y = Ktil ρ t s y x := by
  unfold Ktil K1d K2d rr
  by_cases h : s = t
  · subst h; simp [min_comm, max_comm]
  · have h' : ¬ t = s := fun e => h e.symm
    simp [h, h', min_comm, max_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The (off-diagonal) energy functional of a species kernel `κ` for the discrepancy
`∑ w_i δ_{a_i} - (P - N)`. -/
def Ex (w a : ι → ℝ) (σ : ι → Bool) (P N : Bool → Measure ℝ) (κ : Bool → Bool → ℝ → ℝ → ℝ) : ℝ :=
  (∑ i, ∑ j, if i = j then 0 else w i * w j * κ (σ i) (σ j) (a i) (a j))
    - 2 * rowI w a σ P κ + 2 * rowI w a σ N κ
    + pairI P P κ - pairI P N κ - pairI N P κ + pairI N N κ

/-- sections and products integrable -/
structure Good (a : ι → ℝ) (σ : ι → Bool) (P N : Bool → Measure ℝ)
    (κ : Bool → Bool → ℝ → ℝ → ℝ) : Prop where
  sP : ∀ i τ, Integrable (κ (σ i) τ (a i)) (P τ)
  sN : ∀ i τ, Integrable (κ (σ i) τ (a i)) (N τ)
  pPP : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((P τ).prod (P τ'))
  pPN : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((P τ).prod (N τ'))
  pNP : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((N τ).prod (P τ'))
  pNN : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ τ τ' p.1 p.2) ((N τ).prod (N τ'))

theorem rowI_add {w a : ι → ℝ} {σ : ι → Bool} {μ : Bool → Measure ℝ}
    {κ₁ κ₂ : Bool → Bool → ℝ → ℝ → ℝ} (h₁ : ∀ i τ, Integrable (κ₁ (σ i) τ (a i)) (μ τ))
    (h₂ : ∀ i τ, Integrable (κ₂ (σ i) τ (a i)) (μ τ)) :
    rowI w a σ μ (fun s t x y => κ₁ s t x y + κ₂ s t x y) = rowI w a σ μ κ₁ + rowI w a σ μ κ₂ := by
  unfold rowI
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  exact integral_add (h₁ i τ) (h₂ i τ)

theorem pairI_add {μ ν : Bool → Measure ℝ} [∀ τ, IsFiniteMeasure (μ τ)] [∀ τ, IsFiniteMeasure (ν τ)]
    {κ₁ κ₂ : Bool → Bool → ℝ → ℝ → ℝ}
    (h₁ : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ₁ τ τ' p.1 p.2) ((μ τ).prod (ν τ')))
    (h₂ : ∀ τ τ', Integrable (fun p : ℝ × ℝ => κ₂ τ τ' p.1 p.2) ((μ τ).prod (ν τ'))) :
    pairI μ ν (fun s t x y => κ₁ s t x y + κ₂ s t x y) = pairI μ ν κ₁ + pairI μ ν κ₂ := by
  unfold pairI
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ' _ => ?_)
  have a1 : Integrable (fun x => ∫ y, κ₁ τ τ' x y ∂(ν τ')) (μ τ) := (h₁ τ τ').integral_prod_left
  have a2 : Integrable (fun x => ∫ y, κ₂ τ τ' x y ∂(ν τ')) (μ τ) := (h₂ τ τ').integral_prod_left
  rw [← integral_add a1 a2]
  apply integral_congr_ae
  filter_upwards [(h₁ τ τ').prod_right_ae, (h₂ τ τ').prod_right_ae] with x hx1 hx2
  exact integral_add hx1 hx2

theorem Ex_add {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
    [∀ τ, IsFiniteMeasure (P τ)] [∀ τ, IsFiniteMeasure (N τ)]
    {κ₁ κ₂ : Bool → Bool → ℝ → ℝ → ℝ} (h₁ : Good a σ P N κ₁) (h₂ : Good a σ P N κ₂) :
    Ex w a σ P N (fun s t x y => κ₁ s t x y + κ₂ s t x y) = Ex w a σ P N κ₁ + Ex w a σ P N κ₂ := by
  unfold Ex
  have e1 : (∑ i, ∑ j, if i = j then 0 else w i * w j * (κ₁ (σ i) (σ j) (a i) (a j) + κ₂ (σ i) (σ j) (a i) (a j))) =
      (∑ i, ∑ j, if i = j then 0 else w i * w j * κ₁ (σ i) (σ j) (a i) (a j)) +
      (∑ i, ∑ j, if i = j then 0 else w i * w j * κ₂ (σ i) (σ j) (a i) (a j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [e1, rowI_add h₁.sP h₂.sP, rowI_add h₁.sN h₂.sN, pairI_add h₁.pPP h₂.pPP,
    pairI_add h₁.pPN h₂.pPN, pairI_add h₁.pNP h₂.pNP, pairI_add h₁.pNN h₂.pNN]
  ring

end Final

section Good
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
  {C : ℝ} {ρ : ℝ}

theorem measurable_Ktil (ρ : ℝ) (s t : Bool) : Measurable (fun p : ℝ × ℝ => Ktil ρ s t p.1 p.2) := by
  unfold Ktil
  by_cases h : s = t
  · simp only [h, if_true]; exact measurable_K1d ρ
  · simp only [h, ite_false]; exact measurable_K2d ρ

theorem Ktil_bound (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (s t : Bool) {x y : ℝ} (hx : x ∈ Ioo (0:ℝ) 1)
    (hy : y ∈ Ioo (0:ℝ) 1) :
    |Ktil ρ s t x y| ≤ (|Real.log (1 - ρ)| + 1) + |Real.log x| + |Real.log y| := by
  unfold Ktil
  by_cases h : s = t
  · simp only [h, if_true]
    rw [abs_of_nonneg (K1d_nonneg hρ0 hρ1 hx.1 hx.2 hy.1 hy.2)]
    have := K1d_le hρ0 hρ1 hx.1 hx.2 hy.1 hy.2
    linarith [abs_nonneg (Real.log y)]
  · simp only [h, ite_false]
    have := K2d_abs_le hρ0 hρ1 hx.1 hx.2 hy.1 hy.2
    linarith [abs_nonneg (Real.log y), abs_nonneg (Real.log (1 - ρ))]

theorem Ktil_sec {m : Measure ℝ} (h : BD m C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (s τ : Bool) {x : ℝ}
    (hx : x ∈ Ioo (0:ℝ) 1) : Integrable (Ktil ρ s τ x) m :=
  intK_single h (k := Ktil ρ s τ) (c := |Real.log (1 - ρ)| + 1)
    (fun x => (measurable_Ktil ρ s τ).comp (by fun_prop : Measurable fun y : ℝ => (x, y)))
    (fun x y hx hy => Ktil_bound hρ0 hρ1 _ _ hx hy) hx

theorem Ktil_prd {m m' : Measure ℝ} (h : BD m C) (h' : BD m' C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (τ τ' : Bool) : Integrable (fun p : ℝ × ℝ => Ktil ρ τ τ' p.1 p.2) (m.prod m') :=
  intK_prod h h' (measurable_Ktil ρ τ τ') (c := |Real.log (1 - ρ)| + 1)
    (fun x y hx hy => Ktil_bound hρ0 hρ1 _ _ hx hy)

theorem good_Ktil (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Good a σ P N (Ktil ρ) :=
  ⟨fun i τ => Ktil_sec (hP τ) hρ0 hρ1 _ _ (ha i), fun i τ => Ktil_sec (hN τ) hρ0 hρ1 _ _ (ha i),
    fun τ τ' => Ktil_prd (hP τ) (hP τ') hρ0 hρ1 τ τ', fun τ τ' => Ktil_prd (hP τ) (hN τ') hρ0 hρ1 τ τ',
    fun τ τ' => Ktil_prd (hN τ) (hP τ') hρ0 hρ1 τ τ', fun τ τ' => Ktil_prd (hN τ) (hN τ') hρ0 hρ1 τ τ'⟩

theorem Dk_sec {m : Measure ℝ} (h : BD m C) (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (s τ : Bool)
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : Integrable (Dk ρ s τ x) m := by
  unfold Dk
  by_cases hs : s = τ
  · simp only [hs, if_true]; exact (D1_int h hC hρ0 hρ1 hx).1
  · simp only [hs, ite_false]; exact (D2_int h hρ0 hρ1 hx).1

theorem Dk_prd {m m' : Measure ℝ} (h : BD m C) (h' : BD m' C) (hC : 0 ≤ C) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (τ τ' : Bool) : Integrable (fun p : ℝ × ℝ => Dk ρ τ τ' p.1 p.2) (m.prod m') := by
  unfold Dk
  by_cases hs : τ = τ'
  · simp only [hs, if_true]; exact D1_prod h h' hC hρ0 hρ1
  · simp only [hs, ite_false]; exact D2_prod h h' hρ0 hρ1

theorem good_Dk (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Good a σ P N (Dk ρ) :=
  ⟨fun i τ => Dk_sec (hP τ) hC hρ0 hρ1 _ _ (ha i), fun i τ => Dk_sec (hN τ) hC hρ0 hρ1 _ _ (ha i),
    fun τ τ' => Dk_prd (hP τ) (hP τ') hC hρ0 hρ1 τ τ', fun τ τ' => Dk_prd (hP τ) (hN τ') hC hρ0 hρ1 τ τ',
    fun τ τ' => Dk_prd (hN τ) (hP τ') hC hρ0 hρ1 τ τ', fun τ τ' => Dk_prd (hN τ) (hN τ') hC hρ0 hρ1 τ τ'⟩

end Good

section ExD
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
  {C : ℝ} {ρ : ℝ}

/-- `∫ Dk(x, ·) dm` (summed over the species) is at most `C S` at every `x ∈ (0,1)`. -/
theorem Dk_row_le {m : Bool → Measure ℝ} (h : ∀ τ, BD (m τ) C) (hC : 0 ≤ C) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (s : Bool) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    ∑ τ, ∫ y, Dk ρ s τ x y ∂(m τ) ≤ C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))) := by
  calc ∑ τ, ∫ y, Dk ρ s τ x y ∂(m τ)
      ≤ ∑ τ, (if τ = s then C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))) else 0) := by
        refine Finset.sum_le_sum (fun τ _ => ?_)
        unfold Dk
        by_cases hs : s = τ
        · subst hs
          simp only [eq_self_iff_true, ite_true]
          exact (D1_int (h s) hC hρ0 hρ1 hx).2.2
        · have hs' : ¬ τ = s := fun e => hs e.symm
          simp only [hs, hs', ite_false]
          exact (D2_int (h τ) hρ0 hρ1 hx).2
    _ = _ := by simp

/-- `∫ Dk(x, ·) dm` (summed over the species) is at least `-(1-ρ) |m|` at every `x ∈ (0,1)`. -/
theorem Dk_row_ge {m : Bool → Measure ℝ} (h : ∀ τ, BD (m τ) C) (hC : 0 ≤ C) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (s : Bool) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    -(1 - ρ) * ∑ τ, (m τ).real univ ≤ ∑ τ, ∫ y, Dk ρ s τ x y ∂(m τ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  have := (h τ).finite
  have hm0 : 0 ≤ (m τ).real univ := measureReal_nonneg
  unfold Dk
  have hε : 0 ≤ 1 - ρ := by linarith
  by_cases hs : s = τ
  · subst hs
    simp only [eq_self_iff_true, ite_true]
    have := (D1_int (h s) hC hρ0 hρ1 hx).2.1
    nlinarith
  · simp only [hs, ite_false]
    have : ∫ y, (-(1 - ρ)) ∂(m τ) ≤ ∫ y, D2 ρ x y ∂(m τ) := by
      apply integral_mono_ae (integrable_const _) (D2_int (h τ) hρ0 hρ1 hx).1
      filter_upwards [(h τ).ae_mem] with y hy
      exact D2_ge hρ0 hρ1 hx.1 hy.1
    simpa [Measure.real, mul_comm] using this

/-- `pairI m m' Dk ≤ |m| C S`. -/
theorem pairI_Dk_le {m m' : Bool → Measure ℝ} (h : ∀ τ, BD (m τ) C) (h' : ∀ τ, BD (m' τ) C)
    (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    pairI m m' (Dk ρ) ≤ (∑ τ, (m τ).real univ) * (C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))))) := by
  unfold pairI
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  have := (h τ).finite
  have hfin : ∀ τ', IsFiniteMeasure (m' τ') := fun τ' => (h' τ').finite
  have hint : ∀ τ', Integrable (fun x => ∫ y, Dk ρ τ τ' x y ∂(m' τ')) (m τ) := fun τ' =>
    (Dk_prd (h τ) (h' τ') hC hρ0 hρ1 τ τ').integral_prod_left
  rw [← integral_finsetSum _ (fun τ' _ => hint τ')]
  have step : ∀ᵐ x ∂(m τ), ∑ τ', ∫ y, Dk ρ τ τ' x y ∂(m' τ') ≤
      C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))) := by
    filter_upwards [(h τ).ae_mem] with x hx
    exact Dk_row_le h' hC hρ0 hρ1 τ hx
  have := integral_mono_ae (integrable_finsetSum _ (fun τ' _ => hint τ')) (integrable_const _) step
  simp only [integral_const, smul_eq_mul] at this
  linarith

/-- `pairI m m Dk ≥ -(1-ρ) |m|²` (same as `pairI m' m`, any two BD families). -/
theorem pairI_Dk_ge {m m' : Bool → Measure ℝ} (h : ∀ τ, BD (m τ) C) (h' : ∀ τ, BD (m' τ) C)
    (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    -(1 - ρ) * ((∑ τ, (m τ).real univ) * (∑ τ, (m' τ).real univ)) ≤ pairI m m' (Dk ρ) := by
  unfold pairI
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  have := (h τ).finite
  have hfin : ∀ τ', IsFiniteMeasure (m' τ') := fun τ' => (h' τ').finite
  have hint : ∀ τ', Integrable (fun x => ∫ y, Dk ρ τ τ' x y ∂(m' τ')) (m τ) := fun τ' =>
    (Dk_prd (h τ) (h' τ') hC hρ0 hρ1 τ τ').integral_prod_left
  rw [← integral_finsetSum _ (fun τ' _ => hint τ')]
  have step : ∀ᵐ x ∂(m τ), -(1 - ρ) * ∑ τ', (m' τ').real univ ≤ ∑ τ', ∫ y, Dk ρ τ τ' x y ∂(m' τ') := by
    filter_upwards [(h τ).ae_mem] with x hx
    exact Dk_row_ge h' hC hρ0 hρ1 τ hx
  have := integral_mono_ae (integrable_const _) (integrable_finsetSum _ (fun τ' _ => hint τ')) step
  simp only [integral_const, smul_eq_mul] at this
  nlinarith

theorem Ex_Dk_ge (hw : ∀ i, 0 < w i) (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1)
    (hinj : ∀ i j, i ≠ j → σ i = σ j → a i ≠ a j) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    -(1 - ρ) * ((∑ i, w i) ^ 2 + 2 * (∑ i, w i) * (∑ τ, (N τ).real univ) + (∑ τ, (N τ).real univ) ^ 2
        + (∑ τ, (P τ).real univ) ^ 2)
      - (2 * (∑ i, w i) + ∑ τ, (N τ).real univ + ∑ τ, (P τ).real univ) *
        (C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))))
      ≤ Ex w a σ P N (Dk ρ) := by
  have hε : 0 ≤ 1 - ρ := by linarith
  -- discrete-discrete
  have hdd : -(1 - ρ) * (∑ i, w i) ^ 2 ≤
      ∑ i, ∑ j, if i = j then 0 else w i * w j * Dk ρ (σ i) (σ j) (a i) (a j) := by
    have : (∑ i, w i) ^ 2 = ∑ i, ∑ j, w i * w j := by rw [sq, Finset.sum_mul_sum]
    rw [this, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hww : 0 < w i * w j := mul_pos (hw i) (hw j)
    by_cases hij : i = j
    · simp only [hij, ite_true]; nlinarith
    · simp only [hij, ite_false]
      unfold Dk
      by_cases hs : σ i = σ j
      · simp only [hs, ite_true]
        have := D1_nonneg hρ0 hρ1 (ha i).1 (ha j).1 (hinj i j hij hs)
        nlinarith
      · simp only [hs, ite_false]
        have := D2_ge hρ0 hρ1 (ha i).1 (ha j).1
        nlinarith
  -- atoms against P (upper) and against N (lower)
  have hdP : rowI w a σ P (Dk ρ) ≤ (∑ i, w i) * (C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ))))) := by
    unfold rowI
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (Dk_row_le hP hC hρ0 hρ1 _ (ha i)) (hw i).le)
  have hdN : -(1 - ρ) * ((∑ i, w i) * ∑ τ, (N τ).real univ) ≤ rowI w a σ N (Dk ρ) := by
    unfold rowI
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := mul_le_mul_of_nonneg_left (Dk_row_ge hN hC hρ0 hρ1 (σ i) (ha i)) (hw i).le
    nlinarith
  have hPP := pairI_Dk_ge hP hP hC hρ0 hρ1
  have hNN := pairI_Dk_ge hN hN hC hρ0 hρ1
  have hPN := pairI_Dk_le hP hN hC hρ0 hρ1
  have hNP := pairI_Dk_le hN hP hC hρ0 hρ1
  unfold Ex
  nlinarith [hdd, hdP, hdN, hPP, hNN, hPN, hNP]

end ExD

section Assembly
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
  {C : ℝ} {ρ : ℝ}

theorem Wk_add_int {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} {pr e : Y → ℝ} {k₁ k₂ : ℝ → ℝ → ℝ}
    (h₁ : Integrable (Wk pr e k₁) ((A + M).prod (A + M)))
    (h₂ : Integrable (Wk pr e k₂) ((A + M).prod (A + M))) :
    Integrable (Wk pr e (fun x y => k₁ x y + k₂ x y)) ((A + M).prod (A + M)) := by
  convert h₁.add h₂ using 1
  funext z; simp only [Wk, Pi.add_apply]; ring

theorem Wk_sub_int {Y : Type*} [MeasurableSpace Y] {A M : Measure Y} {pr e : Y → ℝ} {k₁ k₂ : ℝ → ℝ → ℝ}
    (h₁ : Integrable (Wk pr e k₁) ((A + M).prod (A + M)))
    (h₂ : Integrable (Wk pr e k₂) ((A + M).prod (A + M))) :
    Integrable (Wk pr e (fun x y => k₁ x y - k₂ x y)) ((A + M).prod (A + M)) := by
  convert h₁.sub h₂ using 1
  funext z; simp only [Wk, Pi.sub_apply]; ring

theorem Ktil_decomp (ρ : ℝ) (y y' : Bool × ℝ) :
    Ktil ρ y.1 y'.1 y.2 y'.2 =
      (1 / 2) * Wk Prod.snd (fun _ => (1:ℝ)) (fun x z => K1d ρ x z + K2d ρ x z) (y, y') +
      (1 / 2) * Wk Prod.snd sgn (fun x z => K1d ρ x z - K2d ρ x z) (y, y') := by
  obtain ⟨s, x⟩ := y
  obtain ⟨t, x'⟩ := y'
  cases s <;> cases t <;> simp [Ktil, Wk, sgn] <;> ring

theorem Qp_ge (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hmass : (Amu w a σ + Mmu N).real univ = (Mmu P).real univ) :
    (1 / 2) * PP (Amu w a σ + Mmu N) (Mmu P) Prod.snd (fun _ => (1:ℝ)) (ell ρ)
      + (1 / 2) * PP (Amu w a σ + Mmu N) (Mmu P) Prod.snd sgn (ell ρ) ≤
    P2 (Amu w a σ + Mmu N) (Mmu P)
      (fun z : (Bool × ℝ) × (Bool × ℝ) => Ktil ρ z.1.1 z.2.1 z.1.2 z.2.2) := by
  have := Mmu_finite hP
  have := Mmu_finite hN
  have C1 : Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd (fun _ => (1:ℝ)) :=
    ctx_inst ha hP hN measurable_const (fun _ => by simp)
  have C2 : Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd sgn := ctx_inst ha hP hN measurable_sgn abs_sgn_le
  have i1 := Wk_add_int (adm_K1d C1 hρ0 hρ1) (adm_K2d C1 hρ0 hρ1)
  have i2 := Wk_sub_int (adm_K1d C2 hρ0 hρ1) (adm_K2d C2 hρ0 hρ1)
  have hfun : (fun z : (Bool × ℝ) × (Bool × ℝ) => Ktil ρ z.1.1 z.2.1 z.1.2 z.2.2) =
      fun z => (1 / 2) * Wk Prod.snd (fun _ => (1:ℝ)) (fun x y => K1d ρ x y + K2d ρ x y) z +
        (1 / 2) * Wk Prod.snd sgn (fun x y => K1d ρ x y - K2d ρ x y) z := by
    funext z; exact Ktil_decomp ρ z.1 z.2
  rw [hfun, P2_add (i1.const_mul _) (i2.const_mul _), P2_smul, P2_smul]
  have g1 := PP_sum_ge_ell C1 hmass (fun _ => rfl) hρ0 hρ1
  have g2 := PP_H_ge_ell C2 hρ0 hρ1
  unfold PP at g1 g2 ⊢
  linarith

end Assembly

section Moments
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
  {C : ℝ} {ρ : ℝ}

/-- species moment of the signed measure `∑_{σ_i = τ} w_i δ_{a_i} - (P_τ - N_τ)` -/
def mm (w a : ι → ℝ) (σ : ι → Bool) (P N : Bool → Measure ℝ) (τ : Bool) (k : ℕ) : ℝ :=
  (∑ i, if σ i = τ then w i * a i ^ k else 0) - ∫ x, x ^ k ∂(P τ) + ∫ x, x ^ k ∂(N τ)

/-- The quadratic term `L(D_{√ρ} p)` of the species `τ`. -/
def Lpart (w a : ι → ℝ) (σ : ι → Bool) (P N : Bool → Measure ℝ) (ρ : ℝ) (τ : Bool) : ℝ :=
  ∑' k : ℕ, (1 / ((k : ℝ) + 1)) *
    ((∑ i, if σ i = τ then w i * (Real.sqrt ρ * a i) ^ (k + 1) else 0)
      - ∫ y, (Real.sqrt ρ * y) ^ (k + 1) ∂(P τ) + ∫ y, (Real.sqrt ρ * y) ^ (k + 1) ∂(N τ)) ^ 2

theorem int_pow_mul {μ : Bool → Measure ℝ} {τ : Bool} (h : BD (μ τ) C) {c : ℝ} (hc : |c| ≤ 1) (k : ℕ) :
    Integrable (fun x : ℝ => c * x ^ k) (μ τ) := by
  have := h.finite
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (measurable_const.mul (measurable_id.pow_const k)).aestronglyMeasurable
  · filter_upwards [h.ae_mem] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    have h2 : |x| ^ k ≤ 1 := by rw [abs_of_pos hx.1]; exact pow_le_one₀ hx.1.le hx.2.le
    calc |c| * |x| ^ k ≤ 1 * 1 := mul_le_mul hc h2 (by positivity) zero_le_one
      _ = 1 := by norm_num

theorem Lpart_eq (hρ : 0 ≤ ρ) (τ : Bool) :
    Lpart w a σ P N ρ τ = ∑' k : ℕ, ρ ^ (k + 1) / ((k : ℝ) + 1) * (mm w a σ P N τ (k + 1)) ^ 2 := by
  unfold Lpart
  congr 1; funext k
  have e1 : (∑ i, if σ i = τ then w i * (Real.sqrt ρ * a i) ^ (k + 1) else 0) =
      Real.sqrt ρ ^ (k + 1) * ∑ i, if σ i = τ then w i * a i ^ (k + 1) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs
    · rw [mul_pow]; ring
    · simp
  have e2 : ∀ m : Measure ℝ, ∫ y, (Real.sqrt ρ * y) ^ (k + 1) ∂m =
      Real.sqrt ρ ^ (k + 1) * ∫ y, y ^ (k + 1) ∂m := by
    intro m; simp_rw [mul_pow]; exact integral_const_mul _ _
  have e3 : (Real.sqrt ρ ^ (k + 1)) ^ 2 = ρ ^ (k + 1) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hρ]
  rw [e1, e2, e2]
  unfold mm
  rw [show Real.sqrt ρ ^ (k + 1) * (∑ i, if σ i = τ then w i * a i ^ (k + 1) else 0) -
      Real.sqrt ρ ^ (k + 1) * ∫ y, y ^ (k + 1) ∂(P τ) + Real.sqrt ρ ^ (k + 1) * ∫ y, y ^ (k + 1) ∂(N τ) =
      Real.sqrt ρ ^ (k + 1) * ((∑ i, if σ i = τ then w i * a i ^ (k + 1) else 0) -
        ∫ y, y ^ (k + 1) ∂(P τ) + ∫ y, y ^ (k + 1) ∂(N τ)) by ring]
  rw [mul_pow, e3]
  ring

end Moments

section Moments2
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
  {C : ℝ} {ρ : ℝ}

theorem mom_one (hw : ∀ i, 0 < w i) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C) (k : ℕ) :
    mom (Amu w a σ + Mmu N) (Mmu P) Prod.snd (fun _ => (1:ℝ)) k =
      mm w a σ P N true k + mm w a σ P N false k := by
  unfold mom S1
  rw [intAN hw _ (fun τ => by simpa using int_pow_mul (hN τ) (c := 1) (by simp) k),
    intM P _ (fun τ => by simpa using int_pow_mul (hP τ) (c := 1) (by simp) k),
    Fintype.sum_bool, Fintype.sum_bool]
  unfold mm
  have : ∑ i, w i * (1 * a i ^ k) =
      (∑ i, if σ i = true then w i * a i ^ k else 0) + (∑ i, if σ i = false then w i * a i ^ k else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    cases σ i <;> simp
  simp only [one_mul] at this ⊢
  rw [this]; ring

theorem mom_sgn (hw : ∀ i, 0 < w i) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C) (k : ℕ) :
    mom (Amu w a σ + Mmu N) (Mmu P) Prod.snd sgn k =
      mm w a σ P N true k - mm w a σ P N false k := by
  unfold mom S1
  rw [intAN hw _ (fun τ => int_pow_mul (hN τ) (c := sgn (τ, 0)) (abs_sgn_le _) k |>.congr
      (Filter.Eventually.of_forall fun x => by simp [sgn])),
    intM P _ (fun τ => int_pow_mul (hP τ) (c := sgn (τ, 0)) (abs_sgn_le _) k |>.congr
      (Filter.Eventually.of_forall fun x => by simp [sgn])),
    Fintype.sum_bool, Fintype.sum_bool]
  unfold mm
  have : ∑ i, w i * (sgn (σ i, a i) * a i ^ k) =
      (∑ i, if σ i = true then w i * a i ^ k else 0) - (∑ i, if σ i = false then w i * a i ^ k else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    cases σ i <;> simp [sgn]
  have e1 : ∀ m : Measure ℝ, ∫ x, sgn (true, x) * x ^ k ∂m = ∫ x, x ^ k ∂m := by
    intro m; simp [sgn]
  have e2 : ∀ m : Measure ℝ, ∫ x, sgn (false, x) * x ^ k ∂m = -∫ x, x ^ k ∂m := by
    intro m; simp [sgn, integral_neg]
  simp only [Prod.snd] at *
  rw [this, e1, e2, e1, e2]; ring

end Moments2

section Main
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool} {P N : Bool → Measure ℝ}
  {C : ℝ} {ρ : ℝ}

theorem half_sum_eq (hw : ∀ i, 0 < w i) (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C)
    (hN : ∀ τ, BD (N τ) C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (1 / 2) * PP (Amu w a σ + Mmu N) (Mmu P) Prod.snd (fun _ => (1:ℝ)) (ell ρ)
      + (1 / 2) * PP (Amu w a σ + Mmu N) (Mmu P) Prod.snd sgn (ell ρ) =
    Lpart w a σ P N ρ true + Lpart w a σ P N ρ false := by
  have := Mmu_finite hP
  have := Mmu_finite hN
  have C1 : Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd (fun _ => (1:ℝ)) :=
    ctx_inst ha hP hN measurable_const (fun _ => by simp)
  have C2 : Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd sgn := ctx_inst ha hP hN measurable_sgn abs_sgn_le
  have hs1 := PP_ell C1 hρ0 hρ1
  have hs2 := PP_ell C2 hρ0 hρ1
  simp only [mom_one hw hP hN] at hs1
  simp only [mom_sgn hw hP hN] at hs2
  set g : Bool → ℕ → ℝ := fun τ k => ρ ^ (k + 1) / ((k : ℝ) + 1) * (mm w a σ P N τ (k + 1)) ^ 2 with hg
  have hc : ∀ k : ℕ, 0 ≤ ρ ^ (k + 1) / ((k : ℝ) + 1) := fun k => by positivity
  have hsum := (hs1.mul_left (1 / 2)).add (hs2.mul_left (1 / 2))
  have hfun : (fun k : ℕ => 1 / 2 * (ρ ^ (k + 1) / ((k : ℝ) + 1) * (mm w a σ P N true (k + 1) + mm w a σ P N false (k + 1)) ^ 2)
      + 1 / 2 * (ρ ^ (k + 1) / ((k : ℝ) + 1) * (mm w a σ P N true (k + 1) - mm w a σ P N false (k + 1)) ^ 2)) =
      fun k => g true k + g false k := by
    funext k; simp only [hg]; try ring
  rw [hfun] at hsum
  have sg1 : Summable (g true) := Summable.of_nonneg_of_le (fun k => mul_nonneg (hc k) (sq_nonneg _))
    (fun k => by simp only [hg]; nlinarith [mul_nonneg (hc k) (sq_nonneg (mm w a σ P N false (k + 1)))]) hsum.summable
  have sg2 : Summable (g false) := Summable.of_nonneg_of_le (fun k => mul_nonneg (hc k) (sq_nonneg _))
    (fun k => by simp only [hg]; nlinarith [mul_nonneg (hc k) (sq_nonneg (mm w a σ P N true (k + 1)))]) hsum.summable
  rw [Lpart_eq hρ0.le, Lpart_eq hρ0.le]
  have := hsum.tsum_eq
  rw [Summable.tsum_add sg1 sg2] at this
  rw [← this]

theorem F_Ktil_int (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (fun z : (Bool × ℝ) × (Bool × ℝ) => Ktil ρ z.1.1 z.2.1 z.1.2 z.2.2)
      ((Amu w a σ + Mmu N + Mmu P).prod (Amu w a σ + Mmu N + Mmu P)) := by
  have := Mmu_finite hP
  have := Mmu_finite hN
  have C1 : Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd (fun _ => (1:ℝ)) :=
    ctx_inst ha hP hN measurable_const (fun _ => by simp)
  have C2 : Ctx (Amu w a σ + Mmu N) (Mmu P) Prod.snd sgn := ctx_inst ha hP hN measurable_sgn abs_sgn_le
  have i1 := Wk_add_int (adm_K1d C1 hρ0 hρ1) (adm_K2d C1 hρ0 hρ1)
  have i2 := Wk_sub_int (adm_K1d C2 hρ0 hρ1) (adm_K2d C2 hρ0 hρ1)
  have := (i1.const_mul (1 / 2)).add (i2.const_mul (1 / 2))
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  exact (Ktil_decomp ρ z.1 z.2).symm

theorem K1d_diag {ρ x : ℝ} (hx : 0 < x) : K1d ρ x x = -Real.log x - Real.log (1 - ρ) := by
  unfold K1d rr
  rw [max_self, min_self, div_self hx.ne', mul_one]

theorem Ex_Ktil_eq (hw : ∀ i, 0 < w i) (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1) (hP : ∀ τ, BD (P τ) C)
    (hN : ∀ τ, BD (N τ) C) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Ex w a σ P N (Ktil ρ) =
      P2 (Amu w a σ + Mmu N) (Mmu P)
        (fun z : (Bool × ℝ) × (Bool × ℝ) => Ktil ρ z.1.1 z.2.1 z.1.2 z.2.2)
        - ∑ i, w i ^ 2 * (-Real.log (a i) - Real.log (1 - ρ)) := by
  have G := good_Ktil (σ := σ) ha hP hN hρ0 hρ1
  rw [P2_eval hw hP hN (Ktil_symm ρ) G.sP G.sN G.pPP G.pPN G.pNP G.pNN (F_Ktil_int ha hP hN hρ0 hρ1)]
  unfold Ex
  have : (∑ i, ∑ j, w i * w j * Ktil ρ (σ i) (σ j) (a i) (a j)) =
      (∑ i, ∑ j, if i = j then 0 else w i * w j * Ktil ρ (σ i) (σ j) (a i) (a j))
        + ∑ i, w i ^ 2 * (-Real.log (a i) - Real.log (1 - ρ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : ∀ j, w i * w j * Ktil ρ (σ i) (σ j) (a i) (a j) =
        (if i = j then 0 else w i * w j * Ktil ρ (σ i) (σ j) (a i) (a j)) +
          (if i = j then w i * w j * Ktil ρ (σ i) (σ j) (a i) (a j) else 0) := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    have hdiag : Ktil ρ (σ i) (σ i) (a i) (a i) = -Real.log (a i) - Real.log (1 - ρ) := by
      unfold Ktil; rw [if_pos rfl]; exact K1d_diag (ha i).1
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i, if_pos (Finset.mem_univ i), hdiag]
    ring
  rw [this]; ring

end Main

/-! ### The theorem -/
section TheTheorem
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {w a : ι → ℝ} {σ : ι → Bool}
  {P N : Bool → Measure ℝ} {C : ℝ} {ρ : ℝ}

/-- The (off-diagonal) logarithmic energy of the signed configuration
`∑ w_i δ_{x_i} - (P - N)`, with `x_i = ±a_i` according to the label `σ_i` and `P_τ - N_τ` the
(signed) reference of the species `τ`, in the folded coordinates `a = |x|`. -/
def Ioff (w a : ι → ℝ) (σ : ι → Bool) (P N : Bool → Measure ℝ) : ℝ := Ex w a σ P N Kt

theorem mass_real (hw : ∀ i, 0 < w i) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C) :
    (Amu w a σ + Mmu N).real univ = ∑ i, w i + ∑ τ, (N τ).real univ ∧
      (Mmu P).real univ = ∑ τ, (P τ).real univ := by
  have := Mmu_finite hP
  have := Mmu_finite hN
  constructor
  · have := intAN (σ := σ) (a := a) (N := N) hw (fun _ => (1:ℝ))
      (fun τ => by have := (hN τ).finite; exact integrable_const _)
    simpa using this
  · have := intM P (fun _ => (1:ℝ)) (fun τ => by
      have := (hP τ).finite
      exact integrable_const _)
    simpa using this

/-- **Theorem D7.1 (discrete Theorem 7.1) for a signed reference `P - N`.**  With
`W' = ∑ w_i + |N|` (the total mass of the positive side `A + N` of the discrepancy). -/
theorem reflection_energy (hw : ∀ i, 0 < w i) (ha : ∀ i, a i ∈ Ioo (0:ℝ) 1)
    (hinj : ∀ i j, i ≠ j → σ i = σ j → a i ≠ a j) (hP : ∀ τ, BD (P τ) C) (hN : ∀ τ, BD (N τ) C)
    (hC : 0 ≤ C) (hmass : ∑ i, w i + ∑ τ, (N τ).real univ = ∑ τ, (P τ).real univ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∑ τ, Lpart w a σ P N ρ τ) - ∑ i, w i ^ 2 * (-Real.log (a i) + Real.log (1 / (1 - ρ)))
      - (12 * (∑ i, w i + ∑ τ, (N τ).real univ) * C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))
          + 2 * (1 - ρ) * (2 * (∑ i, w i + ∑ τ, (N τ).real univ)) ^ 2) ≤ Ioff w a σ P N := by
  have hfP : ∀ τ, IsFiniteMeasure (P τ) := fun τ => (hP τ).finite
  have hfN : ∀ τ, IsFiniteMeasure (N τ) := fun τ => (hN τ).finite
  obtain ⟨hA, hM⟩ := mass_real (a := a) (σ := σ) hw hP hN
  have hmass' : (Amu w a σ + Mmu N).real univ = (Mmu P).real univ := by rw [hA, hM]; exact hmass
  have hKt : Kt = fun s t x y => Ktil ρ s t x y + Dk ρ s t x y := by
    funext s t x y; exact Kt_eq ρ s t x y
  have hgood1 := good_Ktil (σ := σ) ha hP hN hρ0 hρ1
  have hgood2 := good_Dk (σ := σ) ha hP hN hC hρ0 hρ1
  have e1 : Ioff w a σ P N = Ex w a σ P N (Ktil ρ) + Ex w a σ P N (Dk ρ) := by
    unfold Ioff
    rw [hKt]
    exact Ex_add hgood1 hgood2
  have e2 := Ex_Ktil_eq (σ := σ) hw ha hP hN hρ0 hρ1
  have q1 := Qp_ge (σ := σ) (w := w) ha hP hN hρ0 hρ1 hmass'
  have q2 := half_sum_eq (σ := σ) hw ha hP hN hρ0 hρ1
  have d1 := Ex_Dk_ge (σ := σ) hw ha hinj hP hN hC hρ0 hρ1
  rw [← hmass] at d1
  rw [show (∑ τ, Lpart w a σ P N ρ τ) = Lpart w a σ P N ρ true + Lpart w a σ P N ρ false from
    Fintype.sum_bool _]
  have hlog : Real.log (1 / (1 - ρ)) = -Real.log (1 - ρ) := by rw [one_div, Real.log_inv]
  have hdiag : ∑ i, w i ^ 2 * (-Real.log (a i) + Real.log (1 / (1 - ρ))) =
      ∑ i, w i ^ 2 * (-Real.log (a i) - Real.log (1 - ρ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hlog]; ring
  rw [hdiag]
  set W := ∑ i, w i with hW
  set n := ∑ τ, (N τ).real univ with hn
  have hW : 0 ≤ W := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hn0 : 0 ≤ n := Finset.sum_nonneg (fun τ _ => measureReal_nonneg)
  have hε : 0 ≤ 1 - ρ := by linarith
  have hL : 0 ≤ Real.log (1 / (1 - ρ)) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hS0 : 0 ≤ C * (4 * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))) := by positivity
  rw [e1, e2]
  nlinarith [mul_nonneg hε (sq_nonneg (W + n)), mul_nonneg hS0 hn0, mul_nonneg hS0 hW]

end TheTheorem

end

end CatalanMeasure.Signed.ReflectionEnergy

#print axioms CatalanMeasure.Signed.ReflectionEnergy.reflection_energy
#print axioms CatalanMeasure.Signed.ReflectionEnergy.PP_G_nonneg
#print axioms CatalanMeasure.Signed.ReflectionEnergy.PP_K2d_nonneg
#print axioms CatalanMeasure.Signed.ReflectionEnergy.PP_H_ge_ell
