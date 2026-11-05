module

public import Submission.CatalanMeasure.GenD.Signed.EnergyNear
public import Submission.CatalanMeasure.GenD.Signed.TaylorCell
public import Submission.CatalanMeasure.Parametric.PopulationPhysicalValue
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierPowerLogFormula
public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierChebyshevLogFormula

/-!
# Closed forms of the signed fields (Theorem A, Phase 2, lane FF)

For a trial `D : SignedData` of the *Lean class* (`TrialForm.Spec F D`: finite-part-plus-geometric-tail
sequences `v, a, p`, the split parameter `η`, geometric `R`, the tilt `t = mneg μ`, polynomial-density species
`μ`) every field the certificate
bounds is an explicit sum of
`polynomial + Σ_e P_e(x) log|x - e| + Σ_q Re[ρ_q log (x - p_q)] + constant`
pieces, at the exact finite-`N` parameters `(ν, τ = 1 - e)`:

* A. `polyPot`: the log potential of a polynomial density,
  `∫_lo^hi P(t) log|t - x| dt = A(x) + Qh(x) (hi - x) log|hi - x| + Ql(x) (x - lo) log|x - lo|`,
  with explicit polynomials (`potQ`, `potA`; coefficients `potQc`, `potAc`).
* B. Branch-free conversion `Re[r log (1 - x z)] = Re[r log (x - 1/z)] + Re[r log (-z)]` and
  `Re[r log (1 - 2xz + z²)] = Re[r log (x - (1+z²)/(2z))] + Re[r log (-2z)]`.
* C. `barrierTrialS_tseq`, `barrierTrialT_tseq`: the series of `tseq f tail` (finite part plus
  geometric tail) are polynomial + pole logs + constant (reusing the OAI `barrierTail_S/T_hasSum`).
* D. `fld_gseq`: the dilated series of a geometric sequence is a pole sum (poles `1/(τ w)`).
* E. `polyMeas`: polynomial-density measures; `integral_log_polyMeas`, `integral_log_one_sub_polyMeas`.
* F. `fld_refMoment`, `rowRef_eq`, `rowRef_polyMeas`: the dilated moment series and the reference
  rows are species log potentials.
* G, H. `TrialForm.fNeg_closed, fPos_closed, fPosS_closed, fCol_closed, fNegM_closed, fPosM_closed,
  fPosMS_closed, fPosMR_closed, fNearM_closed, fNearMS_closed`.
* J. `fld_arcNeg_eq`: the arcsine block of the near field as a half-arcsine potential.

The problem's own fields `Rf, Cf` (and `Rm, Rn`) stay as given functions.
-/

@[expose] public section

namespace CatalanMeasure.Signed.FieldForm

open Set MeasureTheory Finset
open scoped BigOperators

noncomputable section

/-! ### A. The log potential of a polynomial density -/

/-- The polynomial `∑_{m<n} p_m t^m`. -/
def pc (n : ℕ) (p : ℕ → ℝ) (t : ℝ) : ℝ := ∑ m ∈ range n, p m * t ^ m

/-- An antiderivative of `pc n p`. -/
def potG (n : ℕ) (p : ℕ → ℝ) (t : ℝ) : ℝ := ∑ m ∈ range n, p m * t ^ (m + 1) / ((m : ℝ) + 1)

/-- `(potG t - potG x) / (t - x)`, as a polynomial in `t` and `x`. -/
def potH (n : ℕ) (p : ℕ → ℝ) (x t : ℝ) : ℝ :=
  ∑ m ∈ range n, p m / ((m : ℝ) + 1) * ∑ j ∈ range (m + 1), x ^ j * t ^ (m - j)

/-- An antiderivative of `potH n p x` in `t`. -/
def potK (n : ℕ) (p : ℕ → ℝ) (x t : ℝ) : ℝ :=
  ∑ m ∈ range n, p m / ((m : ℝ) + 1) *
    ∑ j ∈ range (m + 1), x ^ j * (t ^ (m - j + 1) / ((m - j + 1 : ℕ) : ℝ))

theorem hasDerivAt_potG (n : ℕ) (p : ℕ → ℝ) (t : ℝ) : HasDerivAt (potG n p) (pc n p t) t := by
  unfold potG pc
  have h : ∀ m ∈ range n, HasDerivAt (fun t : ℝ => p m * t ^ (m + 1) / ((m : ℝ) + 1))
      (p m * t ^ m) t := by
    intro m _
    have h1 := (hasDerivAt_pow (m + 1) t).const_mul (p m)
    have h2 := h1.div_const ((m : ℝ) + 1)
    refine h2.congr_deriv ?_
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  exact HasDerivAt.fun_sum h

theorem hasDerivAt_potK (n : ℕ) (p : ℕ → ℝ) (x t : ℝ) :
    HasDerivAt (potK n p x) (potH n p x t) t := by
  unfold potK potH
  have h : ∀ m ∈ range n, HasDerivAt (fun t : ℝ => p m / ((m : ℝ) + 1) *
      ∑ j ∈ range (m + 1), x ^ j * (t ^ (m - j + 1) / ((m - j + 1 : ℕ) : ℝ)))
      (p m / ((m : ℝ) + 1) * ∑ j ∈ range (m + 1), x ^ j * t ^ (m - j)) t := by
    intro m _
    have h0 : ∀ j ∈ range (m + 1), HasDerivAt
        (fun t : ℝ => x ^ j * (t ^ (m - j + 1) / ((m - j + 1 : ℕ) : ℝ)))
        (x ^ j * t ^ (m - j)) t := by
      intro j _
      have h1 := ((hasDerivAt_pow (m - j + 1) t).div_const ((m - j + 1 : ℕ) : ℝ)).const_mul (x ^ j)
      refine h1.congr_deriv ?_
      have : ((m - j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      simp only [Nat.add_sub_cancel]
      field_simp
    exact (HasDerivAt.fun_sum h0).const_mul _
  exact HasDerivAt.fun_sum h

theorem potG_sub (n : ℕ) (p : ℕ → ℝ) (x t : ℝ) :
    potG n p t - potG n p x = (t - x) * potH n p x t := by
  unfold potG potH
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hg := Commute.geom_sum₂_mul (Commute.all t x) (m + 1)
  simp only [Nat.add_sub_cancel] at hg
  have e : ∑ j ∈ range (m + 1), x ^ j * t ^ (m - j) =
      ∑ i ∈ range (m + 1), t ^ i * x ^ (m - i) := by
    have := Finset.sum_range_reflect (fun i => t ^ i * x ^ (m - i)) (m + 1)
    simp only [Nat.add_sub_cancel] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.sub_sub_self hj']
    ring
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [e]
  have : t ^ (m + 1) - x ^ (m + 1) = (∑ i ∈ range (m + 1), t ^ i * x ^ (m - i)) * (t - x) :=
    hg.symm
  calc p m * t ^ (m + 1) / ((m : ℝ) + 1) - p m * x ^ (m + 1) / ((m : ℝ) + 1)
      = p m / ((m : ℝ) + 1) * (t ^ (m + 1) - x ^ (m + 1)) := by ring
    _ = _ := by rw [this]; ring

theorem continuous_sub_mul_log (x : ℝ) : Continuous fun t : ℝ => (t - x) * Real.log |t - x| := by
  have := Real.continuous_mul_log.comp
    (continuous_id.sub continuous_const : Continuous fun t : ℝ => t - x)
  simpa [Function.comp_def, Real.log_abs] using this

theorem intervalIntegrable_mul_log_abs_sub {P : ℝ → ℝ} (hP : Continuous P) (x a b : ℝ) :
    IntervalIntegrable (fun t => P t * Real.log |t - x|) volume a b := by
  have hl : IntervalIntegrable (fun t : ℝ => Real.log |t - x|) volume a b := by
    have := (intervalIntegral.intervalIntegrable_log' (a := a - x) (b := b - x)).comp_sub_right x
    simpa [Real.log_abs] using this
  exact hl.continuousOn_mul hP.continuousOn

/-- FTC for the log potential on an interval not containing `x` in its interior. -/
theorem ftc_log_piece (P G H K : ℝ → ℝ) (x : ℝ)
    (hG : ∀ t, HasDerivAt G (P t) t) (hK : ∀ t, HasDerivAt K (H t) t)
    (hGH : ∀ t, G t - G x = (t - x) * H t) (hH : Continuous H) (hP : Continuous P)
    {a b : ℝ} (hab : a ≤ b) (hx : x ∉ Ioo a b) :
    ∫ t in a..b, P t * Real.log |t - x| =
      ((G b - G x) * Real.log |b - x| - K b) - ((G a - G x) * Real.log |a - x| - K a) := by
  have hKc : Continuous K := continuous_iff_continuousAt.2 fun t => (hK t).continuousAt
  have hcont : Continuous fun t => (G t - G x) * Real.log |t - x| - K t := by
    have : (fun t => (G t - G x) * Real.log |t - x| - K t) =
        fun t => H t * ((t - x) * Real.log |t - x|) - K t := by
      funext t; rw [hGH t]; ring
    rw [this]; exact (hH.mul (continuous_sub_mul_log x)).sub hKc
  have hder : ∀ t ∈ Ioo a b, HasDerivAt (fun t => (G t - G x) * Real.log |t - x| - K t)
      (P t * Real.log |t - x|) t := by
    intro t ht
    have htx : t - x ≠ 0 := sub_ne_zero.2 (fun h => hx (h ▸ ht))
    have h1 : HasDerivAt (fun t : ℝ => Real.log |t - x|) (1 / (t - x)) t := by
      have := ((hasDerivAt_id t).sub_const x).log htx
      simpa [Real.log_abs] using this
    have h2 := ((hG t).sub_const (G x)).mul h1
    have h3 := h2.sub (hK t)
    refine h3.congr_deriv ?_
    have : (G t - G x) * (1 / (t - x)) = H t := by
      rw [hGH t]; field_simp
    rw [this]; ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont.continuousOn hder
    (intervalIntegrable_mul_log_abs_sub hP x a b)

theorem ftc_log (P G H K : ℝ → ℝ) (x : ℝ)
    (hG : ∀ t, HasDerivAt G (P t) t) (hK : ∀ t, HasDerivAt K (H t) t)
    (hGH : ∀ t, G t - G x = (t - x) * H t) (hH : Continuous H) (hP : Continuous P)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, P t * Real.log |t - x| =
      ((G b - G x) * Real.log |b - x| - K b) - ((G a - G x) * Real.log |a - x| - K a) := by
  by_cases hx : x ∈ Ioo a b
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_mul_log_abs_sub hP x a x) (intervalIntegrable_mul_log_abs_sub hP x x b),
      ftc_log_piece P G H K x hG hK hGH hH hP hx.1.le (fun h => lt_irrefl _ h.2),
      ftc_log_piece P G H K x hG hK hGH hH hP hx.2.le (fun h => lt_irrefl _ h.1)]
    ring
  · exact ftc_log_piece P G H K x hG hK hGH hH hP hab hx

theorem continuous_pc (n : ℕ) (p : ℕ → ℝ) : Continuous (pc n p) := by
  unfold pc; fun_prop

theorem continuous_potH (n : ℕ) (p : ℕ → ℝ) (x : ℝ) : Continuous (potH n p x) := by
  unfold potH; fun_prop

/-- The explicit polynomial `Qh(x) = Q(x; hi)` multiplying `(hi - x) log|hi - x|`
(and `Ql(x) = Q(x; lo)` for the lower end). -/
def potQ (n : ℕ) (p : ℕ → ℝ) (x s : ℝ) : ℝ := potH n p x s

/-- The polynomial part of the log potential. -/
def potA (n : ℕ) (p : ℕ → ℝ) (lo hi x : ℝ) : ℝ := potK n p x lo - potK n p x hi

/-- **The log potential of a polynomial density** `∑_{m<n} p_m t^m` on `[lo, hi]`:
`∫ P(t) log|t - x| dt = Qh(x) (hi - x) log|hi - x| + Ql(x) (x - lo) log|x - lo| + A(x)`,
with `Qh = potQ n p · hi`, `Ql = potQ n p · lo`, `A = potA n p lo hi`, all explicit polynomials in
`x` (`potQ`, `potA` are finite sums of monomials; coefficients below). -/
theorem polyPot (n : ℕ) (p : ℕ → ℝ) {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) :
    ∫ t in lo..hi, pc n p t * Real.log |t - x| =
      potQ n p x hi * ((hi - x) * Real.log |hi - x|) +
      potQ n p x lo * ((x - lo) * Real.log |x - lo|) + potA n p lo hi x := by
  rw [ftc_log (pc n p) (potG n p) (potH n p x) (potK n p x) x (hasDerivAt_potG n p)
    (hasDerivAt_potK n p x) (potG_sub n p x) (continuous_potH n p x) (continuous_pc n p) h]
  rw [potG_sub n p x hi, potG_sub n p x lo, abs_sub_comm lo x]
  unfold potQ potA
  ring

/-! Coefficient form: `potQ`, `potA` as polynomials in `x` with explicit coefficients. -/

theorem sum_range_succ_swap (n : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ m ∈ range n, ∑ j ∈ range (m + 1), g m j = ∑ j ∈ range n, ∑ m ∈ Ico j n, g m j := by
  refine Finset.sum_comm' ?_
  intro m j
  simp only [Finset.mem_range, Finset.mem_Ico]
  omega

/-- Coefficient of `x^j` in `Q(x; s)`: `∑_{m ≥ j} p_m s^{m-j}/(m+1)`. -/
def potQc (n : ℕ) (p : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ Ico j n, p m / ((m : ℝ) + 1) * s ^ (m - j)

/-- Coefficient of `x^j` in `K(x; s)`. -/
def potKc (n : ℕ) (p : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ Ico j n, p m / ((m : ℝ) + 1) * (s ^ (m - j + 1) / ((m - j + 1 : ℕ) : ℝ))

/-- Coefficient of `x^j` in the polynomial part `A`. -/
def potAc (n : ℕ) (p : ℕ → ℝ) (lo hi : ℝ) (j : ℕ) : ℝ := potKc n p lo j - potKc n p hi j

theorem potQ_eq_coef (n : ℕ) (p : ℕ → ℝ) (x s : ℝ) :
    potQ n p x s = ∑ j ∈ range n, potQc n p s j * x ^ j := by
  unfold potQ potH potQc
  simp_rw [Finset.mul_sum]
  rw [sum_range_succ_swap n (fun m j => p m / ((m : ℝ) + 1) * (x ^ j * s ^ (m - j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem potK_eq_coef (n : ℕ) (p : ℕ → ℝ) (x s : ℝ) :
    potK n p x s = ∑ j ∈ range n, potKc n p s j * x ^ j := by
  unfold potK potKc
  simp_rw [Finset.mul_sum]
  rw [sum_range_succ_swap n (fun m j => p m / ((m : ℝ) + 1) *
    (x ^ j * (s ^ (m - j + 1) / ((m - j + 1 : ℕ) : ℝ))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem potA_eq_coef (n : ℕ) (p : ℕ → ℝ) (lo hi x : ℝ) :
    potA n p lo hi x = ∑ j ∈ range n, potAc n p lo hi j * x ^ j := by
  unfold potA potAc
  rw [potK_eq_coef, potK_eq_coef, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### B. Complex logarithms: from `log (1 - x z)` to `log (x - p)` -/

/-- `(r log (a b)).re` splits for a real weight `r`. -/
theorem re_mul_log_mul_of_real {a b r : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : r.im = 0) :
    (r * Complex.log (a * b)).re = (r * Complex.log a).re + (r * Complex.log b).re := by
  simp only [Complex.mul_re, hr, zero_mul, sub_zero, Complex.log_re, norm_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)]
  ring

/-- `log (a b) = log a + log b` when `a` and `b` lie in opposite open half planes. -/
theorem log_mul_of_im_opp {a b : ℂ}
    (h : (0 < a.im ∧ b.im < 0) ∨ (a.im < 0 ∧ 0 < b.im)) :
    Complex.log (a * b) = Complex.log a + Complex.log b := by
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hb : b ≠ 0 := by rintro rfl; simp at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 := Complex.arg_nonneg_iff.mpr h1.le
    have a2 := Complex.arg_le_pi a
    have b1 := Complex.arg_neg_iff.mpr h2
    have b2 := Complex.neg_pi_lt_arg b
    exact Complex.log_mul ha hb ⟨by linarith, by linarith⟩
  · have a1 := Complex.arg_neg_iff.mpr h1
    have a2 := Complex.neg_pi_lt_arg a
    have b1 := Complex.arg_nonneg_iff.mpr h2.le
    have b2 := Complex.arg_le_pi b
    exact Complex.log_mul ha hb ⟨by linarith, by linarith⟩

/-- Branch-free splitting of `(r log (a b)).re`: real weight, or opposite half planes. -/
theorem re_mul_log_mul {a b r : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : r.im = 0 ∨ ((0 < a.im ∧ b.im < 0) ∨ (a.im < 0 ∧ 0 < b.im))) :
    (r * Complex.log (a * b)).re = (r * Complex.log a).re + (r * Complex.log b).re := by
  rcases h with h | h
  · exact re_mul_log_mul_of_real ha hb h
  · rw [log_mul_of_im_opp h, mul_add, Complex.add_re]

theorem one_sub_mul_ne_zero {x : ℝ} {z : ℂ} (hx : |x| ≤ 1) (hz : ‖z‖ < 1) :
    (1 : ℂ) - (x : ℂ) * z ≠ 0 := by
  intro h
  have h1 : (x : ℂ) * z = 1 := by linear_combination -h
  have : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_le_of_lt (by nlinarith [norm_nonneg z]) hz
  rw [h1] at this
  simp at this

/-- `1 - x z = (-z) (x - z⁻¹)`. -/
theorem one_sub_mul_eq {x : ℝ} {z : ℂ} (hz : z ≠ 0) :
    (1 : ℂ) - (x : ℂ) * z = (-z) * ((x : ℂ) - z⁻¹) := by
  field_simp
  ring

/-- **S-pole conversion.**  For `‖z‖ < 1`, `|x| ≤ 1` and `z` non-real or `r` real:
`Re[r log (1 - x z)] = Re[r log (x - 1/z)] + Re[r log (-z)]`. -/
theorem re_log_one_sub {x : ℝ} {z r : ℂ} (hx : |x| ≤ 1) (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hzr : z.im ≠ 0 ∨ r.im = 0) :
    (r * Complex.log (1 - (x : ℂ) * z)).re =
      (r * Complex.log ((x : ℂ) - z⁻¹)).re + (r * Complex.log (-z)).re := by
  have hne := one_sub_mul_ne_zero hx hz
  rw [one_sub_mul_eq hz0] at hne ⊢
  have hb : (x : ℂ) - z⁻¹ ≠ 0 := right_ne_zero_of_mul hne
  have ha : -z ≠ 0 := neg_ne_zero.mpr hz0
  have key : (r * Complex.log (((x : ℂ) - z⁻¹) * (-z))).re =
      (r * Complex.log ((x : ℂ) - z⁻¹)).re + (r * Complex.log (-z)).re := by
    apply re_mul_log_mul hb ha
    rcases hzr with h | h
    · right
      have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
      have e1 : (-z).im = -z.im := by simp
      have e2 : ((x : ℂ) - z⁻¹).im = z.im / Complex.normSq z := by
        simp [Complex.inv_im, neg_div]
      rw [e1, e2]
      rcases lt_or_gt_of_ne h with h | h
      · right; exact ⟨div_neg_of_neg_of_pos h hns, by linarith⟩
      · left; exact ⟨div_pos h hns, by linarith⟩
    · left; exact h
  rw [mul_comm (-z), key]

/-- The pole `(1 + z²)/(2z)` of the Chebyshev log `log (1 - 2 x z + z²)`. -/
def tPole (z : ℂ) : ℂ := (1 + z ^ 2) / (2 * z)

theorem tPole_eq {z : ℂ} (hz : z ≠ 0) : tPole z = (z + z⁻¹) / 2 := by
  unfold tPole; field_simp; ring

theorem quad_ne_zero {x : ℝ} {z : ℂ} (hx : |x| ≤ 1) (hz : ‖z‖ < 1) :
    (1 : ℂ) - 2 * (x : ℂ) * z + z ^ 2 ≠ 0 := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hnormA : ‖z * OAI.InternalCatalan.realEnergyCirclePoint x‖ < 1 := by
    simpa only [Complex.norm_mul, OAI.InternalCatalan.realEnergyCirclePoint_norm hx',
      mul_one] using hz
  have hnormB : ‖z * (starRingEnd ℂ) (OAI.InternalCatalan.realEnergyCirclePoint x)‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_conj,
      OAI.InternalCatalan.realEnergyCirclePoint_norm hx', mul_one] using hz
  have hfactor :
      (1 - z * OAI.InternalCatalan.realEnergyCirclePoint x) *
        (1 - z * (starRingEnd ℂ) (OAI.InternalCatalan.realEnergyCirclePoint x)) =
        1 - 2 * (x : ℂ) * z + z ^ 2 := by
    calc
      _ = 1 - z * (OAI.InternalCatalan.realEnergyCirclePoint x +
            (starRingEnd ℂ) (OAI.InternalCatalan.realEnergyCirclePoint x)) +
          z ^ 2 * (OAI.InternalCatalan.realEnergyCirclePoint x *
            (starRingEnd ℂ) (OAI.InternalCatalan.realEnergyCirclePoint x)) := by ring
      _ = _ := by
        rw [OAI.InternalCatalan.realEnergyCirclePoint_add_conj,
          OAI.InternalCatalan.realEnergyCirclePoint_mul_conj hx']
        ring
  rw [← hfactor]
  have h1 : (1 : ℂ) - z * OAI.InternalCatalan.realEnergyCirclePoint x ≠ 0 := by
    intro h
    have : z * OAI.InternalCatalan.realEnergyCirclePoint x = 1 := by linear_combination -h
    rw [this] at hnormA; simp at hnormA
  have h2 : (1 : ℂ) - z * (starRingEnd ℂ) (OAI.InternalCatalan.realEnergyCirclePoint x) ≠ 0 := by
    intro h
    have : z * (starRingEnd ℂ) (OAI.InternalCatalan.realEnergyCirclePoint x) = 1 := by
      linear_combination -h
    rw [this] at hnormB; simp at hnormB
  exact mul_ne_zero h1 h2

theorem quad_eq {x : ℝ} {z : ℂ} (hz : z ≠ 0) :
    (1 : ℂ) - 2 * (x : ℂ) * z + z ^ 2 = (-2 * z) * ((x : ℂ) - tPole z) := by
  unfold tPole; field_simp; ring

/-- **T-pole conversion.**  `Re[r log (1 - 2 x z + z²)] = Re[r log (x - p)] + Re[r log (-2z)]`,
`p = (1 + z²)/(2z)`. -/
theorem re_log_quad {x : ℝ} {z r : ℂ} (hx : |x| ≤ 1) (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hzr : z.im ≠ 0 ∨ r.im = 0) :
    (r * Complex.log (1 - 2 * (x : ℂ) * z + z ^ 2)).re =
      (r * Complex.log ((x : ℂ) - tPole z)).re + (r * Complex.log (-2 * z)).re := by
  have hne := quad_ne_zero hx hz
  rw [quad_eq hz0] at hne ⊢
  have hb : (x : ℂ) - tPole z ≠ 0 := right_ne_zero_of_mul hne
  have ha : -2 * z ≠ 0 := left_ne_zero_of_mul hne
  have key : (r * Complex.log (((x : ℂ) - tPole z) * (-2 * z))).re =
      (r * Complex.log ((x : ℂ) - tPole z)).re + (r * Complex.log (-2 * z)).re := by
    apply re_mul_log_mul hb ha
    rcases hzr with h | h
    · right
      have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
      have hns1 : Complex.normSq z < 1 := by
        have : ‖z‖ ^ 2 = Complex.normSq z := by
          rw [Complex.sq_norm]
        nlinarith [norm_nonneg z]
      have e1 : (-2 * z).im = -2 * z.im := by simp
      have e2 : ((x : ℂ) - tPole z).im = z.im * (1 - Complex.normSq z) / (2 * Complex.normSq z) := by
        rw [tPole_eq hz0]
        simp [Complex.inv_im]
        field_simp
        ring
      rw [e1, e2]
      have hpos : 0 < (1 - Complex.normSq z) / (2 * Complex.normSq z) := by
        apply div_pos (by linarith) (by positivity)
      have e3 : z.im * (1 - Complex.normSq z) / (2 * Complex.normSq z) =
          z.im * ((1 - Complex.normSq z) / (2 * Complex.normSq z)) := by ring
      rw [e3]
      rcases lt_or_gt_of_ne h with h | h
      · right; exact ⟨mul_neg_of_neg_of_pos h hpos, by linarith⟩
      · left; exact ⟨mul_pos h hpos, by linarith⟩
    · left; exact h
  rw [mul_comm (-2 * z), key]

/-! ### C. Sequences: finite part plus geometric tail -/

/-- A tail: entries `(z, r)`, contributing `Re(r z^k)` to the `k`-th term. -/
abbrev Tail := List (ℂ × ℂ)

/-- The sequence `k ↦ f k + Σ Re(r z^k)` (`0` at `k = 0`); `barrierTrial cs tail` is the case
`f = barrierFiniteCoeff cs`. -/
def tseq (f : ℕ → ℝ) (tail : Tail) (k : ℕ) : ℝ :=
  if k = 0 then 0 else f k + (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re

/-- Admissible tails: `‖z‖ < 1`, `z ≠ 0`, and the weight real unless the pole is non-real. -/
def TailOK (tail : Tail) : Prop :=
  ∀ zr ∈ tail, ‖zr.1‖ < 1 ∧ zr.1 ≠ 0 ∧ (zr.1.im ≠ 0 ∨ zr.2.im = 0)

/-- One pole term `Re[ρ log (x - p)]` of the closed forms. -/
def poleLog (ρ p : ℂ) (x : ℝ) : ℝ := (ρ * Complex.log ((x : ℂ) - p)).re

/-- A pole sum `Σ_q Re[ρ_q log (x - p_q)]`, `q = (ρ, p)`. -/
def poleSum (L : List (ℂ × ℂ)) (x : ℝ) : ℝ := (L.map (fun q => poleLog q.1 q.2 x)).sum

/-- S-poles: the tail `(z, r)` of `Σ_k Re(r z^k) x^k/k` gives `ρ = -r`, `p = 1/z`. -/
def sPoles (tail : Tail) : List (ℂ × ℂ) := tail.map (fun zr => (-zr.2, zr.1⁻¹))

/-- The additive constant of the S-closed form: `-Σ Re[r log (-z)]`. -/
def sConst (tail : Tail) : ℝ := -(tail.map (fun zr : ℂ × ℂ => (zr.2 * Complex.log (-zr.1)).re)).sum

/-- T-poles: `ρ = -r/2`, `p = (1 + z²)/(2z)`. -/
def tPoles (tail : Tail) : List (ℂ × ℂ) := tail.map (fun zr => (-zr.2 / 2, tPole zr.1))

/-- The additive constant of the T-closed form: `-(1/2) Σ Re[r log (-2z)]`. -/
def tConst (tail : Tail) : ℝ :=
  -(tail.map (fun zr : ℂ × ℂ => (zr.2 * Complex.log (-2 * zr.1)).re)).sum / 2

theorem list_sum_re {α : Type*} (l : List α) (g : α → ℂ) :
    (l.map g).sum.re = (l.map (fun a => (g a).re)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem tailS_conv {tail : Tail} (hT : TailOK tail) {x : ℝ} (hx : |x| ≤ 1) :
    -(tail.map (fun zr : ℂ × ℂ => zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re =
      poleSum (sPoles tail) x + sConst tail := by
  induction tail with
  | nil => simp [poleSum, sPoles, sConst]
  | cons zr tail ih =>
    have h0 := hT zr List.mem_cons_self
    have ih' := ih (fun w hw => hT w (List.mem_cons_of_mem _ hw))
    have hh := re_log_one_sub (r := zr.2) hx h0.1 h0.2.1 h0.2.2
    simp only [poleSum, sPoles, sConst, List.map_cons, List.sum_cons, Complex.add_re,
      poleLog] at ih' ⊢
    rw [neg_add, ih']
    rw [hh]
    simp only [neg_mul, Complex.neg_re]
    ring

theorem tailT_conv {tail : Tail} (hT : TailOK tail) {x : ℝ} (hx : |x| ≤ 1) :
    -(tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2 =
      poleSum (tPoles tail) x + tConst tail := by
  induction tail with
  | nil => simp [poleSum, tPoles, tConst]
  | cons zr tail ih =>
    have h0 := hT zr List.mem_cons_self
    have ih' := ih (fun w hw => hT w (List.mem_cons_of_mem _ hw))
    have hh := re_log_quad (r := zr.2) hx h0.1 h0.2.1 h0.2.2
    simp only [poleSum, tPoles, tConst, List.map_cons, List.sum_cons, Complex.add_re,
      poleLog] at ih' ⊢
    have e : (-zr.2 / 2 * Complex.log ((x : ℂ) - tPole zr.1)).re =
        -(zr.2 * Complex.log ((x : ℂ) - tPole zr.1)).re / 2 := by
      have : -zr.2 / 2 * Complex.log ((x : ℂ) - tPole zr.1) =
          ((-1 / 2 : ℝ) : ℂ) * (zr.2 * Complex.log ((x : ℂ) - tPole zr.1)) := by
        push_cast; ring
      rw [this, Complex.re_ofReal_mul]; ring
    rw [e]
    linarith [ih', hh]

/-- The finite part of the S series. -/
def finS (f : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range L, f (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

/-- The finite part of the T series. -/
def finT (f : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range L, f (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
    ((k + 1 : ℕ) : ℝ)

/-- **S closed form.**  For `f` supported on `1..L` and an admissible tail, on `|x| ≤ 1`:
`barrierTrialS (tseq f tail) x = finS f L x + Σ_q Re[ρ_q log (x - p_q)] + c`. -/
theorem barrierTrialS_tseq {f : ℕ → ℝ} {L : ℕ} (hf : ∀ k, L < k → f k = 0) {tail : Tail}
    (hT : TailOK tail) {x : ℝ} (hx : |x| ≤ 1) :
    OAI.InternalCatalan.barrierTrialS (tseq f tail) x =
      finS f L x + poleSum (sPoles tail) x + sConst tail := by
  have h1 : HasSum (fun k : ℕ => f (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (finS f L x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : L ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [hf (k + 1) (by omega)]
    simp
  have h2 := OAI.InternalCatalan.barrierTail_S_hasSum tail (fun zr hzr => (hT zr hzr).1) hx
  have h3 := h1.add h2
  have h4 : HasSum (fun k : ℕ => tseq f tail (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (finS f L x + poleSum (sPoles tail) x + sConst tail) := by
    rw [add_assoc, ← tailS_conv hT hx]
    convert h3 using 1
    funext k; simp only [tseq, Nat.succ_ne_zero, ite_false]; ring
  exact h4.tsum_eq

/-- **T closed form** (Chebyshev). -/
theorem barrierTrialT_tseq {f : ℕ → ℝ} {L : ℕ} (hf : ∀ k, L < k → f k = 0) {tail : Tail}
    (hT : TailOK tail) {x : ℝ} (hx : |x| ≤ 1) :
    OAI.InternalCatalan.barrierTrialT (tseq f tail) x =
      finT f L x + poleSum (tPoles tail) x + tConst tail := by
  have h1 : HasSum (fun k : ℕ => f (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) (finT f L x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : L ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [hf (k + 1) (by omega)]
    simp
  have h2 := OAI.InternalCatalan.barrierTail_T_hasSum tail (fun zr hzr => (hT zr hzr).1) hx
  have h3 := h1.add h2
  have h4 : HasSum (fun k : ℕ => tseq f tail (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (finT f L x + poleSum (tPoles tail) x + tConst tail) := by
    rw [add_assoc, ← tailT_conv hT hx]
    convert h3 using 1
    funext k; simp only [tseq, Nat.succ_ne_zero, ite_false]; ring
  exact h4.tsum_eq

/-! ### D. Geometric sequences and the dilated series `fld` -/

/-- The sequence `n ↦ Σ Re(ρ w^{n+1})` for `G = [(w, ρ), …]` (R, t of the trials). -/
def gseq (G : Tail) (n : ℕ) : ℝ := (G.map (fun wr : ℂ × ℂ => wr.2 * wr.1 ^ (n + 1))).sum.re

/-- `(w, ρ) ↦ (τ w, ρ)`. -/
def scaleTail (τ : ℝ) (G : Tail) : Tail := G.map (fun wr => ((τ : ℂ) * wr.1, wr.2))

theorem scaleTail_sum (τ : ℝ) (G : Tail) (k : ℕ) :
    ((scaleTail τ G).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re =
      τ ^ (k + 1) * gseq G k := by
  induction G with
  | nil => simp [scaleTail, gseq]
  | cons wr G ih =>
    simp only [scaleTail, gseq, List.map_cons, List.sum_cons, Complex.add_re] at ih ⊢
    rw [ih]
    have : wr.2 * ((τ : ℂ) * wr.1) ^ (k + 1) =
        ((τ ^ (k + 1) : ℝ) : ℂ) * (wr.2 * wr.1 ^ (k + 1)) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]; ring

theorem scaleTail_ok {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {G : Tail}
    (hG : ∀ wr ∈ G, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) :
    TailOK (scaleTail τ G) := by
  intro zr hzr
  simp only [scaleTail, List.mem_map] at hzr
  obtain ⟨wr, hwr, rfl⟩ := hzr
  obtain ⟨h1, h2, h3⟩ := hG wr hwr
  refine ⟨?_, ?_, ?_⟩
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ.1]
    nlinarith [hτ.1, hτ.2]
  · exact mul_ne_zero (by exact_mod_cast hτ.1.ne') h2
  · rcases h3 with h | h
    · left; simpa [Complex.mul_im, hτ.1.ne'] using h
    · right; exact h

/-- **Closed form of the dilated series of a geometric sequence**:
`fld τ (gseq G) x = Σ Re[ρ_q log (x - p_q)] + c`, poles `1/(τ w)`. -/
theorem fld_gseq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {G : Tail}
    (hG : ∀ wr ∈ G, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) {x : ℝ}
    (hx : |x| ≤ 1) :
    fld τ (gseq G) x = poleSum (sPoles (scaleTail τ G)) x + sConst (scaleTail τ G) := by
  have hT := scaleTail_ok hτ hG
  have h2 := OAI.InternalCatalan.barrierTail_S_hasSum (scaleTail τ G)
    (fun zr hzr => (hT zr hzr).1) hx
  rw [tailS_conv hT hx] at h2
  have h3 : HasSum (fun n : ℕ => (τ * x) ^ (n + 1) * gseq G n / ((n : ℝ) + 1))
      (poleSum (sPoles (scaleTail τ G)) x + sConst (scaleTail τ G)) := by
    convert h2 using 1
    funext n
    rw [scaleTail_sum]
    push_cast
    ring
  exact h3.tsum_eq

/-! ### E. Polynomial-density measures -/

/-- A polynomial piece of density: `∑_{m<n} p_m t^m` on `(lo, hi]`. -/
structure Piece where
  lo : ℝ
  hi : ℝ
  n : ℕ
  p : ℕ → ℝ

/-- The density of a piece. -/
def Piece.dens (q : Piece) (y : ℝ) : ℝ := pc q.n q.p y

/-- The measure of one piece. -/
def Piece.meas (q : Piece) : Measure ℝ :=
  (volume.restrict (Ioc q.lo q.hi)).withDensity (fun y => ENNReal.ofReal (q.dens y))

/-- The measure `Σ` of its pieces. -/
def polyMeas (qs : List Piece) : Measure ℝ := (qs.map Piece.meas).sum

/-- A piece is admissible when `lo ≤ hi` and its density is nonnegative on `[lo, hi]`. -/
def PieceOK (q : Piece) : Prop := q.lo ≤ q.hi ∧ ∀ y ∈ Icc q.lo q.hi, 0 ≤ q.dens y

theorem continuous_dens (q : Piece) : Continuous q.dens := continuous_pc q.n q.p

theorem integrable_piece {q : Piece} (hq : PieceOK q) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc q.lo q.hi)) :
    Integrable g q.meas ∧ ∫ y, g y ∂q.meas = ∫ t in q.lo..q.hi, q.dens t * g t := by
  have hmeas : Measurable fun y => ENNReal.ofReal (q.dens y) :=
    (continuous_dens q).measurable.ennreal_ofReal
  have hlt : ∀ᵐ y ∂(volume.restrict (Ioc q.lo q.hi)), ENNReal.ofReal (q.dens y) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hae : ∀ᵐ y ∂(volume.restrict (Ioc q.lo q.hi)),
      (ENNReal.ofReal (q.dens y)).toReal • g y = q.dens y * g y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [ENNReal.toReal_ofReal (hq.2 y ⟨hy.1.le, hy.2⟩), smul_eq_mul]
  have hint : IntegrableOn (fun y => q.dens y * g y) (Ioc q.lo q.hi) :=
    ((IntegrableOn.continuousOn_mul (continuous_dens q).continuousOn hg isCompact_Icc).mono_set
      Ioc_subset_Icc_self)
  unfold Piece.meas
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hmeas hlt]
    exact hint.congr_fun_ae (Filter.EventuallyEq.symm hae)
  · rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt,
      intervalIntegral.integral_of_le hq.1]
    exact integral_congr_ae hae

theorem integrable_polyMeas {qs : List Piece} {g : ℝ → ℝ}
    (h : ∀ q ∈ qs, PieceOK q ∧ IntegrableOn g (Icc q.lo q.hi)) :
    Integrable g (polyMeas qs) ∧
      ∫ y, g y ∂(polyMeas qs) = (qs.map (fun q => ∫ t in q.lo..q.hi, q.dens t * g t)).sum := by
  induction qs with
  | nil => simp [polyMeas]
  | cons q qs ih =>
    have h1 := h q List.mem_cons_self
    have h2 := ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have e : polyMeas (q :: qs) = q.meas + polyMeas qs := by
      simp [polyMeas]
    have hp := integrable_piece h1.1 h1.2
    rw [e]
    refine ⟨hp.1.add_measure h2.1, ?_⟩
    rw [integral_add_measure hp.1 h2.1, hp.2, h2.2]
    simp

theorem intervalIntegrable_log_abs_sub (w a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log |t - w|) volume a b := by
  have := (intervalIntegral.intervalIntegrable_log' (a := a - w) (b := b - w)).comp_sub_right w
  simpa [Real.log_abs] using this

theorem integrableOn_log_abs_sub (w : ℝ) {a b : ℝ} (h : a ≤ b) :
    IntegrableOn (fun t : ℝ => Real.log |t - w|) (Icc a b) := by
  have := (intervalIntegrable_iff_integrableOn_Icc_of_le h).mp
    (intervalIntegrable_log_abs_sub w a b)
  exact this

/-- The closed form of the log potential of a piece at `w`. -/
def Piece.pot (q : Piece) (w : ℝ) : ℝ :=
  potQ q.n q.p w q.hi * ((q.hi - w) * Real.log |q.hi - w|) +
    potQ q.n q.p w q.lo * ((w - q.lo) * Real.log |w - q.lo|) + potA q.n q.p q.lo q.hi w

/-- The closed form of the log potential `w ↦ ∫ log|y - w| dm(y)` of a piece list. -/
def logPot (qs : List Piece) (w : ℝ) : ℝ := (qs.map (fun q => q.pot w)).sum

/-- The mass `∫ dm` of a piece. -/
def Piece.mass (q : Piece) : ℝ := potG q.n q.p q.hi - potG q.n q.p q.lo

/-- The mass of a piece list. -/
def polyMass (qs : List Piece) : ℝ := (qs.map Piece.mass).sum

/-- **The log potential of a polynomial-density measure**:
`∫ log|y - w| dm(y) = Σ_pieces [A(w) + Qh(w) (hi - w) log|hi - w| + Ql(w) (w - lo) log|w - lo|]`. -/
theorem integral_log_polyMeas {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) (w : ℝ) :
    ∫ y, Real.log |y - w| ∂(polyMeas qs) = logPot qs w := by
  have h := integrable_polyMeas (g := fun y => Real.log |y - w|) (qs := qs)
    (fun q hq => ⟨hqs q hq, integrableOn_log_abs_sub w (hqs q hq).1⟩)
  rw [h.2]
  unfold logPot
  congr 1
  refine List.map_congr_left fun q hq => ?_
  have hq' := hqs q hq
  have := polyPot q.n q.p hq'.1 w
  simp only [Piece.dens, Piece.pot]
  rw [← this]

theorem integral_const_polyMeas {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) :
    ∫ _y, (1 : ℝ) ∂(polyMeas qs) = polyMass qs := by
  have h := integrable_polyMeas (g := fun _ => (1 : ℝ)) (qs := qs)
    (fun q hq => ⟨hqs q hq, integrableOn_const isCompact_Icc.measure_lt_top.ne⟩)
  rw [h.2]
  unfold polyMass
  congr 1
  refine List.map_congr_left fun q hq => ?_
  have hq' := hqs q hq
  simp only [mul_one, Piece.mass, Piece.dens]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_potG q.n q.p t)
    ((continuous_pc q.n q.p).intervalIntegrable _ _)

/-! ### F. Dilated reference series and reference rows -/

open CatalanMeasure.Signed.ReflectionEnergy in
theorem integrable_pow_of_BD {m : Measure ℝ} {C : ℝ} (h : BD m C) (τ : ℝ) (k : ℕ) :
    Integrable (fun y : ℝ => (τ * y) ^ k) m := by
  have := h.finite
  refine Integrable.of_bound (by fun_prop : Continuous fun y : ℝ => (τ * y) ^ k).aestronglyMeasurable
    (|τ| ^ k) ?_
  filter_upwards [h.ae_mem] with y hy
  rw [Real.norm_eq_abs, abs_pow, abs_mul]
  have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (abs_nonneg τ) hy1) k

open CatalanMeasure.Signed.ReflectionEnergy in
/-- **The dilated series of the moments of a bounded-density measure is a log potential**:
`Σ (τ x)^{n+1} ∫ (τ y)^{n+1} dm / (n+1) = -∫ log (1 - τ² x y) dm`. -/
theorem fld_refMoment {m : Measure ℝ} {C : ℝ} (hBD : BD m C) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    fld τ (fun n : ℕ => ∫ y, (τ * y) ^ (n + 1) ∂m) x = -∫ y, Real.log (1 - τ ^ 2 * x * y) ∂m := by
  have := hBD.finite
  set F : ℕ → ℝ → ℝ := fun n y => (τ ^ 2 * x * y) ^ (n + 1) / ((n : ℝ) + 1) with hF
  have hFeq : ∀ n, F n = fun y => ((τ * x) ^ (n + 1) / ((n : ℝ) + 1)) * (τ * y) ^ (n + 1) := by
    intro n; funext y; simp only [hF]; ring
  have hFint : ∀ n, Integrable (F n) m := by
    intro n
    rw [hFeq n]
    exact (integrable_pow_of_BD hBD τ (n + 1)).const_mul _
  have hτ2 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hbd : ∀ n, ∀ᵐ y ∂m, ‖F n y‖ ≤ (τ ^ 2) ^ (n + 1) := by
    intro n
    filter_upwards [hBD.ae_mem] with y hy
    have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have h1 : |τ ^ 2 * x * y| ≤ τ ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ ^ 2)]
      calc τ ^ 2 * |x| * |y| ≤ τ ^ 2 * 1 * 1 := by gcongr
        _ = τ ^ 2 := by ring
    simp only [hF]
    rw [Real.norm_eq_abs, abs_div, abs_pow]
    have hn : (1 : ℝ) ≤ |(n : ℝ) + 1| := by
      rw [abs_of_nonneg (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc |τ ^ 2 * x * y| ^ (n + 1) / |(n : ℝ) + 1| ≤ |τ ^ 2 * x * y| ^ (n + 1) / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos hn
      _ ≤ (τ ^ 2) ^ (n + 1) := by
          rw [div_one]; exact pow_le_pow_left₀ (abs_nonneg _) h1 _
  have hsum : Summable fun n => ∫ y, ‖F n y‖ ∂m := by
    have hg : Summable fun n : ℕ => (m.real univ * τ ^ 2) * (τ ^ 2) ^ n :=
      (summable_geometric_of_lt_one (by positivity) hτ2).mul_left _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_) hg
    calc ∫ y, ‖F n y‖ ∂m ≤ ∫ _y, (τ ^ 2) ^ (n + 1) ∂m :=
          integral_mono_ae (hFint n).norm (integrable_const _) (hbd n)
      _ = (m.real univ * τ ^ 2) * (τ ^ 2) ^ n := by
          rw [integral_const, smul_eq_mul]; ring
  have hHas := hasSum_integral_of_summable_integral_norm hFint hsum
  have hpt : ∀ᵐ y ∂m, ∑' n, F n y = -Real.log (1 - τ ^ 2 * x * y) := by
    filter_upwards [hBD.ae_mem] with y hy
    have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have h1 : |τ ^ 2 * x * y| < 1 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ ^ 2)]
      calc τ ^ 2 * |x| * |y| ≤ τ ^ 2 * 1 * 1 := by gcongr
        _ < 1 := by linarith
    exact (Real.hasSum_pow_div_log_of_abs_lt_one h1).tsum_eq
  have hint : ∫ y, ∑' n, F n y ∂m = -∫ y, Real.log (1 - τ ^ 2 * x * y) ∂m := by
    rw [integral_congr_ae hpt, integral_neg]
  rw [hint] at hHas
  have h3 : HasSum (fun n : ℕ => (τ * x) ^ (n + 1) * (∫ y, (τ * y) ^ (n + 1) ∂m) / ((n : ℝ) + 1))
      (-∫ y, Real.log (1 - τ ^ 2 * x * y) ∂m) := by
    convert hHas using 1
    funext n
    rw [hFeq n, integral_const_mul]
    ring
  exact h3.tsum_eq

theorem log_one_sub_eq {c t : ℝ} (hc : c ≠ 0) (ht : t ≠ c⁻¹) :
    Real.log (1 - c * t) = Real.log |c| + Real.log |t - c⁻¹| := by
  have h2 : 1 - c * t = (-c) * (t - c⁻¹) := by field_simp; ring
  rw [h2, Real.log_mul (neg_ne_zero.2 hc) (sub_ne_zero.2 ht), Real.log_neg_eq_log,
    Real.log_abs, Real.log_abs]

theorem piece_int_log_one_sub {q : Piece} (hq : PieceOK q) {c : ℝ} (hc : c ≠ 0) :
    ∫ t in q.lo..q.hi, q.dens t * Real.log (1 - c * t) =
      Real.log |c| * q.mass + q.pot c⁻¹ := by
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c⁻¹ := by
    rw [ae_iff]; simp
  have h1 : ∫ t in q.lo..q.hi, q.dens t * Real.log (1 - c * t) =
      ∫ t in q.lo..q.hi, (q.dens t * Real.log |c| + q.dens t * Real.log |t - c⁻¹|) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht _
    rw [log_one_sub_eq hc ht]
    ring
  rw [h1, intervalIntegral.integral_add]
  · have h4 : ∫ t in q.lo..q.hi, q.dens t * Real.log |c| = Real.log |c| * q.mass := by
      rw [intervalIntegral.integral_mul_const]
      have : ∫ t in q.lo..q.hi, q.dens t = q.mass :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_potG q.n q.p t)
          ((continuous_dens q).intervalIntegrable _ _)
      rw [this]; ring
    have h5 : ∫ t in q.lo..q.hi, q.dens t * Real.log |t - c⁻¹| = q.pot c⁻¹ := by
      have := polyPot q.n q.p hq.1 c⁻¹
      unfold Piece.pot Piece.dens
      exact this
    rw [h4, h5]
  · exact ((continuous_dens q).mul continuous_const).intervalIntegrable _ _
  · exact intervalIntegrable_mul_log_abs_sub (continuous_dens q) c⁻¹ _ _

theorem sum_map_affine (qs : List Piece) (a w : ℝ) :
    (qs.map (fun q => a * q.mass + q.pot w)).sum = a * polyMass qs + logPot qs w := by
  induction qs with
  | nil => simp [polyMass, logPot]
  | cons q qs ih =>
    simp only [polyMass, logPot, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

/-- **Log potential of a polynomial-density measure at a dilated point**:
`∫ log (1 - c y) dm = log|c| · m(ℝ) + Σ_pieces pot(1/c)`, `c ≠ 0`. -/
theorem integral_log_one_sub_polyMeas {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) {c : ℝ}
    (hc : c ≠ 0) :
    ∫ y, Real.log (1 - c * y) ∂(polyMeas qs) = Real.log |c| * polyMass qs + logPot qs c⁻¹ := by
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c⁻¹ := by
    rw [ae_iff]; simp
  have hi : ∀ q ∈ qs, PieceOK q ∧ IntegrableOn (fun y => Real.log (1 - c * y)) (Icc q.lo q.hi) := by
    intro q hq
    refine ⟨hqs q hq, ?_⟩
    have h0 : IntegrableOn (fun t => Real.log |c| + Real.log |t - c⁻¹|) (Icc q.lo q.hi) :=
      (integrableOn_const isCompact_Icc.measure_lt_top.ne).add
        (integrableOn_log_abs_sub c⁻¹ (hqs q hq).1)
    refine h0.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with t ht
    rw [log_one_sub_eq hc ht]
  have h := integrable_polyMeas (g := fun y => Real.log (1 - c * y)) hi
  rw [h.2]
  rw [← sum_map_affine qs (Real.log |c|) c⁻¹]
  congr 1
  exact List.map_congr_left fun q hq => piece_int_log_one_sub (hqs q hq) hc

open CatalanMeasure.Signed.ReflectionEnergy in
/-- The row field of one nonnegative species family (`rowRef μ = rowRefM μ.P - rowRefM μ.N`). -/
def rowRefM (μ : Bool → Measure ℝ) (x : ℝ) : ℝ := ∑ τ, ∫ y, Kt (decide (0 < x)) τ |x| y ∂(μ τ)

theorem rowRef_eq_M (μ : SRef) (x : ℝ) : rowRef μ x = rowRefM μ.P x - rowRefM μ.N x := by
  unfold rowRef rowRefM; rw [Finset.sum_sub_distrib]

open CatalanMeasure.Signed.ReflectionEnergy in
theorem rowRef_eq (μ : Bool → Measure ℝ) {x : ℝ} (hx : x ≠ 0) :
    rowRefM μ x = -(∫ y, Real.log |y - x| ∂(μ true)) - ∫ y, Real.log |y + x| ∂(μ false) := by
  have kff : ∀ a y : ℝ, Kt false false a y = -Real.log |a - y| := fun a y => by simp [Kt]
  have ktt : ∀ a y : ℝ, Kt true true a y = -Real.log |a - y| := fun a y => by simp [Kt]
  have kft : ∀ a y : ℝ, Kt false true a y = -Real.log (a + y) := fun a y => by simp [Kt]
  have ktf : ∀ a y : ℝ, Kt true false a y = -Real.log (a + y) := fun a y => by simp [Kt]
  unfold rowRefM
  rw [Fintype.sum_bool]
  rcases lt_or_gt_of_ne hx with h | h
  · have hs : decide (0 < x) = false := by simpa using h.le
    rw [hs]
    simp only [kff, kft, abs_of_neg h]
    have c1 : ∀ y : ℝ, Real.log |-x - y| = Real.log |y + x| := fun y => by
      rw [show -x - y = -(y + x) by ring, abs_neg]
    have c2 : ∀ y : ℝ, Real.log (-x + y) = Real.log |y - x| := fun y => by
      rw [← Real.log_abs, show -x + y = y - x by ring]
    simp only [c1, c2, integral_neg]
    ring
  · have hs : decide (0 < x) = true := by simpa using h
    rw [hs]
    simp only [ktt, ktf, abs_of_pos h]
    have c1 : ∀ y : ℝ, Real.log |x - y| = Real.log |y - x| := fun y => by rw [abs_sub_comm]
    have c2 : ∀ y : ℝ, Real.log (x + y) = Real.log |y + x| := fun y => by
      rw [← Real.log_abs, add_comm]
    simp only [c1, c2, integral_neg]
    ring

/-- **Closed form of the reference row** for polynomial-density species measures. -/
theorem rowRef_polyMeas (μ : Bool → Measure ℝ) {qsT qsF : List Piece}
    (hT : ∀ q ∈ qsT, PieceOK q) (hF : ∀ q ∈ qsF, PieceOK q) (hμT : μ true = polyMeas qsT)
    (hμF : μ false = polyMeas qsF) {x : ℝ} (hx : x ≠ 0) :
    rowRefM μ x = -logPot qsT x - logPot qsF (-x) := by
  rw [rowRef_eq μ hx, hμT, hμF, integral_log_polyMeas hT x]
  have : ∫ y, Real.log |y + x| ∂(polyMeas qsF) = ∫ y, Real.log |y - (-x)| ∂(polyMeas qsF) := by
    simp only [sub_neg_eq_add]
  rw [this, integral_log_polyMeas hF (-x)]

/-! ### G. The closed-form blocks -/

/-- A sequence given by a finite part (supported on `1..L`) and a geometric tail. -/
structure SeqForm where
  f : ℕ → ℝ
  L : ℕ
  tail : Tail

/-- S-closed form of a sequence form: polynomial + pole logs + constant. -/
def SeqForm.Sform (d : SeqForm) (x : ℝ) : ℝ :=
  finS d.f d.L x + poleSum (sPoles d.tail) x + sConst d.tail

/-- T-closed form (Chebyshev) of a sequence form. -/
def SeqForm.Tform (d : SeqForm) (x : ℝ) : ℝ :=
  finT d.f d.L x + poleSum (tPoles d.tail) x + tConst d.tail

/-- The reference row, `-V_T(x) - V_F(-x)`, as potentials of the species pieces. -/
def refRowForm (qT qF : List Piece) (x : ℝ) : ℝ := -logPot qT x - logPot qF (-x)

/-- The dilated potential `-∫ log (1 - c y) dm = -(log|c| m(ℝ) + V(1/c))`. -/
def dilPot (qs : List Piece) (c : ℝ) : ℝ := -(Real.log |c| * polyMass qs + logPot qs c⁻¹)

/-- The closed form of `fld τ (gseq G)`. -/
def geoForm (τ : ℝ) (G : Tail) (x : ℝ) : ℝ :=
  poleSum (sPoles (scaleTail τ G)) x + sConst (scaleTail τ G)

/-- The closed form of `fld τ R` for `R n = tseq d.f d.tail (n + 1)` (finite moments plus a
geometric tail). -/
def rForm (τ : ℝ) (d : SeqForm) (x : ℝ) : ℝ := finS d.f d.L (τ * x) + geoForm τ d.tail x

/-- A finitely supported sequence is geometric. -/
theorem isGeom_fin {τ : ℝ} (hτ : 0 < τ) {f : ℕ → ℝ} {L : ℕ} (hf : ∀ k, L < k → f k = 0) :
    IsGeom τ (fun n => f (n + 1)) := by
  refine ⟨∑ k ∈ Finset.range L, |f (k + 1)| / τ ^ (k + 1), fun n => ?_⟩
  by_cases hn : n < L
  · have h1 := Finset.single_le_sum (f := fun k => |f (k + 1)| / τ ^ (k + 1))
      (fun k _ => by positivity) (Finset.mem_range.mpr hn)
    have hp : 0 < τ ^ (n + 1) := by positivity
    calc |f (n + 1)| = (|f (n + 1)| / τ ^ (n + 1)) * τ ^ (n + 1) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hp.le
  · show |f (n + 1)| ≤ _
    rw [hf (n + 1) (by omega), abs_zero]
    exact mul_nonneg (Finset.sum_nonneg fun k _ => by positivity) (by positivity)

/-- The dilated series of a finitely supported sequence is the polynomial `finS` at `τ x`. -/
theorem fld_fin (τ : ℝ) {f : ℕ → ℝ} {L : ℕ} (hf : ∀ k, L < k → f k = 0) (x : ℝ) :
    fld τ (fun n => f (n + 1)) x = finS f L (τ * x) := by
  unfold fld finS
  rw [tsum_eq_sum (s := Finset.range L) (fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    simp only [hf (n + 1) (by omega)]; ring)]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- The dilation error of `finS`: `|finS (τx) - finS x| ≤ (Σ |f|) (1 - τ) |x|`. -/
theorem finS_dil_sub_le (f : ℕ → ℝ) (L : ℕ) {τ x : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hx : |x| ≤ 1) :
    |finS f L (τ * x) - finS f L x| ≤
      (∑ k ∈ Finset.range L, |f (k + 1)|) * ((1 - τ) * |x|) := by
  unfold finS
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hB : 1 - τ ^ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) * (1 - τ) := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ τ - 1 by linarith [hτ.1]) (k + 1)
    rw [show (1 : ℝ) + (τ - 1) = τ by ring] at this
    push_cast at this ⊢
    nlinarith
  have hτp : 0 ≤ 1 - τ ^ (k + 1) := by
    have := pow_le_one₀ (n := k + 1) hτ.1.le hτ.2.le; linarith
  have hpow : |x| ^ (k + 1) ≤ |x| := by
    calc |x| ^ (k + 1) = |x| * |x| ^ k := by ring
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hx) (abs_nonneg _)
      _ = |x| := mul_one _
  have e : f (k + 1) * (τ * x) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
      f (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) =
      -(f (k + 1) * x ^ (k + 1) * (1 - τ ^ (k + 1))) / ((k + 1 : ℕ) : ℝ) := by
    rw [mul_pow]; ring
  rw [e, abs_div, abs_neg, abs_of_pos hk, div_le_iff₀ hk, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg hτp]
  have h1 : |x| ^ (k + 1) * (1 - τ ^ (k + 1)) ≤ |x| * (((k + 1 : ℕ) : ℝ) * (1 - τ)) :=
    mul_le_mul hpow hB hτp (abs_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (f (k + 1)))
  nlinarith [h2]

theorem fld_add' {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c d : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) {x : ℝ} (hx : |x| ≤ 1) :
    fld τ (fun n => c n + d n) x = fld τ c x + fld τ d x := by
  have h := (hasSum_fld hτ hc hx).add (hasSum_fld hτ hd hx)
  unfold fld
  exact (tsum_congr fun n => by ring).trans h.tsum_eq

theorem fld_sub' {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c d : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) {x : ℝ} (hx : |x| ≤ 1) :
    fld τ (fun n => c n - d n) x = fld τ c x - fld τ d x := by
  have h := (hasSum_fld hτ hc hx).sub (hasSum_fld hτ hd hx)
  unfold fld
  exact (tsum_congr fun n => by ring).trans h.tsum_eq

theorem fld_const_mul' {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c : ℕ → ℝ} (hc : IsGeom τ c) (a : ℝ)
    {x : ℝ} (hx : |x| ≤ 1) :
    fld τ (fun n => a * c n) x = a * fld τ c x := by
  have h := (hasSum_fld hτ hc hx).mul_left a
  unfold fld
  exact (tsum_congr fun n => by ring).trans h.tsum_eq

/-- Species moments of one nonnegative family (`mpos μ = mposM μ.P - mposM μ.N`). -/
def mposM (μ : Bool → Measure ℝ) (τ : ℝ) (n : ℕ) : ℝ := ∫ y, (τ * y) ^ (n + 1) ∂(μ true)
def mnegM (μ : Bool → Measure ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  (-1) ^ (n + 1) * ∫ y, (τ * y) ^ (n + 1) ∂(μ false)

theorem mpos_eq_M (μ : SRef) (τ : ℝ) : mpos μ τ = fun n => mposM μ.P τ n - mposM μ.N τ n := rfl

theorem mneg_eq_M (μ : SRef) (τ : ℝ) : mneg μ τ = fun n => mnegM μ.P τ n - mnegM μ.N τ n := by
  funext n; unfold mneg mnegM; ring

open CatalanMeasure.Signed.ReflectionEnergy in
theorem isGeom_mnegM {μ : Bool → Measure ℝ} {C : ℝ} (h : BD (μ false) C) {τ : ℝ} (hτ : 0 < τ) :
    IsGeom τ (mnegM μ τ) := by
  obtain ⟨K, hK⟩ := isGeom_refMoment h hτ
  exact ⟨K, fun n => by
    unfold mnegM; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hK n⟩

open CatalanMeasure.Signed.ReflectionEnergy in
/-- `fld τ (mposM μ τ)` for a polynomial-density positive species. -/
theorem fld_mpos_poly {μ : Bool → Measure ℝ} {C : ℝ} (hBD : BD (μ true) C) {qs : List Piece}
    (hq : ∀ q ∈ qs, PieceOK q) (hμ : μ true = polyMeas qs) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    fld τ (mposM μ τ) x = dilPot qs (τ ^ 2 * x) := by
  have hc : τ ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 hτ.1.ne') hx0
  have := fld_refMoment hBD hτ hx
  unfold mposM
  rw [this, hμ, integral_log_one_sub_polyMeas hq hc]
  rfl

open CatalanMeasure.Signed.ReflectionEnergy in
/-- `fld τ (mneg μ τ)` for a polynomial-density negative species. -/
theorem fld_mneg_poly {μ : Bool → Measure ℝ} {C : ℝ} (hBD : BD (μ false) C) {qs : List Piece}
    (hq : ∀ q ∈ qs, PieceOK q) (hμ : μ false = polyMeas qs) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    fld τ (mnegM μ τ) x = dilPot qs (τ ^ 2 * (-x)) := by
  have hc : τ ^ 2 * (-x) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hτ.1.ne') (neg_ne_zero.mpr hx0)
  have hx' : |-x| ≤ 1 := by rwa [abs_neg]
  have h1 : fld τ (mnegM μ τ) x = fld τ (fun n : ℕ => ∫ y, (τ * y) ^ (n + 1) ∂(μ false)) (-x) := by
    unfold fld mnegM
    refine tsum_congr fun n => ?_
    have : (τ * x) ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) * ∫ y, (τ * y) ^ (n + 1) ∂(μ false)) =
        (τ * -x) ^ (n + 1) * ∫ y, (τ * y) ^ (n + 1) ∂(μ false) := by ring
    rw [this]
  rw [h1, fld_refMoment hBD hτ hx', hμ, integral_log_one_sub_polyMeas hq hc]
  rfl

/-- The trial data of a Lean-class instance: sequences with finite part and geometric tail
(`v` the pin trial, `a` the particle trial, `p` the row Chebyshev trial of the `η`-share), the
split parameter `η`, geometric reference sequences, polynomial-density species of `μ = c_r`. -/
structure TrialForm where
  v : SeqForm
  a : SeqForm
  p : SeqForm
  η : ℝ
  /-- The reference tilt `ρ` of the Λ term: finite moments plus a geometric tail (NOTES-ETA §5). -/
  R : SeqForm
  /-- The particle sup `Sup` (the `ℓ` of J2). -/
  Sup : ℝ
  qT : List Piece
  qF : List Piece
  /-- The pieces of the negative part `N` of the signed reference `P - N` (`P` has `qT`, `qF`). -/
  qTn : List Piece
  qFn : List Piece

/-- `D` is the instance described by `F`. -/
structure TrialForm.Spec (F : TrialForm) (D : SignedData) : Prop where
  hτ : D.τ ∈ Ioo (0 : ℝ) 1
  hv : D.v = tseq F.v.f F.v.tail
  hvf : ∀ k, F.v.L < k → F.v.f k = 0
  hvT : TailOK F.v.tail
  ha : D.a = tseq F.a.f F.a.tail
  haf : ∀ k, F.a.L < k → F.a.f k = 0
  haT : TailOK F.a.tail
  hp : D.p = tseq F.p.f F.p.tail
  hpf : ∀ k, F.p.L < k → F.p.f k = 0
  hpT : TailOK F.p.tail
  hη : D.η = F.η
  /-- The range of the split parameter (`ε = 1 - 2η ∈ (0, 1]`). -/
  hηI : F.η ∈ Ico (0 : ℝ) (1 / 2)
  hR : D.R = fun n => tseq F.R.f F.R.tail (n + 1)
  hRf : ∀ k, F.R.L < k → F.R.f k = 0
  hRok : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)
  /-- Geometric decay of the tail only (the finite part is automatic). -/
  hRgT : IsGeom D.τ (gseq F.R.tail)
  hSup : D.Sup = F.Sup
  ht : D.t = mneg D.μ D.τ
  hμT : D.μ.P true = polyMeas F.qT
  hμF : D.μ.P false = polyMeas F.qF
  hμTn : D.μ.N true = polyMeas F.qTn
  hμFn : D.μ.N false = polyMeas F.qFn
  pT : ∀ q ∈ F.qT, PieceOK q
  pF : ∀ q ∈ F.qF, PieceOK q
  pTn : ∀ q ∈ F.qTn, PieceOK q
  pFn : ∀ q ∈ F.qFn, PieceOK q
  /-- `N` lives on `(0, 1/8]` (its positive-species dilated potential is then uniformly Lipschitz). -/
  hTn : ∀ q ∈ F.qTn, q.hi ≤ 1 / 8
  bd : D.μ.OK D.Cb

/-- The reference row of the signed reference `P - N` in closed form. -/
def TrialForm.refRow (F : TrialForm) (x : ℝ) : ℝ := refRowForm F.qT F.qF x - refRowForm F.qTn F.qFn x
/-- The dilated potential of the positive species of `P - N`. -/
def TrialForm.dilT (F : TrialForm) (c : ℝ) : ℝ := dilPot F.qT c - dilPot F.qTn c
/-- The dilated potential of the negative species of `P - N`. -/
def TrialForm.dilF (F : TrialForm) (c : ℝ) : ℝ := dilPot F.qF c - dilPot F.qFn c

namespace TrialForm

variable {F : TrialForm} {D : SignedData}

/-- `barrierTrialS D.v` in closed form. -/
theorem S_v (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) :
    OAI.InternalCatalan.barrierTrialS D.v x = F.v.Sform x := by
  rw [h.hv]; exact barrierTrialS_tseq h.hvf h.hvT hx

/-- `barrierTrialS D.a` in closed form. -/
theorem S_a (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) :
    OAI.InternalCatalan.barrierTrialS D.a x = F.a.Sform x := by
  rw [h.ha]; exact barrierTrialS_tseq h.haf h.haT hx

/-- `barrierTrialT D.v` in closed form. -/
theorem T_v (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) :
    OAI.InternalCatalan.barrierTrialT D.v x = F.v.Tform x := by
  rw [h.hv]; exact barrierTrialT_tseq h.hvf h.hvT hx

/-- `barrierTrialT D.p` (the `η`-share tangent field `T_p`) in closed form. -/
theorem T_p (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) :
    OAI.InternalCatalan.barrierTrialT D.p x = F.p.Tform x := by
  rw [h.hp]; exact barrierTrialT_tseq h.hpf h.hpT hx

theorem R_eq (h : F.Spec D) : D.R = fun n => F.R.f (n + 1) + gseq F.R.tail n := by
  rw [h.hR]
  funext n
  simp only [tseq, Nat.succ_ne_zero, ite_false, gseq]

/-- The reference tilt is geometric (finite part plus geometric tail). -/
theorem Spec.hRg (h : F.Spec D) : IsGeom D.τ D.R := by
  rw [R_eq h]; exact (isGeom_fin h.hτ.1 h.hRf).add h.hRgT

theorem fld_R (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) :
    fld D.τ D.R x = rForm D.τ F.R x := by
  rw [R_eq h, fld_add' h.hτ (isGeom_fin h.hτ.1 h.hRf) h.hRgT hx, fld_fin _ h.hRf,
    fld_gseq h.hτ h.hRok hx]
  rfl

theorem rowRef_mu (h : F.Spec D) {x : ℝ} (hx : x ≠ 0) :
    rowRef D.μ x = F.refRow x := by
  unfold TrialForm.refRow refRowForm
  rw [rowRef_eq_M, rowRef_polyMeas D.μ.P h.pT h.pF h.hμT h.hμF hx,
    rowRef_polyMeas D.μ.N h.pTn h.pFn h.hμTn h.hμFn hx]

theorem isGeom_mneg' (h : F.Spec D) : IsGeom D.τ (mneg D.μ D.τ) :=
  isGeom_mneg h.bd h.hτ.1

theorem isGeom_mpos' (h : F.Spec D) : IsGeom D.τ (mpos D.μ D.τ) :=
  isGeom_mpos h.bd h.hτ.1

theorem isGeom_t (h : F.Spec D) : IsGeom D.τ D.t := by
  rw [h.ht]; exact isGeom_mneg' h

/-- **The arcsine cross constant vanishes** at the tilt `t = mneg μ`. -/
theorem phConst_eq_zero (h : F.Spec D) : D.phConst = 0 := by
  have e1 : (fun n => mneg D.μ D.τ n - D.t n) = fun _ => (0 : ℝ) := by
    funext n; rw [h.ht]; ring
  unfold SignedData.phConst
  rw [e1]
  simp [ip]

/-- With the certificate's tilt `t = mneg μ`: `fld τ t = dilPot qF (τ²(-x))`. -/
theorem fld_t (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    fld D.τ D.t x = F.dilF (D.τ ^ 2 * (-x)) := by
  unfold TrialForm.dilF
  rw [h.ht, mneg_eq_M, fld_sub' h.hτ (isGeom_mnegM (h.bd.hP false) h.hτ.1)
      (isGeom_mnegM (h.bd.hN false) h.hτ.1) hx,
    fld_mneg_poly (h.bd.hP false) h.pF h.hμF h.hτ hx hx0,
    fld_mneg_poly (h.bd.hN false) h.pFn h.hμFn h.hτ hx hx0]

/-- The negative-row tangent series in closed form: with `t = mneg μ` the species part cancels,
`fld τ (κ (mneg μ - t) - R) = - geo R`. -/
theorem fld_neg (h : F.Spec D) (κ : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    fld D.τ (fun n => κ * (mneg D.μ D.τ n - D.t n) - D.R n) x = -rForm D.τ F.R x := by
  have e : (fun n => κ * (mneg D.μ D.τ n - D.t n) - D.R n) = fun n => (-1 : ℝ) * D.R n := by
    funext n; rw [h.ht]; ring
  rw [e, fld_const_mul' h.hτ h.hRg (-1) hx, fld_R h hx]; ring

/-- The positive-row tangent series in closed form. -/
theorem fld_pos (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x =
      F.dilT (D.τ ^ 2 * x) + rForm D.τ F.R x := by
  unfold TrialForm.dilT
  rw [fld_add' h.hτ (isGeom_mpos' h) h.hRg hx, mpos_eq_M,
    fld_sub' (c := mposM D.μ.P D.τ) (d := mposM D.μ.N D.τ) h.hτ
      (isGeom_refMoment (h.bd.hP true) h.hτ.1) (isGeom_refMoment (h.bd.hN true) h.hτ.1) hx,
    fld_mpos_poly (h.bd.hP true) h.pT h.hμT h.hτ hx hx0,
    fld_mpos_poly (h.bd.hN true) h.pTn h.hμTn h.hτ hx hx0, fld_R h hx]

/-- The near-row tangent series in closed form (the arcsine block kept as the series). -/
theorem fld_near (h : F.Spec D) (β : ℝ) {x : ℝ} (hx : |x| ≤ 1) (hx0 : x ≠ 0) :
    fld D.τ (fun n => D.R n - D.t n + β / 2 * arcNeg D.τ n) x =
      rForm D.τ F.R x - F.dilF (D.τ ^ 2 * (-x)) +
        (1 / 2) * fld D.τ (fun n => β * arcNeg D.τ n) x := by
  have g1 : IsGeom D.τ (fun n => D.R n - D.t n) := h.hRg.sub (isGeom_t h)
  have g2 : IsGeom D.τ (fun n => β / 2 * arcNeg D.τ n) := (isGeom_arcNeg h.hτ).const_mul _
  rw [fld_add' h.hτ g1 g2 hx, fld_sub' h.hτ h.hRg (isGeom_t h) hx, fld_R h hx, fld_t h hx hx0,
    fld_const_mul' h.hτ (isGeom_arcNeg h.hτ) _ hx, fld_const_mul' h.hτ (isGeom_arcNeg h.hτ) _ hx]
  ring

end TrialForm

/-! ### H. The field identities -/

namespace TrialForm

variable {F : TrialForm} {D : SignedData}

theorem abs_neg_tau_le (h : F.Spec D) {x : ℝ} (hx : |x| ≤ 1) : |-D.τ * x| ≤ 1 := by
  have := h.hτ
  rw [abs_mul, abs_neg, abs_of_pos this.1]
  nlinarith [this.1, this.2, abs_nonneg x]

theorem abs_le_one_of_mem_Ioo {x a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hx : x ∈ Ioo a b) :
    |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **`fNeg` in closed form** (negative rows, `x ∈ (-1, 0)`). -/
theorem fNeg_closed (h : F.Spec D) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    D.fNeg x =
      D.Rf x - F.v.Sform x - Real.log (1 - x) / (2 * D.ν) +
        ((1 - F.η) / D.ν) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x -
        (1 / (2 * D.ν)) * Real.log (1 - (D.τ * x) * (D.τ * x)) - 2 * F.a.Sform (-D.τ * x) +
        (-rForm D.τ F.R x) := by
  have hx1 : |x| ≤ 1 := abs_le_one_of_mem_Ioo le_rfl (by norm_num) hx
  have hx0 : x ≠ 0 := hx.2.ne
  unfold SignedData.fNeg SignedData.rowBase
  rw [S_v h hx1, S_a h (abs_neg_tau_le h hx1), rowRef_mu h hx0, T_p h hx1, fld_neg h _ hx1, h.hη]

/-- **`fPos` in closed form** (positive rows, `x ∈ (0, 1)`). -/
theorem fPos_closed (h : F.Spec D) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fPos x =
      D.Rf x - F.v.Sform x - Real.log (1 - x) / (2 * D.ν) +
        ((1 - F.η) / D.ν) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
        2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (F.dilT (D.τ ^ 2 * x) + rForm D.τ F.R x) + 2 * F.Sup := by
  have hx1 : |x| ≤ 1 := abs_le_one_of_mem_Ioo (by norm_num) le_rfl hx
  have hx0 : x ≠ 0 := hx.1.ne'
  unfold SignedData.fPos SignedData.rowBase
  rw [S_v h hx1, S_a h (abs_neg_tau_le h hx1), rowRef_mu h hx0, T_p h hx1, fld_pos h hx1 hx0,
    h.hη, h.hSup]

/-- **`fPosS` in closed form**: `fPos` plus the spike cost. -/
theorem fPosS_closed (h : F.Spec D) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fPosS x =
      D.Rf x - F.v.Sform x - Real.log (1 - x) / (2 * D.ν) +
        ((1 - F.η) / D.ν) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
        2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (F.dilT (D.τ ^ 2 * x) + rForm D.τ F.R x) + 2 * F.Sup +
        D.cs * (if 1 - D.θ < x then 1 else 0) := by
  unfold SignedData.fPosS
  rw [fPos_closed h hx]

/-- **`fCol` in closed form** (columns, `s ∈ (0, 1)`): the column field of the problem plus the
Chebyshev closed form of the pin trial. -/
theorem fCol_closed (h : F.Spec D) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    D.fCol s = D.Cf s + 2 * F.v.Tform s - Real.log (1 - s) / D.ν := by
  have hs1 : |s| ≤ 1 := abs_le_one_of_mem_Ioo (by norm_num) le_rfl hs
  unfold SignedData.fCol
  rw [T_v h hs1]

/-- **`fNegM` in closed form** (first-kind fixed negative nodes). -/
theorem fNegM_closed (h : F.Spec D) (Rm : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    D.fNegM Rm x =
      Rm x + ((1 - F.η) / (4 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        (1 - F.η) * F.refRow x - 2 * F.η * F.p.Tform x -
        (1 / (2 * D.ν)) * Real.log (1 - (D.τ * x) * (D.τ * x)) - 2 * F.a.Sform (-D.τ * x) +
        (-rForm D.τ F.R x) := by
  have hx1 : |x| ≤ 1 := abs_le_one_of_mem_Ioo le_rfl (by norm_num) hx
  have hx0 : x ≠ 0 := hx.2.ne
  unfold SignedData.fNegM SignedData.rowBaseM
  rw [S_a h (abs_neg_tau_le h hx1), rowRef_mu h hx0, T_p h hx1, fld_neg h _ hx1, h.hη]

/-- **`fPosM` in closed form** (first-kind fixed positive nodes). -/
theorem fPosM_closed (h : F.Spec D) (Rm : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fPosM Rm x =
      Rm x + ((1 - F.η) / (4 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        (1 - F.η) * F.refRow x - 2 * F.η * F.p.Tform x +
        2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (F.dilT (D.τ ^ 2 * x) + rForm D.τ F.R x) + 2 * F.Sup := by
  have hx1 : |x| ≤ 1 := abs_le_one_of_mem_Ioo (by norm_num) le_rfl hx
  have hx0 : x ≠ 0 := hx.1.ne'
  unfold SignedData.fPosM SignedData.rowBaseM
  rw [S_a h (abs_neg_tau_le h hx1), rowRef_mu h hx0, T_p h hx1, fld_pos h hx1 hx0, h.hη, h.hSup]

/-- **`fPosMS`** (spike cost attached). -/
theorem fPosMS_closed (h : F.Spec D) (Rm : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fPosMS Rm x =
      Rm x + ((1 - F.η) / (4 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        (1 - F.η) * F.refRow x - 2 * F.η * F.p.Tform x +
        2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (F.dilT (D.τ ^ 2 * x) + rForm D.τ F.R x) + 2 * F.Sup +
        D.cs * (if 1 - D.θ < x then 1 else 0) := by
  unfold SignedData.fPosMS
  rw [fPosM_closed h Rm hx]

/-- **`fPosMR`** (spike cost and the Lemma R′ remainder `rc α (-log (1 - x²))`). -/
theorem fPosMR_closed (h : F.Spec D) (Rm : ℝ → ℝ) (rc α : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fPosMR Rm rc α x =
      Rm x + ((1 - F.η) / (4 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) -
        (1 - F.η) * F.refRow x - 2 * F.η * F.p.Tform x +
        2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (F.dilT (D.τ ^ 2 * x) + rForm D.τ F.R x) + 2 * F.Sup +
        D.cs * (if 1 - D.θ < x then 1 else 0) + rc * α * (-Real.log (1 - x ^ 2)) := by
  unfold SignedData.fPosMR
  rw [fPosMS_closed h Rm hx]

/-- **`fNearM` in closed form** (near-type nodes).  The arcsine block
`(1/2) fld τ (β arcNeg τ)` is the half-arcsine log potential; it is kept as the series. -/
theorem fNearM_closed (h : F.Spec D) (Rn : ℝ → ℝ) (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fNearM Rn α β x =
      Rn x + 2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (rForm D.τ F.R x - F.dilF (D.τ ^ 2 * (-x)) +
          (1 / 2) * fld D.τ (fun n => β * arcNeg D.τ n) x) +
        (α / 2) * Real.log (1 + x) +
        (β / (4 * (1 - F.η)) + 1 / (2 * D.ν)) * (-Real.log (1 - x ^ 2)) +
        ((1 - F.η) / (4 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2)) + Real.log (1 / D.τ ^ 2) +
        D.phConst + remC (1 - 2 * F.η) * β * ip (arcPos D.τ) (arcPos D.τ) +
        (F.η + α / 2) * Real.log 2 + 2 * F.Sup := by
  have hx1 : |x| ≤ 1 := abs_le_one_of_mem_Ioo (by norm_num) le_rfl hx
  have hx0 : x ≠ 0 := hx.1.ne'
  unfold SignedData.fNearM
  rw [S_a h (abs_neg_tau_le h hx1), fld_near h β hx1 hx0, h.hη, h.hSup]

end TrialForm

namespace TrialForm

variable {F : TrialForm} {D : SignedData}

/-- **`fNearMS`** (near-type nodes with the spike cost attached). -/
theorem fNearMS_closed (h : F.Spec D) (Rn : ℝ → ℝ) (α β : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fNearMS Rn α β x =
      Rn x + 2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (rForm D.τ F.R x - F.dilF (D.τ ^ 2 * (-x)) +
          (1 / 2) * fld D.τ (fun n => β * arcNeg D.τ n) x) +
        (α / 2) * Real.log (1 + x) +
        (β / (4 * (1 - F.η)) + 1 / (2 * D.ν)) * (-Real.log (1 - x ^ 2)) +
        ((1 - F.η) / (4 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2)) + Real.log (1 / D.τ ^ 2) +
        D.phConst + remC (1 - 2 * F.η) * β * ip (arcPos D.τ) (arcPos D.τ) +
        (F.η + α / 2) * Real.log 2 + 2 * F.Sup +
        D.cs * (if 1 - D.θ < x then 1 else 0) := by
  unfold SignedData.fNearMS
  rw [fNearM_closed h Rn α β hx]

end TrialForm

/-! ### I. Explicit polynomial coefficients and the bridge to the Taylor-cell checker -/

/-- `Piece.pot` with the explicit coefficient polynomials: with
`Qh = Σ_j potQc(hi)_j x^j`, `Ql = Σ_j potQc(lo)_j x^j`, `A = Σ_j potAc_j x^j`,
`pot = Qh (hi - w) log|hi - w| + Ql (w - lo) log|w - lo| + A`. -/
theorem Piece.pot_eq_coef (q : Piece) (w : ℝ) :
    q.pot w =
      (∑ j ∈ range q.n, potQc q.n q.p q.hi j * w ^ j) * ((q.hi - w) * Real.log |q.hi - w|) +
      (∑ j ∈ range q.n, potQc q.n q.p q.lo j * w ^ j) * ((w - q.lo) * Real.log |w - q.lo|) +
      ∑ j ∈ range q.n, potAc q.n q.p q.lo q.hi j * w ^ j := by
  unfold Piece.pot
  rw [potQ_eq_coef, potQ_eq_coef, potA_eq_coef]

/-- `denPoly` as a polynomial with explicit coefficients (`x^{i+1}` has coefficient
`2 (-1)^{i+1} b_{i+1}/(i+1)`). -/
theorem denPoly_eq_coef (b : ℕ → ℝ) (K : ℕ) (g : ℝ) :
    denPoly b K g = ∑ i ∈ range K, (2 * (-1) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ)) *
      g ^ (i + 1) := by
  unfold denPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]; ring

/-- The pole list in the format of the Taylor-cell checker (`PoleR`: rational data). -/
def poleC (q : CatalanMeasure.CellCert.PoleR) : ℂ × ℂ := (q.rho, q.pc)

theorem poleSum_poleC (ps : List CatalanMeasure.CellCert.PoleR) (x : ℝ) :
    poleSum (ps.map poleC) x =
      (ps.map (fun q => (q.rho * Complex.log ((x : ℂ) - q.pc)).re)).sum := by
  unfold poleSum poleLog poleC
  rw [List.map_map]
  rfl

/-! ### J. The arcsine block of the near field -/

/-- **The arcsine block as a log potential**:
`fld τ (arcNeg τ) x = -∫ 1[cos u ≤ 0] log (1 + τ² x |cos u|) d arcLaw(u)`, i.e.
`-(1/π) ∫_0^π 1[cos θ ≤ 0] log (1 + τ² x |cos θ|) dθ` (a half-arcsine potential, which is a
Clausen/dilogarithm-type function of `τ² x`, not a polynomial-times-log or pole term). -/
theorem fld_arcNeg_eq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {x : ℝ} (hx : |x| ≤ 1) :
    fld τ (arcNeg τ) x =
      ∫ u, (if decide (0 < Real.cos u) = false then
        -Real.log (1 + τ ^ 2 * x * |Real.cos u|) else 0) ∂arcLaw := by
  have := arcLaw_prob
  set F : ℕ → ℝ → ℝ := fun n u =>
    (τ * x) ^ (n + 1) * ((-1) ^ (n + 1) * arcH τ false n u) / ((n : ℝ) + 1) with hF
  have hFeq : ∀ n, F n = fun u => ((τ * x) ^ (n + 1) * (-1) ^ (n + 1) / ((n : ℝ) + 1)) *
      arcH τ false n u := by
    intro n; funext u; simp only [hF]; ring
  have hFint : ∀ n, Integrable (F n) arcLaw := by
    intro n
    rw [hFeq n]
    exact (integrable_arcH hτ false n).const_mul _
  have hτ2 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hbd : ∀ n, ∀ u, ‖F n u‖ ≤ (τ ^ 2) ^ (n + 1) := by
    intro n u
    simp only [hF]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
    have hn : (1 : ℝ) ≤ |(n : ℝ) + 1| := by
      rw [abs_of_nonneg (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h1 : |τ * x| ≤ τ := by
      rw [abs_mul, abs_of_pos hτ.1]; exact mul_le_of_le_one_right hτ.1.le hx
    have h2 := abs_arcH_le hτ false n u
    have h3 : |τ * x| ^ (n + 1) * |arcH τ false n u| ≤ (τ ^ 2) ^ (n + 1) := by
      calc |τ * x| ^ (n + 1) * |arcH τ false n u| ≤ τ ^ (n + 1) * τ ^ (n + 1) :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 _) h2 (abs_nonneg _) (pow_nonneg hτ.1.le _)
        _ = (τ ^ 2) ^ (n + 1) := by ring
    calc |τ * x| ^ (n + 1) * |arcH τ false n u| / |(n : ℝ) + 1|
        ≤ |τ * x| ^ (n + 1) * |arcH τ false n u| / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos hn
      _ ≤ (τ ^ 2) ^ (n + 1) := by rw [div_one]; exact h3
  have hsum : Summable fun n => ∫ u, ‖F n u‖ ∂arcLaw := by
    have hg : Summable fun n : ℕ => (τ ^ 2) * (τ ^ 2) ^ n :=
      (summable_geometric_of_lt_one (by positivity) hτ2).mul_left _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) (fun n => ?_) hg
    calc ∫ u, ‖F n u‖ ∂arcLaw ≤ ∫ _u, (τ ^ 2) ^ (n + 1) ∂arcLaw :=
          integral_mono (hFint n).norm (integrable_const _) (fun u => hbd n u)
      _ = (τ ^ 2) * (τ ^ 2) ^ n := by
          rw [integral_const]; simp [pow_succ]; ring
  have hHas := hasSum_integral_of_summable_integral_norm hFint hsum
  have hpt : ∀ u, ∑' n, F n u = (if decide (0 < Real.cos u) = false then
        -Real.log (1 + τ ^ 2 * x * |Real.cos u|) else 0) := by
    intro u
    by_cases hc : decide (0 < Real.cos u) = false
    · simp only [hc, ↓reduceIte]
      have h1 : |-(τ ^ 2 * x * |Real.cos u|)| < 1 := by
        rw [abs_neg, abs_mul, abs_mul, abs_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ τ ^ 2)]
        calc τ ^ 2 * |x| * |Real.cos u| ≤ τ ^ 2 * 1 * 1 := by
              gcongr; exact Real.abs_cos_le_one u
          _ < 1 := by linarith
      have := (Real.hasSum_pow_div_log_of_abs_lt_one h1).tsum_eq
      rw [show 1 - -(τ ^ 2 * x * |Real.cos u|) = 1 + τ ^ 2 * x * |Real.cos u| by ring] at this
      rw [← this]
      refine tsum_congr fun n => ?_
      simp only [hF, arcH, hc, ↓reduceIte]
      ring
    · rw [ite_cond_eq_false _ _ (eq_false hc)]
      have : ∀ n, F n u = 0 := by
        intro n
        simp only [hF]
        unfold arcH
        rw [if_neg hc]
        ring
      simp [this]
  have hint : ∫ u, ∑' n, F n u ∂arcLaw = ∫ u, (if decide (0 < Real.cos u) = false then
        -Real.log (1 + τ ^ 2 * x * |Real.cos u|) else 0) ∂arcLaw :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hint] at hHas
  have h3 : HasSum (fun n : ℕ => (τ * x) ^ (n + 1) * arcNeg τ n / ((n : ℝ) + 1))
      (∫ u, (if decide (0 < Real.cos u) = false then
        -Real.log (1 + τ ^ 2 * x * |Real.cos u|) else 0) ∂arcLaw) := by
    convert hHas using 1
    funext n
    unfold arcNeg
    rw [hFeq n, integral_const_mul]
    ring
  exact h3.tsum_eq

/-- On `x ≥ 0` the arcsine block is nonpositive. -/
theorem fld_arcNeg_nonpos {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fld τ (arcNeg τ) x ≤ 0 := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  rw [fld_arcNeg_eq hτ hx1]
  refine integral_nonpos fun u => ?_
  simp only [Pi.zero_apply]
  split_ifs
  · have : 0 ≤ Real.log (1 + τ ^ 2 * x * |Real.cos u|) :=
      Real.log_nonneg (by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg τ) hx.1) (abs_nonneg (Real.cos u))])
    linarith
  · exact le_rfl

/-- **The `L`-norm of the positive arcsine half is bounded uniformly in the dilation**:
`ip (arcPos τ) (arcPos τ) ≤ 2 log 2` (Jensen, `Σ c^{2k}/k = -log(1 - c²)` and
`∫ -log (1 - cos² θ) dθ/π = 2 log 2`).  It controls the phantom constant of the near field. -/
theorem ip_arcPos_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ip (arcPos τ) (arcPos τ) ≤ 2 * Real.log 2 := by
  haveI := arcLaw_prob
  have hcos1 : ∀ᵐ u ∂arcLaw, Real.cos u ∈ Ioo (-1 : ℝ) 1 := by
    have hsing : ∀ v : ℝ, ∀ᵐ u ∂arcLaw, u ≠ v := fun v => by
      rw [ae_iff]; simpa using denMeasure_singleton (fun _ => 0) 0 v
    have hmem : ∀ᵐ u ∂arcLaw, u ∈ Icc 0 Real.pi := ae_mem_Icc_denMeasure _ _
    filter_upwards [hmem, hsing 0, hsing Real.pi] with u h1 h2 h3
    have hlt0 : 0 < u := lt_of_le_of_ne h1.1 (Ne.symm h2)
    have hltπ : u < Real.pi := lt_of_le_of_ne h1.2 h3
    constructor
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi h1.1 le_rfl hltπ
      rwa [Real.cos_pi] at this
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl h1.2 hlt0
      rwa [Real.cos_zero] at this
  obtain ⟨i1, e1⟩ := arcLaw_log_cos_sub (c := 1) ⟨by norm_num, le_rfl⟩
  obtain ⟨i2, e2⟩ := arcLaw_log_cos_sub (c := -1) ⟨le_rfl, by norm_num⟩
  set g : ℝ → ℝ := fun u => -Real.log (Real.cos u - 1) - Real.log (Real.cos u - -1) with hg
  have hgi : Integrable g arcLaw := i1.neg.sub i2
  have hgI : ∫ u, g u ∂arcLaw = 2 * Real.log 2 := by
    have h := integral_sub i1.neg i2
    simp only [Pi.neg_apply, integral_neg, e1, e2] at h
    show ∫ u, (-Real.log (Real.cos u - 1) - Real.log (Real.cos u - -1)) ∂arcLaw = _
    rw [h]; ring
  have hmc : ∀ n : ℕ, Measurable (fun u : ℝ => (Real.cos u ^ 2) ^ (n + 1)) := fun n =>
    (Real.continuous_cos.measurable.pow_const 2).pow_const (n + 1)
  have hci : ∀ n : ℕ, Integrable (fun u : ℝ => (Real.cos u ^ 2) ^ (n + 1)) arcLaw := fun n =>
    Integrable.mono' (integrable_const 1) (hmc n).aestronglyMeasurable
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_one₀ (sq_nonneg _) (Real.cos_sq_le_one u))
  have hsq : ∀ n : ℕ, arcPos τ n * arcPos τ n ≤ ∫ u, (Real.cos u ^ 2) ^ (n + 1) ∂arcLaw := by
    intro n
    have hmA := measurable_arcH τ true n
    have hA2 : Integrable (fun u => arcH τ true n u ^ 2) arcLaw :=
      Integrable.mono' (integrable_const 1) (hmA.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs, abs_pow]
          have := (abs_arcH_le hτ true n u).trans (pow_le_one₀ hτ.1.le hτ.2.le)
          exact pow_le_one₀ (abs_nonneg _) this)
    have hj := sq_integral_le_integral_sq (integrable_arcH hτ true n) hA2
    have hpt : ∀ u, arcH τ true n u ^ 2 ≤ (Real.cos u ^ 2) ^ (n + 1) := by
      intro u
      unfold arcH
      split_ifs
      · calc ((τ * |Real.cos u|) ^ (n + 1)) ^ 2 = ((τ * |Real.cos u|) ^ 2) ^ (n + 1) := by ring
          _ ≤ (Real.cos u ^ 2) ^ (n + 1) := by
            apply pow_le_pow_left₀ (sq_nonneg _)
            rw [mul_pow, sq_abs]
            have : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
            nlinarith [sq_nonneg (Real.cos u)]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
    have h2 := integral_mono hA2 (hci n) hpt
    unfold arcPos
    nlinarith [hj, h2]
  have hpart : ∀ K : ℕ, ∑ n ∈ Finset.range K, arcPos τ n * arcPos τ n / ((n : ℝ) + 1) ≤
      2 * Real.log 2 := by
    intro K
    calc ∑ n ∈ Finset.range K, arcPos τ n * arcPos τ n / ((n : ℝ) + 1)
        ≤ ∑ n ∈ Finset.range K, (∫ u, (Real.cos u ^ 2) ^ (n + 1) ∂arcLaw) / ((n : ℝ) + 1) :=
          Finset.sum_le_sum fun n _ => div_le_div_of_nonneg_right (hsq n) (by positivity)
      _ = ∫ u, ∑ n ∈ Finset.range K, (Real.cos u ^ 2) ^ (n + 1) / ((n : ℝ) + 1) ∂arcLaw := by
          rw [integral_finset_sum _ fun n _ => (hci n).div_const _]
          exact Finset.sum_congr rfl fun n _ => (integral_div _ _).symm
      _ ≤ ∫ u, g u ∂arcLaw := by
          refine integral_mono_ae (integrable_finset_sum _ fun n _ => (hci n).div_const _) hgi ?_
          filter_upwards [hcos1] with u hu
          have hc2 : |Real.cos u ^ 2| < 1 := by
            rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hu.1, hu.2]
          have hs := Real.hasSum_pow_div_log_of_abs_lt_one hc2
          have hle := sum_le_hasSum (Finset.range K) (fun n _ => by
            have : 0 ≤ (Real.cos u ^ 2) ^ (n + 1) := by positivity
            positivity) hs
          have e : -Real.log (1 - Real.cos u ^ 2) = g u := by
            simp only [hg]
            have h1 : 0 < 1 - Real.cos u := by linarith [hu.2]
            have h2 : 0 < Real.cos u + 1 := by linarith [hu.1]
            rw [show 1 - Real.cos u ^ 2 = (1 - Real.cos u) * (Real.cos u + 1) by ring,
              Real.log_mul h1.ne' h2.ne', show Real.cos u - 1 = -(1 - Real.cos u) by ring,
              Real.log_neg_eq_log, show Real.cos u - -1 = Real.cos u + 1 by ring]
            ring
          rw [← e]
          exact hle
      _ = 2 * Real.log 2 := hgI
  have hnn : ∀ n : ℕ, 0 ≤ arcPos τ n * arcPos τ n / ((n : ℝ) + 1) := fun n =>
    div_nonneg (mul_self_nonneg _) (by positivity)
  exact Real.tsum_le_of_sum_range_le hnn hpart

/-! ### K. `Rf`, `Cf`: the problem's own free-row and column fields -/

section Physical

open CatalanMeasure.Parametric

/-- The limit (N-independent) coefficients of the physical free-row field. -/
def rfLim (P : Parameters) (x : ℝ) : ℝ :=
  ((P.b0 + P.q0 + 2 * P.g0 : ℕ) : ℝ) / P.n0 * Real.log |x| +
    2 * (P.h0 : ℝ) / P.n0 * Real.log (1 - x) -
    ((P.n0 + P.b0 + P.q0 + P.g0 + P.h0 : ℕ) : ℝ) / P.n0 * Real.log (1 + x ^ 2)

/-- The limit column field (the `m = 0` physical column field is exactly this, for all `N ≥ 1`). -/
def cfLim (P : Parameters) (s : ℝ) : ℝ :=
  (P.b0 : ℝ) / P.n0 * Real.log s + (P.q0 : ℝ) / P.n0 * Real.log (1 - s)

/-- **`Rf` is explicit**: `populationPhysicalFreeField P N = rfLim P + (2/n) log (1 + x²)`:
three logarithms with `N`-independent coefficients plus a vanishing `(2/n) log(1+x²)`. -/
theorem populationPhysicalFreeField_eq (P : Parameters) {N : ℕ} (hN : N ≠ 0) (hn0 : P.n0 ≠ 0)
    (x : ℝ) :
    populationPhysicalFreeField P N x = rfLim P x + 2 / (P.n N : ℝ) * Real.log (1 + x ^ 2) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hn0' : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast hn0
  unfold populationPhysicalFreeField paramPopulationRowField rfLim
  simp only [Parameters.A, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h]
  push_cast
  field_simp
  ring

theorem rf_err_le (P : Parameters) {N : ℕ} (hN : N ≠ 0) (hn0 : P.n0 ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    |populationPhysicalFreeField P N x - rfLim P x| ≤ 2 * Real.log 2 / (P.n N : ℝ) := by
  rw [populationPhysicalFreeField_eq P hN hn0, add_sub_cancel_left]
  have hn : (0 : ℝ) < P.n N := by
    have : 0 < P.n N := Nat.mul_pos (Nat.pos_of_ne_zero hn0) (Nat.pos_of_ne_zero hN)
    exact_mod_cast this
  have h1 : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
  have h2 : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by nlinarith [abs_le.mp hx, sq_abs x, abs_nonneg x])
  rw [abs_of_nonneg (by positivity)]
  calc 2 / (P.n N : ℝ) * Real.log (1 + x ^ 2) ≤ 2 / (P.n N : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * Real.log 2 / (P.n N : ℝ) := by ring

/-- **`Cf` is explicit**: the `m = 0` physical column field is `cfLim`, for every `N ≥ 1`. -/
theorem populationPhysicalColumnField_zero (P : Parameters) {N : ℕ} (hN : N ≠ 0) (hn0 : P.n0 ≠ 0)
    (s : ℝ) : populationPhysicalColumnField P N 0 s = cfLim P s := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hn0' : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast hn0
  unfold populationPhysicalColumnField cfLim
  simp only [Parameters.b, Parameters.q, Parameters.n]
  push_cast
  field_simp
  simp

end Physical

/-! ### L. The arcsine block is dropped by sign, as in the certificate (NOTES §17.2 step 4) -/

theorem fld_const_mul_arcNeg {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (β : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    fld τ (fun n => β * arcNeg τ n) x = β * fld τ (arcNeg τ) x :=
  fld_const_mul' hτ (isGeom_arcNeg hτ) β hx

/-- **`fNearM` without the arcsine block.**  The certificate's `f_near` has no arcsine term: the
cross with the arcsine compensation `-(τ/2) ∬ log(1+x|y|) dπ dω⁻` is dropped as `≤ 0`
(NOTES §17.2 step 4).  Exactly this inequality: for `β ≥ 0`, `x ∈ (0,1)`,
`fNearM ≤ (the closed form of fNearM_closed with the arcsine term removed)`. -/
theorem TrialForm.fNearM_le_noarc {F : TrialForm} {D : SignedData} (h : F.Spec D)
    (Rn : ℝ → ℝ) (α β : ℝ) (hβ : 0 ≤ β) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.fNearM Rn α β x ≤
      Rn x + 2 * F.a.Sform (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
        (rForm D.τ F.R x - F.dilF (D.τ ^ 2 * (-x))) +
        (α / 2) * Real.log (1 + x) +
        (β / (4 * (1 - F.η)) + 1 / (2 * D.ν)) * (-Real.log (1 - x ^ 2)) +
        ((1 - F.η) / (4 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2)) + Real.log (1 / D.τ ^ 2) +
        D.phConst + remC (1 - 2 * F.η) * β * ip (arcPos D.τ) (arcPos D.τ) +
        (F.η + α / 2) * Real.log 2 + 2 * F.Sup := by
  have hx1 : |x| ≤ 1 := abs_le_one_of_mem_Ioo (by norm_num) le_rfl hx
  rw [TrialForm.fNearM_closed h Rn α β hx, fld_const_mul_arcNeg h.hτ β hx1]
  have := fld_arcNeg_nonpos h.hτ ⟨hx.1.le, hx.2.le⟩
  nlinarith [mul_nonneg hβ (neg_nonneg.mpr this)]

/-! ### M. Uniform limit `N → ∞` on compact cells: block estimates -/

/-- Real log is Lipschitz with constant `1/δ` on `[δ, ∞)`. -/
theorem abs_log_sub_le {s s' δ : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) (hs' : δ ≤ s') :
    |Real.log s - Real.log s'| ≤ |s - s'| / δ := by
  have key : ∀ {a b : ℝ}, δ ≤ a → δ ≤ b → Real.log a - Real.log b ≤ |a - b| / δ := by
    intro a b ha hb
    have ha0 : 0 < a := lt_of_lt_of_le hδ ha
    have hb0 : 0 < b := lt_of_lt_of_le hδ hb
    have h1 : Real.log a - Real.log b = Real.log (a / b) := (Real.log_div ha0.ne' hb0.ne').symm
    have h2 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have h3 : a / b - 1 = (a - b) / b := by field_simp
    calc Real.log a - Real.log b ≤ (a - b) / b := by rw [h1]; linarith
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ hb
  rw [abs_le]
  constructor
  · have := key hs' hs
    rw [abs_sub_comm] at this
    linarith
  · exact key hs hs'

/-- Complex log is Lipschitz with constant `1/δ` on `{Re ≥ δ}`. -/
theorem norm_clog_sub_le {u u' : ℂ} {δ : ℝ} (hδ : 0 < δ) (hu : δ ≤ u.re) (hu' : δ ≤ u'.re) :
    ‖Complex.log u - Complex.log u'‖ ≤ ‖u - u'‖ / δ := by
  have hconv : Convex ℝ {z : ℂ | δ ≤ z.re} := convex_halfSpace_re_ge δ
  have hd : ∀ z ∈ {z : ℂ | δ ≤ z.re}, HasDerivWithinAt Complex.log z⁻¹ {z : ℂ | δ ≤ z.re} z := by
    intro z hz
    have : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hδ hz))
    exact (Complex.hasDerivAt_log this).hasDerivWithinAt
  have hb : ∀ z ∈ {z : ℂ | δ ≤ z.re}, ‖z⁻¹‖ ≤ 1 / δ := by
    intro z hz
    have hz' : δ ≤ ‖z‖ := le_trans hz (Complex.re_le_norm z)
    rw [norm_inv, one_div]
    exact inv_anti₀ hδ hz'
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hconv hu' hu
  calc ‖Complex.log u - Complex.log u'‖ ≤ 1 / δ * ‖u - u'‖ := this
    _ = ‖u - u'‖ / δ := by ring

/-- `|y^m - y'^m| ≤ m |y - y'|` for `|y|, |y'| ≤ 1`. -/
theorem abs_pow_sub_pow_le {y y' : ℝ} (hy : |y| ≤ 1) (hy' : |y'| ≤ 1) (m : ℕ) :
    |y ^ m - y' ^ m| ≤ m * |y - y'| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : y ^ (m + 1) - y' ^ (m + 1) = y * (y ^ m - y' ^ m) + y' ^ m * (y - y') := by ring
    rw [e]
    calc |y * (y ^ m - y' ^ m) + y' ^ m * (y - y')|
        ≤ |y * (y ^ m - y' ^ m)| + |y' ^ m * (y - y')| := abs_add_le _ _
      _ = |y| * |y ^ m - y' ^ m| + |y'| ^ m * |y - y'| := by
          rw [abs_mul, abs_mul, abs_pow]
      _ ≤ 1 * (m * |y - y'|) + 1 * |y - y'| := by
          gcongr
          · exact pow_le_one₀ (abs_nonneg _) hy'
      _ = ((m + 1 : ℕ) : ℝ) * |y - y'| := by push_cast; ring

/-- **The power series `barrierTrialS u` is Lipschitz on `[-1, 1]`** with constant `Σ |u_k|`. -/
theorem barrierTrialS_lipschitz {u : ℕ → ℝ} (hu : Summable fun k => |u k|) {y y' : ℝ}
    (hy : |y| ≤ 1) (hy' : |y'| ≤ 1) :
    |OAI.InternalCatalan.barrierTrialS u y - OAI.InternalCatalan.barrierTrialS u y'| ≤
      (∑' k, |u k|) * |y - y'| := by
  have hs := OAI.InternalCatalan.barrierTrialS_summable u hu hy
  have hs' := OAI.InternalCatalan.barrierTrialS_summable u hu hy'
  have hu1 : Summable fun k : ℕ => |u (k + 1)| := (summable_nat_add_iff 1).mpr hu
  have hdiff : ∀ k : ℕ, |u (k + 1) * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
      u (k + 1) * y' ^ (k + 1) / ((k + 1 : ℕ) : ℝ)| ≤ |u (k + 1)| * |y - y'| := by
    intro k
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have : u (k + 1) * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ) - u (k + 1) * y' ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
        = u (k + 1) * (y ^ (k + 1) - y' ^ (k + 1)) / ((k + 1 : ℕ) : ℝ) := by ring
    rw [this, abs_div, abs_mul, abs_of_pos hk, div_le_iff₀ hk]
    have := abs_pow_sub_pow_le hy hy' (k + 1)
    calc |u (k + 1)| * |y ^ (k + 1) - y' ^ (k + 1)|
        ≤ |u (k + 1)| * (((k + 1 : ℕ) : ℝ) * |y - y'|) := by gcongr
      _ = |u (k + 1)| * |y - y'| * ((k + 1 : ℕ) : ℝ) := by ring
  unfold OAI.InternalCatalan.barrierTrialS
  rw [← Summable.tsum_sub hs hs']
  have hsum2 : Summable fun k : ℕ => |u (k + 1)| * |y - y'| := hu1.mul_right _
  calc |∑' k : ℕ, (u (k + 1) * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
        u (k + 1) * y' ^ (k + 1) / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑' k : ℕ, |u (k + 1)| * |y - y'| := by
        have h1 := norm_tsum_le_tsum_norm (f := fun k : ℕ => u (k + 1) * y ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ) - u (k + 1) * y' ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
          ((hs.sub hs').norm)
        refine h1.trans ?_
        exact (hs.sub hs').norm.tsum_le_tsum (fun k => by
          simpa [Real.norm_eq_abs] using hdiff k) hsum2
    _ = (∑' k : ℕ, |u (k + 1)|) * |y - y'| := by rw [tsum_mul_right]
    _ ≤ (∑' k, |u k|) * |y - y'| := by
        have := hu.sum_add_tsum_nat_add 1
        have h0 : 0 ≤ ∑ i ∈ range 1, |u i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

theorem list_norm_sum_sub {α : Type*} (l : List α) (f g : α → ℂ) (c : α → ℝ)
    (h : ∀ a ∈ l, ‖f a - g a‖ ≤ c a) :
    ‖(l.map f).sum - (l.map g).sum‖ ≤ (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    calc ‖f a + (l.map f).sum - (g a + (l.map g).sum)‖
        = ‖(f a - g a) + ((l.map f).sum - (l.map g).sum)‖ := by ring_nf
      _ ≤ ‖f a - g a‖ + ‖(l.map f).sum - (l.map g).sum‖ := norm_add_le _ _
      _ ≤ c a + (l.map c).sum := add_le_add h1 h2

/-- The limit (`τ = 1`) closed form of `fld τ (gseq G)`: `-Re Σ ρ log (1 - x w)`. -/
def geoLim (G : Tail) (x : ℝ) : ℝ :=
  -((G.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1))).sum).re

theorem geoForm_eq_log {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {G : Tail}
    (hG : ∀ wr ∈ G, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) {x : ℝ}
    (hx : |x| ≤ 1) :
    geoForm τ G x =
      -((G.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1)))).sum).re := by
  have hT := scaleTail_ok hτ hG
  unfold geoForm
  rw [← tailS_conv hT hx]
  simp [scaleTail, List.map_map, Function.comp_def]

/-- **Block estimate for the geometric sequences**: for `|x| ≤ ρ < 1`,
`|geoForm τ G x - geoLim G x| ≤ (Σ ‖ρ_q‖) (1 - τ) ρ/(1 - ρ)`. -/
theorem geoForm_sub_geoLim_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {G : Tail}
    (hG : ∀ wr ∈ G, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) {x ρ : ℝ}
    (hxρ : |x| ≤ ρ) (hρ : ρ < 1) :
    |geoForm τ G x - geoLim G x| ≤
      (G.map (fun wr : ℂ × ℂ => ‖wr.2‖)).sum * ((1 - τ) * ρ / (1 - ρ)) := by
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg x) hxρ
  have hx1 : |x| ≤ 1 := by linarith
  rw [geoForm_eq_log hτ hG hx1]
  unfold geoLim
  have key := list_norm_sum_sub G
    (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1)))
    (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1))
    (fun wr => ‖wr.2‖ * ((1 - τ) * ρ / (1 - ρ))) (by
      intro wr hwr
      have hw := (hG wr hwr).1
      rw [← mul_sub, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hre : ∀ w : ℂ, ‖w‖ ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
          1 - ρ ≤ (1 - (x : ℂ) * ((t : ℂ) * w)).re := by
        intro w hw' t ht0 ht1
        have : ((x : ℂ) * ((t : ℂ) * w)).re ≤ ρ := by
          calc ((x : ℂ) * ((t : ℂ) * w)).re ≤ ‖(x : ℂ) * ((t : ℂ) * w)‖ := Complex.re_le_norm _
            _ = |x| * (t * ‖w‖) := by
                rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                  Real.norm_eq_abs, abs_of_pos ht0]
            _ ≤ ρ * (1 * 1) := by
                gcongr
            _ = ρ := by ring
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have h1 := hre wr.1 hw τ hτ.1 hτ.2.le
      have h2 := hre wr.1 hw 1 one_pos le_rfl
      simp only [Complex.ofReal_one, one_mul] at h2
      have := norm_clog_sub_le (by linarith : 0 < 1 - ρ) h1 h2
      refine this.trans ?_
      have e : (1 - (x : ℂ) * ((τ : ℂ) * wr.1)) - (1 - (x : ℂ) * wr.1) =
          ((x * (1 - τ) : ℝ) : ℂ) * wr.1 := by push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by linarith [hτ.2] : 0 < 1 - τ)]
      rw [div_le_div_iff_of_pos_right (by linarith)]
      calc |x| * (1 - τ) * ‖wr.1‖ ≤ ρ * (1 - τ) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hxρ (by linarith [hτ.2])) hw (norm_nonneg _)
              (mul_nonneg hρ0 (by linarith [hτ.2]))
        _ = (1 - τ) * ρ := by ring)
  rw [List.sum_map_mul_right] at key
  have h3 : |(-(List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1))) G).sum.re) -
      (-(List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1)) G).sum.re)| ≤
      ‖(List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1))) G).sum -
        (List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1)) G).sum‖ := by
    rw [show ∀ a b : ℝ, -a - -b = -(a - b) from fun a b => by ring, abs_neg, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  exact h3.trans key

/-- Integrability of `log (1 - c y)` against a polynomial-density measure. -/
theorem integrable_log_one_sub_polyMeas {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) {c : ℝ}
    (hc : c ≠ 0) : Integrable (fun y => Real.log (1 - c * y)) (polyMeas qs) := by
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c⁻¹ := by
    rw [ae_iff]; simp
  have hi : ∀ q ∈ qs, PieceOK q ∧ IntegrableOn (fun y => Real.log (1 - c * y)) (Icc q.lo q.hi) := by
    intro q hq
    refine ⟨hqs q hq, ?_⟩
    have h0 : IntegrableOn (fun t => Real.log |c| + Real.log |t - c⁻¹|) (Icc q.lo q.hi) :=
      (integrableOn_const isCompact_Icc.measure_lt_top.ne).add
        (integrableOn_log_abs_sub c⁻¹ (hqs q hq).1)
    refine h0.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with t ht
    rw [log_one_sub_eq hc ht]
  exact (integrable_polyMeas hi).1

open CatalanMeasure.Signed.ReflectionEnergy in
/-- **Block estimate for the dilated potentials**: for `0 < c, c' ≤ ρ < 1`,
`|dilPot qs c - dilPot qs c'| ≤ m(ℝ) |c - c'|/(1 - ρ)`. -/
theorem dilPot_sub_le {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) {C : ℝ}
    (hBD : BD (polyMeas qs) C) {c c' ρ : ℝ} (hc : 0 < c) (hcρ : c ≤ ρ) (hc' : 0 < c')
    (hc'ρ : c' ≤ ρ) (hρ : ρ < 1) :
    |dilPot qs c - dilPot qs c'| ≤ polyMass qs * (|c - c'| / (1 - ρ)) := by
  have := hBD.finite
  have e : ∀ d : ℝ, d ≠ 0 → dilPot qs d = -∫ y, Real.log (1 - d * y) ∂(polyMeas qs) := by
    intro d hd
    rw [integral_log_one_sub_polyMeas hqs hd]; rfl
  rw [e c hc.ne', e c' hc'.ne']
  have hI := integrable_log_one_sub_polyMeas hqs hc.ne'
  have hI' := integrable_log_one_sub_polyMeas hqs hc'.ne'
  have h1 : -∫ y, Real.log (1 - c * y) ∂(polyMeas qs) - -∫ y, Real.log (1 - c' * y) ∂(polyMeas qs)
      = ∫ y, (Real.log (1 - c' * y) - Real.log (1 - c * y)) ∂(polyMeas qs) := by
    rw [integral_sub hI' hI]; ring
  rw [h1]
  have hb : ∀ᵐ y ∂(polyMeas qs), ‖Real.log (1 - c' * y) - Real.log (1 - c * y)‖ ≤
      |c - c'| / (1 - ρ) := by
    filter_upwards [hBD.ae_mem] with y hy
    have hy1 : y ≤ 1 := hy.2.le
    have hy0 : 0 ≤ y := hy.1.le
    have hs : 1 - ρ ≤ 1 - c * y := by nlinarith
    have hs' : 1 - ρ ≤ 1 - c' * y := by nlinarith
    rw [Real.norm_eq_abs]
    refine (abs_log_sub_le (by linarith) hs' hs).trans ?_
    rw [div_le_div_iff_of_pos_right (by linarith)]
    have : (1 - c' * y) - (1 - c * y) = (c - c') * y := by ring
    rw [this, abs_mul, abs_of_nonneg hy0]
    calc |c - c'| * y ≤ |c - c'| * 1 := by gcongr
      _ = |c - c'| := mul_one _
  have h2 := norm_integral_le_of_norm_le_const hb
  have h3 : (polyMeas qs).real univ = polyMass qs := by
    have := integral_const_polyMeas hqs
    rw [integral_const, smul_eq_mul, mul_one] at this
    exact this
  rw [Real.norm_eq_abs, h3] at h2
  linarith

theorem polyMeas_ae_le {qs : List Piece} {b : ℝ} (hb : ∀ q ∈ qs, q.hi ≤ b) :
    ∀ᵐ y ∂(polyMeas qs), y ≤ b := by
  induction qs with
  | nil => simp [polyMeas]
  | cons q qs ih =>
    have hq : ∀ᵐ y ∂q.meas, y ≤ b := by
      have h1 : ∀ᵐ y ∂(volume.restrict (Ioc q.lo q.hi)), y ≤ b := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact hy.2.trans (hb q (by simp))
      exact (withDensity_absolutelyContinuous _ _).ae_le h1
    have e : polyMeas (q :: qs) = q.meas + polyMeas qs := by simp [polyMeas]
    rw [e, ae_add_measure_iff]
    exact ⟨hq, ih fun r hr => hb r (by simp [hr])⟩

open CatalanMeasure.Signed.ReflectionEnergy in
/-- **Dilated potentials of a measure supported on `(0, b]`, `b < 1`**: for `0 < c, c' ≤ 1`,
`|dilPot qs c - dilPot qs c'| ≤ m(ℝ) |c - c'|/(1 - b)`. -/
theorem dilPot_sub_le_supp {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) {C : ℝ}
    (hBD : BD (polyMeas qs) C) {b : ℝ} (hsupp : ∀ᵐ y ∂(polyMeas qs), y ≤ b) (hb : b < 1)
    {c c' : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hc' : 0 < c') (hc'1 : c' ≤ 1) :
    |dilPot qs c - dilPot qs c'| ≤ polyMass qs * (|c - c'| / (1 - b)) := by
  have := hBD.finite
  have e : ∀ d : ℝ, d ≠ 0 → dilPot qs d = -∫ y, Real.log (1 - d * y) ∂(polyMeas qs) := by
    intro d hd
    rw [integral_log_one_sub_polyMeas hqs hd]; rfl
  rw [e c hc.ne', e c' hc'.ne']
  have hI := integrable_log_one_sub_polyMeas hqs hc.ne'
  have hI' := integrable_log_one_sub_polyMeas hqs hc'.ne'
  have h1 : -∫ y, Real.log (1 - c * y) ∂(polyMeas qs) - -∫ y, Real.log (1 - c' * y) ∂(polyMeas qs)
      = ∫ y, (Real.log (1 - c' * y) - Real.log (1 - c * y)) ∂(polyMeas qs) := by
    rw [integral_sub hI' hI]; ring
  rw [h1]
  have hb' : ∀ᵐ y ∂(polyMeas qs), ‖Real.log (1 - c' * y) - Real.log (1 - c * y)‖ ≤
      |c - c'| / (1 - b) := by
    filter_upwards [hBD.ae_mem, hsupp] with y hy hyb
    have hy1 : y ≤ 1 := hy.2.le
    have hy0 : 0 ≤ y := hy.1.le
    have hs : 1 - b ≤ 1 - c * y := by nlinarith [mul_le_mul_of_nonneg_right hc1 hy0]
    have hs' : 1 - b ≤ 1 - c' * y := by nlinarith [mul_le_mul_of_nonneg_right hc'1 hy0]
    rw [Real.norm_eq_abs]
    refine (abs_log_sub_le (by linarith) hs' hs).trans ?_
    rw [div_le_div_iff_of_pos_right (by linarith)]
    have : (1 - c' * y) - (1 - c * y) = (c - c') * y := by ring
    rw [this, abs_mul, abs_of_nonneg hy0]
    calc |c - c'| * y ≤ |c - c'| * 1 := by gcongr
      _ = |c - c'| := mul_one _
  have h2 := norm_integral_le_of_norm_le_const hb'
  have h3 : (polyMeas qs).real univ = polyMass qs := by
    have := integral_const_polyMeas hqs
    rw [integral_const, smul_eq_mul, mul_one] at this
    exact this
  rw [Real.norm_eq_abs, h3] at h2
  linarith

/-- The explicit logarithmic terms of a free row field (`-log(1-x)/(2ν)`, the diagonal cost
`(κ/ν)(-log|x| + c0)` of the `(1 - η)`-share, `κ = 1 - η`, and `-(1/2ν) log(1-τ²x²)`), vanishing
like `1/ν` and `c0/ν`. -/
def rowLogs (ν τ c0 κ x : ℝ) : ℝ :=
  -Real.log (1 - x) / (2 * ν) + (κ / ν) * (-Real.log |x| + c0) -
    (1 / (2 * ν)) * Real.log (1 - (τ * x) * (τ * x))

theorem abs_rowLogs_le {ν τ c0 κ x m ρ : ℝ} (hν : 0 < ν) (hτ : τ ∈ Ioo (0 : ℝ) 1) (hc0 : 0 ≤ c0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hm : 0 < m) (hmx : m ≤ |x|) (hxρ : |x| ≤ ρ) (hρ : ρ < 1) :
    |rowLogs ν τ c0 κ x| ≤ 2 * (|Real.log m| + |Real.log (1 - ρ)| + Real.log 2) / ν + c0 / ν := by
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg x) hxρ
  have hx0 : 0 < |x| := lt_of_lt_of_le hm hmx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlρ : Real.log (1 - ρ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hA : |Real.log (1 - x)| ≤ |Real.log m| + |Real.log (1 - ρ)| + Real.log 2 := by
    have h1 : Real.log (1 - x) ≤ Real.log 2 :=
      Real.log_le_log (by linarith [abs_le.mp hxρ]) (by linarith [abs_le.mp hxρ])
    have h2 : Real.log (1 - ρ) ≤ Real.log (1 - x) :=
      Real.log_le_log (by linarith) (by linarith [abs_le.mp hxρ])
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg (Real.log m), abs_nonneg (Real.log (1 - ρ)),
      neg_abs_le (Real.log (1 - ρ))]
  have hB : |Real.log (|x|)| ≤ |Real.log m| := by
    have h1 : Real.log m ≤ Real.log |x| := Real.log_le_log hm hmx
    have h2 : Real.log |x| ≤ 0 := Real.log_nonpos hx0.le (by linarith)
    rw [abs_of_nonpos h2]
    have := neg_abs_le (Real.log m)
    linarith
  have hC : |Real.log (1 - (τ * x) * (τ * x))| ≤ |Real.log (1 - ρ)| := by
    have hxx : (τ * x) * (τ * x) ≤ ρ := by
      have : (τ * x) * (τ * x) = τ ^ 2 * |x| ^ 2 := by rw [sq_abs]; ring
      rw [this]
      have h1 : |x| ^ 2 ≤ |x| := by nlinarith [abs_nonneg x, (by linarith : |x| < 1)]
      have h2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
      calc τ ^ 2 * |x| ^ 2 ≤ 1 * |x| := mul_le_mul h2 h1 (sq_nonneg _) zero_le_one
        _ ≤ ρ := by linarith
    have h0 : 0 ≤ (τ * x) * (τ * x) := mul_self_nonneg _
    have h1 : Real.log (1 - ρ) ≤ Real.log (1 - (τ * x) * (τ * x)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (1 - (τ * x) * (τ * x)) ≤ 0 := Real.log_nonpos (by nlinarith) (by linarith)
    rw [abs_of_nonpos h2, abs_of_nonpos hlρ]
    linarith
  set J := |Real.log m| + |Real.log (1 - ρ)| + Real.log 2 with hJ
  have hJ0 : 0 ≤ J := by positivity
  have h2ν : 0 < 2 * ν := by positivity
  unfold rowLogs
  have t1 : |-Real.log (1 - x) / (2 * ν)| ≤ J / (2 * ν) := by
    rw [abs_div, abs_neg, abs_of_pos h2ν]; exact div_le_div_of_nonneg_right hA h2ν.le
  have t2 : |(κ / ν) * (-Real.log |x| + c0)| ≤ (|Real.log m| + c0) / ν := by
    have hX : |-Real.log (|x|) + c0| ≤ |Real.log m| + c0 := by
      calc |-Real.log (|x|) + c0| ≤ |-Real.log (|x|)| + |c0| := abs_add_le _ _
        _ ≤ |Real.log m| + c0 := by rw [abs_neg, abs_of_nonneg hc0]; linarith
    rw [abs_mul, abs_of_nonneg (div_nonneg hκ0 hν.le)]
    calc κ / ν * |-Real.log |x| + c0| ≤ 1 / ν * (|Real.log m| + c0) :=
          mul_le_mul (div_le_div_of_nonneg_right hκ1 hν.le) hX (abs_nonneg _) (by positivity)
      _ = (|Real.log m| + c0) / ν := by ring
  have t3 : |(1 / (2 * ν)) * Real.log (1 - (τ * x) * (τ * x))| ≤ J / (2 * ν) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * ν)), one_div, ← div_eq_inv_mul]
    apply div_le_div_of_nonneg_right _ h2ν.le
    have : |Real.log (1 - ρ)| ≤ J := by rw [hJ]; linarith [abs_nonneg (Real.log m)]
    linarith
  have hfin : J / (2 * ν) + (|Real.log m| + c0) / ν + J / (2 * ν) ≤ 2 * J / ν + c0 / ν := by
    have : |Real.log m| ≤ J := by rw [hJ]; linarith [abs_nonneg (Real.log (1 - ρ)), hlog2]
    rw [show J / (2 * ν) + (|Real.log m| + c0) / ν + J / (2 * ν) = (J + |Real.log m| + c0) / ν by
      field_simp; ring, show 2 * J / ν + c0 / ν = (2 * J + c0) / ν by ring]
    exact div_le_div_of_nonneg_right (by linarith) hν.le
  have u1 := abs_le.mp t1
  have u2 := abs_le.mp t2
  have u3 := abs_le.mp t3
  exact abs_le.mpr ⟨by linarith [u1.1, u2.1, u3.2], by linarith [u1.2, u2.2, u3.1]⟩

open Filter Topology

/-- A family `D N` of the Lean class with fixed trial data `F` and `e_N → 0`, `ν_N → ∞`,
`log(1/(1-τ²))/ν → 0` (`e` tends to `0` slowly), and summable `|a|`. -/
structure Family (D : ℕ → SignedData) (F : TrialForm) : Prop where
  spec : ∀ N, F.Spec (D N)
  hτ : Tendsto (fun N => (D N).τ) atTop (𝓝 1)
  hν : Tendsto (fun N => (D N).ν) atTop atTop
  hℓ : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν) atTop (𝓝 0)
  hasum : Summable fun k => |tseq F.a.f F.a.tail k|

/-- **The damping of the trial family**: `e_N = 2^-30/(N+1)`, common to the two endpoint trials of every
interval.  `e_N ≤ 2^-30` for every `N` (the spike certificates' `emax`, `LinkCert` at `2^-30` via
`Consts.certH_mul_le_mono`), `e_N → 0` (`err_small`), `τ_N = 1 - e_N → 1` (`Family.hτ`) and
`log(1/(1-τ_N²))/(c N) → 0` (`Family.hℓ` with `ν = c N`). -/
def dampE (N : ℕ) : ℝ := 1 / 2 ^ 30 / ((N : ℝ) + 1)

theorem dampE_pos (N : ℕ) : 0 < dampE N := by unfold dampE; positivity

theorem dampE_le (N : ℕ) : dampE N ≤ 1 / 2 ^ 30 := by
  unfold dampE
  exact div_le_self (by positivity) (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)

theorem dampE_mem (N : ℕ) : dampE N ∈ Ioo (0 : ℝ) (1 / 8) :=
  ⟨dampE_pos N, (dampE_le N).trans_lt (by norm_num)⟩

theorem natCast_add_one_tendsto : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem dampE_tendsto : Tendsto dampE atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop natCast_add_one_tendsto

theorem dampE_tau_tendsto : Tendsto (fun N => 1 - dampE N) atTop (𝓝 1) := by
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub dampE_tendsto

theorem log_div_natCast_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / (c * N)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop c (-c) 1 hc.ne').comp natCast_add_one_tendsto
  refine h.congr fun N => ?_
  simp only [Function.comp, pow_one]
  congr 1
  ring

theorem dampE_hℓ {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log (1 / (1 - (1 - dampE N) ^ 2)) / (c * N)) atTop (𝓝 0) := by
  have hup : Tendsto (fun N : ℕ => (30 * Real.log 2) / (c * N) + Real.log ((N : ℝ) + 1) / (c * N))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (30 * Real.log 2) / (c * N)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
    simpa using h1.add (log_div_natCast_tendsto hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun N => ?_) (fun N => ?_)
  · have he := dampE_pos N
    have he1 : dampE N ≤ 1 := (dampE_le N).trans (by norm_num)
    have hq : 0 < 1 - (1 - dampE N) ^ 2 := by nlinarith
    have hq1 : 1 - (1 - dampE N) ^ 2 ≤ 1 := by nlinarith
    exact div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hq]; linarith))
      (mul_nonneg hc.le (Nat.cast_nonneg N))
  · have he := dampE_pos N
    have he1 : dampE N ≤ 1 := (dampE_le N).trans (by norm_num)
    have hq : 0 < 1 - (1 - dampE N) ^ 2 := by nlinarith
    have hqe : dampE N ≤ 1 - (1 - dampE N) ^ 2 := by nlinarith
    have hlog : Real.log (1 / (1 - (1 - dampE N) ^ 2)) ≤
        30 * Real.log 2 + Real.log ((N : ℝ) + 1) := by
      have e1 : 1 / dampE N = 2 ^ 30 * ((N : ℝ) + 1) := by
        unfold dampE; field_simp
      calc Real.log (1 / (1 - (1 - dampE N) ^ 2)) ≤ Real.log (1 / dampE N) :=
            Real.log_le_log (by positivity) (one_div_le_one_div_of_le he hqe)
        _ = 30 * Real.log 2 + Real.log ((N : ℝ) + 1) := by
            rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    rw [← add_div]
    exact div_le_div_of_nonneg_right hlog (mul_nonneg hc.le (Nat.cast_nonneg N))

theorem polyMass_nonneg {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) : 0 ≤ polyMass qs := by
  rw [← integral_const_polyMeas hqs]
  exact integral_nonneg fun _ => zero_le_one

/-- The limit (`τ = 1`) closed form of `fld τ R`. -/
def rLim (d : SeqForm) (x : ℝ) : ℝ := finS d.f d.L x + geoLim d.tail x

/-- The weight of the tilt in the dilation error: tail weights plus the finite moments. -/
def rW (d : SeqForm) : ℝ :=
  (d.tail.map (fun wr : ℂ × ℂ => ‖wr.2‖)).sum + ∑ k ∈ Finset.range d.L, |d.f (k + 1)|

theorem sum_norm_nonneg (G : Tail) : 0 ≤ (G.map (fun wr : ℂ × ℂ => ‖wr.2‖)).sum :=
  List.sum_nonneg (by intro a ha; simp only [List.mem_map] at ha; obtain ⟨b, _, rfl⟩ := ha;
                      exact norm_nonneg _)

theorem rW_nonneg (d : SeqForm) : 0 ≤ rW d :=
  add_nonneg (sum_norm_nonneg d.tail) (Finset.sum_nonneg fun k _ => abs_nonneg _)

/-- **Block estimate for the tilt** on `|x| ≤ ρ < 1`. -/
theorem rForm_sub_rLim_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {d : SeqForm}
    (hf : ∀ k, d.L < k → d.f k = 0)
    (hG : ∀ wr ∈ d.tail, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) {x ρ : ℝ}
    (hxρ : |x| ≤ ρ) (hρ : ρ < 1) :
    |rForm τ d x - rLim d x| ≤ rW d * ((1 - τ) * ρ / (1 - ρ)) := by
  have _ := hf
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg x) hxρ
  have hx1 : |x| ≤ 1 := by linarith
  have h1 := finS_dil_sub_le d.f d.L hτ hx1
  have h2 := geoForm_sub_geoLim_le hτ hG hxρ hρ
  have hq : (1 - τ) * |x| ≤ (1 - τ) * ρ / (1 - ρ) := by
    have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
    have : ρ ≤ ρ / (1 - ρ) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    calc (1 - τ) * |x| ≤ (1 - τ) * ρ := mul_le_mul_of_nonneg_left hxρ h1τ
      _ ≤ (1 - τ) * (ρ / (1 - ρ)) := mul_le_mul_of_nonneg_left this h1τ
      _ = (1 - τ) * ρ / (1 - ρ) := by ring
  have hS : 0 ≤ ∑ k ∈ Finset.range d.L, |d.f (k + 1)| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have h3 := mul_le_mul_of_nonneg_left hq hS
  unfold rForm rLim rW
  have e : finS d.f d.L (τ * x) + geoForm τ d.tail x - (finS d.f d.L x + geoLim d.tail x) =
      (finS d.f d.L (τ * x) - finS d.f d.L x) + (geoForm τ d.tail x - geoLim d.tail x) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  nlinarith [h1, h2, h3]


/-- The generator's limit (`τ = 1`, `ν = ∞`) form of the negative-row field: the paper's
`lfarb2.Trial.mu_parts(-1)` per unit mass (`Crow, SPv, Umn/Ump/Usn` at weight `2(1-η)`, `Cheb/TPu`
at `-4η`, `Pow, PoleLog`; NOTES-ETA §1.5). -/
def fNegLim (F : TrialForm) (RfL : ℝ → ℝ) (x : ℝ) : ℝ :=
  RfL x - F.v.Sform x - 2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x -
    2 * F.a.Sform (-x) + (-rLim F.R x)

/-- The error bound `B_N` of the uniform limit (everything except the `Rf` difference). -/
def limBound (F : TrialForm) (S J ν τ c0 ρ : ℝ) : ℝ :=
  2 * J / ν + c0 / ν + 2 * (S * (1 - τ)) +
    rW F.R * ((1 - τ) * ρ / (1 - ρ))

theorem tend_aux {g : ℕ → ℝ} (hg : Tendsto g atTop (𝓝 0)) (C ρ : ℝ) :
    Tendsto (fun N => C * (g N * ρ / (1 - ρ))) atTop (𝓝 0) := by
  have : Tendsto (fun N => C * (g N * ρ / (1 - ρ))) atTop (𝓝 (C * (0 * ρ / (1 - ρ)))) :=
    tendsto_const_nhds.mul ((hg.mul tendsto_const_nhds).div_const _)
  simpa using this

theorem tendsto_limBound {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) (S J ρ : ℝ) :
    Tendsto (fun N => limBound F S J (D N).ν (D N).τ
      (Real.log (1 / (1 - (D N).τ ^ 2))) ρ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
  have h2 : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hf.hτ.pow 2)
  have h3 : Tendsto (fun N => 2 * J / (D N).ν) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hf.hν
  have h4 := hf.hℓ
  have h5 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
    simpa using (h1.const_mul S).const_mul 2
  have t := ((((h3.add h4).add h5)).add
    (tend_aux h1 (rW F.R) ρ))
  simpa [limBound] using t

/-- **Uniform limit of the negative-row field on a compact cell `[a, b] ⊂ (-1, 0)`.**
`∀ ε > 0, ∀ᶠ N, ∀ x ∈ [a, b], |fNeg (D N) x - fNegLim x| ≤ ε`, given the same for `Rf`. -/
theorem fNeg_unif {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {a b : ℝ}
    (ha : -1 < a) (hab : a ≤ b) (hb : b < 0) {RfL : ℝ → ℝ}
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc a b, |(D N).Rf x - RfL x| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc a b, |(D N).fNeg x - fNegLim F RfL x| ≤ ε := by
  intro ε hε
  set ρ : ℝ := -a with hρdef
  set m : ℝ := -b with hmdef
  have hρ : ρ < 1 := by linarith
  have hm : 0 < m := by linarith
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  set J : ℝ := |Real.log m| + |Real.log (1 - ρ)| + Real.log 2 with hJ
  have hBt := tendsto_limBound hf S J ρ
  have hB : ∀ᶠ N in atTop, limBound F S J (D N).ν (D N).τ (Real.log (1 / (1 - (D N).τ ^ 2))) ρ
      ≤ ε / 2 := hBt.eventually (ge_mem_nhds (by linarith))
  have hνpos : ∀ᶠ N in atTop, 0 < (D N).ν := hf.hν.eventually_gt_atTop 0
  filter_upwards [hRf (ε / 2) (by linarith), hB, hνpos] with N hRfN hBN hνN x hx
  have hs := hf.spec N
  have hτN := hs.hτ
  have hxI : x ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxa : |x| ≤ ρ := by rw [abs_of_neg hxI.2]; linarith [hx.1]
  have hxm : m ≤ |x| := by rw [abs_of_neg hxI.2]; linarith [hx.2]
  have hx1 : |x| ≤ 1 := by linarith
  have hc0 : 0 ≤ Real.log (1 / (1 - (D N).τ ^ 2)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by nlinarith [hτN.1, hτN.2])]
    nlinarith [hτN.1, hτN.2]
  -- the closed form
  rw [TrialForm.fNeg_closed hs hxI]
  unfold fNegLim
  -- block estimates
  have hκ0 : 0 ≤ 1 - F.η := by linarith [hs.hηI.2]
  have hκ1 : 1 - F.η ≤ 1 := by linarith [hs.hηI.1]
  have eLog := abs_rowLogs_le hνN hτN hc0 hκ0 hκ1 hm hxm hxa hρ
  have eSa : |F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)| ≤ S * (1 - (D N).τ) := by
    rw [← TrialForm.S_a hs (TrialForm.abs_neg_tau_le hs hx1),
      ← TrialForm.S_a hs (by rwa [abs_neg]), hs.ha]
    refine (barrierTrialS_lipschitz hf.hasum (TrialForm.abs_neg_tau_le hs hx1)
      (by rwa [abs_neg])).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun k => abs_nonneg _)
    have : -(D N).τ * x - -x = (1 - (D N).τ) * x := by ring
    rw [this, abs_mul, abs_of_pos (by linarith [hτN.2] : 0 < 1 - (D N).τ)]
    nlinarith [hτN.2, abs_nonneg x]
  have eR := rForm_sub_rLim_le hs.hτ hs.hRf hs.hRok hxa hρ
  have eR' : |rForm (D N).τ F.R x - rLim F.R x| ≤
      rW F.R * ((1 - (D N).τ) * ρ / (1 - ρ)) := eR
  -- assemble
  unfold limBound at hBN
  have u1 := abs_le.mp (hRfN x hx)
  have u2 := abs_le.mp eLog
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR'
  have key : (D N).Rf x - F.v.Sform x - Real.log (1 - x) / (2 * (D N).ν) +
        ((1 - F.η) / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x -
        (1 / (2 * (D N).ν)) * Real.log (1 - ((D N).τ * x) * ((D N).τ * x)) -
        2 * F.a.Sform (-(D N).τ * x) +
        (-rForm (D N).τ F.R x) -
      (RfL x - F.v.Sform x - 2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x -
        2 * F.a.Sform (-x) + (-rLim F.R x)) =
      ((D N).Rf x - RfL x) +
        rowLogs (D N).ν (D N).τ (Real.log (1 / (1 - (D N).τ ^ 2))) (1 - F.η) x -
        2 * (F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)) -
        (rForm (D N).τ F.R x - rLim F.R x) := by
    unfold rowLogs; ring
  rw [key]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [u1.1, u1.2, u2.1, u2.2, u3.1, u3.2, u5.1, u5.2]

/-- The logarithmic terms of a positive row field (no `log(1-τ²x²)` term). -/
def rowLogsP (ν c0 κ x : ℝ) : ℝ :=
  -Real.log (1 - x) / (2 * ν) + (κ / ν) * (-Real.log |x| + c0)

theorem abs_rowLogsP_le {ν c0 κ x m ρ : ℝ} (hν : 0 < ν) (hc0 : 0 ≤ c0) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (hm : 0 < m) (hmx : m ≤ |x|) (hxρ : |x| ≤ ρ) (hρ : ρ < 1) :
    |rowLogsP ν c0 κ x| ≤ 2 * (|Real.log m| + |Real.log (1 - ρ)| + Real.log 2) / ν + c0 / ν := by
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg x) hxρ
  have hx0 : 0 < |x| := lt_of_lt_of_le hm hmx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlρ : Real.log (1 - ρ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hA : |Real.log (1 - x)| ≤ |Real.log m| + |Real.log (1 - ρ)| + Real.log 2 := by
    have h1 : Real.log (1 - x) ≤ Real.log 2 :=
      Real.log_le_log (by linarith [abs_le.mp hxρ]) (by linarith [abs_le.mp hxρ])
    have h2 : Real.log (1 - ρ) ≤ Real.log (1 - x) :=
      Real.log_le_log (by linarith) (by linarith [abs_le.mp hxρ])
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg (Real.log m), abs_nonneg (Real.log (1 - ρ)),
      neg_abs_le (Real.log (1 - ρ))]
  have hB : |Real.log (|x|)| ≤ |Real.log m| := by
    have h1 : Real.log m ≤ Real.log |x| := Real.log_le_log hm hmx
    have h2 : Real.log |x| ≤ 0 := Real.log_nonpos hx0.le (by linarith)
    rw [abs_of_nonpos h2]
    have := neg_abs_le (Real.log m)
    linarith
  set J := |Real.log m| + |Real.log (1 - ρ)| + Real.log 2 with hJ
  have hJ0 : 0 ≤ J := by positivity
  have h2ν : 0 < 2 * ν := by positivity
  unfold rowLogsP
  have t1 : |-Real.log (1 - x) / (2 * ν)| ≤ J / (2 * ν) := by
    rw [abs_div, abs_neg, abs_of_pos h2ν]; exact div_le_div_of_nonneg_right hA h2ν.le
  have t2 : |(κ / ν) * (-Real.log |x| + c0)| ≤ (|Real.log m| + c0) / ν := by
    have hX : |-Real.log (|x|) + c0| ≤ |Real.log m| + c0 := by
      calc |-Real.log (|x|) + c0| ≤ |-Real.log (|x|)| + |c0| := abs_add_le _ _
        _ ≤ |Real.log m| + c0 := by rw [abs_neg, abs_of_nonneg hc0]; linarith
    rw [abs_mul, abs_of_nonneg (div_nonneg hκ0 hν.le)]
    calc κ / ν * |-Real.log |x| + c0| ≤ 1 / ν * (|Real.log m| + c0) :=
          mul_le_mul (div_le_div_of_nonneg_right hκ1 hν.le) hX (abs_nonneg _) (by positivity)
      _ = (|Real.log m| + c0) / ν := by ring
  have hfin : J / (2 * ν) + (|Real.log m| + c0) / ν ≤ 2 * J / ν + c0 / ν := by
    have : |Real.log m| ≤ J := by rw [hJ]; linarith [abs_nonneg (Real.log (1 - ρ)), hlog2]
    rw [show J / (2 * ν) + (|Real.log m| + c0) / ν = (J / 2 + |Real.log m| + c0) / ν by
      field_simp; ring, show 2 * J / ν + c0 / ν = (2 * J + c0) / ν by ring]
    exact div_le_div_of_nonneg_right (by linarith) hν.le
  have u1 := abs_le.mp t1
  have u2 := abs_le.mp t2
  exact abs_le.mpr ⟨by linarith [u1.1, u2.1, u2.2], by linarith [u1.2, u2.2]⟩

/-- `|denPoly b K x| ≤ 2 Σ_{i<K} |b_{i+1}|` on `|x| ≤ 1`. -/
theorem abs_denPoly_le (b : ℕ → ℝ) (K : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |denPoly b K x| ≤ 2 * ∑ i ∈ Finset.range K, |b (i + 1)| := by
  unfold denPoly
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hk : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 i
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < ((i + 1 : ℕ) : ℝ))]
  have : |x| ^ (i + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg (b (i + 1)), pow_nonneg (abs_nonneg x) (i + 1)]

/-- The generator's limit form of the positive-row field with spike cost; `σ = lim sp/ν`,
`cs∞ = lim cs`, and `denPoly bL KL` is the (N-independent) denominator polynomial. -/
def fPosLim (F : TrialForm) (RfL : ℝ → ℝ) (σ : ℝ) (bL : ℕ → ℝ) (KL : ℕ) (csL θL : ℝ) (x : ℝ) : ℝ :=
  RfL x - F.v.Sform x - 2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
    2 * F.a.Sform (-x) - σ * denPoly bL KL x + (F.dilT x + rLim F.R x) + 2 * F.Sup +
    csL * (if 1 - θL < x then 1 else 0)

/-- The error bound of the positive-row limit (everything except the `Rf` difference). -/
def limBoundP (F : TrialForm) (S J Db ν τ c0 ρ sν σ cs csL : ℝ) : ℝ :=
  2 * J / ν + c0 / ν + 2 * (S * (1 - τ)) + (polyMass F.qT + polyMass F.qTn) * ((1 - τ ^ 2) * ρ / (1 - ρ)) +
    rW F.R * ((1 - τ) * ρ / (1 - ρ)) + Db * |sν - σ| +
    |cs - csL|

/-- **Uniform limit of the positive-row field (with spike cost) on a compact cell
`[a, b] ⊂ (0, 1)`.** -/
theorem fPosS_unif {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) {RfL : ℝ → ℝ} {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc a b, |(D N).Rf x - RfL x| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc a b,
      |(D N).fPosS x - fPosLim F RfL σ bL KL csL θL x| ≤ ε := by
  intro ε hε
  set ρ : ℝ := b with hρdef
  set m : ℝ := a with hmdef
  have hρ : ρ < 1 := hb
  have hm : 0 < m := ha
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  set J : ℝ := |Real.log m| + |Real.log (1 - ρ)| + Real.log 2 with hJ
  set Db : ℝ := 2 * ∑ i ∈ Finset.range KL, |bL (i + 1)| with hDb
  have hBt : Tendsto (fun N => limBoundP F S J Db (D N).ν (D N).τ
      (Real.log (1 / (1 - (D N).τ ^ 2))) ρ (((D N).sp : ℝ) / (D N).ν) σ (D N).cs csL)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
    have h2 : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hf.hτ.pow 2)
    have h3 : Tendsto (fun N => 2 * J / (D N).ν) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hf.hν
    have h5 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
      simpa using (h1.const_mul S).const_mul 2
    have h6 : Tendsto (fun N => Db * |((D N).sp : ℝ) / (D N).ν - σ|) atTop (𝓝 0) := by
      have := ((hσ.sub_const σ).abs).const_mul Db
      simpa using this
    have h7 : Tendsto (fun N => |(D N).cs - csL|) atTop (𝓝 0) := by
      simpa using (hcs.sub_const csL).abs
    have t := ((((((h3.add hf.hℓ).add h5).add (tend_aux h2 (polyMass F.qT + polyMass F.qTn) ρ)).add
      (tend_aux h1 (rW F.R) ρ)).add h6).add h7)
    simpa [limBoundP] using t
  have hB : ∀ᶠ N in atTop, limBoundP F S J Db (D N).ν (D N).τ
      (Real.log (1 / (1 - (D N).τ ^ 2))) ρ (((D N).sp : ℝ) / (D N).ν) σ (D N).cs csL ≤ ε / 2 :=
    hBt.eventually (ge_mem_nhds (by linarith))
  have hνpos : ∀ᶠ N in atTop, 0 < (D N).ν := hf.hν.eventually_gt_atTop 0
  filter_upwards [hRf (ε / 2) (by linarith), hB, hνpos] with N hRfN hBN hνN x hx
  have hs := hf.spec N
  have hτN := hs.hτ
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxa : |x| ≤ ρ := by rw [abs_of_pos hxI.1]; exact hx.2
  have hxm : m ≤ |x| := by rw [abs_of_pos hxI.1]; exact hx.1
  have hx1 : |x| ≤ 1 := by linarith
  have hc0 : 0 ≤ Real.log (1 / (1 - (D N).τ ^ 2)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by nlinarith [hτN.1, hτN.2])]
    nlinarith [hτN.1, hτN.2]
  rw [TrialForm.fPosS_closed hs hxI, hbL N, hKL N, hθL N]
  unfold fPosLim
  have hκ0 : 0 ≤ 1 - F.η := by linarith [hs.hηI.2]
  have hκ1 : 1 - F.η ≤ 1 := by linarith [hs.hηI.1]
  have eLog := abs_rowLogsP_le hνN hc0 hκ0 hκ1 hm hxm hxa hρ
  have eSa : |F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)| ≤ S * (1 - (D N).τ) := by
    rw [← TrialForm.S_a hs (TrialForm.abs_neg_tau_le hs hx1),
      ← TrialForm.S_a hs (by rwa [abs_neg]), hs.ha]
    refine (barrierTrialS_lipschitz hf.hasum (TrialForm.abs_neg_tau_le hs hx1)
      (by rwa [abs_neg])).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun k => abs_nonneg _)
    have : -(D N).τ * x - -x = (1 - (D N).τ) * x := by ring
    rw [this, abs_mul, abs_of_pos (by linarith [hτN.2] : 0 < 1 - (D N).τ)]
    nlinarith [hτN.2, abs_nonneg x]
  have eDil : |F.dilT ((D N).τ ^ 2 * x) - F.dilT x| ≤
      (polyMass F.qT + polyMass F.qTn) * ((1 - (D N).τ ^ 2) * ρ / (1 - ρ)) := by
    have hBD : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qT) (D N).Cb := by
      have := hs.bd.hP true; rwa [hs.hμT] at this
    have hBDn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qTn) (D N).Cb := by
      have := hs.bd.hN true; rwa [hs.hμTn] at this
    have hxn : 0 < x := hxI.1
    have hτ2 : (D N).τ ^ 2 ≤ 1 := by nlinarith [hτN.1, hτN.2]
    have hd : |(D N).τ ^ 2 * x - x| / (1 - ρ) ≤ (1 - (D N).τ ^ 2) * ρ / (1 - ρ) := by
      rw [div_le_div_iff_of_pos_right (by linarith)]
      have e : (D N).τ ^ 2 * x - x = -((1 - (D N).τ ^ 2) * x) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - (D N).τ ^ 2)]
      exact mul_le_mul_of_nonneg_left hxa (by linarith)
    have h1 := dilPot_sub_le hs.pT hBD (c := (D N).τ ^ 2 * x) (c' := x) (ρ := ρ)
      (mul_pos (pow_pos hτN.1 2) hxn) (by nlinarith [pow_pos hτN.1 2, hx.2]) hxn hx.2 hρ
    have h2 := dilPot_sub_le hs.pTn hBDn (c := (D N).τ ^ 2 * x) (c' := x) (ρ := ρ)
      (mul_pos (pow_pos hτN.1 2) hxn) (by nlinarith [pow_pos hτN.1 2, hx.2]) hxn hx.2 hρ
    have m1 := mul_le_mul_of_nonneg_left hd (polyMass_nonneg hs.pT)
    have m2 := mul_le_mul_of_nonneg_left hd (polyMass_nonneg hs.pTn)
    unfold TrialForm.dilT
    have e2 : dilPot F.qT ((D N).τ ^ 2 * x) - dilPot F.qTn ((D N).τ ^ 2 * x) -
        (dilPot F.qT x - dilPot F.qTn x) =
        (dilPot F.qT ((D N).τ ^ 2 * x) - dilPot F.qT x) -
          (dilPot F.qTn ((D N).τ ^ 2 * x) - dilPot F.qTn x) := by ring
    rw [e2]
    refine (abs_sub _ _).trans ?_
    nlinarith [h1, h2, m1, m2]
  have eR := rForm_sub_rLim_le hs.hτ hs.hRf hs.hRok hxa hρ
  have eR' : |rForm (D N).τ F.R x - rLim F.R x| ≤
      rW F.R * ((1 - (D N).τ) * ρ / (1 - ρ)) := eR
  have eDen : |(((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x| ≤
      Db * |((D N).sp : ℝ) / (D N).ν - σ| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_denPoly_le bL KL hx1) (abs_nonneg _)
  have eCs : |((D N).cs - csL) * (if 1 - θL < x then 1 else 0)| ≤ |(D N).cs - csL| := by
    rw [abs_mul]
    split_ifs <;> simp
  unfold limBoundP at hBN
  have u1 := abs_le.mp (hRfN x hx)
  have u2 := abs_le.mp eLog
  have u3 := abs_le.mp eSa
  have u4 := abs_le.mp eDil
  have u5 := abs_le.mp eR'
  have u6 := abs_le.mp eDen
  have u7 := abs_le.mp eCs
  have key : (D N).Rf x - F.v.Sform x - Real.log (1 - x) / (2 * (D N).ν) +
        ((1 - F.η) / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
        2 * F.a.Sform (-(D N).τ * x) - ((D N).sp : ℝ) / (D N).ν * denPoly bL KL x +
        (F.dilT ((D N).τ ^ 2 * x) + rForm (D N).τ F.R x) + 2 * F.Sup +
        (D N).cs * (if 1 - θL < x then 1 else 0) -
      (RfL x - F.v.Sform x - 2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
        2 * F.a.Sform (-x) - σ * denPoly bL KL x + (F.dilT x + rLim F.R x) + 2 * F.Sup +
        csL * (if 1 - θL < x then 1 else 0)) =
      ((D N).Rf x - RfL x) + rowLogsP (D N).ν (Real.log (1 / (1 - (D N).τ ^ 2))) (1 - F.η) x +
        2 * (F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)) -
        (((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x +
        (F.dilT ((D N).τ ^ 2 * x) - F.dilT x) +
        (rForm (D N).τ F.R x - rLim F.R x) +
        ((D N).cs - csL) * (if 1 - θL < x then 1 else 0) := by
    unfold rowLogsP; ring
  rw [key]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [u1.1, u1.2, u2.1, u2.2, u3.1, u3.2, u4.1, u4.2,
    u5.1, u5.2, u6.1, u6.2, u7.1, u7.2]

/-- **Uniform limit of the column field on a compact cell `[a, b] ⊂ (0, 1)`** (the column field
`Cf s + 2 T_v(s) - log(1-s)/ν`; limit `CfL s + 2 T_v(s)`). -/
theorem fCol_unif {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) {CfL : ℝ → ℝ}
    (hCf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Icc a b, |(D N).Cf s - CfL s| ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Icc a b,
      |(D N).fCol s - (CfL s + 2 * F.v.Tform s)| ≤ ε := by
  intro ε hε
  have h3 : Tendsto (fun N => |Real.log (1 - b)| / (D N).ν) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hf.hν
  have hB : ∀ᶠ N in atTop, |Real.log (1 - b)| / (D N).ν ≤ ε / 2 :=
    h3.eventually (ge_mem_nhds (by linarith))
  have hνpos : ∀ᶠ N in atTop, 0 < (D N).ν := hf.hν.eventually_gt_atTop 0
  filter_upwards [hCf (ε / 2) (by linarith), hB, hνpos] with N hCfN hBN hνN s hs
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [TrialForm.fCol_closed (hf.spec N) hsI]
  have hl : |Real.log (1 - s)| ≤ |Real.log (1 - b)| := by
    have h1 : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith [hsI.2]) (by linarith [hsI.1])
    have h2 : Real.log (1 - b) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have h3 : Real.log (1 - b) ≤ Real.log (1 - s) :=
      Real.log_le_log (by linarith) (by linarith [hs.2])
    rw [abs_of_nonpos h1, abs_of_nonpos h2]; linarith
  have e : |Real.log (1 - s) / (D N).ν| ≤ |Real.log (1 - b)| / (D N).ν := by
    rw [abs_div, abs_of_pos hνN]
    exact div_le_div_of_nonneg_right hl hνN.le
  have u1 := abs_le.mp (hCfN s hs)
  have u2 := abs_le.mp e
  have : (D N).Cf s + 2 * F.v.Tform s - Real.log (1 - s) / (D N).ν -
      (CfL s + 2 * F.v.Tform s) = ((D N).Cf s - CfL s) - Real.log (1 - s) / (D N).ν := by ring
  rw [this]
  exact abs_le.mpr ⟨by linarith [u1.1, u2.2], by linarith [u1.2, u2.1]⟩

/-! ### N. Bridge to the cell checker: per-cell field bounds in the contract's shape -/

theorem le_of_unif {P : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {S : Set ℝ} {T : ℝ}
    (hu : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ S, |P N x - G x| ≤ ε) (hG : ∀ x ∈ S, G x ≤ T) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ S, P N x ≤ T + ε := by
  intro ε hε
  filter_upwards [hu ε hε] with N hN x hx
  have := (abs_le.mp (hN x hx)).2
  linarith [hG x hx]

open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert in
/-- **Per-cell bound for the negative rows.**  If the cell checker accepts `[lo, hi] ⊂ (-1, 0)`
for the generator's field (`fieldTower fq F0 0` = the limit closed form `fNegLim`), then
`∀ ε > 0, ∀ᶠ N, ∀ x ∈ [lo, hi], fNeg (D N) x ≤ T + ε`. -/
theorem rowNeg_cell {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    (fq : FieldQ) (F0 : ℝ → ℝ) (Ls εs : List ℚ) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hlo : (-1 : ℝ) < lo) (hhi : (hi : ℝ) < 0)
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc (lo : ℝ) hi, |(D N).Rf x - RfL x| ≤ ε)
    (hchk : fieldCellCheck fq Ls εs lo hi A0 l1 u1 A2 Bl BM T = true)
    (hLs : LogVals ((lo + hi) / 2) fq.plogs Ls εs)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F0 ((fq.poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : fieldTower fq F0 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |fieldTower fq F0 (Bl.length + 3) x| / (((Bl.length + 3).factorial : ℕ) : ℝ) ≤ (BM : ℝ))
    (hid : ∀ x ∈ Icc (lo : ℝ) hi, fNegLim F RfL x = fieldTower fq F0 0 x) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc (lo : ℝ) hi, (D N).fNeg x ≤ (T : ℝ) + ε := by
  have hsound := fieldCellCheck_sound fq F0 Ls εs lo hi A0 l1 u1 A2 Bl BM T hchk hLs hF h0 blo bhi
    hb1 hb2 hBM
  by_cases hle : (lo : ℝ) ≤ hi
  · refine le_of_unif (fNeg_unif hf hlo hle hhi hRf) fun x hx => ?_
    rw [hid x hx]; exact hsound x hx
  · intro ε hε
    exact Eventually.of_forall fun N x hx => absurd (hx.1.trans hx.2) hle

open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert in
/-- **Per-cell bound for the positive rows (with spike cost)**, cell `[lo, hi] ⊂ (0, 1)`. -/
theorem rowPos_cell {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (fq : FieldQ) (F0 : ℝ → ℝ) (Ls εs : List ℚ) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hlo : (0 : ℝ) < lo) (hhi : (hi : ℝ) < 1)
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc (lo : ℝ) hi, |(D N).Rf x - RfL x| ≤ ε)
    (hchk : fieldCellCheck fq Ls εs lo hi A0 l1 u1 A2 Bl BM T = true)
    (hLs : LogVals ((lo + hi) / 2) fq.plogs Ls εs)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F0 ((fq.poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : fieldTower fq F0 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |fieldTower fq F0 (Bl.length + 3) x| / (((Bl.length + 3).factorial : ℕ) : ℝ) ≤ (BM : ℝ))
    (hid : ∀ x ∈ Icc (lo : ℝ) hi, fPosLim F RfL σ bL KL csL θL x = fieldTower fq F0 0 x) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Icc (lo : ℝ) hi, (D N).fPosS x ≤ (T : ℝ) + ε := by
  have hsound := fieldCellCheck_sound fq F0 Ls εs lo hi A0 l1 u1 A2 Bl BM T hchk hLs hF h0 blo bhi
    hb1 hb2 hBM
  by_cases hle : (lo : ℝ) ≤ hi
  · refine le_of_unif (fPosS_unif hf hlo hle hhi hbL hKL hθL hσ hcs hRf) fun x hx => ?_
    rw [hid x hx]; exact hsound x hx
  · intro ε hε
    exact Eventually.of_forall fun N x hx => absurd (hx.1.trans hx.2) hle

open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert in
/-- **Per-cell bound for the columns**, cell `[lo, hi] ⊂ (0, 1)`. -/
theorem column_cell {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {CfL : ℝ → ℝ}
    (fq : FieldQ) (F0 : ℝ → ℝ) (Ls εs : List ℚ) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ)
    (hlo : (0 : ℝ) < lo) (hhi : (hi : ℝ) < 1)
    (hCf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Icc (lo : ℝ) hi, |(D N).Cf s - CfL s| ≤ ε)
    (hchk : fieldCellCheck fq Ls εs lo hi A0 l1 u1 A2 Bl BM T = true)
    (hLs : LogVals ((lo + hi) / 2) fq.plogs Ls εs)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F0 ((fq.poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : fieldTower fq F0 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |fieldTower fq F0 (Bl.length + 3) x| / (((Bl.length + 3).factorial : ℕ) : ℝ) ≤ (BM : ℝ))
    (hid : ∀ s ∈ Icc (lo : ℝ) hi, CfL s + 2 * F.v.Tform s = fieldTower fq F0 0 s) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Icc (lo : ℝ) hi, (D N).fCol s ≤ (T : ℝ) + ε := by
  have hsound := fieldCellCheck_sound fq F0 Ls εs lo hi A0 l1 u1 A2 Bl BM T hchk hLs hF h0 blo bhi
    hb1 hb2 hBM
  by_cases hle : (lo : ℝ) ≤ hi
  · refine le_of_unif (fCol_unif hf hlo hle hhi hCf) fun x hx => ?_
    rw [hid x hx]; exact hsound x hx
  · intro ε hε
    exact Eventually.of_forall fun N x hx => absurd (hx.1.trans hx.2) hle

/-! ### O. Endpoint cells: one-sided uniform bounds up to `0, ±1` -/

open CatalanMeasure.Signed.ReflectionEnergy in
/-- **Monotonicity of the dilated potential**: `dilPot qs` is nondecreasing on `(0, 1)`
(`-∫ log (1 - c y)` increases with `c`).  Hence `dilPot qs (τ² c) ≤ dilPot qs c`: the
dilation error has the favourable sign all the way to the endpoint `c → 1`. -/
theorem dilPot_mono {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) {C : ℝ}
    (hBD : BD (polyMeas qs) C) {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') (hc' : c' < 1) :
    dilPot qs c ≤ dilPot qs c' := by
  have := hBD.finite
  have e : ∀ d : ℝ, d ≠ 0 → dilPot qs d = -∫ y, Real.log (1 - d * y) ∂(polyMeas qs) := by
    intro d hd
    rw [integral_log_one_sub_polyMeas hqs hd]; rfl
  rw [e c hc.ne', e c' (by linarith)]
  have hI := integrable_log_one_sub_polyMeas hqs hc.ne'
  have hI' := integrable_log_one_sub_polyMeas hqs (by linarith : c' ≠ 0)
  have : ∫ y, Real.log (1 - c' * y) ∂(polyMeas qs) ≤ ∫ y, Real.log (1 - c * y) ∂(polyMeas qs) := by
    refine integral_mono_ae hI' hI ?_
    filter_upwards [hBD.ae_mem] with y hy
    have h1 : 0 < 1 - c' * y := by nlinarith [hy.1, hy.2]
    exact Real.log_le_log h1 (by nlinarith [hy.1, hy.2])
  linarith

/-- Uniform (up to `|x| ≤ 1`) estimate for the geometric blocks when all poles satisfy
`‖w‖ ≤ ω < 1`. -/
theorem geoForm_sub_geoLim_le' {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {G : Tail}
    (hG : ∀ wr ∈ G, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) {ω : ℝ}
    (hω : ∀ wr ∈ G, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {x : ℝ} (hx1 : |x| ≤ 1) :
    |geoForm τ G x - geoLim G x| ≤
      (G.map (fun wr : ℂ × ℂ => ‖wr.2‖)).sum * ((1 - τ) / (1 - ω)) := by
  rw [geoForm_eq_log hτ hG hx1]
  unfold geoLim
  have key := list_norm_sum_sub G
    (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1)))
    (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1))
    (fun wr => ‖wr.2‖ * ((1 - τ) / (1 - ω))) (by
      intro wr hwr
      have hw := hω wr hwr
      rw [← mul_sub, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hre : ∀ t : ℝ, 0 < t → t ≤ 1 → 1 - ω ≤ (1 - (x : ℂ) * ((t : ℂ) * wr.1)).re := by
        intro t ht0 ht1
        have : ((x : ℂ) * ((t : ℂ) * wr.1)).re ≤ ω := by
          calc ((x : ℂ) * ((t : ℂ) * wr.1)).re ≤ ‖(x : ℂ) * ((t : ℂ) * wr.1)‖ :=
                Complex.re_le_norm _
            _ = |x| * (t * ‖wr.1‖) := by
                rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                  Real.norm_eq_abs, abs_of_pos ht0]
            _ ≤ 1 * (1 * ω) := by
                gcongr
            _ = ω := by ring
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have h1 := hre τ hτ.1 hτ.2.le
      have h2 := hre 1 one_pos le_rfl
      simp only [Complex.ofReal_one, one_mul] at h2
      have := norm_clog_sub_le (by linarith : 0 < 1 - ω) h1 h2
      refine this.trans ?_
      have e : (1 - (x : ℂ) * ((τ : ℂ) * wr.1)) - (1 - (x : ℂ) * wr.1) =
          ((x * (1 - τ) : ℝ) : ℂ) * wr.1 := by push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by linarith [hτ.2] : 0 < 1 - τ)]
      rw [div_le_div_iff_of_pos_right (by linarith)]
      calc |x| * (1 - τ) * ‖wr.1‖ ≤ 1 * (1 - τ) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hx1 (by linarith [hτ.2]))
              (hw.trans hω1.le) (norm_nonneg _) (by linarith [hτ.2])
        _ = 1 - τ := by ring)
  rw [List.sum_map_mul_right] at key
  have h3 : |(-(List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1))) G).sum.re) -
      (-(List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1)) G).sum.re)| ≤
      ‖(List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * ((τ : ℂ) * wr.1))) G).sum -
        (List.map (fun wr : ℂ × ℂ => wr.2 * Complex.log (1 - (x : ℂ) * wr.1)) G).sum‖ := by
    rw [show ∀ a b : ℝ, -a - -b = -(a - b) from fun a b => by ring, abs_neg, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  exact h3.trans key

/-- One-sided bound of the logarithmic terms of a negative row, up to the endpoints:
`rowLogs ≤ (-log|x|)/ν + 2 c0/ν` on `(-1, 0)`. -/
theorem rowLogs_le_neg {ν τ c0 κ x : ℝ} (hν : 0 < ν) (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hc0 : c0 = Real.log (1 / (1 - τ ^ 2))) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hx : x ∈ Ioo (-1 : ℝ) 0) :
    rowLogs ν τ c0 κ x ≤ (-Real.log |x|) / ν + 2 * c0 / ν := by
  have h2ν : 0 < 2 * ν := by positivity
  have hτ2 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hx2 : (τ * x) * (τ * x) ≤ τ ^ 2 := by
    have : (τ * x) * (τ * x) = τ ^ 2 * x ^ 2 := by ring
    rw [this]
    have hx21 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    calc τ ^ 2 * x ^ 2 ≤ τ ^ 2 * 1 := mul_le_mul_of_nonneg_left hx21 (sq_nonneg τ)
      _ = τ ^ 2 := mul_one _
  have hlogA : Real.log (1 - x) ≥ 0 := Real.log_nonneg (by linarith [hx.2])
  have hlogC : Real.log (1 - τ ^ 2) ≤ Real.log (1 - (τ * x) * (τ * x)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hc0' : c0 = -Real.log (1 - τ ^ 2) := by
    rw [hc0, one_div, Real.log_inv]
  unfold rowLogs
  have t1 : -Real.log (1 - x) / (2 * ν) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) h2ν.le
  have t3 : -((1 / (2 * ν)) * Real.log (1 - (τ * x) * (τ * x))) ≤ c0 / (2 * ν) := by
    have : -(Real.log (1 - (τ * x) * (τ * x))) ≤ c0 := by linarith
    calc -((1 / (2 * ν)) * Real.log (1 - (τ * x) * (τ * x)))
        = (1 / (2 * ν)) * (-(Real.log (1 - (τ * x) * (τ * x)))) := by ring
      _ ≤ (1 / (2 * ν)) * c0 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = c0 / (2 * ν) := by ring
  have hc0nn : 0 ≤ c0 := by rw [hc0]; exact Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; nlinarith)
  have hX : 0 ≤ -Real.log |x| + c0 := by
    have := Real.log_nonpos (abs_nonneg x) (abs_lt.mpr ⟨hx.1, by linarith [hx.2]⟩).le
    linarith
  have hk : (κ / ν) * (-Real.log |x| + c0) ≤ (1 / ν) * (-Real.log |x| + c0) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hκ1 hν.le) hX
  have e : (1 / ν) * (-Real.log |x| + c0) = (-Real.log |x|) / ν + c0 / ν := by ring
  have : c0 / (2 * ν) ≤ c0 / ν := div_le_div_of_nonneg_left hc0nn hν (by linarith)
  have : 2 * c0 / ν = c0 / ν + c0 / ν := by ring
  nlinarith [e, t1, t3, this, hk]

/-- **Block estimate for the tilt** on `[-1, 1]`, poles of the tail in `‖w‖ ≤ ω < 1`. -/
theorem rForm_sub_rLim_le' {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {d : SeqForm}
    (hf : ∀ k, d.L < k → d.f k = 0)
    (hG : ∀ wr ∈ d.tail, ‖wr.1‖ ≤ 1 ∧ wr.1 ≠ 0 ∧ (wr.1.im ≠ 0 ∨ wr.2.im = 0)) {ω : ℝ}
    (hω : ∀ wr ∈ d.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {x : ℝ} (hx1 : |x| ≤ 1) :
    |rForm τ d x - rLim d x| ≤ rW d * ((1 - τ) / (1 - ω)) := by
  have _ := hf
  have h1 := finS_dil_sub_le d.f d.L hτ hx1
  have h2 := geoForm_sub_geoLim_le' hτ hG hω hω1 hω0 hx1
  have hω0' : 0 < 1 - ω := by linarith
  have h1τ : 0 ≤ 1 - τ := by linarith [hτ.2]
  have hq : (1 - τ) * |x| ≤ (1 - τ) / (1 - ω) := by
    have hle : 1 ≤ 1 / (1 - ω) := by
      rw [le_div_iff₀ hω0']; linarith
    calc (1 - τ) * |x| ≤ (1 - τ) * 1 := mul_le_mul_of_nonneg_left hx1 h1τ
      _ ≤ (1 - τ) * (1 / (1 - ω)) := mul_le_mul_of_nonneg_left hle h1τ
      _ = (1 - τ) / (1 - ω) := by ring
  have hS : 0 ≤ ∑ k ∈ Finset.range d.L, |d.f (k + 1)| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have h3 := mul_le_mul_of_nonneg_left hq hS
  unfold rForm rLim rW
  have e : finS d.f d.L (τ * x) + geoForm τ d.tail x - (finS d.f d.L x + geoLim d.tail x) =
      (finS d.f d.L (τ * x) - finS d.f d.L x) + (geoForm τ d.tail x - geoLim d.tail x) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  nlinarith [h1, h2, h3]

/-- The error bound of the one-sided endpoint estimates (no `Rf`, no unbounded log term). -/
def limBoundE (F : TrialForm) (S ν τ c0 ω : ℝ) : ℝ :=
  2 * c0 / ν + 2 * (S * (1 - τ)) +
    rW F.R * ((1 - τ) / (1 - ω))

theorem tendsto_limBoundE {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) (S ω : ℝ) :
    Tendsto (fun N => limBoundE F S (D N).ν (D N).τ (Real.log (1 / (1 - (D N).τ ^ 2))) ω)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
  have h4 : Tendsto (fun N => 2 * Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν) atTop (𝓝 0) := by
    have : Tendsto (fun N => 2 * Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν) atTop (𝓝 (2 * 0)) :=
      (hf.hℓ.const_mul 2).congr (fun N => by ring)
    simpa only [mul_zero] using this
  have h5 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
    simpa using (h1.const_mul S).const_mul 2
  have h6 : Tendsto (fun N => rW F.R *
      ((1 - (D N).τ) / (1 - ω))) atTop (𝓝 0) := by
    simpa using (h1.div_const (1 - ω)).const_mul (rW F.R)
  simpa [limBoundE] using (h4.add h5).add h6

/-- **One-sided uniform estimate on the whole interval `(-1, 0)`**, up to both endpoints, the
only unbounded perturbation being the explicit `(-log|x|)/ν` (sign: positive, as the certificate's
singular treatment requires).  Needs the poles of `R, t` inside `‖w‖ ≤ ω < 1`. -/
theorem fNeg_le_lim {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ} {ω : ℝ}
    (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω)
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (D N).Rf x - RfL x ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (D N).fNeg x ≤ fNegLim F RfL x + (-Real.log |x|) / (D N).ν + ε := by
  intro ε hε
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  have hBt := tendsto_limBoundE hf S ω
  have hB : ∀ᶠ N in atTop, limBoundE F S (D N).ν (D N).τ (Real.log (1 / (1 - (D N).τ ^ 2))) ω
      ≤ ε / 2 := hBt.eventually (ge_mem_nhds (by linarith))
  have hνpos : ∀ᶠ N in atTop, 0 < (D N).ν := hf.hν.eventually_gt_atTop 0
  filter_upwards [hRf (ε / 2) (by linarith), hB, hνpos] with N hRfN hBN hνN x hxI
  have hs := hf.spec N
  have hτN := hs.hτ
  have hx1 : |x| ≤ 1 := TrialForm.abs_le_one_of_mem_Ioo le_rfl (by norm_num) hxI
  rw [TrialForm.fNeg_closed hs hxI]
  unfold fNegLim
  have hκ0 : 0 ≤ 1 - F.η := by linarith [hs.hηI.2]
  have hκ1 : 1 - F.η ≤ 1 := by linarith [hs.hηI.1]
  have eLog := rowLogs_le_neg hνN hτN rfl hκ0 hκ1 hxI
  have eSa : |F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)| ≤ S * (1 - (D N).τ) := by
    rw [← TrialForm.S_a hs (TrialForm.abs_neg_tau_le hs hx1),
      ← TrialForm.S_a hs (by rwa [abs_neg]), hs.ha]
    refine (barrierTrialS_lipschitz hf.hasum (TrialForm.abs_neg_tau_le hs hx1)
      (by rwa [abs_neg])).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun k => abs_nonneg _)
    have : -(D N).τ * x - -x = (1 - (D N).τ) * x := by ring
    rw [this, abs_mul, abs_of_pos (by linarith [hτN.2] : 0 < 1 - (D N).τ)]
    nlinarith [hτN.2, abs_nonneg x]
  have eR := rForm_sub_rLim_le' hs.hτ hs.hRf hs.hRok hωR hω1 hω0 hx1
  unfold limBoundE at hBN
  have u1 := hRfN x hxI
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR
  have key : (D N).Rf x - F.v.Sform x - Real.log (1 - x) / (2 * (D N).ν) +
        ((1 - F.η) / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x -
        (1 / (2 * (D N).ν)) * Real.log (1 - ((D N).τ * x) * ((D N).τ * x)) -
        2 * F.a.Sform (-(D N).τ * x) +
        (-rForm (D N).τ F.R x) -
      (RfL x - F.v.Sform x - 2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x -
        2 * F.a.Sform (-x) + (-rLim F.R x)) =
      ((D N).Rf x - RfL x) +
        rowLogs (D N).ν (D N).τ (Real.log (1 / (1 - (D N).τ ^ 2))) (1 - F.η) x -
        2 * (F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)) -
        (rForm (D N).τ F.R x - rLim F.R x) := by
    unfold rowLogs; ring
  linarith [key, u1, eLog, u3.1, u3.2, u5.1, u5.2]

/-- **Singular cell `(-r, 0)` of the negative rows** (the certificate's `c log|x|` at `0` taken out
of the series, NOTES §13.3): if the limit field satisfies `fNegLim x ≤ Tr + c log|x|` on
`(-r, 0)` with `c > 0` (regular part `≤ Tr`, coefficient of `log|x|` is `c`), then
`fNeg (D N) ≤ Tr + c log r + ε` on `(-r, 0)` for large `N`.  The unbounded perturbation
`(-log|x|)/ν` has the bad sign but is absorbed by `c > 0` once `ν ≥ 1/c`. -/
theorem fNeg_cell_zero {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω)
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (D N).Rf x - RfL x ≤ ε)
    {r Tr c : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hsing : ∀ x ∈ Ioo (-r) 0, fNegLim F RfL x ≤ Tr + c * Real.log |x|) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-r) 0, (D N).fNeg x ≤ Tr + c * Real.log r + ε := by
  intro ε hε
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  have h1 : ∀ᶠ N in atTop, 1 / c ≤ (D N).ν := hf.hν.eventually_ge_atTop (1 / c)
  have h2 : ∀ᶠ N in atTop, |Real.log r| / (D N).ν ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop hf.hν).eventually (ge_mem_nhds (by linarith))
  filter_upwards [fNeg_le_lim hf hωR hω1 hω0 hRf (ε / 2) (by linarith), h1, h2,
    hf.hν.eventually_gt_atTop 0] with N hN hν1 hν2 hνpos x hx
  have hxI : x ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [hx.1], hx.2⟩
  have hxabs : |x| < r := by rw [abs_of_neg hx.2]; linarith [hx.1]
  have hxpos : 0 < |x| := abs_pos.mpr hx.2.ne
  have hlx : Real.log |x| ≤ Real.log r := Real.log_le_log hxpos hxabs.le
  have hcν : 1 / (D N).ν ≤ c := by
    rw [div_le_iff₀ hνpos]
    have := (div_le_iff₀ hc).mp hν1
    linarith
  have h := hN x hxI
  have h3 := hsing x hx
  have h4 : (c - 1 / (D N).ν) * Real.log |x| ≤ (c - 1 / (D N).ν) * Real.log r :=
    mul_le_mul_of_nonneg_left hlx (by linarith)
  have h5 : (c - 1 / (D N).ν) * Real.log r = c * Real.log r + |Real.log r| / (D N).ν := by
    rw [abs_of_neg hlr]; ring
  have h6 : (-Real.log |x|) / (D N).ν = -(1 / (D N).ν) * Real.log |x| := by ring
  linarith

/-- **Singular cell `(-1, hi]` of the negative rows** (the end `x → -1`): no unbounded
perturbation there; a bound `T` for the limit field gives `T + ε` for `fNeg (D N)`. -/
theorem fNeg_cell_one {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω)
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (D N).Rf x - RfL x ≤ ε)
    {hi T : ℝ} (hhi : hi < 0) (hlim : ∀ x ∈ Ioo (-1 : ℝ) hi, fNegLim F RfL x ≤ T) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) hi, (D N).fNeg x ≤ T + ε := by
  intro ε hε
  have h2 : ∀ᶠ N in atTop, |Real.log (-hi)| / (D N).ν ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop hf.hν).eventually (ge_mem_nhds (by linarith))
  filter_upwards [fNeg_le_lim hf hωR hω1 hω0 hRf (ε / 2) (by linarith), h2,
    hf.hν.eventually_gt_atTop 0] with N hN hν2 hνpos x hx
  have hxI : x ∈ Ioo (-1 : ℝ) 0 := ⟨hx.1, by linarith [hx.2]⟩
  have hxpos : 0 < |x| := abs_pos.mpr hxI.2.ne
  have hge : -hi ≤ |x| := by rw [abs_of_neg hxI.2]; linarith [hx.2]
  have hl : -Real.log |x| ≤ |Real.log (-hi)| := by
    have := Real.log_le_log (by linarith : 0 < -hi) hge
    have h0 := neg_abs_le (Real.log (-hi))
    linarith [le_abs_self (Real.log (-hi))]
  have h6 : (-Real.log |x|) / (D N).ν ≤ |Real.log (-hi)| / (D N).ν :=
    div_le_div_of_nonneg_right hl hνpos.le
  have := hN x hxI
  have := hlim x hx
  linarith

/-- **One-sided uniform estimate on the whole interval `(0, 1)`** (positive rows with spike cost):
up to both endpoints, with the explicit unbounded perturbations `(-log x)/ν + (-log(1-x))/(2ν)`. -/
theorem fPosS_le_lim {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (D N).Rf x - RfL x ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
      (D N).fPosS x ≤ fPosLim F RfL σ bL KL csL θL x + (-Real.log |x|) / (D N).ν +
        (-Real.log (1 - x)) / (2 * (D N).ν) + ε := by
  intro ε hε
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  set Db : ℝ := 2 * ∑ i ∈ Finset.range KL, |bL (i + 1)| with hDb
  set CR : ℝ := rW F.R with hCR
  have hBt : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν + 2 * (S * (1 - (D N).τ)) +
      CR * ((1 - (D N).τ) / (1 - ω)) + Db * |((D N).sp : ℝ) / (D N).ν - σ| +
      |(D N).cs - csL| + polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8))) atTop (𝓝 0) := by
    have h9n : Tendsto (fun N => polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8))) atTop
        (𝓝 0) := by
      have hτ2 : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hf.hτ.pow 2)
      simpa using (hτ2.div_const (1 - 1 / 8)).const_mul (polyMass F.qTn)

    have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
    have h5 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
      simpa using (h1.const_mul S).const_mul 2
    have h6 : Tendsto (fun N => Db * |((D N).sp : ℝ) / (D N).ν - σ|) atTop (𝓝 0) := by
      simpa using ((hσ.sub_const σ).abs).const_mul Db
    have h7 : Tendsto (fun N => |(D N).cs - csL|) atTop (𝓝 0) := by
      simpa using (hcs.sub_const csL).abs
    have h8 : Tendsto (fun N => CR * ((1 - (D N).τ) / (1 - ω))) atTop (𝓝 0) := by
      simpa using (h1.div_const (1 - ω)).const_mul CR
    simpa using (((((hf.hℓ.add h5).add h8).add h6).add h7).add h9n)
  have hB : ∀ᶠ N in atTop, Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν + 2 * (S * (1 - (D N).τ)) +
      CR * ((1 - (D N).τ) / (1 - ω)) + Db * |((D N).sp : ℝ) / (D N).ν - σ| +
      |(D N).cs - csL| + polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8)) ≤ ε / 2 :=
    hBt.eventually (ge_mem_nhds (by linarith))
  have hνpos : ∀ᶠ N in atTop, 0 < (D N).ν := hf.hν.eventually_gt_atTop 0
  filter_upwards [hRf (ε / 2) (by linarith), hB, hνpos] with N hRfN hBN hνN x hxI
  have hs := hf.spec N
  have hτN := hs.hτ
  have hx1 : |x| ≤ 1 := TrialForm.abs_le_one_of_mem_Ioo (by norm_num) le_rfl hxI
  rw [TrialForm.fPosS_closed hs hxI, hbL N, hKL N, hθL N]
  unfold fPosLim
  have hc0 : 0 ≤ Real.log (1 / (1 - (D N).τ ^ 2)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by nlinarith [hτN.1, hτN.2])]
    nlinarith [hτN.1, hτN.2]
  have eSa : |F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)| ≤ S * (1 - (D N).τ) := by
    rw [← TrialForm.S_a hs (TrialForm.abs_neg_tau_le hs hx1),
      ← TrialForm.S_a hs (by rwa [abs_neg]), hs.ha]
    refine (barrierTrialS_lipschitz hf.hasum (TrialForm.abs_neg_tau_le hs hx1)
      (by rwa [abs_neg])).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun k => abs_nonneg _)
    have : -(D N).τ * x - -x = (1 - (D N).τ) * x := by ring
    rw [this, abs_mul, abs_of_pos (by linarith [hτN.2] : 0 < 1 - (D N).τ)]
    nlinarith [hτN.2, abs_nonneg x]
  have eDil : F.dilT ((D N).τ ^ 2 * x) - F.dilT x ≤
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8)) := by
    have hBD : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qT) (D N).Cb := by
      have := hs.bd.hP true; rwa [hs.hμT] at this
    have hBDn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qTn) (D N).Cb := by
      have := hs.bd.hN true; rwa [hs.hμTn] at this
    have h1 := dilPot_mono hs.pT hBD (c := (D N).τ ^ 2 * x) (c' := x)
      (mul_pos (pow_pos hτN.1 2) hxI.1)
      (mul_le_of_le_one_left hxI.1.le (by nlinarith [hτN.1, hτN.2])) hxI.2
    have h2 := dilPot_sub_le_supp hs.pTn hBDn (polyMeas_ae_le hs.hTn)
      (by norm_num : (1 / 8 : ℝ) < 1) (c := (D N).τ ^ 2 * x) (c' := x)
      (mul_pos (pow_pos hτN.1 2) hxI.1) (by nlinarith [hτN.1, hτN.2, hxI.2]) hxI.1 hxI.2.le
    have h3 : |(D N).τ ^ 2 * x - x| ≤ 1 - (D N).τ ^ 2 := by
      have e : (D N).τ ^ 2 * x - x = -((1 - (D N).τ ^ 2) * x) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (by nlinarith [hτN.1, hτN.2] : 0 ≤ 1 - (D N).τ ^ 2),
        abs_of_pos hxI.1]
      exact mul_le_of_le_one_right (by nlinarith [hτN.1, hτN.2]) hxI.2.le
    have h4 := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 8)) (polyMass_nonneg hs.pTn)
    unfold TrialForm.dilT
    have h5 := abs_le.mp h2
    nlinarith [h5.1, h5.2, h1, h4]
  have eR := rForm_sub_rLim_le' hs.hτ hs.hRf hs.hRok hωR hω1 hω0 hx1
  have eDen : |(((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x| ≤
      Db * |((D N).sp : ℝ) / (D N).ν - σ| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_denPoly_le bL KL hx1) (abs_nonneg _)
  have eCs : |((D N).cs - csL) * (if 1 - θL < x then 1 else 0)| ≤ |(D N).cs - csL| := by
    rw [abs_mul]
    split_ifs <;> simp
  have u1 := hRfN x hxI
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR
  have u6 := abs_le.mp eDen
  have u7 := abs_le.mp eCs
  have key : (D N).Rf x - F.v.Sform x - Real.log (1 - x) / (2 * (D N).ν) +
        ((1 - F.η) / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) -
        2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
        2 * F.a.Sform (-(D N).τ * x) - ((D N).sp : ℝ) / (D N).ν * denPoly bL KL x +
        (F.dilT ((D N).τ ^ 2 * x) + rForm (D N).τ F.R x) + 2 * F.Sup +
        (D N).cs * (if 1 - θL < x then 1 else 0) -
      (RfL x - F.v.Sform x - 2 * (1 - F.η) * F.refRow x - 4 * F.η * F.p.Tform x +
        2 * F.a.Sform (-x) - σ * denPoly bL KL x + (F.dilT x + rLim F.R x) + 2 * F.Sup +
        csL * (if 1 - θL < x then 1 else 0)) =
      ((D N).Rf x - RfL x) + rowLogsP (D N).ν (Real.log (1 / (1 - (D N).τ ^ 2))) (1 - F.η) x +
        2 * (F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)) -
        (((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x +
        (F.dilT ((D N).τ ^ 2 * x) - F.dilT x) +
        (rForm (D N).τ F.R x - rLim F.R x) +
        ((D N).cs - csL) * (if 1 - θL < x then 1 else 0) := by
    unfold rowLogsP; ring
  have eLogs : rowLogsP (D N).ν (Real.log (1 / (1 - (D N).τ ^ 2))) (1 - F.η) x ≤
      (-Real.log |x|) / (D N).ν + (-Real.log (1 - x)) / (2 * (D N).ν) +
        Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν := by
    have hκ1 : 1 - F.η ≤ 1 := by linarith [hs.hηI.1]
    have hX : 0 ≤ -Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2)) := by
      have := Real.log_nonpos (abs_nonneg x) hx1
      linarith
    have hk : ((1 - F.η) / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) ≤
        (1 / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hκ1 hνN.le) hX
    unfold rowLogsP
    have e1 : (1 / (D N).ν) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) =
        (-Real.log |x|) / (D N).ν + Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν := by ring
    have e2 : -Real.log (1 - x) / (2 * (D N).ν) = (-Real.log (1 - x)) / (2 * (D N).ν) := by ring
    linarith
  linarith [key, eLogs, u1, u3.1, u3.2, eDil, u5.1, u5.2, u6.1, u6.2, u7.1, u7.2]

/-- **Singular cell `(0, r)` of the positive rows** (`c log x` at `0`): from
`fPosLim x ≤ Tr + c log x` (`c > 0`) to `fPosS (D N) ≤ Tr + c log r + ε`. -/
theorem fPosS_cell_zero {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (D N).Rf x - RfL x ≤ ε)
    {r Tr c : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc : 0 < c)
    (hsing : ∀ x ∈ Ioo 0 r, fPosLim F RfL σ bL KL csL θL x ≤ Tr + c * Real.log |x|) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo 0 r, (D N).fPosS x ≤ Tr + c * Real.log r + ε := by
  intro ε hε
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hl1 : Real.log (1 - r) < 0 := Real.log_neg (by linarith) (by linarith)
  have h1 : ∀ᶠ N in atTop, 1 / c ≤ (D N).ν := hf.hν.eventually_ge_atTop (1 / c)
  have h2 : ∀ᶠ N in atTop, (|Real.log r| + |Real.log (1 - r)|) / (D N).ν ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop hf.hν).eventually (ge_mem_nhds (by linarith))
  filter_upwards [fPosS_le_lim hf hωR hω1 hω0 hbL hKL hθL hσ hcs hRf (ε / 2) (by linarith), h1, h2,
    hf.hν.eventually_gt_atTop 0] with N hN hν1 hν2 hνpos x hx
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hxabs : |x| < r := by rw [abs_of_pos hx.1]; exact hx.2
  have hxpos : 0 < |x| := abs_pos.mpr hx.1.ne'
  have hlx : Real.log |x| ≤ Real.log r := Real.log_le_log hxpos hxabs.le
  have hcν : 1 / (D N).ν ≤ c := by
    rw [div_le_iff₀ hνpos]
    have := (div_le_iff₀ hc).mp hν1
    linarith
  have hl2 : -Real.log (1 - x) ≤ |Real.log (1 - r)| := by
    have := Real.log_le_log (by linarith [hx.2] : 0 < 1 - r) (by linarith [hx.2] : 1 - r ≤ 1 - x)
    have h0 := abs_nonneg (Real.log (1 - r))
    rw [abs_of_neg hl1]; linarith
  have h7 : (-Real.log (1 - x)) / (2 * (D N).ν) ≤ |Real.log (1 - r)| / (D N).ν := by
    calc (-Real.log (1 - x)) / (2 * (D N).ν) ≤ |Real.log (1 - r)| / (2 * (D N).ν) :=
          div_le_div_of_nonneg_right hl2 (by positivity)
      _ ≤ |Real.log (1 - r)| / (D N).ν :=
          div_le_div_of_nonneg_left (abs_nonneg _) hνpos (by linarith)
  have h := hN x hxI
  have h3 := hsing x hx
  have h4 : (c - 1 / (D N).ν) * Real.log |x| ≤ (c - 1 / (D N).ν) * Real.log r :=
    mul_le_mul_of_nonneg_left hlx (by linarith)
  have h5 : (c - 1 / (D N).ν) * Real.log r = c * Real.log r + |Real.log r| / (D N).ν := by
    rw [abs_of_neg hlr]; ring
  have h6 : (-Real.log |x|) / (D N).ν = -(1 / (D N).ν) * Real.log |x| := by ring
  have h8 : (|Real.log r| + |Real.log (1 - r)|) / (D N).ν =
      |Real.log r| / (D N).ν + |Real.log (1 - r)| / (D N).ν := by ring
  linarith

/-- **Singular cell `(lo, 1)` of the positive rows** (`c log(1-x)` at `1`): from
`fPosLim x ≤ Tr + c log(1-x)` (`c > 0`) to `fPosS (D N) ≤ Tr + c log(1-lo) + ε`. -/
theorem fPosS_cell_one {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {RfL : ℝ → ℝ}
    {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (D N).Rf x - RfL x ≤ ε)
    {lo Tr c : ℝ} (hlo0 : 0 < lo) (hlo1 : lo < 1) (hc : 0 < c)
    (hsing : ∀ x ∈ Ioo lo 1, fPosLim F RfL σ bL KL csL θL x ≤ Tr + c * Real.log (1 - x)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo lo 1, (D N).fPosS x ≤ Tr + c * Real.log (1 - lo) + ε := by
  intro ε hε
  have hl1 : Real.log (1 - lo) < 0 := Real.log_neg (by linarith) (by linarith)
  have h1 : ∀ᶠ N in atTop, 1 / (2 * c) ≤ (D N).ν := hf.hν.eventually_ge_atTop (1 / (2 * c))
  have h2 : ∀ᶠ N in atTop, (|Real.log lo| + |Real.log (1 - lo)|) / (D N).ν ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop hf.hν).eventually (ge_mem_nhds (by linarith))
  filter_upwards [fPosS_le_lim hf hωR hω1 hω0 hbL hKL hθL hσ hcs hRf (ε / 2) (by linarith), h1, h2,
    hf.hν.eventually_gt_atTop 0] with N hN hν1 hν2 hνpos x hx
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hxpos : 0 < 1 - x := by linarith [hx.2]
  have hlx : Real.log (1 - x) ≤ Real.log (1 - lo) :=
    Real.log_le_log hxpos (by linarith [hx.1])
  have hcν : 1 / (2 * (D N).ν) ≤ c := by
    have h2c : 0 < 2 * c := by linarith
    have := (div_le_iff₀ h2c).mp hν1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h4 : (c - 1 / (2 * (D N).ν)) * Real.log (1 - x) ≤
      (c - 1 / (2 * (D N).ν)) * Real.log (1 - lo) :=
    mul_le_mul_of_nonneg_left hlx (by linarith)
  have h5 : (c - 1 / (2 * (D N).ν)) * Real.log (1 - lo) =
      c * Real.log (1 - lo) + |Real.log (1 - lo)| / (2 * (D N).ν) := by
    rw [abs_of_neg hl1]; ring
  have h6 : (-Real.log (1 - x)) / (2 * (D N).ν) = -(1 / (2 * (D N).ν)) * Real.log (1 - x) := by
    ring
  have hxabs : |x| = x := abs_of_pos hxI.1
  have hl2 : -Real.log |x| ≤ |Real.log lo| := by
    rw [hxabs]
    have := Real.log_le_log hlo0 hx.1.le
    have h0 := neg_abs_le (Real.log lo)
    linarith [le_abs_self (Real.log lo)]
  have h7 : (-Real.log |x|) / (D N).ν ≤ |Real.log lo| / (D N).ν :=
    div_le_div_of_nonneg_right hl2 hνpos.le
  have h9 : |Real.log (1 - lo)| / (2 * (D N).ν) ≤ |Real.log (1 - lo)| / (D N).ν :=
    div_le_div_of_nonneg_left (abs_nonneg _) hνpos (by linarith)
  have h8 : (|Real.log lo| + |Real.log (1 - lo)|) / (D N).ν =
      |Real.log lo| / (D N).ν + |Real.log (1 - lo)| / (D N).ν := by ring
  have h := hN x hxI
  have h3 := hsing x hx
  linarith

/-- Block: the `S_a` argument shift, uniform on `|x| ≤ 1`. -/
theorem Sa_block {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) (N : ℕ) {x : ℝ}
    (hx1 : |x| ≤ 1) :
    |F.a.Sform (-(D N).τ * x) - F.a.Sform (-x)| ≤
      (∑' k, |tseq F.a.f F.a.tail k|) * (1 - (D N).τ) := by
  have hs := hf.spec N
  have hτN := hs.hτ
  rw [← TrialForm.S_a hs (TrialForm.abs_neg_tau_le hs hx1),
    ← TrialForm.S_a hs (by rwa [abs_neg]), hs.ha]
  refine (barrierTrialS_lipschitz hf.hasum (TrialForm.abs_neg_tau_le hs hx1)
    (by rwa [abs_neg])).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (tsum_nonneg fun k => abs_nonneg _)
  have : -(D N).τ * x - -x = (1 - (D N).τ) * x := by ring
  rw [this, abs_mul, abs_of_pos (by linarith [hτN.2] : 0 < 1 - (D N).τ)]
  nlinarith [hτN.2, abs_nonneg x]

theorem c0_nonneg {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) : 0 ≤ Real.log (1 / (1 - τ ^ 2)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by nlinarith [hτ.1, hτ.2])]
  nlinarith [hτ.1, hτ.2]

/-- **Singular cell `(0, r)` of the columns** (no unbounded perturbation at `0`). -/
theorem fCol_cell_zero {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {CfL : ℝ → ℝ}
    (hCf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (D N).Cf s - CfL s ≤ ε)
    {r T : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hlim : ∀ s ∈ Ioo 0 r, CfL s + 2 * F.v.Tform s ≤ T) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Ioo 0 r, (D N).fCol s ≤ T + ε := by
  intro ε hε
  have h2 : ∀ᶠ N in atTop, |Real.log (1 - r)| / (D N).ν ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop hf.hν).eventually (ge_mem_nhds (by linarith))
  filter_upwards [hCf (ε / 2) (by linarith), h2, hf.hν.eventually_gt_atTop 0] with N hC hν2 hνpos
    s hs
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  rw [TrialForm.fCol_closed (hf.spec N) hsI]
  have hl : -Real.log (1 - s) ≤ |Real.log (1 - r)| := by
    have := Real.log_le_log (by linarith : 0 < 1 - r) (by linarith [hs.2] : 1 - r ≤ 1 - s)
    have h0 := neg_abs_le (Real.log (1 - r))
    linarith [le_abs_self (Real.log (1 - r))]
  have h7 : (-Real.log (1 - s)) / (D N).ν ≤ |Real.log (1 - r)| / (D N).ν :=
    div_le_div_of_nonneg_right hl hνpos.le
  have e := neg_div (D N).ν (Real.log (1 - s))
  have := hC s hsI
  have := hlim s hs
  linarith

/-- **Singular cell `(lo, 1)` of the columns** (`c log(1-s)` at `1`, `c > 0`). -/
theorem fCol_cell_one {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {CfL : ℝ → ℝ}
    (hCf : ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (D N).Cf s - CfL s ≤ ε)
    {lo Tr c : ℝ} (hlo0 : 0 < lo) (hlo1 : lo < 1) (hc : 0 < c)
    (hsing : ∀ s ∈ Ioo lo 1, CfL s + 2 * F.v.Tform s ≤ Tr + c * Real.log (1 - s)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ s ∈ Ioo lo 1, (D N).fCol s ≤ Tr + c * Real.log (1 - lo) + ε := by
  intro ε hε
  have hl1 : Real.log (1 - lo) < 0 := Real.log_neg (by linarith) (by linarith)
  have h1 : ∀ᶠ N in atTop, 1 / c ≤ (D N).ν := hf.hν.eventually_ge_atTop (1 / c)
  have h2 : ∀ᶠ N in atTop, |Real.log (1 - lo)| / (D N).ν ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop hf.hν).eventually (ge_mem_nhds (by linarith))
  filter_upwards [hCf (ε / 2) (by linarith), h1, h2, hf.hν.eventually_gt_atTop 0] with N hC hν1
    hν2 hνpos s hs
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  rw [TrialForm.fCol_closed (hf.spec N) hsI]
  have hxpos : 0 < 1 - s := by linarith [hs.2]
  have hlx : Real.log (1 - s) ≤ Real.log (1 - lo) := Real.log_le_log hxpos (by linarith [hs.1])
  have hcν : 1 / (D N).ν ≤ c := by
    rw [div_le_iff₀ hνpos]
    have := (div_le_iff₀ hc).mp hν1
    linarith
  have h4 : (c - 1 / (D N).ν) * Real.log (1 - s) ≤ (c - 1 / (D N).ν) * Real.log (1 - lo) :=
    mul_le_mul_of_nonneg_left hlx (by linarith)
  have h5 : (c - 1 / (D N).ν) * Real.log (1 - lo) =
      c * Real.log (1 - lo) + |Real.log (1 - lo)| / (D N).ν := by
    rw [abs_of_neg hl1]; ring
  have h6 : -Real.log (1 - s) / (D N).ν = -(1 / (D N).ν) * Real.log (1 - s) := by ring
  have e := neg_div (D N).ν (Real.log (1 - s))
  have := hC s hsI
  have := hsing s hs
  linarith

/-! ### P. Fixed-node fields (`fNegM`, `fPosMS`, `fPosMR`) -/

/-- The limit form of the first-kind fixed negative node field. -/
def fNegMLim (F : TrialForm) (RmL : ℝ → ℝ) (x : ℝ) : ℝ :=
  RmL x - (1 - F.η) * F.refRow x - 2 * F.η * F.p.Tform x - 2 * F.a.Sform (-x) +
    (-rLim F.R x)

/-- **One-sided uniform estimate for `fNegM` on all of `(-1, 0)`.** -/
theorem fNegM_le_lim {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rm : ℕ → ℝ → ℝ}
    {RmL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω)
    (hω1 : ω < 1) (hω0 : 0 ≤ ω)
    (hRm : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, Rm N x - RmL x ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
      (D N).fNegM (Rm N) x ≤ fNegMLim F RmL x + (-Real.log |x|) / (2 * (D N).ν) + ε := by
  intro ε hε
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  have hBt := tendsto_limBoundE hf S ω
  have hB : ∀ᶠ N in atTop, limBoundE F S (D N).ν (D N).τ (Real.log (1 / (1 - (D N).τ ^ 2))) ω
      ≤ ε / 2 := hBt.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hRm (ε / 2) (by linarith), hB, hf.hν.eventually_gt_atTop 0] with N hRmN hBN hνN
    x hxI
  have hs := hf.spec N
  have hτN := hs.hτ
  have hx1 : |x| ≤ 1 := TrialForm.abs_le_one_of_mem_Ioo le_rfl (by norm_num) hxI
  rw [TrialForm.fNegM_closed hs (Rm N) hxI]
  unfold fNegMLim
  have hc0 := c0_nonneg hτN
  have hX : 0 ≤ -Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2)) := by
    have := Real.log_nonpos (abs_nonneg x) hx1
    linarith
  have hk : ((1 - F.η) / (4 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) ≤
      (1 / (2 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) := by
    refine mul_le_mul_of_nonneg_right ?_ hX
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs.hηI.1, hνN]
  have eSa := Sa_block hf N hx1
  have eR := rForm_sub_rLim_le' hs.hτ hs.hRf hs.hRok hωR hω1 hω0 hx1
  unfold limBoundE at hBN
  have u1 := hRmN x hxI
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR
  have eL : (1 / (2 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) -
        (1 / (2 * (D N).ν)) * Real.log (1 - ((D N).τ * x) * ((D N).τ * x)) ≤
      (-Real.log |x|) / (2 * (D N).ν) + 2 * Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν := by
    have h2ν : 0 < 2 * (D N).ν := by positivity
    have hτ2 : (D N).τ ^ 2 < 1 := by nlinarith [hτN.1, hτN.2]
    have hx2 : ((D N).τ * x) * ((D N).τ * x) ≤ (D N).τ ^ 2 := by
      have : ((D N).τ * x) * ((D N).τ * x) = (D N).τ ^ 2 * x ^ 2 := by ring
      rw [this]
      have hx21 : x ^ 2 ≤ 1 := by nlinarith [hxI.1, hxI.2]
      calc (D N).τ ^ 2 * x ^ 2 ≤ (D N).τ ^ 2 * 1 := mul_le_mul_of_nonneg_left hx21 (sq_nonneg _)
        _ = (D N).τ ^ 2 := mul_one _
    have hlogC : Real.log (1 - (D N).τ ^ 2) ≤ Real.log (1 - ((D N).τ * x) * ((D N).τ * x)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hc0' : Real.log (1 / (1 - (D N).τ ^ 2)) = -Real.log (1 - (D N).τ ^ 2) := by
      rw [one_div, Real.log_inv]
    have t3 : -(Real.log (1 - ((D N).τ * x) * ((D N).τ * x))) ≤
        Real.log (1 / (1 - (D N).τ ^ 2)) := by linarith
    have e : (1 / (2 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) -
          (1 / (2 * (D N).ν)) * Real.log (1 - ((D N).τ * x) * ((D N).τ * x)) =
        (-Real.log |x|) / (2 * (D N).ν) + (1 / (2 * (D N).ν)) *
          (Real.log (1 / (1 - (D N).τ ^ 2)) + -(Real.log (1 - ((D N).τ * x) * ((D N).τ * x)))) := by
      ring
    rw [e]
    have : (1 / (2 * (D N).ν)) *
          (Real.log (1 / (1 - (D N).τ ^ 2)) + -(Real.log (1 - ((D N).τ * x) * ((D N).τ * x)))) ≤
        (1 / (2 * (D N).ν)) * (2 * Real.log (1 / (1 - (D N).τ ^ 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : (1 / (2 * (D N).ν)) * (2 * Real.log (1 / (1 - (D N).τ ^ 2))) =
        Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν := by field_simp
    have e3 : 2 * Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν =
        Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν + Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν := by
      ring
    have : 0 ≤ Real.log (1 / (1 - (D N).τ ^ 2)) / (D N).ν := div_nonneg hc0 hνN.le
    linarith
  linarith [u1, eL, u3.1, u3.2, u5.1, u5.2, hk]

/-- **Cell `(-1, hi]` of the first-kind fixed negative nodes** (SigmaCap's range
`x ≤ -g*`): a limit bound `T` gives `fNegM (D N) ≤ T + ε`. -/
theorem fNegM_cell_one {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rm : ℕ → ℝ → ℝ}
    {RmL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω)
    (hω1 : ω < 1) (hω0 : 0 ≤ ω)
    (hRm : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, Rm N x - RmL x ≤ ε)
    {hi T : ℝ} (hhi : hi < 0) (hlim : ∀ x ∈ Ioo (-1 : ℝ) hi, fNegMLim F RmL x ≤ T) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (-1 : ℝ) hi, (D N).fNegM (Rm N) x ≤ T + ε := by
  intro ε hε
  have h2 : ∀ᶠ N in atTop, |Real.log (-hi)| / (2 * (D N).ν) ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop (hf.hν.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually
      (ge_mem_nhds (by linarith))
  filter_upwards [fNegM_le_lim hf hωR hω1 hω0 hRm (ε / 2) (by linarith), h2,
    hf.hν.eventually_gt_atTop 0] with N hN hν2 hνpos x hx
  have hxI : x ∈ Ioo (-1 : ℝ) 0 := ⟨hx.1, by linarith [hx.2]⟩
  have hge : -hi ≤ |x| := by rw [abs_of_neg hxI.2]; linarith [hx.2]
  have hl : -Real.log |x| ≤ |Real.log (-hi)| := by
    have := Real.log_le_log (by linarith : 0 < -hi) hge
    linarith [le_abs_self (Real.log (-hi)), neg_abs_le (Real.log (-hi))]
  have h6 : (-Real.log |x|) / (2 * (D N).ν) ≤ |Real.log (-hi)| / (2 * (D N).ν) :=
    div_le_div_of_nonneg_right hl (by positivity)
  have := hN x hxI
  have := hlim x hx
  linarith

/-- The limit form of the first-kind fixed positive node field with spike cost. -/
def fPosMSLim (F : TrialForm) (RmL : ℝ → ℝ) (σ : ℝ) (bL : ℕ → ℝ) (KL : ℕ) (csL θL : ℝ)
    (x : ℝ) : ℝ :=
  RmL x - (1 - F.η) * F.refRow x - 2 * F.η * F.p.Tform x + 2 * F.a.Sform (-x) -
    σ * denPoly bL KL x + (F.dilT x + rLim F.R x) + 2 * F.Sup + csL * (if 1 - θL < x then 1 else 0)

/-- **Cell `(lo, hi) ⊂ (0, 1]` of the fixed positive nodes with spike cost** (SigmaCap's
`[g*, x_c)` and the top cell `[x_c, 1)`): a limit bound `T` gives `fPosMS (D N) ≤ T + ε`. -/
theorem fPosMS_cell {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rm : ℕ → ℝ → ℝ}
    {RmL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ}
    {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRm : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, Rm N x - RmL x ≤ ε)
    {lo hi : ℝ} {Tf : ℝ → ℝ} (hlo : 0 < lo) (hhi : hi ≤ 1)
    (hlim : ∀ x ∈ Ioo lo hi, fPosMSLim F RmL σ bL KL csL θL x ≤ Tf x) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo lo hi, (D N).fPosMS (Rm N) x ≤ Tf x + ε := by
  intro ε hε
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  set Db : ℝ := 2 * ∑ i ∈ Finset.range KL, |bL (i + 1)| with hDb
  set CR : ℝ := rW F.R with hCR
  have hBt : Tendsto (fun N => (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) / (2 * (D N).ν) +
      2 * (S * (1 - (D N).τ)) + CR * ((1 - (D N).τ) / (1 - ω)) +
      Db * |((D N).sp : ℝ) / (D N).ν - σ| + |(D N).cs - csL| +
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8))) atTop (𝓝 0) := by
    have h9n : Tendsto (fun N => polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8))) atTop
        (𝓝 0) := by
      have hτ2 : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hf.hτ.pow 2)
      simpa using (hτ2.div_const (1 - 1 / 8)).const_mul (polyMass F.qTn)

    have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
    have h5 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
      simpa using (h1.const_mul S).const_mul 2
    have h6 : Tendsto (fun N => Db * |((D N).sp : ℝ) / (D N).ν - σ|) atTop (𝓝 0) := by
      simpa using ((hσ.sub_const σ).abs).const_mul Db
    have h7 : Tendsto (fun N => |(D N).cs - csL|) atTop (𝓝 0) := by
      simpa using (hcs.sub_const csL).abs
    have h8 : Tendsto (fun N => CR * ((1 - (D N).τ) / (1 - ω))) atTop (𝓝 0) := by
      simpa using (h1.div_const (1 - ω)).const_mul CR
    have h9 : Tendsto (fun N => (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) /
        (2 * (D N).ν)) atTop (𝓝 0) := by
      have a1 : Tendsto (fun N => |Real.log lo| / (2 * (D N).ν)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (hf.hν.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      have a2 : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν)) atTop
          (𝓝 0) := by
        have : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν)) atTop
            (𝓝 ((1 / 2 : ℝ) * 0)) :=
          (hf.hℓ.const_mul (1 / 2 : ℝ)).congr (fun N => by ring)
        simpa only [mul_zero] using this
      simpa [add_div] using a1.add a2
    simpa using (((((h9.add h5).add h8).add h6).add h7).add h9n)
  have hB : ∀ᶠ N in atTop, (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) / (2 * (D N).ν) +
      2 * (S * (1 - (D N).τ)) + CR * ((1 - (D N).τ) / (1 - ω)) +
      Db * |((D N).sp : ℝ) / (D N).ν - σ| + |(D N).cs - csL| +
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8)) ≤ ε / 2 :=
    hBt.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hRm (ε / 2) (by linarith), hB, hf.hν.eventually_gt_atTop 0] with N hRmN hBN hνN
    x hx
  have hs := hf.spec N
  have hτN := hs.hτ
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hx1 : |x| ≤ 1 := TrialForm.abs_le_one_of_mem_Ioo (by norm_num) le_rfl hxI
  rw [TrialForm.fPosMS_closed hs (Rm N) hxI, hbL N, hKL N, hθL N]
  have hc0 := c0_nonneg hτN
  have eSa := Sa_block hf N hx1
  have eDil : F.dilT ((D N).τ ^ 2 * x) - F.dilT x ≤
      polyMass F.qTn * ((1 - (D N).τ ^ 2) / (1 - 1 / 8)) := by
    have hBD : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qT) (D N).Cb := by
      have := hs.bd.hP true; rwa [hs.hμT] at this
    have hBDn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qTn) (D N).Cb := by
      have := hs.bd.hN true; rwa [hs.hμTn] at this
    have h1 := dilPot_mono hs.pT hBD (c := (D N).τ ^ 2 * x) (c' := x)
      (mul_pos (pow_pos hτN.1 2) hxI.1)
      (mul_le_of_le_one_left hxI.1.le (by nlinarith [hτN.1, hτN.2])) hxI.2
    have h2 := dilPot_sub_le_supp hs.pTn hBDn (polyMeas_ae_le hs.hTn)
      (by norm_num : (1 / 8 : ℝ) < 1) (c := (D N).τ ^ 2 * x) (c' := x)
      (mul_pos (pow_pos hτN.1 2) hxI.1) (by nlinarith [hτN.1, hτN.2, hxI.2]) hxI.1 hxI.2.le
    have h3 : |(D N).τ ^ 2 * x - x| ≤ 1 - (D N).τ ^ 2 := by
      have e : (D N).τ ^ 2 * x - x = -((1 - (D N).τ ^ 2) * x) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (by nlinarith [hτN.1, hτN.2] : 0 ≤ 1 - (D N).τ ^ 2),
        abs_of_pos hxI.1]
      exact mul_le_of_le_one_right (by nlinarith [hτN.1, hτN.2]) hxI.2.le
    have h4 := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 8)) (polyMass_nonneg hs.pTn)
    unfold TrialForm.dilT
    have h5 := abs_le.mp h2
    nlinarith [h5.1, h5.2, h1, h4]
  have eR := rForm_sub_rLim_le' hs.hτ hs.hRf hs.hRok hωR hω1 hω0 hx1
  have eDen : |(((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x| ≤
      Db * |((D N).sp : ℝ) / (D N).ν - σ| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_denPoly_le bL KL hx1) (abs_nonneg _)
  have eCs : |((D N).cs - csL) * (if 1 - θL < x then 1 else 0)| ≤ |(D N).cs - csL| := by
    rw [abs_mul]
    split_ifs <;> simp
  have hl : -Real.log |x| ≤ |Real.log lo| := by
    rw [abs_of_pos hxI.1]
    have := Real.log_le_log hlo hx.1.le
    linarith [le_abs_self (Real.log lo), neg_abs_le (Real.log lo)]
  have eL : ((1 - F.η) / (4 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) ≤
      (|Real.log lo| + Real.log (1 / (1 - (D N).τ ^ 2))) / (2 * (D N).ν) := by
    have hX : 0 ≤ -Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2)) := by
      have := Real.log_nonpos (abs_nonneg x) hx1
      linarith
    have hk : ((1 - F.η) / (4 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) ≤
        (1 / (2 * (D N).ν)) * (-Real.log |x| + Real.log (1 / (1 - (D N).τ ^ 2))) := by
      refine mul_le_mul_of_nonneg_right ?_ hX
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hs.hηI.1, hνN]
    refine hk.trans ?_
    rw [one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have u1 := hRmN x hxI
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR
  have u6 := abs_le.mp eDen
  have u7 := abs_le.mp eCs
  have h := hlim x hx
  unfold fPosMSLim at h
  linarith [u1, eL, u3.1, u3.2, eDil, u5.1, u5.2, u6.1, u6.2, u7.1, u7.2]

/-- `fPosMR` cell: the remainder `rc α (-log(1-x²))` is N-independent, so it carries over. -/
theorem fPosMR_cell {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rm : ℕ → ℝ → ℝ}
    {RmL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ}
    {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRm : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, Rm N x - RmL x ≤ ε)
    (rc α : ℝ) {lo hi T : ℝ} (hlo : 0 < lo) (hhi : hi ≤ 1)
    (hlim : ∀ x ∈ Ioo lo hi, fPosMSLim F RmL σ bL KL csL θL x + rc * α * (-Real.log (1 - x ^ 2)) ≤ T) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo lo hi, (D N).fPosMR (Rm N) rc α x ≤ T + ε := by
  intro ε hε
  have h := fPosMS_cell hf hωR hω1 hω0 hbL hKL hθL hσ hcs hRm hlo hhi
    (Tf := fun x => T - rc * α * (-Real.log (1 - x ^ 2))) (fun x hx => by
      have := hlim x hx
      linarith) ε hε
  filter_upwards [h] with N hN x hx
  have := hN x hx
  unfold SignedData.fPosMR
  linarith

open CatalanMeasure.Signed.ReflectionEnergy in
/-- Block estimate for the dilated potential at **negative** arguments (`1 - c y ≥ 1`):
`|dilPot qs c - dilPot qs c'| ≤ m(ℝ) |c - c'|`. -/
theorem dilPot_sub_le_neg {qs : List Piece} (hqs : ∀ q ∈ qs, PieceOK q) {C : ℝ}
    (hBD : BD (polyMeas qs) C) {c c' : ℝ} (hc : c < 0) (hc' : c' < 0) :
    |dilPot qs c - dilPot qs c'| ≤ polyMass qs * |c - c'| := by
  have := hBD.finite
  have e : ∀ d : ℝ, d ≠ 0 → dilPot qs d = -∫ y, Real.log (1 - d * y) ∂(polyMeas qs) := by
    intro d hd
    rw [integral_log_one_sub_polyMeas hqs hd]; rfl
  rw [e c hc.ne, e c' hc'.ne]
  have hI := integrable_log_one_sub_polyMeas hqs hc.ne
  have hI' := integrable_log_one_sub_polyMeas hqs hc'.ne
  have h1 : -∫ y, Real.log (1 - c * y) ∂(polyMeas qs) - -∫ y, Real.log (1 - c' * y) ∂(polyMeas qs)
      = ∫ y, (Real.log (1 - c' * y) - Real.log (1 - c * y)) ∂(polyMeas qs) := by
    rw [integral_sub hI' hI]; ring
  rw [h1]
  have hb : ∀ᵐ y ∂(polyMeas qs), ‖Real.log (1 - c' * y) - Real.log (1 - c * y)‖ ≤ |c - c'| := by
    filter_upwards [hBD.ae_mem] with y hy
    have hs : 1 ≤ 1 - c * y := by nlinarith [hy.1]
    have hs' : 1 ≤ 1 - c' * y := by nlinarith [hy.1]
    rw [Real.norm_eq_abs]
    refine (abs_log_sub_le one_pos hs' hs).trans ?_
    rw [div_one]
    have : (1 - c' * y) - (1 - c * y) = (c - c') * y := by ring
    rw [this, abs_mul, abs_of_nonneg hy.1.le]
    calc |c - c'| * y ≤ |c - c'| * 1 := by gcongr; exact hy.2.le
      _ = |c - c'| := mul_one _
  have h2 := norm_integral_le_of_norm_le_const hb
  have h3 : (polyMeas qs).real univ = polyMass qs := by
    have := integral_const_polyMeas hqs
    rw [integral_const, smul_eq_mul, mul_one] at this
    exact this
  rw [Real.norm_eq_abs, h3] at h2
  linarith

/-- The limit form of the near-type fixed node field with spike cost (arcsine block dropped by
sign; the cross constant `phConst` vanishes, `phConst_eq_zero`). -/
def fNearMSLim (F : TrialForm) (RnL : ℝ → ℝ) (α β σ : ℝ) (bL : ℕ → ℝ) (KL : ℕ) (csL θL : ℝ)
    (x : ℝ) : ℝ :=
  RnL x + 2 * F.a.Sform (-x) - σ * denPoly bL KL x +
    (rLim F.R x - F.dilF (-x)) + (α / 2) * Real.log (1 + x) +
    (β / (4 * (1 - F.η))) * (-Real.log (1 - x ^ 2)) +
    remC (1 - 2 * F.η) * β * (2 * Real.log 2) + (F.η + α / 2) * Real.log 2 + 2 * F.Sup +
    csL * (if 1 - θL < x then 1 else 0)

theorem tendsto_log_inv_sq {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) :
    Tendsto (fun N => Real.log (1 / (D N).τ ^ 2)) atTop (𝓝 0) := by
  have hc : ContinuousAt (fun t : ℝ => Real.log (1 / t ^ 2)) 1 :=
    ContinuousAt.log (continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)) (by norm_num)
  have := hc.tendsto.comp hf.hτ
  simp only [Function.comp_def, one_pow, div_one, Real.log_one] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **One-sided uniform estimate for the near-type fixed nodes on all of `(0, 1)`**, with the
explicit perturbation `(1/(2ν)) (-log(1-x²))` of the `rS`-coefficient (the arcsine block is dropped
by sign, `β ≥ 0`). -/
theorem fNearMS_le_lim {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rn : ℕ → ℝ → ℝ}
    {RnL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω)
    (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRn : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, Rn N x - RnL x ≤ ε) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo (0 : ℝ) 1,
      (D N).fNearMS (Rn N) α β x ≤ fNearMSLim F RnL α β σ bL KL csL θL x +
        (1 / (2 * (D N).ν)) * (-Real.log (1 - x ^ 2)) + ε := by
  intro ε hε
  set S : ℝ := ∑' k, |tseq F.a.f F.a.tail k| with hS
  set Db : ℝ := 2 * ∑ i ∈ Finset.range KL, |bL (i + 1)| with hDb
  set CR : ℝ := rW F.R with hCR
  set M2 : ℝ := polyMass F.qF + polyMass F.qFn with hM2
  set Bf : ℕ → ℝ := fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν) +
      Real.log (1 / (D N).τ ^ 2) + 2 * (S * (1 - (D N).τ)) +
      CR * ((1 - (D N).τ) / (1 - ω)) +
      M2 * (1 - (D N).τ ^ 2) +
      Db * |((D N).sp : ℝ) / (D N).ν - σ| + |(D N).cs - csL| with hBf
  have hBt : Tendsto Bf atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => 1 - (D N).τ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hf.hτ
    have h2 : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hf.hτ.pow 2)
    have a1 : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν)) atTop (𝓝 0) := by
      have : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν)) atTop
          (𝓝 ((1 / 2 : ℝ) * 0)) := (hf.hℓ.const_mul (1 / 2 : ℝ)).congr (fun N => by ring)
      simpa only [mul_zero] using this
    have a2 := tendsto_log_inv_sq hf
    have a4 : Tendsto (fun N => 2 * (S * (1 - (D N).τ))) atTop (𝓝 0) := by
      simpa using (h1.const_mul S).const_mul 2
    have a5 : Tendsto (fun N => CR * ((1 - (D N).τ) / (1 - ω))) atTop (𝓝 0) := by
      simpa using (h1.div_const (1 - ω)).const_mul CR
    have a6 : Tendsto (fun N => M2 * (1 - (D N).τ ^ 2)) atTop (𝓝 0) := by
      simpa using h2.const_mul M2
    have a7 : Tendsto (fun N => Db * |((D N).sp : ℝ) / (D N).ν - σ|) atTop (𝓝 0) := by
      simpa using ((hσ.sub_const σ).abs).const_mul Db
    have a8 : Tendsto (fun N => |(D N).cs - csL|) atTop (𝓝 0) := by
      simpa using (hcs.sub_const csL).abs
    simpa [hBf] using (((((a1.add a2).add a4).add a5).add a6).add a7).add a8
  have hB : ∀ᶠ N in atTop, Bf N ≤ ε / 2 := hBt.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hRn (ε / 2) (by linarith), hB, hf.hν.eventually_gt_atTop 0] with N hRnN hBN hνN
    α β hβ x hxI
  have hs := hf.spec N
  have hτN := hs.hτ
  have hx1 : |x| ≤ 1 := TrialForm.abs_le_one_of_mem_Ioo (by norm_num) le_rfl hxI
  have hnoarc := TrialForm.fNearM_le_noarc hs (Rn N) α β hβ hxI
  have hb := hbL N
  have hk := hKL N
  have hθ := hθL N
  unfold SignedData.fNearMS
  rw [hb, hk] at hnoarc
  rw [hθ]
  have hc0 := c0_nonneg hτN
  have eSa := Sa_block hf N hx1
  have hxn : 0 < x := hxI.1
  have eR := rForm_sub_rLim_le' hs.hτ hs.hRf hs.hRok hωR hω1 hω0 hx1
  have eDil2 : |F.dilF ((D N).τ ^ 2 * (-x)) - F.dilF (-x)| ≤ M2 * (1 - (D N).τ ^ 2) := by
    have hBD : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qF) (D N).Cb := by
      have := hs.bd.hP false; rwa [hs.hμF] at this
    have hBDn : CatalanMeasure.Signed.ReflectionEnergy.BD (polyMeas F.qFn) (D N).Cb := by
      have := hs.bd.hN false; rwa [hs.hμFn] at this
    have hd : |(D N).τ ^ 2 * -x - -x| ≤ 1 - (D N).τ ^ 2 := by
      have e : (D N).τ ^ 2 * -x - -x = (1 - (D N).τ ^ 2) * x := by ring
      rw [e, abs_mul, abs_of_nonneg (by nlinarith [hτN.1, hτN.2] : 0 ≤ 1 - (D N).τ ^ 2),
        abs_of_pos hxn]
      exact mul_le_of_le_one_right (by nlinarith [hτN.1, hτN.2]) hxI.2.le
    have h1 := dilPot_sub_le_neg hs.pF hBD (c := (D N).τ ^ 2 * (-x)) (c' := -x)
      (by nlinarith [pow_pos hτN.1 2]) (by linarith)
    have h2 := dilPot_sub_le_neg hs.pFn hBDn (c := (D N).τ ^ 2 * (-x)) (c' := -x)
      (by nlinarith [pow_pos hτN.1 2]) (by linarith)
    have m1 := mul_le_mul_of_nonneg_left hd (polyMass_nonneg hs.pF)
    have m2 := mul_le_mul_of_nonneg_left hd (polyMass_nonneg hs.pFn)
    unfold TrialForm.dilF
    have e2 : dilPot F.qF ((D N).τ ^ 2 * -x) - dilPot F.qFn ((D N).τ ^ 2 * -x) -
        (dilPot F.qF (-x) - dilPot F.qFn (-x)) =
        (dilPot F.qF ((D N).τ ^ 2 * -x) - dilPot F.qF (-x)) -
          (dilPot F.qFn ((D N).τ ^ 2 * -x) - dilPot F.qFn (-x)) := by ring
    rw [e2, hM2]
    refine (abs_sub _ _).trans ?_
    nlinarith [h1, h2, m1, m2]
  have eDen : |(((D N).sp : ℝ) / (D N).ν - σ) * denPoly bL KL x| ≤
      Db * |((D N).sp : ℝ) / (D N).ν - σ| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_denPoly_le bL KL hx1) (abs_nonneg _)
  have eCs : |((D N).cs - csL) * (if 1 - θL < x then 1 else 0)| ≤ |(D N).cs - csL| := by
    rw [abs_mul]
    split_ifs <;> simp
  have hlog1x2 : 0 ≤ -Real.log (1 - x ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by nlinarith [hxI.1, hxI.2]) (by nlinarith [sq_nonneg x]))
  have hlogτ : 0 ≤ Real.log (1 / (D N).τ ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (pow_pos hτN.1 2)]
    nlinarith [hτN.1, hτN.2]
  have u1 := hRnN x hxI
  have u3 := abs_le.mp eSa
  have u5 := abs_le.mp eR
  have u5' := abs_le.mp eDil2
  have u6 := abs_le.mp eDen
  have u7 := abs_le.mp eCs
  have hz : (D N).phConst = 0 := TrialForm.phConst_eq_zero hs
  have hBN' := hBN
  simp only [hBf] at hBN'
  unfold fNearMSLim
  have e1 : ((1 - F.η) / (4 * (D N).ν)) * Real.log (1 / (1 - (D N).τ ^ 2)) ≤
      Real.log (1 / (1 - (D N).τ ^ 2)) / (2 * (D N).ν) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs.hηI.1, hνN, hc0, mul_nonneg hc0 hνN.le]
  have e2 : (β / (4 * (1 - F.η)) + 1 / (2 * (D N).ν)) * (-Real.log (1 - x ^ 2)) =
      (β / (4 * (1 - F.η))) * (-Real.log (1 - x ^ 2)) +
        (1 / (2 * (D N).ν)) * (-Real.log (1 - x ^ 2)) := by ring
  have hrc : 0 ≤ remC (1 - 2 * F.η) := by
    unfold remC
    have : 0 < 1 - 2 * F.η := by linarith [hs.hηI.2]
    positivity
  have hip := mul_le_mul_of_nonneg_left (ip_arcPos_le hτN) (mul_nonneg hrc hβ)
  linarith [hnoarc, e1, e2, u1, u3.1, u3.2, u5.1, u5.2, u5'.1, u5'.2, u6.1, u6.2,
    u7.1, u7.2, hz, hip]

/-- **Cell `(lo, hi)`, `0 ≤ lo`, `hi < 1`, of the near-type fixed nodes** (SigmaCap's
`[g*, x_c)`), uniform in `α` and `β ≥ 0`: a limit bound `T α β` gives
`fNearMS (D N) ≤ T α β + ε`. -/
theorem fNearMS_cell {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) {Rn : ℕ → ℝ → ℝ}
    {RnL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω)
    (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRn : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, Rn N x - RnL x ≤ ε)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi < 1) {T : ℝ → ℝ → ℝ}
    (hlim : ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo lo hi,
      fNearMSLim F RnL α β σ bL KL csL θL x ≤ T α β) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo lo hi,
      (D N).fNearMS (Rn N) α β x ≤ T α β + ε := by
  intro ε hε
  have h2 : ∀ᶠ N in atTop, (-Real.log (1 - hi ^ 2)) / (2 * (D N).ν) ≤ ε / 2 :=
    (tendsto_const_nhds.div_atTop
      (hf.hν.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually (ge_mem_nhds (by linarith))
  filter_upwards [fNearMS_le_lim hf hωR hω1 hω0 hbL hKL hθL hσ hcs hRn (ε / 2) (by linarith),
    h2, hf.hν.eventually_gt_atTop 0] with N hN hν2 hνpos α β hβ x hx
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hlo hx.1, hx.2.trans hhi⟩
  have hhi0 : 0 < hi := hxI.1.trans hx.2
  have hx2 : x ^ 2 ≤ hi ^ 2 := by nlinarith [hxI.1, hx.2]
  have hlog : Real.log (1 - hi ^ 2) ≤ Real.log (1 - x ^ 2) :=
    Real.log_le_log (by nlinarith) (by linarith)
  have h6 : (1 / (2 * (D N).ν)) * (-Real.log (1 - x ^ 2)) ≤
      (-Real.log (1 - hi ^ 2)) / (2 * (D N).ν) := by
    rw [one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have := hN α β hβ x hxI
  have := hlim α β hβ x hx
  linarith

/-- **Top cell `(xc, 1)` of the near-type fixed nodes** with the certificate's explicit
`rS (-log(1-x²))` term (SigmaCap's top-cell hypothesis shape): from
`lim x ≤ gS + r0 (-log(1-x²))` and `r0 + δ ≤ rS` (uniform gap `δ > 0`) to
`fNearMS (D N) ≤ gS + ε + rS (-log(1-x²))`. -/
theorem fNearMS_cell_top {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F)
    {Rn : ℕ → ℝ → ℝ} {RnL : ℝ → ℝ} {ω : ℝ} (hωR : ∀ wr ∈ F.R.tail, ‖wr.1‖ ≤ ω) (hω1 : ω < 1) (hω0 : 0 ≤ ω) {σ csL θL : ℝ} {bL : ℕ → ℝ} {KL : ℕ}
    (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) (hθL : ∀ N, (D N).θ = θL)
    (hσ : Tendsto (fun N => ((D N).sp : ℝ) / (D N).ν) atTop (𝓝 σ))
    (hcs : Tendsto (fun N => (D N).cs) atTop (𝓝 csL))
    (hRn : ∀ ε > 0, ∀ᶠ N in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, Rn N x - RnL x ≤ ε)
    {xc : ℝ} (hxc : 0 ≤ xc) {gS r0 rS : ℝ → ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hr : ∀ α β : ℝ, 0 ≤ β → r0 α β + δ ≤ rS α β)
    (hsing : ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo xc 1,
      fNearMSLim F RnL α β σ bL KL csL θL x ≤ gS α β + r0 α β * (-Real.log (1 - x ^ 2))) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ α β : ℝ, 0 ≤ β → ∀ x ∈ Ioo xc 1,
      (D N).fNearMS (Rn N) α β x ≤ gS α β + ε + rS α β * (-Real.log (1 - x ^ 2)) := by
  intro ε hε
  have h1 : ∀ᶠ N in atTop, 1 / (2 * δ) ≤ (D N).ν := hf.hν.eventually_ge_atTop (1 / (2 * δ))
  filter_upwards [fNearMS_le_lim hf hωR hω1 hω0 hbL hKL hθL hσ hcs hRn ε hε, h1,
    hf.hν.eventually_gt_atTop 0] with N hN h1N hνpos α β hβ x hx
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hxc hx.1, hx.2⟩
  have hL : 0 ≤ -Real.log (1 - x ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by nlinarith [hxI.1, hxI.2]) (by nlinarith [sq_nonneg x]))
  have hgap : 1 / (2 * (D N).ν) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp h1N
    nlinarith
  have h3 : (1 / (2 * (D N).ν)) * (-Real.log (1 - x ^ 2)) ≤ δ * (-Real.log (1 - x ^ 2)) :=
    mul_le_mul_of_nonneg_right hgap hL
  have h4 : (r0 α β + δ) * (-Real.log (1 - x ^ 2)) ≤ rS α β * (-Real.log (1 - x ^ 2)) :=
    mul_le_mul_of_nonneg_right (hr α β hβ) hL
  have := hN α β hβ x hxI
  have := hsing α β hβ x hx
  linarith

/-! ### Q. The decidable form of `hid` for the potential part: computable `FieldQ` of a piece list -/

section Hid

open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert

theorem polyTow_zero_cons (a : ℚ) (as : List ℚ) (x : ℝ) :
    polyTow (a :: as) 0 x = (a : ℝ) + x * polyTow as 0 x := rfl

theorem polyTow_zero_nil (x : ℝ) : polyTow [] 0 x = 0 := rfl

theorem polyTow_zero_vecAdd : ∀ (a b : List ℚ) (x : ℝ),
    polyTow (vecAdd a b) 0 x = polyTow a 0 x + polyTow b 0 x
  | [], b, x => by simp [vecAdd, polyTow_zero_nil]
  | a :: as, [], x => by simp [vecAdd, polyTow_zero_nil]
  | a :: as, b :: bs, x => by
      simp only [vecAdd, polyTow_zero_cons, polyTow_zero_vecAdd as bs x]
      push_cast; ring

theorem polyTow_zero_map_mul (a : ℚ) : ∀ (c : List ℚ) (x : ℝ),
    polyTow (c.map (fun t => a * t)) 0 x = (a : ℝ) * polyTow c 0 x
  | [], x => by simp [polyTow_zero_nil]
  | t :: ts, x => by
      simp only [List.map_cons, polyTow_zero_cons, polyTow_zero_map_mul a ts x]
      push_cast; ring

/-- Coefficients of `(a + b x) · c(x)`. -/
def mulLinQ (a b : ℚ) (c : List ℚ) : List ℚ :=
  vecAdd (c.map (fun t => a * t)) (0 :: c.map (fun t => b * t))

theorem polyTow_zero_mulLinQ (a b : ℚ) (c : List ℚ) (x : ℝ) :
    polyTow (mulLinQ a b c) 0 x = ((a : ℝ) + (b : ℝ) * x) * polyTow c 0 x := by
  unfold mulLinQ
  rw [polyTow_zero_vecAdd, polyTow_zero_map_mul, polyTow_zero_cons, polyTow_zero_map_mul]
  push_cast; ring

/-- A piece with rational data: density coefficients `p` (low to high). -/
structure PieceQ where
  lo : ℚ
  hi : ℚ
  p : List ℚ

/-- The real piece of a rational piece. -/
def PieceQ.toPiece (q : PieceQ) : Piece :=
  ⟨q.lo, q.hi, q.p.length, fun m => (q.p.getD m 0 : ℝ)⟩

/-- Rational coefficient of `x^j` in `Q(x; s)`. -/
def potQcQ (p : List ℚ) (s : ℚ) (j : ℕ) : ℚ :=
  ∑ m ∈ Finset.Ico j p.length, p.getD m 0 / ((m : ℚ) + 1) * s ^ (m - j)

/-- Rational coefficient of `x^j` in `K(x; s)`. -/
def potKcQ (p : List ℚ) (s : ℚ) (j : ℕ) : ℚ :=
  ∑ m ∈ Finset.Ico j p.length,
    p.getD m 0 / ((m : ℚ) + 1) * (s ^ (m - j + 1) / ((m - j + 1 : ℕ) : ℚ))

/-- The coefficient lists of `Qh`, `Ql`, `A` of a rational piece. -/
def PieceQ.qh (q : PieceQ) : List ℚ := (List.range q.p.length).map (potQcQ q.p q.hi)
def PieceQ.ql (q : PieceQ) : List ℚ := (List.range q.p.length).map (potQcQ q.p q.lo)
def PieceQ.apoly (q : PieceQ) : List ℚ :=
  (List.range q.p.length).map (fun j => potKcQ q.p q.lo j - potKcQ q.p q.hi j)

/-- **The `FieldQ` of the log potential of a rational piece**:
`A(x) + (Qh · (hi − x)) log|x − hi| + (Ql · (x − lo)) log|x − lo|`. -/
def PieceQ.fieldQ (q : PieceQ) : FieldQ where
  poly := q.apoly
  plogs := [(mulLinQ q.hi (-1) q.qh, q.hi), (mulLinQ (-q.lo) 1 q.ql, q.lo)]
  poles := []

theorem polyTow_zero_range_map (n : ℕ) (f : ℕ → ℚ) (x : ℝ) :
    polyTow ((List.range n).map f) 0 x = ∑ j ∈ Finset.range n, (f j : ℝ) * x ^ j := by
  induction n generalizing f with
  | zero => simp [polyTow_zero_nil]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyTow_zero_cons,
      Finset.sum_range_succ']
    have := ih (f ∘ Nat.succ)
    rw [this, Finset.mul_sum, add_comm]
    simp only [pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, pow_succ]
    ring

theorem potQcQ_cast (q : PieceQ) (s : ℚ) (j : ℕ) :
    ((potQcQ q.p s j : ℚ) : ℝ) = potQc q.toPiece.n q.toPiece.p (s : ℝ) j := by
  unfold potQcQ potQc PieceQ.toPiece
  push_cast
  rfl

theorem potKcQ_cast (q : PieceQ) (s : ℚ) (j : ℕ) :
    ((potKcQ q.p s j : ℚ) : ℝ) = potKc q.toPiece.n q.toPiece.p (s : ℝ) j := by
  unfold potKcQ potKc PieceQ.toPiece
  push_cast
  rfl

/-- **The potential of a rational piece is the `FieldQ` evaluation** (so a data module's `hid` for
this block is `rfl`/`decide` on the coefficient lists). -/
theorem PieceQ.pot_eq_fieldTower (q : PieceQ) (w : ℝ) :
    q.toPiece.pot w = fieldTower q.fieldQ (fun _ => 0) 0 w := by
  rw [Piece.pot_eq_coef]
  have hn : q.toPiece.n = q.p.length := rfl
  simp only [fieldTower, PieceQ.fieldQ, plogSumTower, poleTower_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, mulTower_zero, logTower]
  rw [PieceQ.apoly, polyTow_zero_range_map]
  rw [polyTow_zero_mulLinQ, polyTow_zero_mulLinQ, PieceQ.qh, PieceQ.ql,
    polyTow_zero_range_map, polyTow_zero_range_map]
  simp only [potAc, hn, potQcQ_cast, potKcQ_cast, Rat.cast_sub, sub_mul]
  push_cast
  have e1 : |w - (q.hi : ℝ)| = |(q.hi : ℝ) - w| := abs_sub_comm _ _
  have e2 : |w - (q.lo : ℝ)| = |w - (q.lo : ℝ)| := rfl
  rw [e1]
  simp only [add_zero, PieceQ.toPiece]
  ring

/-- Sum of `FieldQ`s (polynomial parts added, logs and poles concatenated). -/
def fqAdd (a b : FieldQ) : FieldQ := ⟨vecAdd a.poly b.poly, a.plogs ++ b.plogs, a.poles ++ b.poles⟩

theorem fieldTower_add (a b : FieldQ) (Fa Fb : ℝ → ℝ) (x : ℝ) :
    fieldTower (fqAdd a b) (fun y => Fa y + Fb y) 0 x =
      fieldTower a Fa 0 x + fieldTower b Fb 0 x := by
  simp only [fieldTower, fqAdd, plogSumTower, poleTower_zero, List.map_append, List.sum_append,
    polyTow_zero_vecAdd]
  ring

/-- Negation of the polynomial and log parts (pole-free fields only). -/
def fqNeg (f : FieldQ) : FieldQ :=
  ⟨f.poly.map (fun t => -1 * t), f.plogs.map (fun t => (t.1.map (fun s => -1 * s), t.2)), []⟩

theorem fieldTower_neg (f : FieldQ) (hp : f.poles = []) (x : ℝ) :
    fieldTower (fqNeg f) (fun _ => 0) 0 x = -fieldTower f (fun _ => 0) 0 x := by
  simp only [fieldTower, fqNeg, plogSumTower, poleTower_zero, hp, polyTow_zero_map_mul,
    mulTower_zero]
  have : ∀ l : List (List ℚ × ℚ), (l.map (fun t => polyTow (t.1.map (fun s => -1 * s)) 0 x *
      logTower (t.2 : ℝ) 0 x)).sum = -(l.map (fun t => polyTow t.1 0 x * logTower (t.2 : ℝ) 0 x)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons t ts ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, polyTow_zero_map_mul]
      push_cast; ring
  simp only [List.map_map, Function.comp_def, mulTower_zero] at this ⊢
  rw [this]
  simp
  ring

/-- Coefficients of `c(-x)`. -/
def negX : List ℚ → List ℚ
  | [] => []
  | a :: as => a :: (negX as).map (fun t => -1 * t)

theorem polyTow_zero_negX : ∀ (c : List ℚ) (x : ℝ), polyTow (negX c) 0 x = polyTow c 0 (-x)
  | [], x => by simp [negX, polyTow_zero_nil]
  | a :: as, x => by
      simp only [negX, polyTow_zero_cons, polyTow_zero_map_mul, polyTow_zero_negX as x]
      push_cast; ring

/-- The reflection `x ↦ -x` of a pole-free polynomial-plus-log field. -/
def fqReflect (f : FieldQ) : FieldQ :=
  ⟨negX f.poly, f.plogs.map (fun t => (negX t.1, -t.2)), []⟩

theorem fieldTower_reflect (f : FieldQ) (hp : f.poles = []) (x : ℝ) :
    fieldTower (fqReflect f) (fun _ => 0) 0 x = fieldTower f (fun _ => 0) 0 (-x) := by
  have key : ∀ t : List ℚ × ℚ,
      mulTower (polyTow (negX t.1)) (logTower (((-t.2 : ℚ)) : ℝ)) 0 x =
        mulTower (polyTow t.1) (logTower (t.2 : ℝ)) 0 (-x) := by
    intro t
    simp only [mulTower_zero, logTower, polyTow_zero_negX]
    push_cast
    rw [show x - -(t.2 : ℝ) = -(-x - (t.2 : ℝ)) by ring, abs_neg]
  have hpl : plogSumTower (f.plogs.map (fun t => (negX t.1, -t.2))) 0 x =
      plogSumTower f.plogs 0 (-x) := by
    unfold plogSumTower
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left fun t _ => key t)
  unfold fieldTower
  rw [hp]
  simp only [fqReflect, poleTower_zero, polyTow_zero_negX, hpl]

/-- The `FieldQ` of the log potential of a list of rational pieces. -/
def piecesFieldQ (qs : List PieceQ) : FieldQ :=
  qs.foldr (fun q acc => fqAdd q.fieldQ acc) ⟨[], [], []⟩

theorem piecesFieldQ_poles (qs : List PieceQ) : (piecesFieldQ qs).poles = [] := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [piecesFieldQ, fqAdd, PieceQ.fieldQ] at ih ⊢; exact ih

theorem logPot_eq_fieldTower (qs : List PieceQ) (w : ℝ) :
    logPot (qs.map PieceQ.toPiece) w = fieldTower (piecesFieldQ qs) (fun _ => 0) 0 w := by
  induction qs with
  | nil =>
    simp [logPot, piecesFieldQ, fieldTower, plogSumTower, poleTower_zero, polyTow_zero_nil]
  | cons q qs ih =>
    have := fieldTower_add q.fieldQ (piecesFieldQ qs) (fun _ => 0) (fun _ => 0) w
    simp only [add_zero] at this
    simp only [logPot, List.map_cons, List.sum_cons] at ih ⊢
    rw [PieceQ.pot_eq_fieldTower, ih]
    simp only [piecesFieldQ, List.foldr_cons]
    exact this.symm

/-- **`FieldQ` of the reference row** `refRowForm qT qF = −V_T(x) − V_F(−x)`: the data module's
`hid` for this block is `rfl` on this definition. -/
def refRowFieldQ (qT qF : List PieceQ) : FieldQ :=
  fqAdd (fqNeg (piecesFieldQ qT)) (fqNeg (fqReflect (piecesFieldQ qF)))

theorem refRowForm_eq_fieldTower (qT qF : List PieceQ) (x : ℝ) :
    refRowForm (qT.map PieceQ.toPiece) (qF.map PieceQ.toPiece) x =
      fieldTower (refRowFieldQ qT qF) (fun _ => 0) 0 x := by
  unfold refRowForm refRowFieldQ
  have := fieldTower_add (fqNeg (piecesFieldQ qT)) (fqNeg (fqReflect (piecesFieldQ qF)))
    (fun _ => 0) (fun _ => 0) x
  have this : fieldTower (fqAdd (fqNeg (piecesFieldQ qT)) (fqNeg (fqReflect (piecesFieldQ qF))))
      (fun _ => 0) 0 x = fieldTower (fqNeg (piecesFieldQ qT)) (fun _ => 0) 0 x +
        fieldTower (fqNeg (fqReflect (piecesFieldQ qF))) (fun _ => 0) 0 x := by simpa using this
  rw [this, fieldTower_neg (piecesFieldQ qT) (piecesFieldQ_poles qT),
    fieldTower_neg (fqReflect (piecesFieldQ qF)) (by simp [fqReflect]),
    fieldTower_reflect _ (piecesFieldQ_poles qF), logPot_eq_fieldTower, logPot_eq_fieldTower]
  ring

/-! ### R. The dilated blocks as Laurent fields (decidable `hid` for `dilPot`)

`dilPot qs x = -(log|x| m + V(1/x))`, with `V(w) = Σ_pieces [A(w) + Qh(w)(hi − w) log|hi − w| +
Ql(w)(w − lo) log|w − lo|]`.  With `w = 1/x`: `log|w − e| = log|e x − 1| − log|x|`, so the block is a
list of Laurent terms (`Σ_s a_s x^{-s}` times `log|α x − β|`, TaylorCell section 14) with the
*rational* data below; the identity holds for every `x ≠ 0` (at `e x = 1` both sides carry the
vanishing factor `e − w`). -/

theorem inv_log_key (a x : ℝ) (hx : x ≠ 0) :
    (a - x⁻¹) * Real.log |x⁻¹ - a| = (a - x⁻¹) * (Real.log |a * x - 1| - Real.log |x|) := by
  by_cases h : a - x⁻¹ = 0
  · rw [h]; simp
  · have hne : a * x - 1 ≠ 0 := by
      intro h0
      apply h
      have h1 : a * x = 1 := by linarith
      exact sub_eq_zero.mpr (eq_inv_of_mul_eq_one_left h1)
    have e : x⁻¹ - a = -(a * x - 1) / x := by field_simp; ring
    rw [e, abs_div, abs_neg, Real.log_div (abs_ne_zero.mpr hne) (abs_ne_zero.mpr hx)]

/-- Scalar multiple of a list of Laurent terms. -/
def scaleL (r : ℚ) (ts : List LTerm) : List LTerm :=
  ts.map (fun t => (t.1.map (fun s => r * s), t.2))

/-- Reflection `x ↦ -x` of a list of Laurent terms. -/
def reflL (ts : List LTerm) : List LTerm :=
  ts.map (fun t => (negX t.1, t.2.map (fun ab => (ab.1, -ab.2))))

theorem lfieldTower_cons (t : LTerm) (ts : List LTerm) (j : ℕ) (x : ℝ) :
    lfieldTower (t :: ts) j x = mulTower (zTow t.1) (lfTower t.2) j x + lfieldTower ts j x := by
  simp [lfieldTower]

theorem lfieldTower_append (A B : List LTerm) (j : ℕ) (x : ℝ) :
    lfieldTower (A ++ B) j x = lfieldTower A j x + lfieldTower B j x := by
  simp [lfieldTower, List.map_append, List.sum_append]

theorem lfieldTower_nil (j : ℕ) (x : ℝ) : lfieldTower [] j x = 0 := by simp [lfieldTower]

theorem lfieldTower_zero_cons (t : LTerm) (ts : List LTerm) (x : ℝ) :
    lfieldTower (t :: ts) 0 x = polyTow t.1 0 x⁻¹ * lfTower t.2 0 x + lfieldTower ts 0 x := by
  rw [lfieldTower_cons, mulTower_zero, zTow_zero]

theorem lfieldTower_scaleL_zero (r : ℚ) (ts : List LTerm) (x : ℝ) :
    lfieldTower (scaleL r ts) 0 x = (r : ℝ) * lfieldTower ts 0 x := by
  induction ts with
  | nil => simp [scaleL, lfieldTower_nil]
  | cons t ts ih =>
    have e : scaleL r (t :: ts) = (t.1.map (fun s => r * s), t.2) :: scaleL r ts := by
      simp [scaleL]
    rw [e, lfieldTower_zero_cons, ih, lfieldTower_zero_cons, polyTow_zero_map_mul]
    ring

theorem lfTower_refl_zero (o : Option (ℚ × ℚ)) (x : ℝ) :
    lfTower (o.map (fun ab => (ab.1, -ab.2))) 0 x = lfTower o 0 (-x) := by
  cases o with
  | none => simp [lfTower, oneTower]
  | some ab =>
    simp only [Option.map_some, lfTower, linLogTower]
    congr 1
    rw [← abs_neg]
    congr 1
    push_cast
    ring

theorem lfieldTower_reflL_zero (ts : List LTerm) (x : ℝ) :
    lfieldTower (reflL ts) 0 x = lfieldTower ts 0 (-x) := by
  induction ts with
  | nil => simp [reflL, lfieldTower_nil]
  | cons t ts ih =>
    have e : reflL (t :: ts) = (negX t.1, t.2.map (fun ab => (ab.1, -ab.2))) :: reflL ts := by
      simp [reflL]
    rw [e, lfieldTower_zero_cons, ih, lfieldTower_zero_cons, polyTow_zero_negX,
      lfTower_refl_zero, inv_neg]

/-- The mass of a rational piece. -/
def PieceQ.massQ (q : PieceQ) : ℚ :=
  ∑ m ∈ Finset.range q.p.length, q.p.getD m 0 / ((m : ℚ) + 1) * (q.hi ^ (m + 1) - q.lo ^ (m + 1))

theorem PieceQ.massQ_cast (q : PieceQ) : ((q.massQ : ℚ) : ℝ) = q.toPiece.mass := by
  unfold PieceQ.massQ Piece.mass potG PieceQ.toPiece
  push_cast
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/-- The Laurent terms of the potential `Piece.pot (1/x)` of a rational piece. -/
def PieceQ.dilTerms (q : PieceQ) : List LTerm :=
  [(mulLinQ q.hi (-1) q.qh, some (q.hi, 1)),
   ((mulLinQ q.hi (-1) q.qh).map (fun s => -1 * s), some (1, 0)),
   (mulLinQ (-q.lo) 1 q.ql, some (q.lo, 1)),
   ((mulLinQ (-q.lo) 1 q.ql).map (fun s => -1 * s), some (1, 0)),
   (q.apoly, none)]

theorem PieceQ.pot_dil (q : PieceQ) (x : ℝ) (hx : x ≠ 0) :
    q.toPiece.pot x⁻¹ = lfieldTower q.dilTerms 0 x := by
  rw [PieceQ.pot_eq_fieldTower]
  have k1 := inv_log_key (q.hi : ℝ) x hx
  have k2 := inv_log_key (q.lo : ℝ) x hx
  simp only [fieldTower, PieceQ.fieldQ, plogSumTower, poleTower_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, mulTower_zero, logTower, PieceQ.dilTerms, lfieldTower_zero_cons,
    lfieldTower_nil, lfTower, linLogTower, oneTower, polyTow_zero_map_mul, polyTow_zero_mulLinQ,
    Rat.cast_one, Rat.cast_zero, one_mul, sub_zero, Rat.cast_neg]
  linear_combination (polyTow q.qh 0 x⁻¹) * k1 + (-(polyTow q.ql 0 x⁻¹)) * k2

/-- The Laurent terms of `dilPot qs x`. -/
def dilTermsQ (qs : List PieceQ) : List LTerm :=
  ([-(qs.map PieceQ.massQ).sum], some (1, 0)) :: scaleL (-1) (qs.flatMap PieceQ.dilTerms)

theorem polyMass_cast (qs : List PieceQ) :
    polyMass (qs.map PieceQ.toPiece) = (((qs.map PieceQ.massQ).sum : ℚ) : ℝ) := by
  induction qs with
  | nil => simp [polyMass]
  | cons q qs ih =>
    simp only [polyMass, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, ← PieceQ.massQ_cast]
    push_cast; rfl

/-- **`hid` for a dilated block**: `dilPot qs x` is the Laurent tower of the rational data
`dilTermsQ qs` (so the data module's identification is `rfl`/`decide` on those lists). -/
theorem dilPot_eq_lfieldTower (qs : List PieceQ) (x : ℝ) (hx : x ≠ 0) :
    dilPot (qs.map PieceQ.toPiece) x = lfieldTower (dilTermsQ qs) 0 x := by
  have hlog : ∀ qs : List PieceQ, logPot (qs.map PieceQ.toPiece) x⁻¹ =
      lfieldTower (qs.flatMap PieceQ.dilTerms) 0 x := by
    intro qs
    induction qs with
    | nil => simp [logPot, lfieldTower_nil]
    | cons q qs ih =>
      simp only [logPot, List.map_cons, List.sum_cons] at ih ⊢
      rw [List.flatMap_cons, lfieldTower_append, ← ih, PieceQ.pot_dil q x hx]
  unfold dilPot
  rw [dilTermsQ, lfieldTower_zero_cons, lfieldTower_scaleL_zero, ← hlog, polyMass_cast]
  simp only [polyTow, lfTower, linLogTower, Rat.cast_one, Rat.cast_zero, one_mul, sub_zero,
    Rat.cast_neg, Rat.cast_sum, mul_zero, add_zero]
  push_cast
  ring

theorem dilPot_neg_eq_lfieldTower (qs : List PieceQ) (x : ℝ) (hx : x ≠ 0) :
    dilPot (qs.map PieceQ.toPiece) (-x) = lfieldTower (reflL (dilTermsQ qs)) 0 x := by
  rw [lfieldTower_reflL_zero]
  exact dilPot_eq_lfieldTower qs (-x) (neg_ne_zero.mpr hx)

/-- Laurent terms of the near-type dilated block `-(dilPot qFf (-x) + dilPot qF (-x))/2`. -/
def nearDilTerms (qFf qF : List PieceQ) : List LTerm :=
  scaleL (-1 / 2) (reflL (dilTermsQ qFf) ++ reflL (dilTermsQ qF))

theorem nearDil_eq (qFf qF : List PieceQ) (x : ℝ) (hx : x ≠ 0) :
    -(dilPot (qFf.map PieceQ.toPiece) (-x) + dilPot (qF.map PieceQ.toPiece) (-x)) / 2 =
      lfieldTower (nearDilTerms qFf qF) 0 x := by
  rw [nearDilTerms, lfieldTower_scaleL_zero, lfieldTower_append, ← dilPot_neg_eq_lfieldTower _ x hx,
    ← dilPot_neg_eq_lfieldTower _ x hx]
  push_cast
  ring

/-- The two reference rows of the positive/near fields, `-V_T(x) - V_F(-x)` for the true and the
fixed measure, as one `FieldQ` (poles empty). -/
def refRowsNegFieldQ (qT qF qTf qFf : List PieceQ) : FieldQ :=
  fqNeg (fqAdd (refRowFieldQ qT qF) (refRowFieldQ qTf qFf))

theorem refRowsNeg_eq (qT qF qTf qFf : List PieceQ) (x : ℝ) :
    -refRowForm (qT.map PieceQ.toPiece) (qF.map PieceQ.toPiece) x -
        refRowForm (qTf.map PieceQ.toPiece) (qFf.map PieceQ.toPiece) x =
      fieldTower (refRowsNegFieldQ qT qF qTf qFf) (fun _ => 0) 0 x := by
  have hp : (fqAdd (refRowFieldQ qT qF) (refRowFieldQ qTf qFf)).poles = [] := by
    simp [fqAdd, refRowFieldQ, fqNeg]
  unfold refRowsNegFieldQ
  rw [fieldTower_neg _ hp]
  have := fieldTower_add (refRowFieldQ qT qF) (refRowFieldQ qTf qFf) (fun _ => 0) (fun _ => 0) x
  simp only [add_zero] at this
  rw [this, ← refRowForm_eq_fieldTower, ← refRowForm_eq_fieldTower]
  ring

/-- **`hid` for the dilated and reference blocks of the positive-row closed form**:
`-refRow(T) - refRow(Tf) + dilPot qT x = fieldTower (refRows) + lfieldTower (dilTermsQ qT)`. -/
theorem posBlock_eq (qT qF qTf qFf : List PieceQ) (x : ℝ) (hx : x ≠ 0) :
    -refRowForm (qT.map PieceQ.toPiece) (qF.map PieceQ.toPiece) x -
        refRowForm (qTf.map PieceQ.toPiece) (qFf.map PieceQ.toPiece) x +
        dilPot (qT.map PieceQ.toPiece) x =
      fieldTower (refRowsNegFieldQ qT qF qTf qFf) (fun _ => 0) 0 x +
        lfieldTower (dilTermsQ qT) 0 x := by
  rw [refRowsNeg_eq, dilPot_eq_lfieldTower qT x hx]

/-- The same for the near-type block. -/
theorem nearBlock_eq (qT qF qTf qFf : List PieceQ) (x : ℝ) (hx : x ≠ 0) :
    -refRowForm (qT.map PieceQ.toPiece) (qF.map PieceQ.toPiece) x -
        refRowForm (qTf.map PieceQ.toPiece) (qFf.map PieceQ.toPiece) x +
        (-(dilPot (qFf.map PieceQ.toPiece) (-x) + dilPot (qF.map PieceQ.toPiece) (-x)) / 2) =
      fieldTower (refRowsNegFieldQ qT qF qTf qFf) (fun _ => 0) 0 x +
        lfieldTower (nearDilTerms qFf qF) 0 x := by
  rw [refRowsNeg_eq, nearDil_eq qFf qF x hx]


end Hid

end

end CatalanMeasure.Signed.FieldForm

#print axioms CatalanMeasure.Signed.FieldForm.polyPot
#print axioms CatalanMeasure.Signed.FieldForm.re_log_one_sub
#print axioms CatalanMeasure.Signed.FieldForm.re_log_quad
#print axioms CatalanMeasure.Signed.FieldForm.barrierTrialS_tseq
#print axioms CatalanMeasure.Signed.FieldForm.barrierTrialT_tseq
#print axioms CatalanMeasure.Signed.FieldForm.fld_gseq
#print axioms CatalanMeasure.Signed.FieldForm.integral_log_polyMeas
#print axioms CatalanMeasure.Signed.FieldForm.integral_log_one_sub_polyMeas
#print axioms CatalanMeasure.Signed.FieldForm.fld_refMoment
#print axioms CatalanMeasure.Signed.FieldForm.rowRef_polyMeas
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fNeg_closed
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fPosS_closed
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fCol_closed
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fNegM_closed
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fPosMR_closed
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fNearMS_closed
#print axioms CatalanMeasure.Signed.FieldForm.fld_arcNeg_eq
#print axioms CatalanMeasure.Signed.FieldForm.fld_arcNeg_nonpos
#print axioms CatalanMeasure.Signed.FieldForm.populationPhysicalFreeField_eq
#print axioms CatalanMeasure.Signed.FieldForm.populationPhysicalColumnField_zero
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.fNearM_le_noarc
#print axioms CatalanMeasure.Signed.FieldForm.geoForm_sub_geoLim_le
#print axioms CatalanMeasure.Signed.FieldForm.dilPot_sub_le
#print axioms CatalanMeasure.Signed.FieldForm.fNeg_unif
#print axioms CatalanMeasure.Signed.FieldForm.fPosS_unif
#print axioms CatalanMeasure.Signed.FieldForm.fCol_unif
#print axioms CatalanMeasure.Signed.FieldForm.rowNeg_cell
#print axioms CatalanMeasure.Signed.FieldForm.rowPos_cell
#print axioms CatalanMeasure.Signed.FieldForm.column_cell
#print axioms CatalanMeasure.Signed.FieldForm.dilPot_mono
#print axioms CatalanMeasure.Signed.FieldForm.geoForm_sub_geoLim_le'
#print axioms CatalanMeasure.Signed.FieldForm.fNeg_le_lim
#print axioms CatalanMeasure.Signed.FieldForm.fNeg_cell_zero
#print axioms CatalanMeasure.Signed.FieldForm.fNeg_cell_one
#print axioms CatalanMeasure.Signed.FieldForm.fPosS_le_lim
#print axioms CatalanMeasure.Signed.FieldForm.fPosS_cell_zero
#print axioms CatalanMeasure.Signed.FieldForm.fPosS_cell_one
#print axioms CatalanMeasure.Signed.FieldForm.fCol_cell_zero
#print axioms CatalanMeasure.Signed.FieldForm.fCol_cell_one
#print axioms CatalanMeasure.Signed.FieldForm.fNegM_le_lim
#print axioms CatalanMeasure.Signed.FieldForm.fNegM_cell_one
#print axioms CatalanMeasure.Signed.FieldForm.fPosMS_cell
#print axioms CatalanMeasure.Signed.FieldForm.fPosMR_cell
#print axioms CatalanMeasure.Signed.FieldForm.dilPot_sub_le_neg
#print axioms CatalanMeasure.Signed.FieldForm.fNearMS_le_lim
#print axioms CatalanMeasure.Signed.FieldForm.fNearMS_cell
#print axioms CatalanMeasure.Signed.FieldForm.fNearMS_cell_top
#print axioms CatalanMeasure.Signed.FieldForm.PieceQ.pot_eq_fieldTower
#print axioms CatalanMeasure.Signed.FieldForm.logPot_eq_fieldTower
#print axioms CatalanMeasure.Signed.FieldForm.refRowForm_eq_fieldTower
#print axioms CatalanMeasure.Signed.FieldForm.TrialForm.phConst_eq_zero
#print axioms CatalanMeasure.Signed.FieldForm.fNearMS_le_lim
#print axioms CatalanMeasure.Signed.FieldForm.dilPot_eq_lfieldTower
#print axioms CatalanMeasure.Signed.FieldForm.dilPot_neg_eq_lfieldTower
#print axioms CatalanMeasure.Signed.FieldForm.posBlock_eq
#print axioms CatalanMeasure.Signed.FieldForm.nearBlock_eq
#print axioms CatalanMeasure.Signed.FieldForm.PieceQ.pot_dil
#print axioms CatalanMeasure.Signed.FieldForm.dampE_mem
#print axioms CatalanMeasure.Signed.FieldForm.dampE_tendsto
#print axioms CatalanMeasure.Signed.FieldForm.dampE_tau_tendsto
#print axioms CatalanMeasure.Signed.FieldForm.dampE_hℓ
