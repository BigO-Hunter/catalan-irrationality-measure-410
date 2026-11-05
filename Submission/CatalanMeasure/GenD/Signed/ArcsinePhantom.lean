module

public import Submission.CatalanMeasure.GenD.Signed.Energy
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# D7.1 with an arcsine compensation of a mass defect

The arcsine compensation of NOTES §17.2 step 2 (PROOF-A §17.43): when the near-type rows are
taken out of the Vandermonde, the rows have mass `(n - s)/ν` while the reference `μ` keeps mass
`n/ν`.  The paper adds `(s/ν) ω`, `ω` the arcsine law, whose logarithmic potential is constant
(`-log 2`) on `[-1, 1]`, so that the energy is unchanged and Theorem 7.1 applies.

Here the arcsine mass is carried by `s` *phantom rows* at independent arcsine-distributed points
`cos θ_j` (`θ_j` uniform on `[0, π]`).  D7.1 (`rows_vandermonde_le`) holds for almost every phantom
configuration; averaging it over the phantoms:

* the cross terms rows–phantoms and phantom–phantom and the phantom reference potential are
  constants (`∫ log |cos θ - c| dθ/π = -log 2`, `arcLaw_log_cos_sub`, `arcLaw_rowRef`);
* the `L`-terms are convex in the phantom moments, so their average dominates the `L`-terms of the
  averaged moments (`P + (s/ν) arcPos`, `B + (s/ν) arcNeg`), exactly the moments of
  `δ + (s/ν) ω` of the paper;
* the phantom diagonal cost is `(s/(2ν²)) log (1/(1-τ²))` after the cancellations.

Main result: `rows_vandermonde_phantom`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set MeasureTheory Finset
open CatalanMeasure.Signed.ReflectionEnergy
open scoped Interval

noncomputable section

/-! ### The arcsine law in angle coordinates -/

/-- The arcsine law, as the law of `θ` (uniform on `[0, π]`); the point is `cos θ`. -/
abbrev arcLaw : Measure ℝ := denMeasure (fun _ => 0) 0

theorem arcLaw_prob : IsProbabilityMeasure arcLaw :=
  isProbabilityMeasure_denMeasure isTrial_arcsine

theorem arcLaw_eq : arcLaw = ENNReal.ofReal (1 / Real.pi) • volume.restrict (Icc 0 Real.pi) := by
  have h : (fun θ : ℝ => ENNReal.ofReal (denQ (fun _ => 0) 0 θ)) =
      fun _ => ENNReal.ofReal (1 / Real.pi) := by
    funext θ; simp [denQ, chebP]
  show (volume.restrict (Icc 0 Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (denQ (fun _ => 0) 0 θ)) = _
  rw [h, withDensity_const]

theorem log_sin_periodic : Function.Periodic (fun x : ℝ => Real.log (Real.sin x)) Real.pi := by
  intro x
  simp only [Real.sin_add_pi, Real.log_neg_eq_log]

theorem intervalIntegrable_log_sin_affine (a b d : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin (θ / 2 + d))) volume a b := by
  have h : AnalyticOnNhd ℝ (fun θ : ℝ => Real.sin (θ / 2 + d)) (Set.uIcc a b) := by
    intro x _
    have h1 : AnalyticAt ℝ (fun θ : ℝ => θ / 2 + d) x := by fun_prop
    exact Real.analyticAt_sin.comp h1
  exact h.meromorphicOn.intervalIntegrable_log

/-- **The arcsine potential:** `∫₀^π log |cos θ - c| dθ = -π log 2` for `c ∈ [-1, 1]`. -/
theorem intervalIntegral_log_cos_sub {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.log (Real.cos θ - c) = -Real.log 2 * Real.pi := by
  set φ := Real.arccos c
  have hφ : Real.cos φ = c := Real.cos_arccos hc.1 hc.2
  have hcount : Set.Countable
      {θ : ℝ | Real.sin (θ / 2 + φ / 2) = 0 ∨ Real.sin (θ / 2 + -(φ / 2)) = 0} := by
    refine ((Set.countable_range (fun n : ℤ => 2 * ((n : ℝ) * Real.pi) - φ)).union
      (Set.countable_range (fun n : ℤ => 2 * ((n : ℝ) * Real.pi) + φ))).mono ?_
    intro θ hθ
    rcases hθ with h | h
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      exact Or.inl ⟨n, by linarith⟩
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      exact Or.inr ⟨n, by linarith⟩
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι (0 : ℝ) Real.pi →
      Real.log (Real.cos θ - c) = Real.log 2 + (Real.log (Real.sin (θ / 2 + φ / 2)) +
        Real.log (Real.sin (θ / 2 + -(φ / 2)))) := by
    filter_upwards [hcount.ae_notMem volume] with θ hθ _
    simp only [Set.mem_setOf_eq, not_or] at hθ
    have e : Real.cos θ - c =
        -(2 * (Real.sin (θ / 2 + φ / 2) * Real.sin (θ / 2 + -(φ / 2)))) := by
      rw [← hφ, Real.cos_sub_cos, show (θ + φ) / 2 = θ / 2 + φ / 2 by ring,
        show (θ - φ) / 2 = θ / 2 + -(φ / 2) by ring]
      ring
    rw [e, Real.log_neg_eq_log, Real.log_mul two_ne_zero (mul_ne_zero hθ.1 hθ.2),
      Real.log_mul hθ.1 hθ.2]
  rw [intervalIntegral.integral_congr_ae hae]
  have i1 := intervalIntegrable_log_sin_affine 0 Real.pi (φ / 2)
  have i2 := intervalIntegrable_log_sin_affine 0 Real.pi (-(φ / 2))
  rw [intervalIntegral.integral_add intervalIntegrable_const (i1.add i2),
    intervalIntegral.integral_add i1 i2]
  have s1 : ∫ θ in (0 : ℝ)..Real.pi, Real.log (Real.sin (θ / 2 + φ / 2)) =
      2 * ∫ u in (φ / 2)..(Real.pi / 2 + φ / 2), Real.log (Real.sin u) := by
    have := intervalIntegral.integral_comp_div_add (a := 0) (b := Real.pi)
      (fun u => Real.log (Real.sin u)) (two_ne_zero : (2 : ℝ) ≠ 0) (φ / 2)
    simp only [zero_div, zero_add, smul_eq_mul] at this
    exact this
  have s2 : ∫ θ in (0 : ℝ)..Real.pi, Real.log (Real.sin (θ / 2 + -(φ / 2))) =
      2 * ∫ u in (φ / 2 - Real.pi / 2)..(φ / 2), Real.log (Real.sin u) := by
    have := intervalIntegral.integral_comp_div_add (a := 0) (b := Real.pi)
      (fun u => Real.log (Real.sin u)) (two_ne_zero : (2 : ℝ) ≠ 0) (-(φ / 2))
    simp only [zero_div, zero_add, smul_eq_mul] at this
    rw [this]
    congr 1
    have hn := intervalIntegral.integral_comp_neg (a := -(φ / 2)) (b := Real.pi / 2 + -(φ / 2))
      (fun u => Real.log (Real.sin u))
    simp only [Real.sin_neg, Real.log_neg_eq_log] at hn
    rw [hn]
    congr 1 <;> ring
  rw [s1, s2]
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_sin (a := φ / 2 - Real.pi / 2) (b := φ / 2))
    (intervalIntegrable_log_sin (a := φ / 2) (b := Real.pi / 2 + φ / 2))
  have hper := log_sin_periodic.intervalIntegral_add_eq (φ / 2 - Real.pi / 2) 0
  rw [show φ / 2 - Real.pi / 2 + Real.pi = Real.pi / 2 + φ / 2 by ring, zero_add] at hper
  have hsum : (∫ u in (φ / 2)..(Real.pi / 2 + φ / 2), Real.log (Real.sin u)) +
      (∫ u in (φ / 2 - Real.pi / 2)..(φ / 2), Real.log (Real.sin u)) = -Real.log 2 * Real.pi := by
    have e1 : (∫ u in (φ / 2 - Real.pi / 2)..(φ / 2), Real.log (Real.sin u)) +
        (∫ u in (φ / 2)..(Real.pi / 2 + φ / 2), Real.log (Real.sin u)) =
        ∫ u in (φ / 2 - Real.pi / 2)..(Real.pi / 2 + φ / 2), Real.log (Real.sin u) := hadj
    rw [add_comm, e1, hper, integral_log_sin_zero_pi]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  linarith

theorem arcLaw_log_cos_sub {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    Integrable (fun θ => Real.log (Real.cos θ - c)) arcLaw ∧
      ∫ θ, Real.log (Real.cos θ - c) ∂arcLaw = -Real.log 2 := by
  constructor
  · rw [arcLaw_eq]
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    have hii : IntervalIntegrable (fun θ : ℝ => Real.log (Real.cos θ - c)) volume 0 Real.pi := by
      have h : AnalyticOnNhd ℝ (fun θ : ℝ => Real.cos θ - c) (Set.uIcc 0 Real.pi) := by
        intro x _
        exact Real.analyticAt_cos.sub analyticAt_const
      exact h.meromorphicOn.intervalIntegrable_log
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mp hii
  · rw [integral_denMeasure isTrial_arcsine]
    have h : ∀ θ : ℝ, denQ (fun _ => 0) 0 θ * Real.log (Real.cos θ - c) =
        (1 / Real.pi) * Real.log (Real.cos θ - c) := fun θ => by simp [denQ, chebP]
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_log_cos_sub hc]
    field_simp

/-! ### The reference potential averaged over the arcsine law -/

/-- The sign of a species. -/
def sgnR (t : Bool) : ℝ := if t then 1 else -1

theorem sgnR_mem (t : Bool) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : sgnR t * y ∈ Icc (-1 : ℝ) 1 := by
  cases t <;> simp only [sgnR, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] <;>
    constructor <;> linarith [hy.1, hy.2]

theorem Kt_eq_log (t : Bool) (u y : ℝ) :
    Kt (decide (0 < u)) t |u| y = -Real.log (u - sgnR t * y) := by
  unfold Kt sgnR
  rcases lt_or_ge 0 u with hu | hu
  · have hd : decide (0 < u) = true := by simp [hu]
    rw [hd, abs_of_pos hu]
    cases t
    · simp only [Bool.true_eq_false, ↓reduceIte, Bool.false_eq_true]
      congr 2; ring
    · simp only [↓reduceIte, one_mul, Real.log_abs]
  · have hd : decide (0 < u) = false := by simp [not_lt.mpr hu]
    rw [hd, abs_of_nonpos hu]
    cases t
    · simp only [↓reduceIte, Bool.false_eq_true]
      rw [Real.log_abs, ← Real.log_neg_eq_log (-u - y)]
      congr 2; ring
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [← Real.log_neg_eq_log (u - y)]
      congr 2; ring

theorem rowRef_eq_log (μ : SRef) (u : ℝ) :
    rowRef μ u = ∑ t, (∫ y, -Real.log (u - sgnR t * y) ∂(μ.P t) -
      ∫ y, -Real.log (u - sgnR t * y) ∂(μ.N t)) := by
  unfold rowRef
  simp_rw [Kt_eq_log]

theorem log_le_log_two_of_mem {a c : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (hc : c ∈ Icc (-1 : ℝ) 1) :
    Real.log (a - c) ≤ Real.log 2 := by
  rw [← Real.log_abs]
  rcases eq_or_ne (a - c) 0 with h | h
  · rw [h, abs_zero, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
  · exact Real.log_le_log (abs_pos.mpr h)
      (abs_le.mpr ⟨by linarith [ha.1, hc.2], by linarith [ha.2, hc.1]⟩)

/-- `∫ ∑_t ∫ -log(cos θ - sgn_t y) dμ_t(y) dθ/π = log 2 · |μ|` for one nonnegative family. -/
theorem arcLaw_logsum {μ : Bool → Measure ℝ} {C : ℝ} (hμ : ∀ t, BD (μ t) C) :
    Integrable (fun θ => ∑ t, ∫ y, -Real.log (Real.cos θ - sgnR t * y) ∂(μ t)) arcLaw ∧
      ∫ θ, ∑ t, ∫ y, -Real.log (Real.cos θ - sgnR t * y) ∂(μ t) ∂arcLaw =
        Real.log 2 * ∑ t, (μ t).real univ := by
  haveI := arcLaw_prob
  have hcos : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 :=
    fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have key : ∀ t : Bool,
      Integrable (fun p : ℝ × ℝ => -Real.log (Real.cos p.1 - sgnR t * p.2)) (arcLaw.prod (μ t)) ∧
      ∫ θ, ∫ y, -Real.log (Real.cos θ - sgnR t * y) ∂(μ t) ∂arcLaw =
        Real.log 2 * (μ t).real univ := by
    intro t
    haveI := (hμ t).finite
    have hm : Measurable (fun p : ℝ × ℝ => -Real.log (Real.cos p.1 - sgnR t * p.2)) :=
      (Real.measurable_log.comp ((Real.continuous_cos.measurable.comp measurable_fst).sub
        (measurable_const.mul measurable_snd))).neg
    have hin : ∀ y ∈ Ioo (0 : ℝ) 1,
        Integrable (fun θ => -Real.log (Real.cos θ - sgnR t * y)) arcLaw ∧
          ∫ θ, -Real.log (Real.cos θ - sgnR t * y) ∂arcLaw = Real.log 2 := by
      intro y hy
      obtain ⟨h1, h2⟩ := arcLaw_log_cos_sub (sgnR_mem t hy)
      exact ⟨h1.neg, by rw [integral_neg, h2, neg_neg]⟩
    have hnorm : ∀ y ∈ Ioo (0 : ℝ) 1,
        ∫ θ, ‖-Real.log (Real.cos θ - sgnR t * y)‖ ∂arcLaw ≤ 3 * Real.log 2 := by
      intro y hy
      obtain ⟨h1, h2⟩ := hin y hy
      have hb : ∀ θ, ‖-Real.log (Real.cos θ - sgnR t * y)‖ ≤
          -Real.log (Real.cos θ - sgnR t * y) + 2 * Real.log 2 := by
        intro θ
        have := log_le_log_two_of_mem (hcos θ) (sgnR_mem t hy)
        have hl2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      calc ∫ θ, ‖-Real.log (Real.cos θ - sgnR t * y)‖ ∂arcLaw
          ≤ ∫ θ, (-Real.log (Real.cos θ - sgnR t * y) + 2 * Real.log 2) ∂arcLaw :=
            integral_mono h1.norm (h1.add (integrable_const _)) hb
        _ = 3 * Real.log 2 := by
            rw [integral_add h1 (integrable_const _), h2, integral_const]
            simp; ring
    have hint : Integrable (fun p : ℝ × ℝ => -Real.log (Real.cos p.1 - sgnR t * p.2))
        (arcLaw.prod (μ t)) := by
      rw [integrable_prod_iff' hm.aestronglyMeasurable]
      constructor
      · filter_upwards [(hμ t).ae_mem] with y hy using (hin y hy).1
      · refine Integrable.mono' (integrable_const (3 * Real.log 2))
          (hm.norm.stronglyMeasurable.integral_prod_left' (μ := arcLaw)).aestronglyMeasurable ?_
        filter_upwards [(hμ t).ae_mem] with y hy
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hnorm y hy
    refine ⟨hint, ?_⟩
    have hsw := integral_integral_swap (f := fun θ y => -Real.log (Real.cos θ - sgnR t * y)) hint
    rw [hsw]
    have : ∫ y, ∫ θ, -Real.log (Real.cos θ - sgnR t * y) ∂arcLaw ∂(μ t) =
        ∫ _y, Real.log 2 ∂(μ t) := by
      refine integral_congr_ae ?_
      filter_upwards [(hμ t).ae_mem] with y hy using (hin y hy).2
    rw [this, integral_const, smul_eq_mul, mul_comm]
  have hI : ∀ t ∈ (Finset.univ : Finset Bool),
      Integrable (fun θ => ∫ y, -Real.log (Real.cos θ - sgnR t * y) ∂(μ t)) arcLaw :=
    fun t _ => by haveI := (hμ t).finite; exact (key t).1.integral_prod_left
  refine ⟨integrable_finsetSum _ hI, ?_⟩
  rw [integral_finsetSum _ hI, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => (key t).2

/-- `∫ rowRef μ (cos θ) dθ/π = log 2 · (|P| - |N|)` for the signed reference `μ = P - N`. -/
theorem arcLaw_rowRef {μ : SRef} {C : ℝ} (hμ : μ.OK C) :
    Integrable (fun θ => rowRef μ (Real.cos θ)) arcLaw ∧
      ∫ θ, rowRef μ (Real.cos θ) ∂arcLaw = Real.log 2 * μ.mass := by
  obtain ⟨hP1, hP2⟩ := arcLaw_logsum hμ.hP
  obtain ⟨hN1, hN2⟩ := arcLaw_logsum hμ.hN
  have hf : (fun θ => rowRef μ (Real.cos θ)) = fun θ =>
      (∑ t, ∫ y, -Real.log (Real.cos θ - sgnR t * y) ∂(μ.P t)) -
        ∑ t, ∫ y, -Real.log (Real.cos θ - sgnR t * y) ∂(μ.N t) := by
    funext θ; rw [rowRef_eq_log, Finset.sum_sub_distrib]
  rw [hf]
  refine ⟨hP1.sub hN1, ?_⟩
  rw [integral_sub hP1 hN1, hP2, hN2]; unfold SRef.mass; ring

/-! ### Phantom configurations -/

/-- The law of `s` independent phantom angles. -/
abbrev phLaw (s : ℕ) : Measure (Fin s → ℝ) := denPi (fun _ => 0) 0 s

theorem phLaw_prob (s : ℕ) : IsProbabilityMeasure (phLaw s) := by
  haveI := arcLaw_prob
  unfold phLaw denPi
  infer_instance

theorem integrable_phEval {s : ℕ} (l : Fin s) {g : ℝ → ℝ} (hg : Integrable g arcLaw) :
    Integrable (fun θ : Fin s → ℝ => g (θ l)) (phLaw s) := by
  haveI := arcLaw_prob
  have e : (phLaw s).map (fun θ => θ l) = arcLaw :=
    (measurePreserving_eval (fun _ : Fin s => arcLaw) l).map_eq
  rw [← e] at hg
  exact hg.comp_measurable (measurable_pi_apply l)

theorem ae_phEval {s : ℕ} (l : Fin s) {p : ℝ → Prop} (h : ∀ᵐ u ∂arcLaw, p u) :
    ∀ᵐ θ ∂(phLaw s), p (θ l) := by
  haveI := arcLaw_prob
  exact (measurePreserving_eval (fun _ : Fin s => arcLaw) l).quasiMeasurePreserving.ae h

theorem ae_phLaw_good {s m : ℕ} (Z : Fin m → ℝ) :
    ∀ᵐ θ ∂(phLaw s), (∀ j, Real.cos (θ j) ∈ Ioo (-1 : ℝ) 1 ∧ Real.cos (θ j) ≠ 0 ∧
      ∀ i, Real.cos (θ j) ≠ Z i) ∧ ∀ j j', j ≠ j' → Real.cos (θ j) ≠ Real.cos (θ j') := by
  haveI := arcLaw_prob
  have hsing : ∀ v : ℝ, ∀ᵐ u ∂arcLaw, u ≠ v := fun v => by
    rw [ae_iff]; simpa using denMeasure_singleton (fun _ => 0) 0 v
  have hmem : ∀ᵐ u ∂arcLaw, u ∈ Icc 0 Real.pi := ae_mem_Icc_denMeasure _ _
  have hone : ∀ᵐ u ∂arcLaw, u ∈ Icc 0 Real.pi ∧ u ≠ 0 ∧ u ≠ Real.pi ∧ u ≠ Real.pi / 2 ∧
      ∀ i, u ≠ Real.arccos (Z i) := by
    filter_upwards [hmem, hsing 0, hsing Real.pi, hsing (Real.pi / 2),
      ae_all_iff.mpr fun i => hsing (Real.arccos (Z i))] with u h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hpair : ∀ j j' : Fin s, j ≠ j' → ∀ᵐ θ ∂(phLaw s), θ j ≠ θ j' := by
    intro j j' hne
    have hmp : MeasurePreserving (fun θ : Fin s → ℝ => (θ j, θ j')) (phLaw s)
        (arcLaw.prod arcLaw) :=
      ⟨by fun_prop, map_pair_denPi isTrial_arcsine hne⟩
    exact hmp.quasiMeasurePreserving.ae (ae_ne_prod_denMeasure isTrial_arcsine)
  have hall1 : ∀ᵐ θ ∂(phLaw s), ∀ j, θ j ∈ Icc 0 Real.pi ∧ θ j ≠ 0 ∧ θ j ≠ Real.pi ∧
      θ j ≠ Real.pi / 2 ∧ ∀ i, θ j ≠ Real.arccos (Z i) :=
    ae_all_iff.mpr fun j => ae_phEval j hone
  have hall2 : ∀ᵐ θ ∂(phLaw s), ∀ j j' : Fin s, j ≠ j' → θ j ≠ θ j' :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun j' => by
      by_cases hne : j = j'
      · exact ae_of_all _ fun _ h => absurd hne h
      · filter_upwards [hpair j j' hne] with θ h _ using h
  filter_upwards [hall1, hall2] with θ h1 h2
  have hpi2 : Real.pi / 2 ∈ Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  refine ⟨fun j => ?_, fun j j' hne heq => ?_⟩
  · obtain ⟨hI, h0, hπ, h2', hZ⟩ := h1 j
    have hlt0 : 0 < θ j := lt_of_le_of_ne hI.1 (Ne.symm h0)
    have hltπ : θ j < Real.pi := lt_of_le_of_ne hI.2 hπ
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi hI.1 le_rfl hltπ
      rwa [Real.cos_pi] at this
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hI.2 hlt0
      rwa [Real.cos_zero] at this
    · intro hc
      apply h2'
      apply Real.injOn_cos hI hpi2
      rw [hc, Real.cos_pi_div_two]
    · intro i hc
      apply hZ i
      rw [← hc, Real.arccos_cos hI.1 hI.2]
  · exact h2 j j' hne (Real.injOn_cos (h1 j).1 (h1 j').1 heq)

theorem append_injective {p m : ℕ} {x : Fin p → ℝ} {y : Fin m → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : Function.Injective (Fin.append x y) := by
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left i' => simp only [Fin.append_left] at hab; rw [hx hab]
    | right j' => simp only [Fin.append_left, Fin.append_right] at hab; exact absurd hab (hxy i j')
  | right j =>
    induction b using Fin.addCases with
    | left i' =>
      simp only [Fin.append_left, Fin.append_right] at hab; exact absurd hab.symm (hxy i' j)
    | right j' => simp only [Fin.append_right] at hab; rw [hy hab]

theorem sum_Ioi_append {p m : ℕ} (H : ℝ → ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    ∑ a : Fin (p + m), ∑ b ∈ Finset.Ioi a, H (Fin.append x y a) (Fin.append x y b) =
      (∑ i : Fin p, ∑ i' ∈ Finset.Ioi i, H (x i) (x i')) + (∑ i : Fin p, ∑ j : Fin m, H (x i) (y j)) +
        ∑ j : Fin m, ∑ j' ∈ Finset.Ioi j, H (y j) (y j') := by
  have hI : ∀ {n : ℕ} (f : Fin n → Fin n → ℝ),
      ∑ a : Fin n, ∑ b ∈ Finset.Ioi a, f a b = ∑ a : Fin n, ∑ b : Fin n, if a < b then f a b else 0 := by
    intro n f
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp
  rw [hI (fun a b => H (Fin.append x y a) (Fin.append x y b)), hI (fun i i' => H (x i) (x i')),
    hI (fun j j' => H (y j) (y j'))]
  have h1 : ∀ (i i' : Fin p), (Fin.castAdd m i < Fin.castAdd m i') ↔ i < i' := by
    intro i i'
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h2 : ∀ (i : Fin p) (j : Fin m), Fin.castAdd m i < Fin.natAdd p j := by
    intro i j
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : ∀ (i : Fin p) (j : Fin m), ¬ (Fin.natAdd p j < Fin.castAdd m i) := by
    intro i j
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h4 : ∀ (j j' : Fin m), (Fin.natAdd p j < Fin.natAdd p j') ↔ j < j' := by
    intro j j'
    simp only [Fin.lt_def, Fin.val_natAdd]
    omega
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, h1, h2, h3, h4,
    ite_true, ite_false, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  ring

/-! ### The phantom moments -/

/-- A phantom's contribution to the species-`t` moment of index `n + 1`. -/
def arcH (τ : ℝ) (t : Bool) (n : ℕ) (u : ℝ) : ℝ :=
  if decide (0 < Real.cos u) = t then (τ * |Real.cos u|) ^ (n + 1) else 0

/-- Moments of the positive half of the arcsine law (dilated by `τ`). -/
def arcPos (τ : ℝ) (n : ℕ) : ℝ := ∫ u, arcH τ true n u ∂arcLaw

/-- Signed moments of the negative half of the arcsine law (dilated by `τ`), as `mneg`. -/
def arcNeg (τ : ℝ) (n : ℕ) : ℝ := (-1) ^ (n + 1) * ∫ u, arcH τ false n u ∂arcLaw

theorem measurableSet_cos_sign (t : Bool) : MeasurableSet {u : ℝ | decide (0 < Real.cos u) = t} := by
  cases t
  · simp only [decide_eq_false_iff_not, not_lt]
    exact measurableSet_le Real.continuous_cos.measurable measurable_const
  · simp only [decide_eq_true_eq]
    exact measurableSet_lt measurable_const Real.continuous_cos.measurable

theorem measurable_arcH (τ : ℝ) (t : Bool) (n : ℕ) : Measurable (arcH τ t n) := by
  unfold arcH
  exact Measurable.ite (measurableSet_cos_sign t)
    ((continuous_const.mul Real.continuous_cos.abs).pow (n + 1)).measurable measurable_const

theorem abs_arcH_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (t : Bool) (n : ℕ) (u : ℝ) :
    |arcH τ t n u| ≤ τ ^ (n + 1) := by
  unfold arcH
  split_ifs
  · rw [abs_pow, abs_mul, abs_of_pos hτ.1, abs_abs]
    exact pow_le_pow_left₀ (mul_nonneg hτ.1.le (abs_nonneg _))
      (mul_le_of_le_one_right hτ.1.le (Real.abs_cos_le_one u)) _
  · simp only [abs_zero]; exact pow_nonneg hτ.1.le _

theorem arcH_nonneg {τ : ℝ} (hτ : 0 < τ) (t : Bool) (n : ℕ) (u : ℝ) : 0 ≤ arcH τ t n u := by
  unfold arcH; split_ifs
  · exact pow_nonneg (mul_nonneg hτ.le (abs_nonneg _)) _
  · exact le_rfl

theorem integrable_arcH {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (t : Bool) (n : ℕ) :
    Integrable (arcH τ t n) arcLaw := by
  haveI := arcLaw_prob
  exact Integrable.mono' (integrable_const (τ ^ (n + 1)))
    (measurable_arcH τ t n).aestronglyMeasurable
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact abs_arcH_le hτ t n u)

theorem abs_integral_arcH_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (t : Bool) (n : ℕ) :
    |∫ u, arcH τ t n u ∂arcLaw| ≤ τ ^ (n + 1) := by
  haveI := arcLaw_prob
  have := norm_integral_le_of_norm_le_const (μ := arcLaw)
    (ae_of_all _ fun u => (by rw [Real.norm_eq_abs]; exact abs_arcH_le hτ t n u :
      ‖arcH τ t n u‖ ≤ τ ^ (n + 1)))
  simpa [Real.norm_eq_abs] using this

theorem isGeom_arcPos {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) : IsGeom τ (arcPos τ) :=
  ⟨1, fun n => by rw [one_mul]; exact abs_integral_arcH_le hτ true n⟩

theorem isGeom_arcNeg {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) : IsGeom τ (arcNeg τ) :=
  ⟨1, fun n => by
    unfold arcNeg
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, one_mul]
    exact abs_integral_arcH_le hτ false n⟩

theorem arcPos_nonneg {τ : ℝ} (hτ : 0 < τ) (n : ℕ) : 0 ≤ arcPos τ n :=
  integral_nonneg fun u => arcH_nonneg hτ true n u

/-! ### Jensen for a square -/

theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Integrable f P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) : (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  set m := ∫ ω, f ω ∂P with hm
  have hg : Integrable (fun ω => 2 * m * f ω - m ^ 2) P :=
    (hf.const_mul (2 * m)).sub (integrable_const (m ^ 2))
  have hpt : ∀ ω, 2 * m * f ω - m ^ 2 ≤ f ω ^ 2 := fun ω => by nlinarith [sq_nonneg (f ω - m)]
  have hI : ∫ ω, (2 * m * f ω - m ^ 2) ∂P ≤ ∫ ω, f ω ^ 2 ∂P := integral_mono hg hf2 hpt
  have hE : ∫ ω, (2 * m * f ω - m ^ 2) ∂P = 2 * m * m - m ^ 2 := by
    rw [integral_sub (f := fun ω => 2 * m * f ω) (g := fun _ => m ^ 2) (hf.const_mul (2 * m))
      (integrable_const (m ^ 2)), integral_const_mul, integral_const, ← hm]
    simp
  nlinarith [hI, hE]

/-! ### The species sums of D7.1 -/

theorem Lpart_summable {ι : Type*} [Fintype ι] (w a : ι → ℝ) (σ : ι → Bool)
    (μ : SRef) {C τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (t : Bool) (hμ : μ.OK C) :
    Summable (fun k : ℕ => (1 / ((k : ℝ) + 1)) *
      ((∑ i, if σ i = t then w i * (τ * a i) ^ (k + 1) else 0) -
        ∫ y, (τ * y) ^ (k + 1) ∂(μ.P t) + ∫ y, (τ * y) ^ (k + 1) ∂(μ.N t)) ^ 2) := by
  have hS : IsGeom τ (fun k : ℕ => ∑ i, if σ i = t then w i * (τ * a i) ^ (k + 1) else 0) := by
    refine ⟨∑ i, w i, fun k => ?_⟩
    calc |∑ i, if σ i = t then w i * (τ * a i) ^ (k + 1) else 0|
        ≤ ∑ i, |if σ i = t then w i * (τ * a i) ^ (k + 1) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i * τ ^ (k + 1) := Finset.sum_le_sum fun i _ => by
          split_ifs
          · rw [abs_mul, abs_of_nonneg (hw i), abs_pow, abs_mul, abs_of_pos hτ.1,
              abs_of_nonneg (ha i).1]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hτ.1.le (ha i).1)
              (mul_le_of_le_one_right hτ.1.le (ha i).2) _) (hw i)
          · simp only [abs_zero]; exact mul_nonneg (hw i) (pow_nonneg hτ.1.le _)
      _ = (∑ i, w i) * τ ^ (k + 1) := by rw [Finset.sum_mul]
  have hG := (hS.sub (isGeom_refMoment (hμ.hP t) hτ.1)).add (isGeom_refMoment (hμ.hN t) hτ.1)
  have hD := hG.summable_mul hτ hG
  refine hD.congr fun k => ?_
  ring

/-- The rows' weighted species sum (as in `Lpart_true_eq`): positives. -/
theorem species_sum_true_w {k q : ℕ} {τ : ℝ} (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (wN : Fin k → ℝ) (wG : Fin q → ℝ) (hn : ∀ b, xn b < 0) (hg : ∀ p, 0 < gp p) (n : ℕ) :
    (∑ i : Fin (k + q), if decide (0 < Fin.append xn gp i) = true then
      Fin.append wN wG i * (τ * |Fin.append xn gp i|) ^ (n + 1) else 0) = wpow τ wG gp n := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ b : Fin k, (if decide (0 < Fin.append xn gp (Fin.castAdd q b)) = true then
      Fin.append wN wG (Fin.castAdd q b) * (τ * |Fin.append xn gp (Fin.castAdd q b)|) ^ (n + 1)
      else 0) = 0 := by
    intro b
    simp [Fin.append_left, not_lt.mpr (hn b).le]
  have h2 : ∀ p : Fin q, (if decide (0 < Fin.append xn gp (Fin.natAdd k p)) = true then
      Fin.append wN wG (Fin.natAdd k p) * (τ * |Fin.append xn gp (Fin.natAdd k p)|) ^ (n + 1)
      else 0) = wG p * (τ * gp p) ^ (n + 1) := by
    intro p
    simp [Fin.append_right, hg p, abs_of_pos (hg p)]
  simp only [h1, h2, Finset.sum_const_zero, zero_add]
  rfl

/-- The rows' weighted species sum: negatives (signed as `mneg`). -/
theorem species_sum_false_w {k q : ℕ} {τ : ℝ} (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (wN : Fin k → ℝ) (wG : Fin q → ℝ) (hn : ∀ b, xn b < 0) (hg : ∀ p, 0 < gp p) (n : ℕ) :
    (∑ i : Fin (k + q), if decide (0 < Fin.append xn gp i) = false then
      Fin.append wN wG i * (τ * |Fin.append xn gp i|) ^ (n + 1) else 0) =
      (-1) ^ (n + 1) * wpow τ wN xn n := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ b : Fin k, (if decide (0 < Fin.append xn gp (Fin.castAdd q b)) = false then
      Fin.append wN wG (Fin.castAdd q b) * (τ * |Fin.append xn gp (Fin.castAdd q b)|) ^ (n + 1)
      else 0) = (-1) ^ (n + 1) * (wN b * (τ * xn b) ^ (n + 1)) := by
    intro b
    have : decide (0 < Fin.append xn gp (Fin.castAdd q b)) = false := by
      simp [Fin.append_left, not_lt.mpr (hn b).le]
    rw [if_pos this]
    simp only [Fin.append_left, abs_of_neg (hn b)]
    rw [show τ * -xn b = -1 * (τ * xn b) by ring, mul_pow]
    ring
  have h2 : ∀ p : Fin q, (if decide (0 < Fin.append xn gp (Fin.natAdd k p)) = false then
      Fin.append wN wG (Fin.natAdd k p) * (τ * |Fin.append xn gp (Fin.natAdd k p)|) ^ (n + 1)
      else 0) = 0 := by
    intro p
    simp [Fin.append_right, hg p]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]
  unfold wpow
  rw [← Finset.mul_sum]

theorem pos_append_weights {a b : ℕ} {wN : Fin a → ℝ} {wG : Fin b → ℝ} (hwN : ∀ i, 0 < wN i)
    (hwG : ∀ i, 0 < wG i) : ∀ i, 0 < Fin.append wN wG i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact hwN j
  · simp only [Fin.append_right]; exact hwG j

/-! ### D7.1 with phantoms -/

set_option maxHeartbeats 3200000 in
/-- **Weighted D7.1 with an arcsine compensation.**  Rows: negatives `XN`, positives `GP` with
positive weights `wN`, `wG`; reference `μ` of mass `Σ w + s ω` (a mass defect `s ω` filled by
`s` arcsine phantoms of weight `ω`).  The bound is D7.1's with the `L`-terms of
`δ + s ω · arcsine` (moments `wpow wG GP + s ω arcPos`, `wpow wN XN + s ω arcNeg`), the D7.1
error at total mass `Σ w + s ω` and the extra diagonal cost `(s ω²/2) log (1/(1-τ²))`.  The
`η`-split uses it with weights `1/ν` (free rows), `1/(2ν)` (fixed rows) and `ω = 1/(2ν)`
(NOTES §17.2 step 2, NOTES-ETA §1.2). -/
theorem rows_vandermonde_phantom {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {a b s : ℕ} (XN : Fin a → ℝ) (GP : Fin b → ℝ) (wN : Fin a → ℝ) (wG : Fin b → ℝ)
    (hwN : ∀ i, 0 < wN i) (hwG : ∀ i, 0 < wG i) {ω : ℝ} (hω : 0 < ω) {φ : ℝ}
    (hφ : (s : ℝ) * ω = φ)
    (hXN : ∀ i, XN i ∈ Ioo (-1 : ℝ) 0) (hGP : ∀ i, GP i ∈ Ioo (0 : ℝ) 1)
    (hinj : Function.Injective (Fin.append XN GP))
    (μ : SRef) {C : ℝ} (hμ : μ.OK C) (hC : 0 ≤ C)
    (hmass : (∑ i, Fin.append wN wG i) + (s : ℝ) * ω = μ.mass) :
    (∑ i, ∑ j ∈ Finset.Ioi i, Fin.append wN wG i * Fin.append wN wG j *
        Real.log |Fin.append XN GP j - Fin.append XN GP i|) ≤
      -(1 / 2) * ip (fun n => wpow τ wG GP n + φ * arcPos τ n - mpos μ τ n)
          (fun n => wpow τ wG GP n + φ * arcPos τ n - mpos μ τ n)
      - (1 / 2) * ip (fun n => wpow τ wN XN n + φ * arcNeg τ n - mneg μ τ n)
          (fun n => wpow τ wN XN n + φ * arcNeg τ n - mneg μ τ n)
      + (1 / 2) * (∑ i, Fin.append wN wG i ^ 2 * (-Real.log |Fin.append XN GP i| +
          Real.log (1 / (1 - τ ^ 2))))
      + (1 / 2) * ((s : ℝ) * ω ^ 2) * Real.log (1 / (1 - τ ^ 2))
      + (1 / 2) * (12 * ((∑ i, Fin.append wN wG i) + (s : ℝ) * ω + 1) * C * (1 - τ ^ 2) *
          (1 + Real.log (1 / (1 - τ ^ 2))) +
          2 * (1 - τ ^ 2) * (2 * ((∑ i, Fin.append wN wG i) + (s : ℝ) * ω + 1)) ^ 2)
      - (∑ i, Fin.append wN wG i * rowRef μ (Fin.append XN GP i)) + (1 / 2) * refEnergy μ := by
  subst hφ
  classical
  haveI := arcLaw_prob
  haveI := phLaw_prob s
  have hρ0 : 0 < τ ^ 2 := pow_pos hτ.1 2
  have hρ1 : τ ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
  have hsq : Real.sqrt (τ ^ 2) = τ := Real.sqrt_sq hτ.1.le
  have hW : ∀ i, 0 < Fin.append wN wG i := pos_append_weights hwN hwG
  have hZm : ∀ i, Fin.append XN GP i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact ⟨(hXN b).1, by linarith [(hXN b).2]⟩
    · simp only [Fin.append_right]; exact ⟨by linarith [(hGP p).1], (hGP p).2⟩
  have hZ0 : ∀ i, Fin.append XN GP i ≠ 0 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact (hXN b).2.ne
    · simp only [Fin.append_right]; exact (hGP p).1.ne'
  have hZI : ∀ i, Fin.append XN GP i ∈ Icc (-1 : ℝ) 1 := fun i => ⟨(hZm i).1.le, (hZm i).2.le⟩
  -- single-coordinate integrals
  obtain ⟨hR1, hR2⟩ := arcLaw_rowRef hμ
  have hl0 : Integrable (fun u => Real.log |Real.cos u|) arcLaw ∧
      ∫ u, Real.log |Real.cos u| ∂arcLaw = -Real.log 2 := by
    have h := arcLaw_log_cos_sub (c := 0) ⟨by norm_num, by norm_num⟩
    simp only [sub_zero] at h
    simpa only [Real.log_abs] using h
  have hlZ : ∀ i, Integrable (fun u => Real.log |Real.cos u - Fin.append XN GP i|) arcLaw ∧
      ∫ u, Real.log |Real.cos u - Fin.append XN GP i| ∂arcLaw = -Real.log 2 := fun i => by
    simpa only [Real.log_abs] using arcLaw_log_cos_sub (hZI i)
  have hdg : Integrable (fun u => ω ^ 2 * (-Real.log |Real.cos u| +
      Real.log (1 / (1 - τ ^ 2)))) arcLaw :=
    (hl0.1.neg.add (integrable_const _)).const_mul _
  have hdgI : ∫ u, ω ^ 2 * (-Real.log |Real.cos u| + Real.log (1 / (1 - τ ^ 2))) ∂arcLaw =
      ω ^ 2 * (Real.log 2 + Real.log (1 / (1 - τ ^ 2))) := by
    rw [integral_const_mul, integral_add (f := fun u => -Real.log |Real.cos u|)
      (g := fun _ => Real.log (1 / (1 - τ ^ 2))) hl0.1.neg (integrable_const _), integral_neg,
      hl0.2, integral_const]
    simp
  -- moments
  set c : Bool → ℕ → ℝ := fun t k =>
    (∑ i, if decide (0 < Fin.append XN GP i) = t then
        Fin.append wN wG i * (τ * |Fin.append XN GP i|) ^ (k + 1) else 0) -
      (∫ y, (τ * y) ^ (k + 1) ∂(μ.P t) - ∫ y, (τ * y) ^ (k + 1) ∂(μ.N t)) with hc
  set X : Bool → ℕ → (Fin s → ℝ) → ℝ := fun t k θ => ω * ∑ j, arcH τ t k (θ j) with hX
  have hXm : ∀ t k, Measurable (X t k) := fun t k =>
    measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      (measurable_arcH τ t k).comp (measurable_pi_apply j))
  have hXb : ∀ t k θ, |X t k θ| ≤ (s : ℝ) * ω := by
    intro t k θ
    simp only [hX]
    rw [abs_mul, abs_of_pos hω]
    have : |∑ j, arcH τ t k (θ j)| ≤ (s : ℝ) := by
      calc |∑ j, arcH τ t k (θ j)| ≤ ∑ j : Fin s, |arcH τ t k (θ j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin s, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
            (abs_arcH_le hτ t k _).trans (pow_le_one₀ hτ.1.le hτ.2.le)
        _ = s := by simp
    calc ω * |∑ j, arcH τ t k (θ j)| ≤ ω * s := mul_le_mul_of_nonneg_left this hω.le
      _ = (s : ℝ) * ω := by ring
  have hXi : ∀ t k, Integrable (X t k) (phLaw s) := fun t k =>
    Integrable.mono' (integrable_const ((s : ℝ) * ω)) (hXm t k).aestronglyMeasurable
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hXb t k θ)
  have hXI : ∀ t k, ∫ θ, X t k θ ∂(phLaw s) = ((s : ℝ) * ω) * ∫ u, arcH τ t k u ∂arcLaw := by
    intro t k
    simp only [hX]
    rw [integral_const_mul, integral_finsetSum _ fun j _ =>
      integrable_phEval j (integrable_arcH hτ t k)]
    simp only [fun j => integral_single_denPi isTrial_arcsine (s := s) j
      (measurable_arcH τ t k).aestronglyMeasurable, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsqi : ∀ t k, Integrable (fun θ => (c t k + X t k θ) ^ 2) (phLaw s) := fun t k =>
    Integrable.mono' (integrable_const ((|c t k| + (s : ℝ) * ω) ^ 2))
      (((measurable_const.add (hXm t k)).pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun θ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans
          (add_le_add le_rfl (hXb t k θ))) 2)
  -- the averaged terms
  set A : ℕ → ℝ := fun k => ∑ t, (1 / ((k : ℝ) + 1)) *
      (c t k + ((s : ℝ) * ω) * ∫ u, arcH τ t k u ∂arcLaw) ^ 2 with hA
  have hA0 : ∀ k, 0 ≤ A k := fun k => Finset.sum_nonneg fun t _ =>
    mul_nonneg (by positivity) (sq_nonneg _)
  -- the pair terms
  have hkerL := (integrable_kerL_and_energy_ge isTrial_arcsine).1
  have hpairI : ∀ j j' : Fin s, j ≠ j' →
      Integrable (fun θ : Fin s → ℝ => kerL (θ j') (θ j)) (phLaw s) := fun j j' hne =>
    integrable_pair_denPi isTrial_arcsine (Ne.symm hne) hkerL
  have hpairE : ∀ j j' : Fin s, j ≠ j' →
      ∫ θ, kerL (θ j') (θ j) ∂(phLaw s) = -Real.log 2 := fun j j' hne => by
    rw [integral_pair_denPi isTrial_arcsine (Ne.symm hne) measurable_kerL.aestronglyMeasurable,
      arcsine_energy isTrial_arcsine]
  have hpairs : ∀ j : Fin s, ((Finset.Ioi j).card : ℝ) ≤ (s : ℝ) - 1 := by
    intro j
    have h1 : (Finset.Ioi j).card < (Finset.univ : Finset (Fin s)).card :=
      Finset.card_lt_card ⟨Finset.subset_univ _, fun h => by simpa using h (Finset.mem_univ j)⟩
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have : ((Finset.Ioi j).card : ℝ) + 1 ≤ s := by exact_mod_cast h1
    linarith
  -- integrability of the phantom pieces
  have iS : ∀ K : ℕ, Integrable (fun θ : Fin s → ℝ => ∑ k ∈ Finset.range K, ∑ t,
      (1 / ((k : ℝ) + 1)) * (c t k + X t k θ) ^ 2) (phLaw s) := fun K =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun t _ => (hsqi t k).const_mul _
  have iD : Integrable (fun θ : Fin s → ℝ => ∑ j, ω ^ 2 * (-Real.log |Real.cos (θ j)| +
      Real.log (1 / (1 - τ ^ 2)))) (phLaw s) :=
    integrable_finsetSum _ fun j _ => integrable_phEval j hdg
  have iR : Integrable (fun θ : Fin s → ℝ => ∑ j, rowRef μ (Real.cos (θ j))) (phLaw s) :=
    integrable_finsetSum _ fun j _ => integrable_phEval j hR1
  have iC : Integrable (fun θ : Fin s → ℝ =>
      ∑ i, Fin.append wN wG i * ∑ j, Real.log |Real.cos (θ j) - Fin.append XN GP i|)
      (phLaw s) :=
    integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      integrable_phEval j (hlZ i).1).const_mul _
  have iP : Integrable (fun θ : Fin s → ℝ => ∑ j, ∑ j' ∈ Finset.Ioi j, kerL (θ j') (θ j))
      (phLaw s) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun j' hj' =>
      hpairI j j' (ne_of_lt (Finset.mem_Ioi.mp hj'))
  -- their integrals
  have IS : ∀ K : ℕ, ∑ k ∈ Finset.range K, A k ≤ ∫ θ, ∑ k ∈ Finset.range K, ∑ t,
      (1 / ((k : ℝ) + 1)) * (c t k + X t k θ) ^ 2 ∂(phLaw s) := by
    intro K
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun t _ =>
      (hsqi t k).const_mul _]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [integral_finsetSum _ fun t _ => (hsqi t k).const_mul _]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hj := sq_integral_le_integral_sq (f := fun θ => c t k + X t k θ)
      ((integrable_const (c t k)).add (hXi t k)) (hsqi t k)
    rw [integral_add (f := fun _ => c t k) (g := X t k) (integrable_const _) (hXi t k),
      integral_const, hXI] at hj
    simpa using hj
  have ID : ∫ θ, ∑ j, ω ^ 2 * (-Real.log |Real.cos (θ j)| + Real.log (1 / (1 - τ ^ 2)))
      ∂(phLaw s) = (s : ℝ) * (ω ^ 2 * (Real.log 2 + Real.log (1 / (1 - τ ^ 2)))) := by
    rw [integral_finsetSum _ fun j _ => integrable_phEval j hdg]
    simp only [fun j => integral_single_denPi isTrial_arcsine (s := s) j hdg.aestronglyMeasurable,
      hdgI, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have IR : ∫ θ, ∑ j, rowRef μ (Real.cos (θ j)) ∂(phLaw s) =
      (s : ℝ) * (Real.log 2 * μ.mass) := by
    rw [integral_finsetSum _ fun j _ => integrable_phEval j hR1]
    simp only [fun j => integral_single_denPi isTrial_arcsine (s := s) j
      (g := fun u => rowRef μ (Real.cos u)) hR1.aestronglyMeasurable, hR2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have IC1 : ∀ i, ∫ θ, ∑ j, Real.log |Real.cos (θ j) - Fin.append XN GP i| ∂(phLaw s) =
      (s : ℝ) * (-Real.log 2) := by
    intro i
    rw [integral_finsetSum _ fun j _ => integrable_phEval j (hlZ i).1]
    simp only [fun j => integral_single_denPi isTrial_arcsine (s := s) j
      (g := fun u => Real.log |Real.cos u - Fin.append XN GP i|) (hlZ i).1.aestronglyMeasurable,
      (hlZ i).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have IC : ∫ θ, ∑ i, Fin.append wN wG i * ∑ j, Real.log |Real.cos (θ j) - Fin.append XN GP i|
      ∂(phLaw s) = (∑ i, Fin.append wN wG i) * ((s : ℝ) * (-Real.log 2)) := by
    rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
      integrable_phEval j (hlZ i).1).const_mul _]
    simp only [integral_const_mul, IC1, Finset.sum_mul]
  have IP : ∫ θ, ∑ j, ∑ j' ∈ Finset.Ioi j, kerL (θ j') (θ j) ∂(phLaw s) =
      ∑ j : Fin s, ((Finset.Ioi j).card : ℝ) * (-Real.log 2) := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' hj' =>
      hpairI j j' (ne_of_lt (Finset.mem_Ioi.mp hj'))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun j' hj' => hpairI j j' (ne_of_lt (Finset.mem_Ioi.mp hj')),
      Finset.sum_congr rfl fun j' hj' => hpairE j j' (ne_of_lt (Finset.mem_Ioi.mp hj'))]
    simp
  -- the constant part
  set Vz := ∑ i, ∑ j ∈ Finset.Ioi i, Fin.append wN wG i * Fin.append wN wG j *
      Real.log |Fin.append XN GP j - Fin.append XN GP i| with hVz
  set Wt : ℝ := (∑ i, Fin.append wN wG i) + (s : ℝ) * ω with hWt
  set c0 : ℝ := (1 / 2) * (∑ i, Fin.append wN wG i ^ 2 * (-Real.log |Fin.append XN GP i| +
        Real.log (1 / (1 - τ ^ 2)))) +
      (1 / 2) * (12 * (Wt + 1) * C * (1 - τ ^ 2) * (1 + Real.log (1 / (1 - τ ^ 2))) +
        2 * (1 - τ ^ 2) * (2 * (Wt + 1)) ^ 2) -
      (∑ i, Fin.append wN wG i * rowRef μ (Fin.append XN GP i)) + (1 / 2) * refEnergy μ with hc0
  -- the main bound, for each truncation `K`
  have hK : ∀ K : ℕ, Vz ≤ c0 - (1 / 2) * ∑ k ∈ Finset.range K, A k +
      (1 / 2) * ((s : ℝ) * ω ^ 2) * Real.log (1 / (1 - τ ^ 2)) := by
    intro K
    set F : (Fin s → ℝ) → ℝ := fun θ =>
      c0 - (1 / 2) * (∑ k ∈ Finset.range K, ∑ t, (1 / ((k : ℝ) + 1)) * (c t k + X t k θ) ^ 2) +
        (1 / 2) * (∑ j, ω ^ 2 * (-Real.log |Real.cos (θ j)| +
          Real.log (1 / (1 - τ ^ 2)))) -
        ω * (∑ j, rowRef μ (Real.cos (θ j))) -
        ω * (∑ i, Fin.append wN wG i * ∑ j, Real.log |Real.cos (θ j) - Fin.append XN GP i|) -
        (ω * ω) * (∑ j, ∑ j' ∈ Finset.Ioi j, kerL (θ j') (θ j)) with hF
    -- pointwise a.e.
    have hpt : ∀ᵐ θ ∂(phLaw s), Vz ≤ F θ := by
      filter_upwards [ae_phLaw_good (s := s) (Fin.append XN GP)] with θ hθ
      have hphinj : Function.Injective (fun j => Real.cos (θ j)) := fun j j' h => by
        by_contra hne; exact hθ.2 j j' hne h
      have hYinj : Function.Injective
          (Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j))) :=
        append_injective hinj hphinj fun i j h => (hθ.1 j).2.2 i h.symm
      have hY0 : ∀ i, Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i ≠ 0 := by
        intro i
        refine Fin.addCases (fun b => ?_) (fun p => ?_) i
        · simp only [Fin.append_left]; exact hZ0 b
        · simp only [Fin.append_right]; exact (hθ.1 p).2.1
      have hYm : ∀ i, Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i ∈
          Ioo (-1 : ℝ) 1 := by
        intro i
        refine Fin.addCases (fun b => ?_) (fun p => ?_) i
        · simp only [Fin.append_left]; exact hZm b
        · simp only [Fin.append_right]; exact (hθ.1 p).1
      have hVw : ∀ i, 0 < Fin.append (Fin.append wN wG) (fun _ : Fin s => ω) i :=
        pos_append_weights hW (fun _ => hω)
      have hmassY : ∑ i, Fin.append (Fin.append wN wG) (fun _ : Fin s => ω) i =
          μ.mass := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        exact hmass
      have hD := rows_vandermonde_le_w (Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)))
        (Fin.append (Fin.append wN wG) (fun _ : Fin s => ω)) hVw hY0 hYm hYinj μ hμ hC
        hmassY hρ0 hρ1
      rw [wvand_append] at hD
      have hdS : ∑ i, Fin.append (Fin.append wN wG) (fun _ : Fin s => ω) i ^ 2 *
          (-Real.log |Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i| +
            Real.log (1 / (1 - τ ^ 2))) =
          (∑ i, Fin.append wN wG i ^ 2 * (-Real.log |Fin.append XN GP i| +
            Real.log (1 / (1 - τ ^ 2)))) +
          ∑ j, ω ^ 2 * (-Real.log |Real.cos (θ j)| + Real.log (1 / (1 - τ ^ 2))) := by
        rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]
      have hrS : ∑ i, Fin.append (Fin.append wN wG) (fun _ : Fin s => ω) i *
          rowRef μ (Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i) =
          (∑ i, Fin.append wN wG i * rowRef μ (Fin.append XN GP i)) +
            ω * ∑ j, rowRef μ (Real.cos (θ j)) := by
        rw [Fin.sum_univ_add, Finset.mul_sum]; simp only [Fin.append_left, Fin.append_right]
      have hmS : ∑ i, Fin.append (Fin.append wN wG) (fun _ : Fin s => ω) i =
          (∑ i, Fin.append wN wG i) + (s : ℝ) * ω := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      have hcrossE : ∑ i, ∑ j, Fin.append wN wG i * (fun _ : Fin s => ω) j *
          Real.log |(fun j => Real.cos (θ j)) j - Fin.append XN GP i| =
          ω * (∑ i, Fin.append wN wG i * ∑ j, Real.log |Real.cos (θ j) - Fin.append XN GP i|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hppE : ∑ j, ∑ j' ∈ Finset.Ioi j, (fun _ : Fin s => ω) j * (fun _ : Fin s => ω) j' *
          Real.log |(fun j => Real.cos (θ j)) j' - (fun j => Real.cos (θ j)) j| =
          (ω * ω) * ∑ j, ∑ j' ∈ Finset.Ioi j, kerL (θ j') (θ j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j' _ => by simp only [kerL]
      rw [hdS, hrS, hmS, hcrossE, hppE] at hD
      -- the L-terms: `Lpart ≥` the truncated sum
      have hLp : ∀ t, ∑ k ∈ Finset.range K, (1 / ((k : ℝ) + 1)) * (c t k + X t k θ) ^ 2 ≤
          Lpart (Fin.append (Fin.append wN wG) (fun _ : Fin s => ω))
            (fun i => |Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i|)
            (fun i => decide (0 < Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i))
            μ.P μ.N (τ ^ 2) t := by
        intro t
        have hsum := Lpart_summable (Fin.append (Fin.append wN wG) (fun _ : Fin s => ω))
          (fun i => |Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i|)
          (fun i => decide (0 < Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i)) μ hτ
          (fun i => (hVw i).le)
          (fun i => ⟨abs_nonneg _, (abs_lt.mpr (hYm i)).le⟩) t hμ
        unfold Lpart
        rw [hsq]
        refine le_trans (le_of_eq ?_) (hsum.sum_le_tsum (Finset.range K)
          (fun k _ => mul_nonneg (by positivity) (sq_nonneg _)))
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hc, hX, Fin.sum_univ_add, Fin.append_left, Fin.append_right, arcH,
          Finset.mul_sum, mul_ite, mul_zero]
        ring
      have hLsum : ∑ k ∈ Finset.range K, ∑ t, (1 / ((k : ℝ) + 1)) * (c t k + X t k θ) ^ 2 ≤
          ∑ t, Lpart (Fin.append (Fin.append wN wG) (fun _ : Fin s => ω))
            (fun i => |Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i|)
            (fun i => decide (0 < Fin.append (Fin.append XN GP) (fun j => Real.cos (θ j)) i))
            μ.P μ.N (τ ^ 2) t := by
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun t _ => hLp t
      simp only [hF, hVz, hc0, hWt]
      linarith [hD, hLsum]
    -- integrate
    have i5 := ((((integrable_const c0).sub ((iS K).const_mul (1 / 2))).add
      (iD.const_mul (1 / 2))).sub (iR.const_mul ω)).sub (iC.const_mul ω)
    have hFi : Integrable F (phLaw s) := i5.sub (iP.const_mul (ω * ω))
    have hle : Vz ≤ ∫ θ, F θ ∂(phLaw s) := by
      have := integral_mono_ae (integrable_const Vz) hFi hpt
      simpa using this
    have hFI : ∫ θ, F θ ∂(phLaw s) = c0 - (1 / 2) * (∫ θ, ∑ k ∈ Finset.range K, ∑ t,
          (1 / ((k : ℝ) + 1)) * (c t k + X t k θ) ^ 2 ∂(phLaw s)) +
        (1 / 2) * ((s : ℝ) * (ω ^ 2 * (Real.log 2 + Real.log (1 / (1 - τ ^ 2))))) -
        ω * ((s : ℝ) * (Real.log 2 * μ.mass)) -
        ω * ((∑ i, Fin.append wN wG i) * ((s : ℝ) * (-Real.log 2))) -
        (ω * ω) * (∑ j : Fin s, ((Finset.Ioi j).card : ℝ) * (-Real.log 2)) := by
      have e1 := integral_sub i5 (iP.const_mul (ω * ω))
      have e2 := integral_sub ((((integrable_const c0).sub ((iS K).const_mul (1 / 2))).add
        (iD.const_mul (1 / 2))).sub (iR.const_mul ω)) (iC.const_mul ω)
      have e3 := integral_sub (((integrable_const c0).sub ((iS K).const_mul (1 / 2))).add
        (iD.const_mul (1 / 2))) (iR.const_mul ω)
      have e4 := integral_add ((integrable_const c0).sub ((iS K).const_mul (1 / 2)))
        (iD.const_mul (1 / 2))
      have e5 := integral_sub (integrable_const c0) ((iS K).const_mul (1 / 2))
      simp only [Pi.sub_apply, Pi.add_apply] at e1 e2 e3 e4 e5
      have hFe : (fun θ => F θ) = fun θ =>
          c0 - (1 / 2) * (∑ k ∈ Finset.range K, ∑ t, (1 / ((k : ℝ) + 1)) *
            (c t k + X t k θ) ^ 2) +
          (1 / 2) * (∑ j, ω ^ 2 * (-Real.log |Real.cos (θ j)| +
            Real.log (1 / (1 - τ ^ 2)))) -
          ω * (∑ j, rowRef μ (Real.cos (θ j))) -
          ω * (∑ i, Fin.append wN wG i * ∑ j, Real.log |Real.cos (θ j) - Fin.append XN GP i|) -
          (ω * ω) * (∑ j, ∑ j' ∈ Finset.Ioi j, kerL (θ j') (θ j)) := rfl
      rw [hFe, e1, e2, e3, e4, e5, integral_const, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul, ID, IR, IC, IP]
      simp
    rw [hFI] at hle
    have hcnt : ∑ j : Fin s, ((Finset.Ioi j).card : ℝ) ≤ (s : ℝ) * ((s : ℝ) - 1) := by
      calc ∑ j : Fin s, ((Finset.Ioi j).card : ℝ) ≤ ∑ _j : Fin s, ((s : ℝ) - 1) :=
            Finset.sum_le_sum fun j _ => hpairs j
        _ = (s : ℝ) * ((s : ℝ) - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcntE : ∑ j : Fin s, ((Finset.Ioi j).card : ℝ) * (-Real.log 2) =
        -(Real.log 2) * ∑ j : Fin s, ((Finset.Ioi j).card : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hcntE, ← hmass] at hle
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have key : (1 / 2) * ((s : ℝ) * (ω ^ 2 * (Real.log 2 + Real.log (1 / (1 - τ ^ 2))))) -
        ω * ((s : ℝ) * (Real.log 2 * Wt)) -
        ω * ((∑ i, Fin.append wN wG i) * ((s : ℝ) * (-Real.log 2))) -
        (ω * ω) * (-(Real.log 2) * ∑ j : Fin s, ((Finset.Ioi j).card : ℝ)) ≤
        (1 / 2) * ((s : ℝ) * ω ^ 2) * Real.log (1 / (1 - τ ^ 2)) := by
      have e : (1 / 2) * ((s : ℝ) * (ω ^ 2 * (Real.log 2 + Real.log (1 / (1 - τ ^ 2))))) -
          ω * ((s : ℝ) * (Real.log 2 * Wt)) -
          ω * ((∑ i, Fin.append wN wG i) * ((s : ℝ) * (-Real.log 2))) -
          (ω * ω) * (-(Real.log 2) * ∑ j : Fin s, ((Finset.Ioi j).card : ℝ)) =
          (1 / 2) * ((s : ℝ) * ω ^ 2) * Real.log (1 / (1 - τ ^ 2)) +
            ω ^ 2 * Real.log 2 * ((s : ℝ) / 2 - (s : ℝ) ^ 2 +
              ∑ j : Fin s, ((Finset.Ioi j).card : ℝ)) := by rw [hWt]; ring
      rw [e]
      have : ω ^ 2 * Real.log 2 * ((s : ℝ) / 2 - (s : ℝ) ^ 2 +
          ∑ j : Fin s, ((Finset.Ioi j).card : ℝ)) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg ω) hlog2)
        have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
        nlinarith [hcnt]
      linarith
    have hT' := mul_le_mul_of_nonneg_left (IS K) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  -- the limit `K → ∞`
  have htsum : ∑' k, A k ≤
      2 * (c0 + (1 / 2) * ((s : ℝ) * ω ^ 2) * Real.log (1 / (1 - τ ^ 2)) - Vz) :=
    Real.tsum_le_of_sum_range_le hA0 fun K => by have := hK K; linarith
  -- identify the averaged series with the inner products
  have hPg : IsGeom τ (fun n => wpow τ wG GP n + ((s : ℝ) * ω) * arcPos τ n - mpos μ τ n) :=
    ((isGeom_wpow hτ.1 wG GP fun p =>
      (abs_lt.mpr ⟨by linarith [(hGP p).1], (hGP p).2⟩).le).add
      ((isGeom_arcPos hτ).const_mul _)).sub (isGeom_mpos hμ hτ.1)
  have hNg : IsGeom τ (fun n => wpow τ wN XN n + ((s : ℝ) * ω) * arcNeg τ n - mneg μ τ n) :=
    ((isGeom_wpow hτ.1 wN XN fun p =>
      (abs_lt.mpr ⟨(hXN p).1, by linarith [(hXN p).2]⟩).le).add
      ((isGeom_arcNeg hτ).const_mul _)).sub (isGeom_mneg hμ hτ.1)
  have hAsum : HasSum A
      (ip (fun n => wpow τ wG GP n + ((s : ℝ) * ω) * arcPos τ n - mpos μ τ n)
        (fun n => wpow τ wG GP n + ((s : ℝ) * ω) * arcPos τ n - mpos μ τ n) +
      ip (fun n => wpow τ wN XN n + ((s : ℝ) * ω) * arcNeg τ n - mneg μ τ n)
        (fun n => wpow τ wN XN n + ((s : ℝ) * ω) * arcNeg τ n - mneg μ τ n)) := by
    have h := (hasSum_ip hτ hPg hPg).add (hasSum_ip hτ hNg hNg)
    convert h using 1
    funext k
    simp only [hA, hc, Fintype.sum_bool]
    rw [species_sum_true_w XN GP wN wG (fun b => (hXN b).2) (fun p => (hGP p).1),
      species_sum_false_w XN GP wN wG (fun b => (hXN b).2) (fun p => (hGP p).1)]
    unfold arcPos arcNeg mpos mneg
    have hsg : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (1 / ((k : ℝ) + 1)) * (wpow τ wN XN k ^ 2 -
      (((s : ℝ) * ω) * (∫ u, arcH τ false k u ∂arcLaw) -
        (∫ y, (τ * y) ^ (k + 1) ∂(μ.P false) - ∫ y, (τ * y) ^ (k + 1) ∂(μ.N false))) ^ 2) * hsg
  rw [hAsum.tsum_eq, hc0] at htsum
  linarith

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.intervalIntegral_log_cos_sub
#print axioms CatalanMeasure.Signed.arcLaw_rowRef
#print axioms CatalanMeasure.Signed.rows_vandermonde_phantom
