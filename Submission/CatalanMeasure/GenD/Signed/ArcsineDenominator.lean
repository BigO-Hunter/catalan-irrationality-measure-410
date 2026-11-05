module

public import Submission.CatalanMeasure.GenD.Signed.CrossDilation
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The arcsine/Jensen denominator (J5)

Lemma 3.5 and Lemma 7.4 of PROOF-LG in the `θ`-form.  The trial class is a finite Chebyshev
polynomial times the arcsine law,
`ν' = chebP b K (cos θ) dθ / π`, `chebP b K = 1 + 2 Σ_{k=1}^K b_k T_k`, with a positive lower bound
`c` on `[-1, 1]` (`IsTrial b K c`).  With `u = cos θ`, `ν'` is `P(u) dη(u)`, `η` the arcsine law.

* `integral_kerL_denMeasure`: `Σ(ν') = ∬ log |cos θ - cos φ| dν' dν' = -log 2 - Σ_k 2 b_k²/k`
  (proved by damped Chebyshev series at `r_n ↑ 1`, a reverse Fatou lemma for integrability and
  the lower bound, and the pointwise bound `log |u - v| ≤ K_r(u, v) - log r` for the upper one).
* `integral_crossLog_denMeasure`: `∫ l(x, u) dν'(u) = -2 Σ_k (-x)^k b_k / k` for `|x| < 1`, a
  polynomial in `x` (the arcsine part contributes `0`: `arcsine_cross_field`).
* `denEntropy_ge`: the crude entropy bound `h(q) ≥ log π - 2 Σ b_k²`.
* `arcsine_jensen_denominator` (J5): for a bounded measurable field `Q` and
  `Z = ∫_{[0,π]^s} exp (Σ_{l≠l'} log |cos θ_l - cos θ_l'| + Σ_l Q(cos θ_l)) dθ`,
  `0 < Z` and `s(s-1) Σ(ν') + s ∫ Q dν' + s h(q) ≤ log Z`, by Jensen's inequality
  (`ConvexOn.map_integral_le`) for the product density `Π_l q(θ_l)`.  The `_crude` variant puts the
  closed form `log π - 2 Σ b_k²` for the entropy.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set MeasureTheory

noncomputable section

/-! ### A. The trial polynomial and its moments -/

/-- The finite Chebyshev polynomial `1 + 2 Σ_{k=1}^K b_k T_k`. -/
def chebP (b : ℕ → ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range K, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u

theorem chebP_cos (b : ℕ → ℝ) (K : ℕ) (θ : ℝ) :
    chebP b K (Real.cos θ) =
      1 + 2 * ∑ k ∈ Finset.range K, b (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  unfold chebP
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.T_real_cos]
  push_cast
  rfl

theorem continuous_chebP (b : ℕ → ℝ) (K : ℕ) : Continuous (chebP b K) := by
  unfold chebP
  exact continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Polynomial.continuous _)))

theorem continuous_chebP_cos (b : ℕ → ℝ) (K : ℕ) :
    Continuous (fun θ => chebP b K (Real.cos θ)) :=
  (continuous_chebP b K).comp Real.continuous_cos

theorem integral_cos_int_mul_zero {m : ℤ} (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((m : ℝ) * θ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos]
  simp [Real.sin_int_mul_pi]

theorem integral_cos_mul_cos_nat (j k : ℕ) (_hj : j ≠ 0) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ) =
      if j = k then Real.pi / 2 else 0 := by
  have h : ∀ θ : ℝ, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ) =
      (Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ) +
        Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hsum : ((j : ℤ) + (k : ℤ)) ≠ 0 := by omega
  rw [integral_cos_int_mul_zero hsum]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hd : ((j : ℤ) - (k : ℤ)) ≠ 0 := by omega
    rw [integral_cos_int_mul_zero hd]
    simp [hjk]

theorem integral_chebP_cos (b : ℕ → ℝ) (K : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, chebP b K (Real.cos θ) = Real.pi := by
  simp_rw [chebP_cos]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun i _ => by apply Continuous.intervalIntegrable; fun_prop)]
  have : ∀ i ∈ Finset.range K, ∫ θ in (0 : ℝ)..Real.pi,
      b (i + 1) * Real.cos (((i + 1 : ℕ) : ℝ) * θ) = 0 := by
    intro i _
    rw [intervalIntegral.integral_const_mul]
    have := integral_cos_int_mul_zero (m := ((i + 1 : ℕ) : ℤ)) (by omega)
    push_cast at this ⊢
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero this]
  simp

/-- The Chebyshev moments of the trial: `∫₀^π P(cos θ) cos (jθ) dθ = π b_j` for `1 ≤ j ≤ K`
and `0` for `j > K`. -/
theorem integral_chebP_cos_mul (b : ℕ → ℝ) (K j : ℕ) (hj : j ≠ 0) :
    ∫ θ in (0 : ℝ)..Real.pi, chebP b K (Real.cos θ) * Real.cos ((j : ℝ) * θ) =
      if j ≤ K then Real.pi * b j else 0 := by
  have hexp : ∀ θ : ℝ, chebP b K (Real.cos θ) * Real.cos ((j : ℝ) * θ) =
      Real.cos ((j : ℝ) * θ) + 2 * ∑ i ∈ Finset.range K,
        b (i + 1) * (Real.cos (((i + 1 : ℕ) : ℝ) * θ) * Real.cos ((j : ℝ) * θ)) := by
    intro θ
    rw [chebP_cos, add_mul, one_mul, mul_assoc, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun i _ => by apply Continuous.intervalIntegrable; fun_prop)]
  have h0 := integral_cos_int_mul_zero (m := (j : ℤ)) (by omega)
  push_cast at h0
  rw [h0, zero_add]
  have hterm : ∀ i ∈ Finset.range K, ∫ θ in (0 : ℝ)..Real.pi,
      b (i + 1) * (Real.cos (((i + 1 : ℕ) : ℝ) * θ) * Real.cos ((j : ℝ) * θ)) =
      if i = j - 1 then b (i + 1) * (Real.pi / 2) else 0 := by
    intro i _
    rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos_nat (i + 1) j (by omega) hj]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega) | simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range K) (j - 1)]
  by_cases hjK : j ≤ K
  · have : j - 1 ∈ Finset.range K := by simp; omega
    have h2 : j - 1 + 1 = j := by omega
    simp only [this, hjK, ↓reduceIte, h2]
    ring
  · have : j - 1 ∉ Finset.range K := by simp; omega
    simp only [this, hjK, ↓reduceIte]
    ring

theorem integral_chebP_cos_sq (b : ℕ → ℝ) (K : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, chebP b K (Real.cos θ) ^ 2 =
      Real.pi * (1 + 2 * ∑ k ∈ Finset.range K, b (k + 1) ^ 2) := by
  have hexp : ∀ θ : ℝ, chebP b K (Real.cos θ) ^ 2 = chebP b K (Real.cos θ) +
      2 * ∑ i ∈ Finset.range K, b (i + 1) *
        (chebP b K (Real.cos θ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) := by
    intro θ
    have : chebP b K (Real.cos θ) ^ 2 = chebP b K (Real.cos θ) *
        (1 + 2 * ∑ k ∈ Finset.range K, b (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) := by
      rw [← chebP_cos]; ring
    rw [this, mul_add, mul_one, mul_left_comm, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hexp]
  have hc := continuous_chebP_cos b K
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun i _ => by apply Continuous.intervalIntegrable; fun_prop), integral_chebP_cos]
  have hterm : ∀ i ∈ Finset.range K, ∫ θ in (0 : ℝ)..Real.pi,
      b (i + 1) * (chebP b K (Real.cos θ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) =
      Real.pi * b (i + 1) ^ 2 := by
    intro i hi
    have hle : i + 1 ≤ K := by simp at hi; omega
    rw [intervalIntegral.integral_const_mul, integral_chebP_cos_mul b K (i + 1) (by omega)]
    simp only [hle, ↓reduceIte]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-! ### B. The trial measure `ν' = P(cos θ) dθ / π` on `[0, π]` -/

/-- The density (in `θ`) of the trial. -/
def denQ (b : ℕ → ℝ) (K : ℕ) (θ : ℝ) : ℝ := chebP b K (Real.cos θ) / Real.pi

/-- A positive lower bound for the trial polynomial on `[-1, 1]`. -/
def IsTrial (b : ℕ → ℝ) (K : ℕ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ u ∈ Icc (-1 : ℝ) 1, c ≤ chebP b K u

/-- The trial probability measure. -/
def denMeasure (b : ℕ → ℝ) (K : ℕ) : Measure ℝ :=
  (volume.restrict (Icc 0 Real.pi)).withDensity fun θ => ENNReal.ofReal (denQ b K θ)

theorem continuous_denQ (b : ℕ → ℝ) (K : ℕ) : Continuous (denQ b K) :=
  (continuous_chebP_cos b K).div_const _

theorem denQ_pos {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (θ : ℝ) : 0 < denQ b K θ := by
  unfold denQ
  have := h.2 (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  exact div_pos (lt_of_lt_of_le h.1 this) Real.pi_pos

theorem denQ_ge {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (θ : ℝ) :
    c / Real.pi ≤ denQ b K θ := by
  unfold denQ
  exact div_le_div_of_nonneg_right (h.2 (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
    Real.pi_pos.le

theorem abs_chebP_cos_le (b : ℕ → ℝ) (K : ℕ) (θ : ℝ) :
    |chebP b K (Real.cos θ)| ≤ 1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)| := by
  rw [chebP_cos]
  have h1 : |∑ k ∈ Finset.range K, b (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)| ≤
      ∑ k ∈ Finset.range K, |b (k + 1)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  calc _ ≤ |(1 : ℝ)| + |2 * ∑ k ∈ Finset.range K, b (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)| :=
        abs_add_le _ _
    _ ≤ _ := by
      rw [abs_one, abs_mul, abs_two]
      linarith

theorem denQ_le (b : ℕ → ℝ) (K : ℕ) (θ : ℝ) :
    denQ b K θ ≤ (1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi :=
  div_le_div_of_nonneg_right ((le_abs_self _).trans (abs_chebP_cos_le b K θ)) Real.pi_pos.le

theorem integral_denQ (b : ℕ → ℝ) (K : ℕ) : ∫ θ in (0 : ℝ)..Real.pi, denQ b K θ = 1 := by
  unfold denQ
  rw [intervalIntegral.integral_div, integral_chebP_cos]
  exact div_self Real.pi_pos.ne'

theorem integral_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (g : ℝ → ℝ) :
    ∫ θ, g θ ∂(denMeasure b K) = ∫ θ in (0 : ℝ)..Real.pi, denQ b K θ * g θ := by
  unfold denMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_denQ b K).measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (denQ_pos h _).le, smul_eq_mul]
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Icc_eq_integral_Ioc]

theorem isProbabilityMeasure_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) :
    IsProbabilityMeasure (denMeasure b K) := by
  refine ⟨?_⟩
  unfold denMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ?_ ?_]
  · have := integral_denQ b K
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc] at this
    rw [this]
    simp
  · exact (continuous_denQ b K).continuousOn.integrableOn_Icc
  · exact ae_of_all _ fun x => (denQ_pos h x).le

/-! ### C. A Fatou lemma and the log kernel -/

open Filter Topology OAI.InternalCatalan

/-- A real-valued reverse Fatou lemma on a probability space: functions bounded above,
converging a.e., with converging integrals. -/
theorem fatou_real {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g) (hfC : ∀ n x, f n x ≤ C)
    (hint : ∀ n, Integrable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {I : ℝ} (hI : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 I)) :
    Integrable g μ ∧ I ≤ ∫ x, g x ∂μ := by
  have hnn : ∀ᵐ x ∂μ, 0 ≤ C - g x := by
    filter_upwards [hlim] with x hx
    have : g x ≤ C := le_of_tendsto' hx (fun n => hfC n x)
    linarith
  have hIC : I ≤ C := by
    refine le_of_tendsto' hI fun n => ?_
    calc ∫ x, f n x ∂μ ≤ ∫ _x, C ∂μ := integral_mono (hint n) (integrable_const C) (hfC n)
      _ = C := by simp
  have hlint : ∀ n, ∫⁻ x, ENNReal.ofReal (C - f n x) ∂μ =
      ENNReal.ofReal (C - ∫ x, f n x ∂μ) := by
    intro n
    have hI1 : Integrable (fun x => C - f n x) μ := (integrable_const C).sub (hint n)
    rw [← ofReal_integral_eq_lintegral_ofReal hI1
      (ae_of_all _ fun x => sub_nonneg.mpr (hfC n x)), integral_sub (integrable_const C) (hint n)]
    simp
  have hF : ∫⁻ x, ENNReal.ofReal (C - g x) ∂μ ≤ ENNReal.ofReal (C - I) := by
    have h1 : ∀ᵐ x ∂μ, ENNReal.ofReal (C - g x) =
        liminf (fun n => ENNReal.ofReal (C - f n x)) atTop := by
      filter_upwards [hlim] with x hx
      have : Tendsto (fun n => ENNReal.ofReal (C - f n x)) atTop
          (𝓝 (ENNReal.ofReal (C - g x))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hx)
      exact this.liminf_eq.symm
    calc ∫⁻ x, ENNReal.ofReal (C - g x) ∂μ
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (C - f n x)) atTop ∂μ := lintegral_congr_ae h1
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (C - f n x) ∂μ) atTop :=
          lintegral_liminf_le' (fun n => ((hfm n).const_sub C).ennreal_ofReal.aemeasurable)
      _ = ENNReal.ofReal (C - I) := by
          simp_rw [hlint]
          exact ((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.sub hI)).liminf_eq
  have hfin : ∫⁻ x, ENNReal.ofReal (C - g x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hF
  have hCg : Integrable (fun x => C - g x) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hgm.const_sub C).aestronglyMeasurable hnn).mp hfin
  have hg : Integrable g μ := by
    have h : Integrable (fun x => C - (C - g x)) μ := (integrable_const C).sub hCg
    simpa using h
  refine ⟨hg, ?_⟩
  have h2 : ∫ x, (C - g x) ∂μ ≤ C - I := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn (hgm.const_sub C).aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (C - I)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hF
      _ = C - I := ENNReal.toReal_ofReal (by linarith)
  rw [integral_sub (integrable_const C) hg] at h2
  simp at h2
  linarith

/-- The log kernel `log |cos θ - cos φ|`. -/
def kerL (θ φ : ℝ) : ℝ := Real.log |Real.cos θ - Real.cos φ|

theorem measurable_kerL : Measurable (fun p : ℝ × ℝ => kerL p.1 p.2) := by
  unfold kerL
  exact Real.measurable_log.comp
    ((Real.continuous_cos.comp continuous_fst |>.sub (Real.continuous_cos.comp continuous_snd)).abs.measurable)

theorem kerL_le (θ φ : ℝ) : kerL θ φ ≤ Real.log 2 := by
  unfold kerL
  have hb : |Real.cos θ - Real.cos φ| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, Real.neg_one_le_cos φ,
      Real.cos_le_one φ]
  rcases (abs_nonneg (Real.cos θ - Real.cos φ)).eq_or_lt with h | h
  · rw [← h, Real.log_zero]; exact Real.log_nonneg (by norm_num)
  · exact Real.log_le_log h hb

theorem log_le_log_two_of_le {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : Real.log x ≤ Real.log 2 := by
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; exact Real.log_nonneg (by norm_num)
  · exact Real.log_le_log h h2

theorem kernel_le_log_two {r u v : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hv : v ∈ Icc (-1 : ℝ) 1) : realEnergyCosineKernel r u v ≤ Real.log 2 := by
  have key : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖(1 : ℂ) - (r : ℂ) * ζ‖ ≤ 2 := by
    intro ζ hζ
    calc ‖(1 : ℂ) - (r : ℂ) * ζ‖ ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * ζ‖ := norm_sub_le _ _
      _ = 1 + r := by simp [hζ, abs_of_nonneg hr.1]
      _ ≤ 2 := by linarith [hr.2]
  have h1 : ‖realEnergyCirclePoint u * realEnergyCirclePoint v‖ = 1 := by
    rw [norm_mul, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv, one_mul]
  have h2 : ‖realEnergyCirclePoint u * (starRingEnd ℂ) (realEnergyCirclePoint v)‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, realEnergyCirclePoint_norm hu, realEnergyCirclePoint_norm hv,
      one_mul]
  have l1 := log_le_log_two_of_le (norm_nonneg _) (key _ h1)
  have l2 := log_le_log_two_of_le (norm_nonneg _) (key _ h2)
  unfold realEnergyCosineKernel
  linarith

theorem kernel_tendsto {u v : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huv : u ≠ v) : Tendsto (fun r => realEnergyCosineKernel r u v) (𝓝 1)
      (𝓝 (Real.log |u - v|)) := by
  have hp := realEnergy_cosine_chord_product hu hv
  have hprod : ‖(1 : ℂ) - realEnergyCirclePoint u * realEnergyCirclePoint v‖ *
        ‖(1 : ℂ) - realEnergyCirclePoint u * (starRingEnd ℂ) (realEnergyCirclePoint v)‖ ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hne1 := (mul_ne_zero_iff.mp hprod).1
  have hne2 := (mul_ne_zero_iff.mp hprod).2
  have hc : ContinuousAt (fun r : ℝ => realEnergyCosineKernel r u v) 1 := by
    unfold realEnergyCosineKernel
    refine ContinuousAt.add (ContinuousAt.add continuousAt_const ?_) ?_
    · refine (Real.continuousAt_log ?_).comp (f := fun r : ℝ =>
        ‖(1 : ℂ) - (r : ℂ) * (realEnergyCirclePoint u * realEnergyCirclePoint v)‖) ?_
      · simpa using hne1
      · fun_prop
    · refine (Real.continuousAt_log ?_).comp (f := fun r : ℝ =>
        ‖(1 : ℂ) - (r : ℂ) * (realEnergyCirclePoint u *
          (starRingEnd ℂ) (realEnergyCirclePoint v))‖) ?_
      · simpa using hne2
      · fun_prop
  rw [← realEnergyCosineKernel_one hu hv huv]
  exact hc.tendsto

theorem measurable_kernel (r : ℝ) :
    Measurable (fun p : ℝ × ℝ => realEnergyCosineKernel r (Real.cos p.1) (Real.cos p.2)) := by
  unfold realEnergyCosineKernel realEnergyCirclePoint
  fun_prop

/-! ### D. The energy of the trial -/

theorem integral_cheb_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {k : ℕ}
    (hk : k ≠ 0) :
    ∫ θ, (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) ∂(denMeasure b K) =
      if k ≤ K then b k else 0 := by
  rw [integral_denMeasure h]
  have : ∀ θ, denQ b K θ * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) =
      chebP b K (Real.cos θ) * Real.cos ((k : ℝ) * θ) / Real.pi := by
    intro θ
    rw [Polynomial.Chebyshev.T_real_cos]
    simp only [denQ, Int.cast_natCast]
    ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, integral_chebP_cos_mul b K k hk]
  split_ifs
  · field_simp
  · simp

theorem kernel_series_bound {r u v : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    |realEnergyCosineKernel r u v| ≤ Real.log 2 + 2 / (1 - r) := by
  have hs := energy_hasSum_cosine_kernel hr hu hv
  have hsum := energy_summable_abs_cosine_kernel hr hu hv
  have hb : ∀ k : ℕ, |2 * r ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u *
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v / (k : ℝ)| ≤ 2 * r ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have h1 := energy_chebyshev_abs_le_one k hu
    have h2 := energy_chebyshev_abs_le_one k hv
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hrk : 0 ≤ r ^ k := pow_nonneg hr.1 k
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hrk, abs_two, Nat.abs_cast,
      div_le_iff₀ (by linarith)]
    have := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    nlinarith [abs_nonneg ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u),
      abs_nonneg ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v)]
  have hgeo : Summable (fun k : ℕ => 2 * r ^ k) :=
    (summable_geometric_of_lt_one hr.1 hr.2).mul_left 2
  have h3 : ∑' k : ℕ, |2 * r ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u *
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v / (k : ℝ)| ≤ ∑' k : ℕ, 2 * r ^ k :=
    hsum.tsum_le_tsum hb hgeo
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr.1 hr.2] at h3
  have h4 := hs.tsum_eq
  have h5 : |∑' k : ℕ, 2 * r ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u *
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v / (k : ℝ)| ≤
      ∑' k : ℕ, |2 * r ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v / (k : ℝ)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (f := fun k : ℕ => 2 * r ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v / (k : ℝ))
      (by simpa only [Real.norm_eq_abs] using hsum)
  have h6 : realEnergyCosineKernel r u v = -(∑' k : ℕ, 2 * r ^ k *
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v /
        (k : ℝ)) - Real.log 2 := by linarith
  have h7 : (2 : ℝ) * (1 - r)⁻¹ = 2 / (1 - r) := by rw [div_eq_mul_inv]
  rw [h6]
  calc _ ≤ |∑' k : ℕ, 2 * r ^ k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval u *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval v / (k : ℝ)| + |Real.log 2| := by
        rw [sub_eq_add_neg, ← abs_neg (∑' k : ℕ, _), ← abs_neg (Real.log 2)]
        exact abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
      linarith

theorem integrable_kernel_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => realEnergyCosineKernel r (Real.cos p.1) (Real.cos p.2))
      ((denMeasure b K).prod (denMeasure b K)) := by
  have := isProbabilityMeasure_denMeasure h
  refine Integrable.mono' (integrable_const (Real.log 2 + 2 / (1 - r)))
    (measurable_kernel r).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  exact kernel_series_bound hr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem integral_kernel_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    ∫ p : ℝ × ℝ, realEnergyCosineKernel r (Real.cos p.1) (Real.cos p.2)
        ∂((denMeasure b K).prod (denMeasure b K)) =
      -Real.log 2 - ∑ i ∈ Finset.range K, 2 * r ^ (i + 1) * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) := by
  have := isProbabilityMeasure_denMeasure h
  set ν := denMeasure b K with hν
  set F : ℕ → ℝ × ℝ → ℝ := fun k p => 2 * r ^ k *
    (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos p.1) *
    (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos p.2) / (k : ℝ) with hF
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hKeq : ∀ p : ℝ × ℝ, realEnergyCosineKernel r (Real.cos p.1) (Real.cos p.2) =
      -Real.log 2 - ∑' k, F k p := by
    intro p
    have := (energy_hasSum_cosine_kernel hr (hmem p.1) (hmem p.2)).tsum_eq
    simp only [hF]
    linarith
  have hTc : ∀ k : ℕ, Continuous fun θ : ℝ =>
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) :=
    fun k => (Polynomial.continuous _).comp Real.continuous_cos
  have hFc : ∀ k, Continuous (F k) := by
    intro k
    simp only [hF]
    exact (((continuous_const.mul ((hTc k).comp continuous_fst)).mul
      ((hTc k).comp continuous_snd)).div_const _)
  have hFb : ∀ k p, ‖F k p‖ ≤ 2 * r ^ k := by
    intro k p
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF]
    have h1 := energy_chebyshev_abs_le_one k (hmem p.1)
    have h2 := energy_chebyshev_abs_le_one k (hmem p.2)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hrk : 0 ≤ r ^ k := pow_nonneg hr.1 k
    simp only [hF, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hrk, abs_two, Nat.abs_cast,
      div_le_iff₀ (by linarith)]
    have := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    nlinarith [abs_nonneg ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos p.1)),
      abs_nonneg ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos p.2))]
  have hFint : ∀ k, Integrable (F k) (ν.prod ν) := fun k =>
    Integrable.mono' (integrable_const (2 * r ^ k)) (hFc k).aestronglyMeasurable
      (ae_of_all _ (hFb k))
  have hgeo : Summable (fun k : ℕ => 2 * r ^ k) :=
    (summable_geometric_of_lt_one hr.1 hr.2).mul_left 2
  have hFsum : Summable (fun k => ∫ p, ‖F k p‖ ∂(ν.prod ν)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun p => norm_nonneg _)
      (fun k => ?_) hgeo
    calc ∫ p, ‖F k p‖ ∂(ν.prod ν) ≤ ∫ _p, 2 * r ^ k ∂(ν.prod ν) :=
          integral_mono (hFint k).norm (integrable_const _) (hFb k)
      _ = 2 * r ^ k := by simp
  have htsum := (hasSum_integral_of_summable_integral_norm hFint hFsum)
  -- the moments
  have hmom : ∀ k : ℕ, ∫ p, F k p ∂(ν.prod ν) =
      if 1 ≤ k ∧ k ≤ K then 2 * r ^ k * b k ^ 2 / (k : ℝ) else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF]
    have hk0 : k ≠ 0 := hk.ne'
    have : ∀ p : ℝ × ℝ, F k p = (2 * r ^ k / (k : ℝ)) *
        ((Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos p.1) *
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos p.2)) := by
      intro p
      simp only [hF]
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_prod_mul (fun θ : ℝ =>
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ)) (fun θ : ℝ =>
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ)), integral_cheb_denMeasure h hk0]
    by_cases hkK : k ≤ K
    · simp only [hkK, ↓reduceIte, and_true, show 1 ≤ k from hk]
      ring
    · simp [hkK]
  have hfin : HasSum (fun k => ∫ p, F k p ∂(ν.prod ν))
      (∑ i ∈ Finset.range K, 2 * r ^ (i + 1) * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) := by
    have h1 : HasSum (fun k => ∫ p, F k p ∂(ν.prod ν))
        (∑ k ∈ Finset.range (K + 1), ∫ p, F k p ∂(ν.prod ν)) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        simp only [Finset.mem_range, not_lt] at hk
        have hn : ¬ (1 ≤ k ∧ k ≤ K) := by omega
        rw [hmom k]
        simp only [hn, ↓reduceIte])
    convert h1 using 1
    rw [Finset.sum_range_succ']
    have h0 : ∫ p, F 0 p ∂(ν.prod ν) = 0 := by rw [hmom 0]; simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hy : 1 ≤ i + 1 ∧ i + 1 ≤ K := ⟨by omega, by simp at hi; omega⟩
    rw [hmom (i + 1)]
    simp only [hy, ↓reduceIte, and_self]
  have hGint : Integrable (fun p => ∑' k, F k p) (ν.prod ν) := by
    have : (fun p : ℝ × ℝ => ∑' k, F k p) = fun p =>
        -Real.log 2 - realEnergyCosineKernel r (Real.cos p.1) (Real.cos p.2) := by
      funext p; rw [hKeq p]; ring
    rw [this]
    exact (integrable_const _).sub (integrable_kernel_denMeasure h hr)
  simp_rw [hKeq]
  rw [integral_sub (integrable_const _) hGint, ← htsum.tsum_eq, hfin.tsum_eq]
  simp

/-- The sequence `r_n = 1 - 1/(n+2)` increasing to `1`. -/
def rseq (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem rseq_mem (n : ℕ) : rseq n ∈ Ico (0 : ℝ) 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : 0 < 1 / ((n : ℝ) + 2) := by positivity
  constructor <;> simp only [rseq] <;> linarith

theorem rseq_tendsto : Tendsto rseq atTop (𝓝 1) := by
  have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub this
  rw [sub_zero] at h
  exact h

theorem ae_mem_Icc_denMeasure (b : ℕ → ℝ) (K : ℕ) :
    ∀ᵐ θ ∂(denMeasure b K), θ ∈ Icc 0 Real.pi :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

theorem denMeasure_singleton (b : ℕ → ℝ) (K : ℕ) (x : ℝ) : denMeasure b K {x} = 0 := by
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left Real.volume_singleton

theorem ae_ne_prod_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) :
    ∀ᵐ p : ℝ × ℝ ∂((denMeasure b K).prod (denMeasure b K)), p.1 ≠ p.2 := by
  have := isProbabilityMeasure_denMeasure h
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (s := {p : ℝ × ℝ | p.1 ≠ p.2}) hs).mpr ?_
  refine ae_of_all _ fun x => ?_
  have : ∀ᵐ y ∂(denMeasure b K), y ∉ ({x} : Set ℝ) := by
    rw [ae_iff]
    simpa using denMeasure_singleton b K x
  filter_upwards [this] with y hy
  simpa [eq_comm] using hy

/-- The energy of the trial: `∬ log |cos θ - cos φ| dν dν ≥ -log 2 - Σ_k 2 b_k² / k`, and the
kernel is integrable. -/
theorem integrable_kerL_and_energy_ge {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) :
    Integrable (fun p : ℝ × ℝ => kerL p.1 p.2) ((denMeasure b K).prod (denMeasure b K)) ∧
    -Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) ≤
      ∫ p : ℝ × ℝ, kerL p.1 p.2 ∂((denMeasure b K).prod (denMeasure b K)) := by
  have hprob := isProbabilityMeasure_denMeasure h
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hae1 : ∀ᵐ p : ℝ × ℝ ∂((denMeasure b K).prod (denMeasure b K)), p.1 ∈ Icc 0 Real.pi :=
    Measure.quasiMeasurePreserving_fst.ae (ae_mem_Icc_denMeasure b K)
  have hae2 : ∀ᵐ p : ℝ × ℝ ∂((denMeasure b K).prod (denMeasure b K)), p.2 ∈ Icc 0 Real.pi :=
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_Icc_denMeasure b K)
  have hae3 := ae_ne_prod_denMeasure h
  have hfm : ∀ n, Measurable (fun p : ℝ × ℝ =>
      realEnergyCosineKernel (rseq n) (Real.cos p.1) (Real.cos p.2)) :=
    fun n => measurable_kernel _
  have hfC : ∀ n (p : ℝ × ℝ),
      realEnergyCosineKernel (rseq n) (Real.cos p.1) (Real.cos p.2) ≤ Real.log 2 :=
    fun n p => kernel_le_log_two ⟨(rseq_mem n).1, (rseq_mem n).2.le⟩ (hmem _) (hmem _)
  have hint : ∀ n, Integrable (fun p : ℝ × ℝ =>
      realEnergyCosineKernel (rseq n) (Real.cos p.1) (Real.cos p.2))
      ((denMeasure b K).prod (denMeasure b K)) :=
    fun n => integrable_kernel_denMeasure h (rseq_mem n)
  have hlim : ∀ᵐ p : ℝ × ℝ ∂((denMeasure b K).prod (denMeasure b K)),
      Tendsto (fun n => realEnergyCosineKernel (rseq n) (Real.cos p.1) (Real.cos p.2)) atTop
        (𝓝 (kerL p.1 p.2)) := by
    filter_upwards [hae1, hae2, hae3] with p h1 h2 h3
    have hne : Real.cos p.1 ≠ Real.cos p.2 := fun heq => h3 (Real.injOn_cos h1 h2 heq)
    exact (kernel_tendsto (hmem p.1) (hmem p.2) hne).comp rseq_tendsto
  have hI : Tendsto (fun n => ∫ p : ℝ × ℝ,
      realEnergyCosineKernel (rseq n) (Real.cos p.1) (Real.cos p.2)
        ∂((denMeasure b K).prod (denMeasure b K))) atTop
      (𝓝 (-Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))) := by
    simp_rw [integral_kernel_denMeasure h (rseq_mem _)]
    refine tendsto_const_nhds.sub ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    have := (((rseq_tendsto.pow (i + 1)).const_mul 2).mul_const (b (i + 1) ^ 2)).div_const
      ((i + 1 : ℕ) : ℝ)
    convert this using 2
    simp
  exact fatou_real _ _ (Real.log 2) hfm measurable_kerL hfC hint hlim hI

/-! ### E. The cross field of the trial is a polynomial -/

/-- `∫ l(x, cos θ) dν' = -2 Σ_{k=1}^K (-x)^k b_k / k` for `|x| < 1`: the arcsine part contributes
`0` and the Chebyshev part a polynomial in `x`. -/
theorem integral_crossLog_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ θ, crossLog x (Real.cos θ) ∂(denMeasure b K) =
      -2 * ∑ i ∈ Finset.range K, (-x) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ) := by
  have hprob := isProbabilityMeasure_denMeasure h
  set ν := denMeasure b K with hν
  set F : ℕ → ℝ → ℝ := fun k θ => -2 * (-x) ^ (k + 1) *
    (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) / ((k + 1 : ℕ) : ℝ) with hF
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hsum : ∀ θ, HasSum (fun k => F k θ) (crossLog x (Real.cos θ)) :=
    fun θ => crossLog_hasSum hx (hmem θ)
  have hFc : ∀ k, Continuous (F k) := by
    intro k
    simp only [hF]
    exact (continuous_const.mul ((Polynomial.continuous _).comp Real.continuous_cos)).div_const _
  have hxa : |x| < 1 := abs_lt.mpr hx
  have hFb : ∀ k θ, ‖F k θ‖ ≤ 2 * |x| ^ (k + 1) := by
    intro k θ
    have h1 := energy_chebyshev_abs_le_one (k + 1) (hmem θ)
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    simp only [hF, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_mul, abs_neg, abs_two, abs_pow, Nat.abs_cast,
      div_le_iff₀ (by linarith), abs_neg]
    have h2 : 0 ≤ |x| ^ (k + 1) := pow_nonneg (abs_nonneg _) _
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h2)
    nlinarith [abs_nonneg ((Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))]
  have hFint : ∀ k, Integrable (F k) ν := fun k =>
    Integrable.mono' (integrable_const (2 * |x| ^ (k + 1))) (hFc k).aestronglyMeasurable
      (ae_of_all _ (hFb k))
  have hgeo : Summable (fun k : ℕ => 2 * |x| ^ (k + 1)) := by
    have := (summable_geometric_of_lt_one (abs_nonneg x) hxa).mul_left (2 * |x|)
    refine this.congr fun k => ?_
    ring
  have hFsum : Summable (fun k => ∫ θ, ‖F k θ‖ ∂ν) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun θ => norm_nonneg _)
      (fun k => ?_) hgeo
    calc ∫ θ, ‖F k θ‖ ∂ν ≤ ∫ _θ, 2 * |x| ^ (k + 1) ∂ν :=
          integral_mono (hFint k).norm (integrable_const _) (hFb k)
      _ = 2 * |x| ^ (k + 1) := by simp
  have htsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hmom : ∀ k : ℕ, ∫ θ, F k θ ∂ν =
      if k + 1 ≤ K then -2 * (-x) ^ (k + 1) * b (k + 1) / ((k + 1 : ℕ) : ℝ) else 0 := by
    intro k
    have : ∀ θ, F k θ = (-2 * (-x) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) := by
      intro θ
      simp only [hF]
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_cheb_denMeasure h (Nat.succ_ne_zero k)]
    by_cases hkK : k + 1 ≤ K
    · simp only [hkK, ↓reduceIte]
      ring
    · simp [hkK]
  have hfin : HasSum (fun k => ∫ θ, F k θ ∂ν)
      (∑ i ∈ Finset.range K, -2 * (-x) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ)) := by
    have h1 : HasSum (fun k => ∫ θ, F k θ ∂ν) (∑ k ∈ Finset.range K, ∫ θ, F k θ ∂ν) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        simp only [Finset.mem_range, not_lt] at hk
        have hn : ¬ (k + 1 ≤ K) := by omega
        rw [hmom k]
        simp only [hn, ↓reduceIte])
    convert h1 using 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hy : i + 1 ≤ K := by simp at hi; omega
    rw [hmom i]
    simp only [hy, ↓reduceIte]
  have heq : (fun θ => ∑' k, F k θ) = fun θ => crossLog x (Real.cos θ) :=
    funext fun θ => (hsum θ).tsum_eq
  rw [← heq, ← htsum.tsum_eq, hfin.tsum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### F. Product measures on `[0, π]^s` -/

/-- Lebesgue measure on the cube `[0, π]^s`. -/
def lebPi (s : ℕ) : Measure (Fin s → ℝ) := Measure.pi fun _ => volume.restrict (Icc 0 Real.pi)

/-- The product of `s` copies of the trial measure. -/
abbrev denPi (b : ℕ → ℝ) (K s : ℕ) : Measure (Fin s → ℝ) := Measure.pi fun _ => denMeasure b K

theorem integrable_denQ_restrict (b : ℕ → ℝ) (K : ℕ) (t : Set ℝ) :
    Integrable (denQ b K) ((volume.restrict (Icc 0 Real.pi)).restrict t) :=
  Integrable.mono' (integrable_const ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi))
    (continuous_denQ b K).aestronglyMeasurable (by
      refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs]
      unfold denQ
      rw [abs_div, abs_of_pos Real.pi_pos]
      exact div_le_div_of_nonneg_right (abs_chebP_cos_le b K x) Real.pi_pos.le)

theorem denMeasure_apply {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {t : Set ℝ}
    (ht : MeasurableSet t) :
    denMeasure b K t = ENNReal.ofReal (∫ x in t, denQ b K x ∂(volume.restrict (Icc 0 Real.pi))) := by
  unfold denMeasure
  rw [withDensity_apply _ ht, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_denQ_restrict b K t) (ae_of_all _ fun x => (denQ_pos h x).le)]

theorem continuous_prodQ (b : ℕ → ℝ) (K s : ℕ) :
    Continuous (fun θ : Fin s → ℝ => ∏ l, denQ b K (θ l)) :=
  continuous_finsetProd _ fun l _ => (continuous_denQ b K).comp (continuous_apply l)

theorem denPi_eq_withDensity {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (s : ℕ) :
    denPi b K s = (lebPi s).withDensity fun θ => ENNReal.ofReal (∏ l, denQ b K (θ l)) := by
  have hprob := isProbabilityMeasure_denMeasure h
  unfold denPi
  refine Measure.pi_eq fun t ht => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi ht)]
  unfold lebPi
  rw [Measure.restrict_pi_pi, ← ofReal_integral_eq_lintegral_ofReal ?_ ?_]
  · rw [integral_fintype_prod_eq_prod (fun _ x => denQ b K x),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun x => (denQ_pos h x).le)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [denMeasure_apply h (ht i)]
  · refine Integrable.mono' (integrable_const (∏ _l : Fin s,
        (1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi))
      (continuous_prodQ b K s).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun l _ => (denQ_pos h _).le)]
    exact Finset.prod_le_prod₀ (fun l _ => (denQ_pos h _).le) fun l _ => denQ_le b K _
  · exact ae_of_all _ fun x => Finset.prod_nonneg fun l _ => (denQ_pos h _).le

theorem map_pair_denPi {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {s : ℕ}
    {l l' : Fin s} (hne : l ≠ l') :
    (denPi b K s).map (fun θ => (θ l, θ l')) = (denMeasure b K).prod (denMeasure b K) := by
  have hprob := isProbabilityMeasure_denMeasure h
  unfold denPi
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin s => denMeasure b K)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have h1 : ProbabilityTheory.IndepFun (fun ω : Fin s → ℝ => ω l) (fun ω : Fin s → ℝ => ω l')
      (Measure.pi fun _ : Fin s => denMeasure b K) := hind.indepFun hne
  have hfl : AEMeasurable (fun ω : Fin s → ℝ => ω l) (Measure.pi fun _ : Fin s => denMeasure b K) :=
    (measurable_pi_apply l).aemeasurable
  have hfl' : AEMeasurable (fun ω : Fin s → ℝ => ω l')
      (Measure.pi fun _ : Fin s => denMeasure b K) := (measurable_pi_apply l').aemeasurable
  have h2 := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hfl hfl').mp h1
  have e1 : (Measure.pi fun _ : Fin s => denMeasure b K).map (fun θ => θ l) = denMeasure b K :=
    (measurePreserving_eval (fun _ : Fin s => denMeasure b K) l).map_eq
  have e2 : (Measure.pi fun _ : Fin s => denMeasure b K).map (fun θ => θ l') = denMeasure b K :=
    (measurePreserving_eval (fun _ : Fin s => denMeasure b K) l').map_eq
  rw [e1, e2] at h2
  exact h2

theorem integral_pair_denPi {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {s : ℕ}
    {l l' : Fin s} (hne : l ≠ l') {g : ℝ × ℝ → ℝ}
    (hg : AEStronglyMeasurable g ((denMeasure b K).prod (denMeasure b K))) :
    ∫ θ, g (θ l, θ l') ∂(denPi b K s) = ∫ p, g p ∂((denMeasure b K).prod (denMeasure b K)) := by
  have hm : Measurable (fun θ : Fin s → ℝ => (θ l, θ l')) := by fun_prop
  rw [← map_pair_denPi h hne, integral_map hm.aemeasurable (by rwa [map_pair_denPi h hne])]

theorem integrable_pair_denPi {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {s : ℕ}
    {l l' : Fin s} (hne : l ≠ l') {g : ℝ × ℝ → ℝ}
    (hg : Integrable g ((denMeasure b K).prod (denMeasure b K))) :
    Integrable (fun θ : Fin s → ℝ => g (θ l, θ l')) (denPi b K s) := by
  have hm : Measurable (fun θ : Fin s → ℝ => (θ l, θ l')) := by fun_prop
  rw [← map_pair_denPi h hne] at hg
  exact (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).mp hg

theorem integral_single_denPi {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {s : ℕ}
    (l : Fin s) {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (denMeasure b K)) :
    ∫ θ, g (θ l) ∂(denPi b K s) = ∫ x, g x ∂(denMeasure b K) := by
  have hprob := isProbabilityMeasure_denMeasure h
  have e1 : (denPi b K s).map (fun θ => θ l) = denMeasure b K :=
    (measurePreserving_eval (fun _ : Fin s => denMeasure b K) l).map_eq
  have hm : Measurable (fun θ : Fin s → ℝ => θ l) := measurable_pi_apply l
  rw [← e1] at hg
  rw [← e1]
  exact (integral_map hm.aemeasurable hg).symm

/-! ### G. The Jensen lower bound -/

/-- The log-gas exponent on `[0, π]^s`: `Σ_{l ≠ l'} log |cos θ_l - cos θ_l'| + Σ_l Q(cos θ_l)`. -/
def denEnergy (Q : ℝ → ℝ) (s : ℕ) (θ : Fin s → ℝ) : ℝ :=
  ∑ l, ∑ l' ∈ Finset.univ.erase l, kerL (θ l) (θ l') + ∑ l, Q (Real.cos (θ l))

/-- The denominator `Z = ∫_{[0,π]^s} exp (denEnergy) dθ`. -/
def denZ (Q : ℝ → ℝ) (s : ℕ) : ℝ := ∫ θ, Real.exp (denEnergy Q s θ) ∂(lebPi s)

/-- The differential entropy `-∫₀^π q log q dθ` of the trial density. -/
def denEntropy (b : ℕ → ℝ) (K : ℕ) : ℝ :=
  -∫ θ in (0 : ℝ)..Real.pi, denQ b K θ * Real.log (denQ b K θ)

theorem sum_erase_const (s : ℕ) (S : ℝ) :
    ∑ l : Fin s, ∑ _l' ∈ Finset.univ.erase l, S = (s : ℝ) * ((s : ℝ) - 1) * S := by
  cases s with
  | zero => simp
  | succ n =>
    have hc : ∀ l : Fin (n + 1), (Finset.univ.erase l).card = n := fun l => by simp
    simp only [Finset.sum_const, hc, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

theorem measurable_denEnergy {Q : ℝ → ℝ} (hQm : Measurable Q) (s : ℕ) :
    Measurable (denEnergy Q s) := by
  have hk : ∀ l l' : Fin s, Measurable fun θ : Fin s → ℝ => kerL (θ l) (θ l') := fun l l' => by
    unfold kerL
    fun_prop
  have hq : ∀ l : Fin s, Measurable fun θ : Fin s → ℝ => Q (Real.cos (θ l)) := fun l => by fun_prop
  have h1 : Measurable fun θ : Fin s → ℝ => ∑ l, ∑ l' ∈ Finset.univ.erase l, kerL (θ l) (θ l') :=
    Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun l' _ => hk l l'
  have h2 : Measurable fun θ : Fin s → ℝ => ∑ l, Q (Real.cos (θ l)) :=
    Finset.measurable_sum _ fun l _ => hq l
  exact h1.add h2

theorem denEnergy_le {Q : ℝ → ℝ} {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ)
    (θ : Fin s → ℝ) :
    denEnergy Q s θ ≤ (s : ℝ) * ((s : ℝ) - 1) * Real.log 2 + s * M := by
  unfold denEnergy
  have e := sum_erase_const s (Real.log 2)
  have h1 : ∑ l, ∑ l' ∈ Finset.univ.erase l, kerL (θ l) (θ l') ≤
      ∑ l : Fin s, ∑ _l' ∈ Finset.univ.erase l, Real.log 2 :=
    Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => kerL_le _ _
  have h2 : ∑ l, Q (Real.cos (θ l)) ≤ ∑ _l : Fin s, M :=
    Finset.sum_le_sum fun l _ =>
      (le_abs_self _).trans (hQb _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  linarith

theorem abs_log_denQ_le {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (θ : ℝ) :
    |Real.log (denQ b K θ)| ≤
      |Real.log (c / Real.pi)| + |Real.log ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi)| := by
  have hq := denQ_pos h θ
  have hc : 0 < c / Real.pi := div_pos h.1 Real.pi_pos
  have h1 : Real.log (c / Real.pi) ≤ Real.log (denQ b K θ) := Real.log_le_log hc (denQ_ge h θ)
  have h2 : Real.log (denQ b K θ) ≤
      Real.log ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi) :=
    Real.log_le_log hq (denQ_le b K θ)
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log (c / Real.pi)),
    le_abs_self (Real.log ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi)),
    abs_nonneg (Real.log (c / Real.pi)),
    abs_nonneg (Real.log ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi))]

/-- The tilted exponent `g = E - log P` of Jensen's inequality. -/
def denTilt (b : ℕ → ℝ) (K : ℕ) (Q : ℝ → ℝ) (s : ℕ) (θ : Fin s → ℝ) : ℝ :=
  denEnergy Q s θ - ∑ l, Real.log (denQ b K (θ l))

theorem denZ_eq_integral_tilt {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (Q : ℝ → ℝ)
    (s : ℕ) : denZ Q s = ∫ θ, Real.exp (denTilt b K Q s θ) ∂(denPi b K s) := by
  rw [denPi_eq_withDensity h s, integral_withDensity_eq_integral_toReal_smul
    (continuous_prodQ b K s).measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  unfold denZ
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  have hD : 0 < ∏ l, denQ b K (θ l) := Finset.prod_pos fun l _ => denQ_pos h _
  simp only [denTilt, smul_eq_mul]
  rw [ENNReal.toReal_ofReal hD.le, Real.exp_sub, Real.exp_sum]
  have : ∏ l, Real.exp (Real.log (denQ b K (θ l))) = ∏ l, denQ b K (θ l) :=
    Finset.prod_congr rfl fun l _ => Real.exp_log (denQ_pos h _)
  rw [this]
  field_simp

theorem integrable_single_denPi {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {Q : ℝ → ℝ}
    (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) {s : ℕ} (l : Fin s) :
    Integrable (fun θ : Fin s → ℝ => Q (Real.cos (θ l))) (denPi b K s) := by
  have hprob := isProbabilityMeasure_denMeasure h
  exact Integrable.mono' (integrable_const M)
    (hQm.comp (Real.continuous_cos.measurable.comp (measurable_pi_apply l))).aestronglyMeasurable
    (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs]
      exact hQb _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

theorem integrable_denEnergy {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {Q : ℝ → ℝ}
    (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) :
    Integrable (denEnergy Q s) (denPi b K s) := by
  have hK := (integrable_kerL_and_energy_ge h).1
  unfold denEnergy
  refine Integrable.add (integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun l' hl' => ?_)
    (integrable_finsetSum _ fun l _ => integrable_single_denPi h hQm hQb l)
  exact integrable_pair_denPi h (Ne.symm (Finset.ne_of_mem_erase hl')) hK

theorem integral_denEnergy {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {Q : ℝ → ℝ}
    (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) :
    ∫ θ, denEnergy Q s θ ∂(denPi b K s) =
      (s : ℝ) * ((s : ℝ) - 1) * ∫ p : ℝ × ℝ, kerL p.1 p.2 ∂((denMeasure b K).prod (denMeasure b K)) +
        (s : ℝ) * ∫ x, Q (Real.cos x) ∂(denMeasure b K) := by
  have hK := (integrable_kerL_and_energy_ge h).1
  have hQ : AEStronglyMeasurable (fun x => Q (Real.cos x)) (denMeasure b K) :=
    (hQm.comp Real.continuous_cos.measurable).aestronglyMeasurable
  unfold denEnergy
  rw [integral_add (integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun l' hl' =>
      integrable_pair_denPi h (Ne.symm (Finset.ne_of_mem_erase hl')) hK)
    (integrable_finsetSum _ fun l _ => integrable_single_denPi h hQm hQb l)]
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun l' hl' =>
      integrable_pair_denPi h (Ne.symm (Finset.ne_of_mem_erase hl')) hK),
    integral_finsetSum _ (fun l _ => integrable_single_denPi h hQm hQb l)]
  have h1 : ∀ l : Fin s, ∫ θ, ∑ l' ∈ Finset.univ.erase l, kerL (θ l) (θ l') ∂(denPi b K s) =
      ∑ _l' ∈ Finset.univ.erase l, ∫ p : ℝ × ℝ, kerL p.1 p.2 ∂((denMeasure b K).prod (denMeasure b K)) := by
    intro l
    rw [integral_finsetSum _ (fun l' hl' =>
      integrable_pair_denPi h (Ne.symm (Finset.ne_of_mem_erase hl')) hK)]
    refine Finset.sum_congr rfl fun l' hl' => ?_
    exact integral_pair_denPi h (Ne.symm (Finset.ne_of_mem_erase hl')) hK.aestronglyMeasurable
  have h2 : ∀ l : Fin s, ∫ θ, Q (Real.cos (θ l)) ∂(denPi b K s) =
      ∫ x, Q (Real.cos x) ∂(denMeasure b K) := fun l => integral_single_denPi h l hQ
  simp_rw [h1, h2]
  rw [sum_erase_const]
  simp

theorem integral_log_denPi {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) (s : ℕ) :
    Integrable (fun θ : Fin s → ℝ => ∑ l, Real.log (denQ b K (θ l))) (denPi b K s) ∧
    ∫ θ, ∑ l, Real.log (denQ b K (θ l)) ∂(denPi b K s) = s * (-denEntropy b K) := by
  have hprob := isProbabilityMeasure_denMeasure h
  have hm : Measurable (fun x => Real.log (denQ b K x)) :=
    Real.measurable_log.comp (continuous_denQ b K).measurable
  have hint : ∀ l : Fin s, Integrable (fun θ : Fin s → ℝ => Real.log (denQ b K (θ l)))
      (denPi b K s) := by
    intro l
    exact Integrable.mono'
      (integrable_const (|Real.log (c / Real.pi)| +
        |Real.log ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi)|))
      (hm.comp (measurable_pi_apply l)).aestronglyMeasurable
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact abs_log_denQ_le h _)
  refine ⟨integrable_finsetSum _ fun l _ => hint l, ?_⟩
  rw [integral_finsetSum _ (fun l _ => hint l)]
  have h2 : ∀ l : Fin s, ∫ θ, Real.log (denQ b K (θ l)) ∂(denPi b K s) =
      -denEntropy b K := by
    intro l
    rw [integral_single_denPi h l hm.aestronglyMeasurable, integral_denMeasure h]
    unfold denEntropy
    rw [neg_neg]
  simp_rw [h2]
  simp

theorem integrable_tilt {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {Q : ℝ → ℝ}
    (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) :
    Integrable (denTilt b K Q s) (denPi b K s) ∧
      Integrable (fun θ => Real.exp (denTilt b K Q s θ)) (denPi b K s) := by
  have hprob := isProbabilityMeasure_denMeasure h
  set L0 := |Real.log (c / Real.pi)| +
    |Real.log ((1 + 2 * ∑ k ∈ Finset.range K, |b (k + 1)|) / Real.pi)| with hL0
  have hint : Integrable (denTilt b K Q s) (denPi b K s) :=
    (integrable_denEnergy h hQm hQb s).sub (integral_log_denPi h s).1
  refine ⟨hint, ?_⟩
  have hbd : ∀ θ, denTilt b K Q s θ ≤ (s : ℝ) * ((s : ℝ) - 1) * Real.log 2 + s * M + s * L0 := by
    intro θ
    unfold denTilt
    have h1 := denEnergy_le hQb s θ
    have h2 : -∑ l, Real.log (denQ b K (θ l)) ≤ s * L0 := by
      have : ∑ l, |Real.log (denQ b K (θ l))| ≤ ∑ _l : Fin s, L0 :=
        Finset.sum_le_sum fun l _ => abs_log_denQ_le h _
      have h3 : -∑ l, Real.log (denQ b K (θ l)) ≤ ∑ l, |Real.log (denQ b K (θ l))| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun l _ => neg_le_abs _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    linarith
  refine Integrable.mono'
    (integrable_const (Real.exp ((s : ℝ) * ((s : ℝ) - 1) * Real.log 2 + s * M + s * L0)))
    (Real.continuous_exp.comp_aestronglyMeasurable hint.aestronglyMeasurable)
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (hbd θ)

theorem sq_le_aux (q : ℝ) (hq : 0 < q) :
    -(Real.pi * q ^ 2) + q + Real.log Real.pi * q ≤ -(q * Real.log q) := by
  have h1 : Real.log (Real.pi * q) ≤ Real.pi * q - 1 :=
    Real.log_le_sub_one_of_pos (mul_pos Real.pi_pos hq)
  rw [Real.log_mul Real.pi_pos.ne' hq.ne'] at h1
  nlinarith [mul_pos hq hq]

/-- The crude entropy bound `h(q) ≥ log π - 2 Σ b_k²`, from `log (π q) ≤ π q - 1`. -/
theorem denEntropy_ge {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) :
    Real.log Real.pi - 2 * ∑ k ∈ Finset.range K, b (k + 1) ^ 2 ≤ denEntropy b K := by
  unfold denEntropy
  rw [← intervalIntegral.integral_neg]
  have hc := continuous_denQ b K
  have hlog : Continuous (fun θ => denQ b K θ * Real.log (denQ b K θ)) :=
    hc.mul (hc.log fun θ => (denQ_pos h θ).ne')
  have hmono : ∫ θ in (0 : ℝ)..Real.pi,
      (-(Real.pi * denQ b K θ ^ 2) + denQ b K θ + Real.log Real.pi * denQ b K θ) ≤
      ∫ θ in (0 : ℝ)..Real.pi, -(denQ b K θ * Real.log (denQ b K θ)) :=
    intervalIntegral.integral_mono_on Real.pi_pos.le
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; exact hlog.neg)
      fun θ _ => sq_le_aux _ (denQ_pos h θ)
  refine le_trans (le_of_eq ?_) hmono
  have hsq : ∫ θ in (0 : ℝ)..Real.pi, denQ b K θ ^ 2 =
      (1 + 2 * ∑ k ∈ Finset.range K, b (k + 1) ^ 2) / Real.pi := by
    have : ∀ θ, denQ b K θ ^ 2 = chebP b K (Real.cos θ) ^ 2 / Real.pi ^ 2 := by
      intro θ; unfold denQ; rw [div_pow]
    simp_rw [this]
    rw [intervalIntegral.integral_div, integral_chebP_cos_sq]
    field_simp
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_denQ, hsq]
  field_simp
  ring

/-- **J5, Jensen lower bound for the denominator** (Lemma 3.5 / Lemma 7.4 in `θ`-form).
For a trial `ν' = P(cos θ) dθ / π` with `P = 1 + 2 Σ_{k=1}^K b_k T_k ≥ c > 0` on `[-1, 1]` and a
bounded measurable field `Q`,
`log Z ≥ s(s-1) Σ(ν') + s ∫ Q dν' + s h(ν')`, with `Σ(ν') ≥ -log 2 - Σ_k 2 b_k²/k`. -/
theorem arcsine_jensen_denominator {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) {Q : ℝ → ℝ}
    (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) :
    0 < denZ Q s ∧
    (s : ℝ) * ((s : ℝ) - 1) *
        (-Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      s * (∫ θ in (0 : ℝ)..Real.pi, denQ b K θ * Q (Real.cos θ)) + s * denEntropy b K ≤
      Real.log (denZ Q s) := by
  have hprob := isProbabilityMeasure_denMeasure h
  obtain ⟨hgi, hegi⟩ := integrable_tilt h hQm hQb s
  have hJ : Real.exp (∫ θ, denTilt b K Q s θ ∂(denPi b K s)) ≤
      ∫ θ, Real.exp (denTilt b K Q s θ) ∂(denPi b K s) :=
    ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => mem_univ _) hgi hegi
  have hZ := denZ_eq_integral_tilt h Q s
  have hZpos : 0 < denZ Q s := by
    rw [hZ]; exact lt_of_lt_of_le (Real.exp_pos _) hJ
  refine ⟨hZpos, ?_⟩
  have hlog : ∫ θ, denTilt b K Q s θ ∂(denPi b K s) ≤ Real.log (denZ Q s) := by
    rw [Real.le_log_iff_exp_le hZpos, hZ]
    exact hJ
  have hint : ∫ θ, denTilt b K Q s θ ∂(denPi b K s) =
      (∫ θ, denEnergy Q s θ ∂(denPi b K s)) -
        ∫ θ, ∑ l, Real.log (denQ b K (θ l)) ∂(denPi b K s) :=
    integral_sub (integrable_denEnergy h hQm hQb s) (integral_log_denPi h s).1
  rw [hint, integral_denEnergy h hQm hQb s, (integral_log_denPi h s).2,
    integral_denMeasure h (fun x => Q (Real.cos x))] at hlog
  have hnn : (0 : ℝ) ≤ (s : ℝ) * ((s : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      exact mul_nonneg (by linarith) (by linarith)
  have hS := (integrable_kerL_and_energy_ge h).2
  have := mul_le_mul_of_nonneg_left hS hnn
  linarith

/-- The same with the entropy replaced by its crude lower bound `log π - 2 Σ b_k²`. -/
theorem arcsine_jensen_denominator_crude {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c)
    {Q : ℝ → ℝ} (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) :
    0 < denZ Q s ∧
    (s : ℝ) * ((s : ℝ) - 1) *
        (-Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      s * (∫ θ in (0 : ℝ)..Real.pi, denQ b K θ * Q (Real.cos θ)) +
      s * (Real.log Real.pi - 2 * ∑ k ∈ Finset.range K, b (k + 1) ^ 2) ≤
      Real.log (denZ Q s) := by
  obtain ⟨h1, h2⟩ := arcsine_jensen_denominator h hQm hQb s
  refine ⟨h1, le_trans ?_ h2⟩
  have := mul_le_mul_of_nonneg_left (denEntropy_ge h) (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  linarith

/-! ### H. The energy of the trial is exact -/

theorem tendsto_energy_series (b : ℕ → ℝ) (K : ℕ) :
    Tendsto (fun n => -Real.log 2 -
      ∑ i ∈ Finset.range K, 2 * rseq n ^ (i + 1) * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) atTop
      (𝓝 (-Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))) := by
  refine tendsto_const_nhds.sub ?_
  refine tendsto_finsetSum _ fun i _ => ?_
  have := (((rseq_tendsto.pow (i + 1)).const_mul 2).mul_const (b (i + 1) ^ 2)).div_const
    ((i + 1 : ℕ) : ℝ)
  convert this using 2
  simp

/-- **The energy of the trial** (Lemma 7.4 (i)):
`Σ(ν') = ∬ log |u - v| dν' dν' = -log 2 - Σ_{k=1}^K 2 b_k² / k`. -/
theorem integral_kerL_denMeasure {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) :
    ∫ p : ℝ × ℝ, kerL p.1 p.2 ∂((denMeasure b K).prod (denMeasure b K)) =
      -Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) := by
  have hprob := isProbabilityMeasure_denMeasure h
  refine le_antisymm ?_ (integrable_kerL_and_energy_ge h).2
  have hI := (integrable_kerL_and_energy_ge h).1
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hae := ae_ne_prod_denMeasure h
  have hbound : ∀ n, ∫ p : ℝ × ℝ, kerL p.1 p.2 ∂((denMeasure b K).prod (denMeasure b K)) ≤
      (-Real.log 2 - ∑ i ∈ Finset.range K,
        2 * rseq n ^ (i + 1) * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) - Real.log (rseq n) := by
    intro n
    have hr0 : 0 < rseq n := by
      have := (rseq_mem n).1
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      simp only [rseq] at *
      linarith
    have hKint := integrable_kernel_denMeasure h (rseq_mem n)
    calc ∫ p : ℝ × ℝ, kerL p.1 p.2 ∂((denMeasure b K).prod (denMeasure b K))
        ≤ ∫ p : ℝ × ℝ, (realEnergyCosineKernel (rseq n) (Real.cos p.1) (Real.cos p.2) -
            Real.log (rseq n)) ∂((denMeasure b K).prod (denMeasure b K)) := by
          refine integral_mono_ae hI (hKint.sub (integrable_const _)) ?_
          filter_upwards [(Measure.quasiMeasurePreserving_fst.ae (ae_mem_Icc_denMeasure b K)),
            (Measure.quasiMeasurePreserving_snd.ae (ae_mem_Icc_denMeasure b K)), hae]
            with p h1 h2 h3
          have hne : Real.cos p.1 ≠ Real.cos p.2 := fun heq => h3 (Real.injOn_cos h1 h2 heq)
          exact realEnergyCosineKernel_compare (hmem _) (hmem _) hne hr0
      _ = _ := by
          rw [integral_sub hKint (integrable_const _), integral_kernel_denMeasure h (rseq_mem n)]
          simp
  have hlim : Tendsto (fun n => (-Real.log 2 - ∑ i ∈ Finset.range K,
        2 * rseq n ^ (i + 1) * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) - Real.log (rseq n)) atTop
      (𝓝 (-Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))) := by
    have hl : Tendsto (fun n => Real.log (rseq n)) atTop (𝓝 0) := by
      have := (Real.continuousAt_log one_ne_zero).tendsto.comp rseq_tendsto
      simpa [Function.comp_def] using this
    simpa using (tendsto_energy_series b K).sub hl
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound

/-- The two arcsine facts: for `K = 0` (the pure arcsine law) the energy is `-log 2`, i.e.
`U^η = -log 2` on `[-1, 1]` in the integrated form, and the cross field is `0`. -/
theorem arcsine_energy {c : ℝ} (h : IsTrial (fun _ => 0) 0 c) :
    ∫ p : ℝ × ℝ, kerL p.1 p.2
      ∂((denMeasure (fun _ => 0) 0).prod (denMeasure (fun _ => 0) 0)) = -Real.log 2 := by
  rw [integral_kerL_denMeasure h]
  simp

theorem arcsine_cross_field {c : ℝ} (h : IsTrial (fun _ => 0) 0 c) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ θ, crossLog x (Real.cos θ) ∂(denMeasure (fun _ => 0) 0) = 0 := by
  rw [integral_crossLog_denMeasure h hx]
  simp

theorem isTrial_arcsine : IsTrial (fun _ => 0) 0 1 := by
  refine ⟨one_pos, fun u _ => ?_⟩
  simp [chebP]

/-! ### I. Trials with summable Chebyshev coefficients

The class of §B (`IsTrial`, a finite Chebyshev polynomial) is a special case (`isTrialS_bTrunc`)
of the class of trials `P = 1 + 2 Σ_{k ≥ 1} b_k T_k` with `Σ |b_k| < ∞`.  The finite theorems above
are kept as they are; the summable versions are obtained from them by a limit `K → ∞` in the
truncations `chebP b K`, which converge uniformly (`abs_chebPs_sub_chebP_le`) and are themselves
trials for large `K` (`eventually_isTrial`). -/

/-- The Chebyshev series `1 + 2 Σ_{k ≥ 1} b_k T_k(u)` (a convergent series when `Σ |b_k| < ∞`). -/
def chebPs (b : ℕ → ℝ) (u : ℝ) : ℝ :=
  1 + 2 * ∑' k : ℕ, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u

/-- Trial class with summable coefficients: `Σ |b_k| < ∞` and `P ≥ c > 0` on `[-1, 1]`. -/
def IsTrialS (b : ℕ → ℝ) (c : ℝ) : Prop :=
  Summable (fun k : ℕ => |b (k + 1)|) ∧ 0 < c ∧ ∀ u ∈ Icc (-1 : ℝ) 1, c ≤ chebPs b u

/-- The density (in `θ`) of the trial with summable coefficients. -/
def denQs (b : ℕ → ℝ) (θ : ℝ) : ℝ := chebPs b (Real.cos θ) / Real.pi

/-- Truncation of a coefficient sequence: keep `b_k` for `k ≤ K`. -/
def bTrunc (b : ℕ → ℝ) (K : ℕ) (k : ℕ) : ℝ := if k ≤ K then b k else 0

theorem summable_chebTerm {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    Summable fun k : ℕ => b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u := by
  refine Summable.of_norm_bounded hb fun k => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (energy_chebyshev_abs_le_one (k + 1) hu)

theorem tendsto_chebP_chebPs {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun K => chebP b K u) atTop (𝓝 (chebPs b u)) := by
  have h := (summable_chebTerm hb hu).hasSum.tendsto_sum_nat
  unfold chebP chebPs
  exact tendsto_const_nhds.add (h.const_mul 2)

/-- Uniform tail bound `|P - P_K| ≤ 2 Σ_{k > K} |b_k|` on `[-1, 1]`. -/
theorem abs_chebPs_sub_chebP_le {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (K : ℕ) :
    |chebPs b u - chebP b K u| ≤ 2 * ∑' i : ℕ, |b (i + K + 1)| := by
  have hs := summable_chebTerm hb hu
  have h1 := hs.sum_add_tsum_nat_add K
  have hg : Summable fun i : ℕ => |b (i + K + 1)| := (summable_nat_add_iff K).2 hb
  have hbd : ‖∑' i : ℕ, b (i + K + 1) *
      (Polynomial.Chebyshev.T ℝ ((i + K + 1 : ℕ) : ℤ)).eval u‖ ≤ ∑' i : ℕ, |b (i + K + 1)| := by
    refine tsum_of_norm_bounded hg.hasSum fun i => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (energy_chebyshev_abs_le_one (i + K + 1) hu)
  have heq : chebPs b u - chebP b K u = 2 * ∑' i : ℕ, b (i + K + 1) *
      (Polynomial.Chebyshev.T ℝ ((i + K + 1 : ℕ) : ℤ)).eval u := by
    unfold chebPs chebP
    have : ∑' k : ℕ, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u =
        ∑ k ∈ Finset.range K, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u +
        ∑' i : ℕ, b (i + K + 1) * (Polynomial.Chebyshev.T ℝ ((i + K + 1 : ℕ) : ℤ)).eval u :=
      h1.symm
    rw [this]; ring
  rw [heq, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hbd) (by norm_num)

theorem eventually_isTrial {b : ℕ → ℝ} {c : ℝ} (h : IsTrialS b c) :
    ∀ᶠ K in atTop, IsTrial b K (c / 2) := by
  have ht : Tendsto (fun K : ℕ => ∑' i : ℕ, |b (i + K + 1)|) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k : ℕ => |b (k + 1)|)
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < c / 4 by linarith [h.2.1]))]
    with K hK
  refine ⟨by linarith [h.2.1], fun u hu => ?_⟩
  have h1 := abs_chebPs_sub_chebP_le h.1 hu K
  have h2 := h.2.2 u hu
  rw [abs_le] at h1
  linarith [h1.1, h1.2]

theorem abs_denQ_le_of_summable {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) (K : ℕ)
    (θ : ℝ) : |denQ b K θ| ≤ (1 + 2 * ∑' k : ℕ, |b (k + 1)|) / Real.pi := by
  unfold denQ
  rw [abs_div, abs_of_pos Real.pi_pos]
  refine div_le_div_of_nonneg_right ((abs_chebP_cos_le b K θ).trans ?_) Real.pi_pos.le
  have : ∑ k ∈ Finset.range K, |b (k + 1)| ≤ ∑' k : ℕ, |b (k + 1)| :=
    hb.sum_le_tsum _ fun _ _ => abs_nonneg _
  linarith

/-- Dominated convergence for the truncated densities against a bounded measurable test
function. -/
theorem tendsto_integral_denQ_mul {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    {G : ℝ → ℝ} (hGm : Measurable G) {M : ℝ} (hGb : ∀ θ, |G θ| ≤ M) :
    Tendsto (fun K => ∫ θ in (0 : ℝ)..Real.pi, denQ b K θ * G θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..Real.pi, denQs b θ * G θ)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 + 2 * ∑' k : ℕ, |b (k + 1)|) / Real.pi * M) ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall fun K =>
      ((continuous_denQ b K).measurable.mul hGm).aestronglyMeasurable
  · refine Eventually.of_forall fun K => Eventually.of_forall fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_denQ_le_of_summable hb K θ) (hGb θ) (abs_nonneg _)
      (div_nonneg (by have h0 : 0 ≤ ∑' k : ℕ, |b (k + 1)| := tsum_nonneg fun k => abs_nonneg _; linarith)
        Real.pi_pos.le)
  · refine Eventually.of_forall fun θ _ => ?_
    have := tendsto_chebP_chebPs hb (u := Real.cos θ)
      ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    exact (this.div_const Real.pi).mul_const (G θ)

theorem summable_energy_coeff {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) :
    Summable (fun i : ℕ => 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) ∧
    Summable (fun i : ℕ => b (i + 1) ^ 2) := by
  set S := ∑' k : ℕ, |b (k + 1)| with hS
  have hbS : ∀ i : ℕ, |b (i + 1)| ≤ S := fun i =>
    hb.le_tsum i fun j _ => abs_nonneg _
  have hsq : Summable (fun i : ℕ => b (i + 1) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) (hb.mul_left S)
    rw [← sq_abs]
    nlinarith [abs_nonneg (b (i + 1)), hbS i]
  refine ⟨?_, hsq⟩
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hsq.mul_left 2)
  have : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (b (i + 1))]

/-- **J5 for trials with summable Chebyshev coefficients** (crude entropy form): for a measurable
field `Q` bounded on `[-1, 1]`,
`s(s-1) Σ(ν') + s ∫ Q dν' + s (log π - 2 Σ b_k²) ≤ log Z`, where
`Σ(ν') = -log 2 - Σ_{k ≥ 1} 2 b_k² / k` (the exact energy of the trial). -/
theorem arcsine_jensen_denominator_crude_sum {b : ℕ → ℝ} {c : ℝ} (h : IsTrialS b c) {Q : ℝ → ℝ}
    (hQm : Measurable Q) {M : ℝ} (hQb : ∀ u ∈ Icc (-1 : ℝ) 1, |Q u| ≤ M) (s : ℕ) :
    0 < denZ Q s ∧
    (s : ℝ) * ((s : ℝ) - 1) *
        (-Real.log 2 - ∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      s * (∫ θ in (0 : ℝ)..Real.pi, denQs b θ * Q (Real.cos θ)) +
      s * (Real.log Real.pi - 2 * ∑' k : ℕ, b (k + 1) ^ 2) ≤
      Real.log (denZ Q s) := by
  obtain ⟨hen, hsq⟩ := summable_energy_coeff h.1
  have hev := eventually_isTrial h
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hlim : Tendsto (fun K : ℕ => (s : ℝ) * ((s : ℝ) - 1) *
        (-Real.log 2 - ∑ i ∈ Finset.range K, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      s * (∫ θ in (0 : ℝ)..Real.pi, denQ b K θ * Q (Real.cos θ)) +
      s * (Real.log Real.pi - 2 * ∑ k ∈ Finset.range K, b (k + 1) ^ 2)) atTop
      (𝓝 ((s : ℝ) * ((s : ℝ) - 1) *
        (-Real.log 2 - ∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
      s * (∫ θ in (0 : ℝ)..Real.pi, denQs b θ * Q (Real.cos θ)) +
      s * (Real.log Real.pi - 2 * ∑' k : ℕ, b (k + 1) ^ 2))) := by
    have h1 := (tendsto_const_nhds (x := -Real.log 2)).sub hen.hasSum.tendsto_sum_nat
    have h2 := tendsto_integral_denQ_mul h.1 (G := fun θ => Q (Real.cos θ))
      (hQm.comp Real.measurable_cos) (M := M) (fun θ => hQb _ (hmem θ))
    have h3 := (tendsto_const_nhds (x := Real.log Real.pi)).sub
      (hsq.hasSum.tendsto_sum_nat.const_mul 2)
    exact ((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _)
  obtain ⟨K0, hK0⟩ := hev.exists
  have hpos := (arcsine_jensen_denominator_crude hK0 hQm hQb s).1
  refine ⟨hpos, le_of_tendsto hlim ?_⟩
  filter_upwards [hev] with K hK
  exact (arcsine_jensen_denominator_crude hK hQm hQb s).2

theorem measurable_crossLog (x : ℝ) : Measurable (crossLog x) := by
  unfold crossLog
  exact Real.measurable_log.comp (by fun_prop)

/-- Uniform bound of the cross field: `|l(x, u)| ≤ log 4 + 2 |log (1 - |x|)|` on `[-1, 1]`. -/
theorem abs_crossLog_le {x : ℝ} (hxa : |x| < 1) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    |crossLog x u| ≤ Real.log 4 + 2 * |Real.log (1 - |x|)| := by
  have hp := cross_pos hxa hu
  have hlo := sq_one_sub_abs_le_cross (x := x) hu
  have hup : 1 + 2 * x * u + x ^ 2 ≤ 4 := by
    have hxc : |x * u| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg x, abs_le.mpr hu, abs_nonneg u]
    nlinarith [abs_le.mp hxc, sq_abs x, abs_nonneg x]
  have h1 : crossLog x u ≤ Real.log 4 := Real.log_le_log hp hup
  have h1a : 0 < 1 - |x| := sub_pos.mpr hxa
  have h2 : 2 * Real.log (1 - |x|) ≤ crossLog x u := by
    rw [show (2 : ℝ) * Real.log (1 - |x|) = Real.log ((1 - |x|) ^ 2) by
      rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (pow_pos h1a 2) hlo
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [neg_abs_le (Real.log (1 - |x|)), le_abs_self (Real.log (1 - |x|))]

/-- **The cross field of a summable trial**: `∫ l(x, cos θ) dν' = -2 Σ_{k ≥ 1} (-x)^k b_k / k`
for `|x| < 1`. -/
theorem integral_crossLog_denQs {b : ℕ → ℝ} {c : ℝ} (h : IsTrialS b c) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ θ in (0 : ℝ)..Real.pi, denQs b θ * crossLog x (Real.cos θ) =
      -2 * ∑' i : ℕ, (-x) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ) := by
  have hxa : |x| < 1 := abs_lt.mpr hx
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hGb : ∀ θ, |crossLog x (Real.cos θ)| ≤ Real.log 4 + 2 * |Real.log (1 - |x|)| :=
    fun θ => abs_crossLog_le hxa (hmem θ)
  have hlimL := tendsto_integral_denQ_mul h.1 (G := fun θ => crossLog x (Real.cos θ))
    (by unfold crossLog; exact Real.measurable_log.comp (by fun_prop)) hGb
  have hterm : Summable fun i : ℕ => (-x) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ) := by
    refine Summable.of_norm_bounded h.1 fun i => ?_
    have : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, Nat.abs_cast,
      div_le_iff₀ (by linarith)]
    have h1 : |x| ^ (i + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hxa.le
    nlinarith [abs_nonneg (b (i + 1)), mul_le_mul_of_nonneg_right h1 (abs_nonneg (b (i + 1)))]
  have hlimR := (hterm.hasSum.tendsto_sum_nat).const_mul (-2)
  have hlimR' : Tendsto (fun K : ℕ => -2 * ∑ i ∈ Finset.range K,
      (-x) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ)) atTop
      (𝓝 (-2 * ∑' i : ℕ, (-x) ^ (i + 1) * b (i + 1) / ((i + 1 : ℕ) : ℝ))) := hlimR
  refine tendsto_nhds_unique_of_eventuallyEq hlimL hlimR' ?_
  filter_upwards [eventually_isTrial h] with K hK
  have := integral_crossLog_denMeasure hK hx
  rw [integral_denMeasure hK] at this
  exact this

/-- The truncation of a finite trial has the same Chebyshev series. -/
theorem chebPs_bTrunc (b : ℕ → ℝ) (K : ℕ) (u : ℝ) : chebPs (bTrunc b K) u = chebP b K u := by
  unfold chebPs chebP
  congr 2
  rw [tsum_eq_sum (s := Finset.range K)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have : k + 1 ≤ K := by simp at hk; omega
    simp [bTrunc, this]
  · intro k hk
    have : ¬ (k + 1 ≤ K) := by simp at hk; omega
    simp [bTrunc, this]

/-- The finite trial class is a special case of the summable one. -/
theorem isTrialS_bTrunc {b : ℕ → ℝ} {K : ℕ} {c : ℝ} (h : IsTrial b K c) :
    IsTrialS (bTrunc b K) c := by
  refine ⟨?_, h.1, fun u hu => ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
    have : ¬ (k + 1 ≤ K) := by simp at hk; omega
    simp [bTrunc, this]
  · rw [chebPs_bTrunc]; exact h.2 u hu

/-! ### J. Fourier coefficients of summable trials, and the Poisson trials

`integral_denQs_cos`: the trial `ν' = P(cos θ) dθ / π` has `∫ T_k dν' = b_k`.
The Poisson trial `b_k = (-ρ)^k` is the balayage `β_ρ`: its density is
`(1/π)(1 - ρ²)/(1 + 2ρ cos θ + ρ²)`. -/

theorem continuous_chebPs_cos {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) :
    Continuous fun θ : ℝ => chebPs b (Real.cos θ) := by
  unfold chebPs
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_tsum (u := fun k : ℕ => |b (k + 1)|) (fun k => ?_) hb (fun k θ => ?_)
  · exact continuous_const.mul ((Polynomial.continuous _).comp Real.continuous_cos)
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (energy_chebyshev_abs_le_one (k + 1) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)

theorem continuous_denQs {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) :
    Continuous (denQs b) :=
  (continuous_chebPs_cos hb).div_const _

theorem abs_denQs_le {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) (θ : ℝ) :
    |denQs b θ| ≤ (1 + 2 * ∑' k : ℕ, |b (k + 1)|) / Real.pi := by
  have hmem : Real.cos θ ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h1' : ‖∑' k : ℕ, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval
      (Real.cos θ)‖ ≤ ∑' k : ℕ, |b (k + 1)| := by
    refine tsum_of_norm_bounded hb.hasSum fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (energy_chebyshev_abs_le_one (k + 1) hmem)
  have h1 : |∑' k : ℕ, b (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval
      (Real.cos θ)| ≤ ∑' k : ℕ, |b (k + 1)| := by simpa [Real.norm_eq_abs] using h1'
  unfold denQs chebPs
  rw [abs_div, abs_of_pos Real.pi_pos]
  refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
  have h0 : 0 ≤ ∑' k : ℕ, |b (k + 1)| := tsum_nonneg fun k => abs_nonneg _
  calc _ ≤ |(1 : ℝ)| + |2 * ∑' k : ℕ, b (k + 1) * (Polynomial.Chebyshev.T ℝ
        ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_one, abs_mul, abs_two]; linarith

/-- Dominated convergence against the fixed density `denQs b` and a uniformly bounded sequence
of test functions converging pointwise. -/
theorem tendsto_integral_denQs_mul {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|)
    {G : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hGm : ∀ K, Measurable (G K)) {M : ℝ}
    (hGb : ∀ K θ, |G K θ| ≤ M) (hlim : ∀ θ, Tendsto (fun K => G K θ) atTop (𝓝 (g θ))) :
    Tendsto (fun K => ∫ θ in (0 : ℝ)..Real.pi, denQs b θ * G K θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..Real.pi, denQs b θ * g θ)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 + 2 * ∑' k : ℕ, |b (k + 1)|) / Real.pi * M) ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall fun K =>
      ((continuous_denQs hb).measurable.mul (hGm K)).aestronglyMeasurable
  · refine Eventually.of_forall fun K => Eventually.of_forall fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_denQs_le hb θ) (hGb K θ) (abs_nonneg _)
      (div_nonneg (by have h0 : 0 ≤ ∑' k : ℕ, |b (k + 1)| := tsum_nonneg fun k => abs_nonneg _
                      linarith) Real.pi_pos.le)
  · exact Eventually.of_forall fun θ _ => (hlim θ).const_mul _

/-- `∫₀^π P(cos θ) cos (jθ) dθ / π = b_j` for `j ≥ 1`. -/
theorem integral_denQs_cos {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) {j : ℕ}
    (hj : j ≠ 0) :
    ∫ θ in (0 : ℝ)..Real.pi, denQs b θ * Real.cos ((j : ℝ) * θ) = b j := by
  have h := tendsto_integral_denQ_mul hb (G := fun θ => Real.cos ((j : ℝ) * θ))
    (by fun_prop) (M := 1) (fun θ => Real.abs_cos_le_one _)
  refine tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop j] with K hK
  have : ∀ θ, denQ b K θ * Real.cos ((j : ℝ) * θ) =
      chebP b K (Real.cos θ) * Real.cos ((j : ℝ) * θ) / Real.pi := fun θ => by
    unfold denQ; ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, integral_chebP_cos_mul b K j hj]
  simp only [hK, ↓reduceIte]
  field_simp

theorem integral_denQs {b : ℕ → ℝ} (hb : Summable fun k : ℕ => |b (k + 1)|) :
    ∫ θ in (0 : ℝ)..Real.pi, denQs b θ = 1 := by
  have h := tendsto_integral_denQ_mul hb (G := fun _ => (1 : ℝ)) (by fun_prop) (M := 1)
    (fun θ => by simp)
  simp only [mul_one, integral_denQ] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The Poisson (balayage) trial sequence `b_k = (-ρ)^k`. -/
def poisSeq (ρ : ℝ) (k : ℕ) : ℝ := (-ρ) ^ k

theorem summable_poisSeq {ρ : ℝ} (hρ : |ρ| < 1) :
    Summable fun k : ℕ => |poisSeq ρ (k + 1)| := by
  have : Summable fun k : ℕ => |ρ| ^ (k + 1) :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).comp_injective (add_left_injective 1)
  refine this.congr fun k => ?_
  unfold poisSeq
  rw [abs_pow, abs_neg]

/-- The Poisson kernel as a Chebyshev series. -/
theorem chebPs_poisSeq_cos {ρ : ℝ} (hρ : |ρ| < 1) (θ : ℝ) :
    chebPs (poisSeq ρ) (Real.cos θ) =
      (1 - ρ ^ 2) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by
  set z : ℂ := -(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs]
    exact hρ
  have hgeo := (hasSum_geometric_of_norm_lt_one hzn).mul_left z
  have hre := Complex.reCLM.hasSum hgeo
  have hterm : ∀ n : ℕ, (z * z ^ n).re = poisSeq ρ (n + 1) *
      (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval (Real.cos θ) := by
    intro n
    rw [← pow_succ' z n, hz, mul_pow, ← Complex.exp_nat_mul]
    rw [show ((n + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) = (((n + 1 : ℕ) : ℝ) * θ : ℝ) * Complex.I by
      push_cast; ring]
    rw [show (-(ρ : ℂ)) ^ (n + 1) = (((-ρ) ^ (n + 1) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Polynomial.Chebyshev.T_real_cos]
    simp [poisSeq]
  simp only [Complex.reCLM_apply, hterm] at hre
  have hsum := hre.tsum_eq
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hD : 0 < 1 + 2 * ρ * Real.cos θ + ρ ^ 2 :=
    cross_pos hρ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hzre : z.re = -ρ * Real.cos θ := by
    rw [hz]; simp [Complex.exp_ofReal_mul_I_re]
  have hzim : z.im = -ρ * Real.sin θ := by
    rw [hz]; simp [Complex.exp_ofReal_mul_I_im]
  have hnorm : Complex.normSq (1 - z) = 1 + 2 * ρ * Real.cos θ + ρ ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hzre, hzim]
    nlinarith [hcs]
  have hre1 : ((1 - z)⁻¹).re = (1 + ρ * Real.cos θ) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by
    rw [Complex.inv_re, hnorm, Complex.sub_re, Complex.one_re, hzre]; ring
  have hre2 : ((1 - z)⁻¹).im = -(ρ * Real.sin θ) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by
    rw [Complex.inv_im, hnorm, Complex.sub_im, Complex.one_im, hzim]; ring
  have h2 : ρ ^ 2 * Real.cos θ ^ 2 + ρ ^ 2 * Real.sin θ ^ 2 = ρ ^ 2 := by
    rw [← mul_add, hcs, mul_one]
  have hval : (z * (1 - z)⁻¹).re = (-ρ * Real.cos θ - ρ ^ 2) /
      (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by
    rw [Complex.mul_re, hre1, hre2, hzre, hzim]
    have : -ρ * Real.cos θ * ((1 + ρ * Real.cos θ) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2)) -
        -ρ * Real.sin θ * (-(ρ * Real.sin θ) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2)) =
        (-ρ * Real.cos θ * (1 + ρ * Real.cos θ) - ρ ^ 2 * Real.sin θ ^ 2) /
          (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by ring
    rw [this]
    congr 1
    linear_combination (-1 : ℝ) * h2
  have hsum' : ∑' n : ℕ, poisSeq ρ (n + 1) *
      (Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval (Real.cos θ) =
      (-ρ * Real.cos θ - ρ ^ 2) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by
    rw [← hval, ← hsum]
  unfold chebPs
  rw [hsum']
  field_simp
  ring

theorem chebPs_poisSeq {ρ : ℝ} (hρ : |ρ| < 1) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    chebPs (poisSeq ρ) u = (1 - ρ ^ 2) / (1 + 2 * ρ * u + ρ ^ 2) := by
  have h := chebPs_poisSeq_cos hρ (Real.arccos u)
  rwa [Real.cos_arccos hu.1 hu.2] at h

theorem isTrialS_poisSeq {ρ : ℝ} (hρ : |ρ| < 1) :
    IsTrialS (poisSeq ρ) ((1 - ρ ^ 2) / (1 + |ρ|) ^ 2) := by
  refine ⟨summable_poisSeq hρ, ?_, fun u hu => ?_⟩
  · have : 0 < 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
    positivity
  · rw [chebPs_poisSeq hρ hu]
    have hD : 0 < 1 + 2 * ρ * u + ρ ^ 2 := cross_pos hρ hu
    have h1 : 1 + 2 * ρ * u + ρ ^ 2 ≤ (1 + |ρ|) ^ 2 := by
      have : |ρ * u| ≤ |ρ| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr hu)
      nlinarith [(abs_le.mp this).2, sq_abs ρ]
    have h2 : 0 ≤ 1 - ρ ^ 2 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
    exact div_le_div_of_nonneg_left h2 hD h1

/-- The Poisson kernel is a positive probability density. -/
theorem denQs_poisSeq_pos {ρ : ℝ} (hρ : |ρ| < 1) (θ : ℝ) : 0 < denQs (poisSeq ρ) θ := by
  have h := isTrialS_poisSeq hρ
  have := h.2.2 (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  unfold denQs
  exact div_pos (lt_of_lt_of_le h.2.1 this) Real.pi_pos

/-- **Poisson average.** If a Chebyshev series with summable coefficients is `≤ ℓ` on `[-1, 1]`,
its Poisson average `Σ c_k (-ρ)^k` is `≤ ℓ`. -/
theorem poisson_average_le {c : ℕ → ℝ} (hc : Summable fun k : ℕ => |c (k + 1)|) {ℓ : ℝ}
    (hℓ : ∀ u ∈ Icc (-1 : ℝ) 1,
      ∑' k : ℕ, c (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u ≤ ℓ)
    {ρ : ℝ} (hρ : |ρ| < 1) :
    ∑' k : ℕ, c (k + 1) * (-ρ) ^ (k + 1) ≤ ℓ := by
  have hp := summable_poisSeq hρ
  have hmem : ∀ θ : ℝ, Real.cos θ ∈ Icc (-1 : ℝ) 1 := fun θ =>
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  set G : ℝ → ℝ := fun θ => ∑' k : ℕ, c (k + 1) *
    (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) with hG
  set GK : ℕ → ℝ → ℝ := fun K θ => ∑ k ∈ Finset.range K, c (k + 1) *
    (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) with hGK
  have hGc : Continuous G := by
    refine continuous_tsum (u := fun k : ℕ => |c (k + 1)|) (fun k => ?_) hc (fun k θ => ?_)
    · exact continuous_const.mul ((Polynomial.continuous _).comp Real.continuous_cos)
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (energy_chebyshev_abs_le_one (k + 1) (hmem θ))
  have hGKc : ∀ K, Continuous (GK K) := fun K => by
    simp only [hGK]
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul ((Polynomial.continuous _).comp Real.continuous_cos)
  set S := ∑' k : ℕ, |c (k + 1)| with hS
  have hGKb : ∀ K θ, |GK K θ| ≤ S := by
    intro K θ
    simp only [hGK]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hc.sum_le_tsum _ fun _ _ => abs_nonneg _)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (energy_chebyshev_abs_le_one (k + 1) (hmem θ))
  have hGKlim : ∀ θ, Tendsto (fun K => GK K θ) atTop (𝓝 (G θ)) := by
    intro θ
    have hs : Summable fun k : ℕ => c (k + 1) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ) :=
      summable_chebTerm hc (hmem θ)
    exact hs.hasSum.tendsto_sum_nat
  have h1 := tendsto_integral_denQs_mul (b := poisSeq ρ) hp (fun K => (hGKc K).measurable) hGKb
    hGKlim
  -- the finite integrals
  have hfin : ∀ K, ∫ θ in (0 : ℝ)..Real.pi, denQs (poisSeq ρ) θ * GK K θ =
      ∑ k ∈ Finset.range K, c (k + 1) * (-ρ) ^ (k + 1) := by
    intro K
    simp only [hGK]
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have : ∀ θ, denQs (poisSeq ρ) θ * (c (k + 1) *
          (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) =
          c (k + 1) * (denQs (poisSeq ρ) θ * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) := by
        intro θ
        rw [Polynomial.Chebyshev.T_real_cos]
        simp only [Int.cast_natCast]
        ring
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, integral_denQs_cos hp (Nat.succ_ne_zero k)]
      simp [poisSeq]
    · intro k _
      apply Continuous.intervalIntegrable
      exact (continuous_denQs hp).mul (continuous_const.mul
        ((Polynomial.continuous _).comp Real.continuous_cos))
  have hcp : Summable fun k : ℕ => c (k + 1) * (-ρ) ^ (k + 1) := by
    refine Summable.of_norm_bounded hc fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ.le)
  have h2 : Tendsto (fun K => ∫ θ in (0 : ℝ)..Real.pi, denQs (poisSeq ρ) θ * GK K θ) atTop
      (𝓝 (∑' k : ℕ, c (k + 1) * (-ρ) ^ (k + 1))) := by
    simp_rw [hfin]
    exact hcp.hasSum.tendsto_sum_nat
  have h3 := tendsto_nhds_unique h1 h2
  rw [← h3]
  calc ∫ θ in (0 : ℝ)..Real.pi, denQs (poisSeq ρ) θ * G θ
      ≤ ∫ θ in (0 : ℝ)..Real.pi, denQs (poisSeq ρ) θ * ℓ := by
        refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ ?_ fun θ _ => ?_
        · exact ((continuous_denQs hp).mul hGc).intervalIntegrable _ _
        · exact ((continuous_denQs hp).mul continuous_const).intervalIntegrable _ _
        · exact mul_le_mul_of_nonneg_left (hℓ _ (hmem θ)) (denQs_poisSeq_pos hρ θ).le
    _ = ℓ := by
        rw [intervalIntegral.integral_mul_const, integral_denQs hp, one_mul]

/-- The Poisson energy sum. -/
theorem energy_poisSeq {ρ : ℝ} (hρ : |ρ| < 1) :
    ∑' i : ℕ, 2 * poisSeq ρ (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) = -2 * Real.log (1 - ρ ^ 2) := by
  have hr : |ρ ^ 2| < 1 := by
    rw [abs_pow, sq_abs]; nlinarith [abs_nonneg ρ, mul_nonneg (abs_nonneg ρ) (sub_nonneg.2 hρ.le), sq_abs ρ]
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hr).mul_left 2
  rw [show -2 * Real.log (1 - ρ ^ 2) = 2 * -Real.log (1 - ρ ^ 2) by ring, ← h.tsum_eq]
  refine tsum_congr fun k => ?_
  unfold poisSeq
  rw [show ((-ρ) ^ (k + 1)) ^ 2 = (ρ ^ 2) ^ (k + 1) by rw [← pow_mul, mul_comm, pow_mul]; simp]
  push_cast; ring

theorem sq_poisSeq {ρ : ℝ} (hρ : |ρ| < 1) :
    ∑' k : ℕ, poisSeq ρ (k + 1) ^ 2 = ρ ^ 2 / (1 - ρ ^ 2) := by
  have hr : ρ ^ 2 < 1 := by
    nlinarith [abs_nonneg ρ, mul_nonneg (abs_nonneg ρ) (sub_nonneg.2 hρ.le), sq_abs ρ]
  have h0 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have h := (hasSum_geometric_of_lt_one h0 hr).mul_left (ρ ^ 2)
  have h2 : HasSum (fun k : ℕ => poisSeq ρ (k + 1) ^ 2) (ρ ^ 2 * (1 - ρ ^ 2)⁻¹) := by
    convert h using 1
    funext k
    unfold poisSeq
    rw [← pow_mul, mul_comm, pow_mul, pow_succ']
    simp
  rw [h2.tsum_eq]; field_simp

/-! ### Audit -/

#print axioms CatalanMeasure.Signed.chebP_cos
#print axioms CatalanMeasure.Signed.integral_chebP_cos
#print axioms CatalanMeasure.Signed.integral_chebP_cos_mul
#print axioms CatalanMeasure.Signed.integral_chebP_cos_sq
#print axioms CatalanMeasure.Signed.isProbabilityMeasure_denMeasure
#print axioms CatalanMeasure.Signed.integral_denMeasure
#print axioms CatalanMeasure.Signed.fatou_real
#print axioms CatalanMeasure.Signed.integrable_kerL_and_energy_ge
#print axioms CatalanMeasure.Signed.integral_kerL_denMeasure
#print axioms CatalanMeasure.Signed.integral_crossLog_denMeasure
#print axioms CatalanMeasure.Signed.arcsine_energy
#print axioms CatalanMeasure.Signed.arcsine_cross_field
#print axioms CatalanMeasure.Signed.isTrial_arcsine
#print axioms CatalanMeasure.Signed.denPi_eq_withDensity
#print axioms CatalanMeasure.Signed.integral_denEnergy
#print axioms CatalanMeasure.Signed.denEntropy_ge
#print axioms CatalanMeasure.Signed.arcsine_jensen_denominator
#print axioms CatalanMeasure.Signed.arcsine_jensen_denominator_crude
#print axioms CatalanMeasure.Signed.arcsine_jensen_denominator_crude_sum
#print axioms CatalanMeasure.Signed.integral_crossLog_denQs
#print axioms CatalanMeasure.Signed.poisson_average_le
#print axioms CatalanMeasure.Signed.chebPs_poisSeq
#print axioms CatalanMeasure.Signed.isTrialS_poisSeq
#print axioms CatalanMeasure.Signed.integral_denQs_cos
#print axioms CatalanMeasure.Signed.integral_denQs
#print axioms CatalanMeasure.Signed.isTrialS_bTrunc
#print axioms CatalanMeasure.Signed.eventually_isTrial
#print axioms CatalanMeasure.Signed.denQs_poisSeq_pos
#print axioms CatalanMeasure.Signed.energy_poisSeq
#print axioms CatalanMeasure.Signed.sq_poisSeq

end

end CatalanMeasure.Signed
