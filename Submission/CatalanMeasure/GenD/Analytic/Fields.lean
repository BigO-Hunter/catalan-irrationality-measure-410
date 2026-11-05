module

public import Submission.CatalanMeasure.GenD.Analytic.Const

@[expose] public section

/-!
# Analytic layer, fields: marked-field identity and regularization errors (design-generic)

Generic versions of `twenty_grouped_marked_field_identity`, `twenty_log_reciprocal_eventually`,
`twenty_reciprocal_three_term_tendsto`, `exists_small_population_damping`,
`twenty_grouped_error_eventually` and `twentyFirstDampingError_eventually`.
Only `1 / (n0 N) → 0` is used about the scale; the limit constants are those of the (design-free)
regularization errors.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

theorem grouped_marked_field_identity {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    (x : ℝ) :
    groupedMarkedField P N x =
      -gRes P * Real.log (1 + x ^ 2) + Real.log (1 + x ^ 2) / (P.n N : ℝ) := by
  have hg := two_g_lt_n hP hN
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnpos := n_pos hP hN
  have hdR : ((P.n N - P.g N - 1 : ℕ) : ℝ) = (P.n N : ℝ) - (P.g0 : ℝ) * N - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ P.n N - P.g N), Nat.cast_sub (by omega : P.g N ≤ P.n N)]
    simp [Parameters.g]
  unfold groupedMarkedField gRes
  rw [hdR, n_cast]
  field_simp
  ring

/-- `1 / (n0 N) → 0`. -/
theorem invScale_tendsto {P : Parameters} (hP : Admissible P) :
    Tendsto (fun N : ℕ => 1 / ((P.n0 : ℝ) * N)) atTop (𝓝 0) := by
  simpa only [div_div] using (tendsto_const_div_atTop_nhds_zero_nat (1 / (P.n0 : ℝ)))

theorem log_reciprocal_eventually {P : Parameters} (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log 2 / (P.n N : ℝ) ≤ ε := by
  have ht : Tendsto (fun N : ℕ => Real.log 2 / (P.n N : ℝ)) atTop (𝓝 0) := by
    have hh := (invScale_tendsto hP).const_mul (Real.log 2)
    convert hh using 1
    · funext N
      rw [n_cast]
      ring
    · ring
  exact ((tendsto_order.mp ht).2 ε hε).mono fun _ h => h.le

theorem reciprocal_three_term_tendsto {P : Parameters} (hP : Admissible P) (A B C D : ℝ) :
    Tendsto (fun N : ℕ => A / ((P.n0 : ℝ) * N) + B / (2 * ((P.n0 : ℝ) * N)) +
      C / ((P.n0 : ℝ) * N) + D) atTop (𝓝 D) := by
  have hh := ((invScale_tendsto hP).const_mul (A + B / 2 + C)).add_const D
  convert hh using 1
  · funext N
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · ring

theorem exists_small_damping {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∃ e : ℝ, e ∈ Ioo (0 : ℝ) (1 / 8) ∧ e * c < δ := by
  let e : ℝ := min (1 / 16) (δ / (2 * (c + 1)))
  have he0 : 0 < e := lt_min (by norm_num) (div_pos hδ (by linarith only [hc]))
  have hehi : e ≤ 1 / 16 := min_le_left _ _
  have heδ := min_le_right (1 / 16 : ℝ) (δ / (2 * (c + 1)))
  have heδ' : e * (2 * (c + 1)) ≤ δ := by
    apply (le_div_iff₀ (by linarith only [hc] : (0 : ℝ) < 2 * (c + 1))).mp heδ
  refine ⟨e, ⟨he0, by linarith only [hehi]⟩, ?_⟩
  nlinarith only [heδ', he0, hδ]

theorem grouped_error_tendsto {P : Parameters} (hP : Admissible P) (e : ℝ) (pp v : ℕ → ℝ) :
    Tendsto (fun N : ℕ => groupedPopulationError ((P.n0 : ℝ) * N) e pp pp v) atTop
      (𝓝 (e * (4 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + |pp 1| + 20))) := by
  have hh := reciprocal_three_term_tendsto hP
    ((3 / 2 : ℝ) * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)))
    (Real.log 2 - Real.log e) (Real.log 2 - 2 * Real.log e)
    (e * (4 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + |pp 1| + 20))
  convert hh using 1
  funext N
  unfold groupedPopulationError coupledCosineError freePopulationRegularizationError
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem grouped_error_eventually {P : Parameters} (hP : Admissible P) (pp v : ℕ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ e : ℝ, e ∈ Ioo (0 : ℝ) (1 / 8) ∧
      ∀ᶠ N : ℕ in atTop, groupedPopulationError ((P.n0 : ℝ) * N) e pp pp v ≤ δ := by
  have hp : 0 ≤ ∑' j, |pp j| := tsum_nonneg (fun j => abs_nonneg _)
  have hv : 0 ≤ ∑' j, |v j| := tsum_nonneg (fun j => abs_nonneg _)
  have hp1 : 0 ≤ |pp 1| := abs_nonneg _
  obtain ⟨e, he, hec⟩ := exists_small_damping
    (by linarith only [hp, hv, hp1] : (0 : ℝ) ≤
      4 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + |pp 1| + 20) hδ
  refine ⟨e, he, ?_⟩
  exact ((tendsto_order.mp (grouped_error_tendsto hP e pp v)).2 δ hec).mono
    (fun _ h => h.le)

/-- The first-population damping error (generic form of `twentyFirstDampingError`). -/
def firstDampingError (P : Parameters) (lambda e : ℝ) (pp v : ℕ → ℝ) (N : ℕ) : ℝ :=
  lambda / ((P.n0 : ℝ) * N) + 2 * e * (∑' j, |pp j|) + 4 * e * (∑' j, |v j|) +
    freePopulationRegularizationError ((P.n0 : ℝ) * N) e

theorem firstDampingError_tendsto {P : Parameters} (hP : Admissible P) (lambda e : ℝ)
    (pp v : ℕ → ℝ) :
    Tendsto (firstDampingError P lambda e pp v) atTop
      (𝓝 (e * (2 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + 14))) := by
  have hh := reciprocal_three_term_tendsto hP
    ((Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / 2 + lambda)
    (Real.log 2 - Real.log e) (Real.log 2 - 2 * Real.log e)
    (e * (2 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + 14))
  convert hh using 1
  funext N
  unfold firstDampingError freePopulationRegularizationError
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem firstDampingError_eventually {P : Parameters} (hP : Admissible P) (lambda : ℝ)
    (pp v : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : ℝ, e ∈ Ioo (0 : ℝ) (1 / 8) ∧
      ∀ᶠ N : ℕ in atTop, firstDampingError P lambda e pp v N ≤ δ := by
  have hp : 0 ≤ ∑' j, |pp j| := tsum_nonneg (fun j => abs_nonneg _)
  have hv : 0 ≤ ∑' j, |v j| := tsum_nonneg (fun j => abs_nonneg _)
  obtain ⟨e, he, hec⟩ := exists_small_damping
    (by linarith only [hp, hv] : (0 : ℝ) ≤ 2 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + 14) hδ
  refine ⟨e, he, ?_⟩
  exact ((tendsto_order.mp (firstDampingError_tendsto hP lambda e pp v)).2 δ hec).mono
    (fun _ h => h.le)

end
end Analytic
end CatalanMeasure.GenD
