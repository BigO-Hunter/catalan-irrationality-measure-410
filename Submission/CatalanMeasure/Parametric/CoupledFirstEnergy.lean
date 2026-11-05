module

public import Submission.CatalanMeasure.Parametric.CrossFirstMoment
public import Submission.CatalanMeasure.PinDampedDual

/-!
# Retaining a first-mode square in the energy dual

This supplies the coupled canonical estimate behind the elementary
cross-product majorant. The near population uses the zero trial.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

theorem energy_tangent_with_first_remainder (u a : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {K S : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, |a k| ≤ K)
    (hS : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S) :
    -S ≤ barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) -
        (a 1 - u 1) ^ 2 := by
  have huS : HasSum (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (barrierTrialNormSq u) := (energy_trial_norm_summable u hu).hasSum
  have hp := (energy_trial_product_summable u a hu hK ha).hasSum
  have hr : HasSum (fun k : ℕ => (a (k + 1) - u (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (barrierTrialNormSq u + S -
        2 * (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ))) := by
    convert (huS.add hS).sub (hp.mul_left 2) using 1
    funext k
    ring
  have hle := hr.summable.le_tsum 0 (fun k _ =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg (k + 1)))
  rw [hr.tsum_eq] at hle
  norm_num only [Nat.zero_add, Nat.cast_one, div_one] at hle
  linarith only [hle]

theorem coupled_energy_tangent_of_hasSum (u a b : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) {K A B : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, |a k| ≤ K)
    (hA : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) A)
    (hB : HasSum (fun k : ℕ => b (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) B) :
    -A - B - a 1 * b 1 ≤ barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) - u 1 * b 1 := by
  have ht := energy_tangent_with_first_remainder u a hu hK ha hA
  have hb := hB.summable.le_tsum 0 (fun k _ =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg (k + 1)))
  rw [hB.tsum_eq] at hb
  norm_num only [Nat.zero_add, Nat.cast_one, div_one] at hb
  have hc := first_moment_coupled_dual (a 1 - u 1) (b 1) 0 0
  nlinarith only [ht, hb, hc]

theorem pin_coupled_first_tangent {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p q : ℕ} (hp : (p : ℝ) ≤ ν)
    {x : Fin p → ℝ} {y : Fin q → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    ((∑ i : Fin p, ∑ j : Fin p,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
      ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2 +
    ((∑ i : Fin q, ∑ j : Fin q,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (y i) (y j)) / ν ^ 2 +
      ((q : ℝ) / ν) ^ 2 * Real.log 2) / 2 -
      pinCosineMoment ν e x 1 * pinCosineMoment ν e y 1 ≤
    barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * pinCosineMoment ν e x (k + 1) /
        ((k + 1 : ℕ) : ℝ)) - u 1 * pinCosineMoment ν e y 1 := by
  have hA : HasSum
      (fun k : ℕ => pinCosineMoment ν e x (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin p, ∑ j : Fin p,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
        ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e x k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hx
  have hB : HasSum
      (fun k : ℕ => pinCosineMoment ν e y (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin q, ∑ j : Fin q,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (y i) (y j)) / ν ^ 2 +
        ((q : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e y k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hy
  have h := coupled_energy_tangent_of_hasSum u (pinCosineMoment ν e x)
    (pinCosineMoment ν e y) hu (by norm_num : (0 : ℝ) ≤ 1)
    (pin_cosineMoment_abs_le_one hν he hp hx) hA hB
  linarith only [h]

end

end CatalanMeasure.Parametric
