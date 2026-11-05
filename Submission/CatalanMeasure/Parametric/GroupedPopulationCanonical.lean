module

public import Submission.CatalanMeasure.Parametric.CoupledCosineRegularization
public import Submission.CatalanMeasure.FreePopulationFields

/-!
# The complete grouped interaction energy

The actual and near populations have separate Vandermondes. A subset of the
actual nodes additionally participates in the free/column Cauchy determinant.
The theorem below is valid for arbitrary such families, without a cross-group
injectivity assumption.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

def groupedPopulationInteraction (ν : ℝ) {a b r : ℕ}
    (x : Fin a → ℝ) (y : Fin b → ℝ) (z s : Fin r → ℝ) : ℝ :=
  pinOffDiagonalInteraction ν 1 z s +
    (∑ i : Fin a, ∑ j ∈ Ioi i, Real.log |x j - x i|) / ν ^ 2 +
    (∑ i : Fin b, ∑ j ∈ Ioi i, Real.log |y j - y i|) / ν ^ 2 +
    Real.log (crossCauchyProduct x y) / ν ^ 2

def groupedPopulationError (ν e : ℝ) (u v w : ℕ → ℝ) : ℝ :=
  coupledCosineError ν e u + 2 * e * (∑' k, |v k|) +
    4 * e * (∑' k, |w k|) + freePopulationRegularizationError ν e

theorem grouped_population_canonical {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {a b r : ℕ}
    (ha : (a : ℝ) ≤ ν) (hb : (b : ℝ) ≤ ν) (hr : (r : ℝ) ≤ ν)
    (x : Fin a → ℝ) (y : Fin b → ℝ) (z s : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hyi : Function.Injective y)
    (hzi : Function.Injective z) (hsi : Function.Injective s)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) (hw : Summable (fun k => |w k|)) :
    groupedPopulationInteraction ν x y z s ≤
      -(1 / 2 : ℝ) * (((a : ℝ) / ν) ^ 2 + ((b : ℝ) / ν) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq u + barrierTrialNormSq v + barrierTrialNormSq w / 2 +
      (∑ i, -2 * barrierTrialT u (x i)) / ν +
      (∑ i, -u 1 * y i) / ν +
      (∑ i, (-2 * barrierTrialT v (z i) - barrierTrialS w (z i))) / ν +
      (∑ i, 2 * barrierTrialT w (s i)) / ν -
      (∑ i, Real.log (1 - z i)) / (2 * ν ^ 2) -
      (∑ i, Real.log (1 - s i)) / ν ^ 2 + groupedPopulationError ν e u v w := by
  have hc := grouped_cosine_cross_canonical hν he ha hb x y hx hy hxi hyi u hu
  have hf := free_population_canonical hν he hr hz hs hzi hsi v w hv hw
  have hySum : -u 1 * ((∑ i, y i) / ν) = (∑ i, -u 1 * y i) / ν := by
    rw [← mul_sum]
    ring
  unfold groupedPopulationInteraction groupedPopulationError
  linarith only [hc, hf, hySum]

end

end CatalanMeasure.Parametric
