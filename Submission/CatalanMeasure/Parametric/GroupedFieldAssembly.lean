module

public import Submission.CatalanMeasure.Parametric.GroupedPopulationCanonical

/-!
# Assemble free, marked actual, near and column field caps

The diagonal correction belongs only to the free/column populations. The marked
actual and near populations use their own scalar caps.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

def groupedValueWithFields (ν constant : ℝ) {r a b : ℕ}
    (R M L C : ℝ → ℝ) (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ)
    (s : Fin r → ℝ) : ℝ :=
  constant + groupedPopulationInteraction ν (Fin.append z x) y z s +
    (∑ i, R (z i)) / ν + (∑ i, M (x i)) / ν +
    (∑ i, L (y i)) / ν + (∑ i, C (s i)) / ν

set_option maxHeartbeats 800000 in
theorem grouped_field_caps_bound {ν e constant : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r a b : ℕ}
    (ha : ((r + a : ℕ) : ℝ) ≤ ν) (hb : (b : ℝ) ≤ ν)
    (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ)
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective z) (hxi : Function.Injective (Fin.append z x))
    (hyi : Function.Injective y) (hsi : Function.Injective s)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) (hw : Summable (fun k => |w k|))
    (R M L C : ℝ → ℝ) (RF MF LF CF : ℝ)
    (hR : ∀ i, R (z i) - 2 * barrierTrialT u (z i) -
      2 * barrierTrialT v (z i) - barrierTrialS w (z i) - Real.log (1 - z i) / (2 * ν) ≤ RF)
    (hM : ∀ i, M (x i) - 2 * barrierTrialT u (x i) ≤ MF)
    (hL : ∀ i, L (y i) - u 1 * y i ≤ LF)
    (hC : ∀ i, C (s i) + 2 * barrierTrialT w (s i) - Real.log (1 - s i) / ν ≤ CF) :
    groupedValueWithFields ν constant R M L C z x y s ≤
      constant - (1 / 2 : ℝ) * ((((r + a : ℕ) : ℝ) / ν) ^ 2 + ((b : ℝ) / ν) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq u + barrierTrialNormSq v + barrierTrialNormSq w / 2 +
      ((r : ℝ) / ν) * (RF + CF) + ((a : ℝ) / ν) * MF + ((b : ℝ) / ν) * LF +
      groupedPopulationError ν e u v w := by
  have hr : (r : ℝ) ≤ ν := by
    have ht : (r : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right r a
    exact ht.trans ha
  have hzx : ∀ i, Fin.append z x i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hz j
    · simpa using hx j
  have hi := grouped_population_canonical hν he ha hb hr (Fin.append z x) y z s
    hzx hy hz hs hxi hyi hzi hsi u v w hu hv hw
  have hf := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun i _ => hR i)) hν.le
  have hm := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun i _ => hM i)) hν.le
  have hl := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun i _ => hL i)) hν.le
  have hc := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun i _ => hC i)) hν.le
  have hsplit : (∑ i : Fin (r + a), -2 * barrierTrialT u (Fin.append z x i)) =
      (∑ i : Fin r, -2 * barrierTrialT u (z i)) +
        (∑ i : Fin a, -2 * barrierTrialT u (x i)) := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hsplit] at hi
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_div, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul] at hi hf hm hl hc
  unfold groupedValueWithFields
  ring_nf at hi hf hm hl hc ⊢
  linarith only [hi, hf, hm, hl, hc]

end

end CatalanMeasure.Parametric
