module

public import Submission.CatalanMeasure.GenD.Analytic.MarkedSecond
public import Submission.CatalanMeasure.GenD.Analytic.MarkedMixedMajorant

@[expose] public section

/-!
# Analytic layer: the marked sheet bound `marked_sheet_on` (design-generic)

Generic form of `Parametric.marked_sheet_on` (GapAtomCost).  Inputs: a first-population trial
`F : FirstTrialBounds P target c` and a second-population trial
`D : SecondTrialBounds P target residual nearCap cost G`; the single cost coefficient `r` must
dominate `n0 · c` and `n0 · cost`.  No P20 certificate is imported.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open scoped BigOperators Topology

noncomputable section

theorem marked_sheet_on {P : Parameters} (hP : Admissible P)
    {target c residual nearCap cost r : ℝ}
    (F : FirstTrialBounds P target c) (G : ℝ → Prop)
    (D : SecondTrialBounds P target residual nearCap cost G)
    (hfc : (P.n0 : ℝ) * c ≤ r) (hsc : (P.n0 : ℝ) * cost ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) →
      Function.Injective s →
      markedSheetProduct P N hpm x y s ≤
        (5 : ℝ) ^ m * sheetPrefactor P N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m) := by
  filter_upwards [first_marked_sheet hP F hε,
      second_marked_sheet_product_on hP target ((P.n0 : ℝ) * cost) G
        (fun _ he => grouped_marked_product hP D he) hε] with N hfirst hsecond
  intro p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi
  have hxi : Function.Injective x := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (hzi (by simpa using hij))
  have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  have hH : 0 ≤ sheetPrefactor P N := by unfold sheetPrefactor; positivity
  have hF : (3 / 2 : ℝ) ^ P.n N *
      (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) ≤ sheetPrefactor P N := by
    unfold sheetPrefactor
    exact le_add_of_nonneg_right (by positivity)
  have hI : (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N ≤
      sheetPrefactor P N := by
    unfold sheetPrefactor
    exact le_add_of_nonneg_left (by positivity)
  by_cases hcase : -1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)
  · have hh := hfirst p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
    apply hh.trans
    apply mul_le_mul
    · exact hF.trans (le_mul_of_one_le_left hH h5)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N * m := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right hfc hNm]
    · exact (Real.exp_pos _).le
    · positivity
  · have hh := hsecond p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi (le_of_not_gt hcase)
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hI (pow_nonneg (by norm_num) _)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_right hsc hNm]
    · exact (Real.exp_pos _).le
    · positivity

end
end Analytic
end CatalanMeasure.GenD
