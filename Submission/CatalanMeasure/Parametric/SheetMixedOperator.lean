module

public import Submission.CatalanMeasure.Parametric.CoefficientGram
public import Submission.CatalanMeasure.Parametric.GroupedEvaluation

/-!
# The actual mixed first-sheet evaluation operator on coefficient space

The operator is reversal plus interpolated multiplication by h. Its bounded
norm can now be used on only the actual-column group in a mixed determinant.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan

noncomputable section

def sheetSpaceMixedOperator {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (hxi : Function.Injective x) (h : ℂ → ℂ) :
    firstSheetSpace x hx →ₗ[ℂ] firstSheetSpace x hx :=
  (firstSheetSpaceEquiv x hx hxi).toLinearMap.comp
    (((firstSheetEvaluationOperator x hxi h).comp (firstSheetReverse n).toLinearMap).comp
      (firstSheetSpaceEquiv x hx hxi).symm.toLinearMap)

theorem sheetSpaceMixedOperator_norm_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall (0 : ℂ) 1)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖h z‖ ≤ K)
    (u : firstSheetSpace x hx) :
    ‖sheetSpaceMixedOperator x hx hxi h u‖ ≤ (1 + K) * ‖u‖ := by
  obtain ⟨a, rfl⟩ := (firstSheetSpaceEquiv x hx hxi).surjective u
  change ‖firstSheetSpaceEquiv x hx hxi
    (firstSheetEvaluationOperator x hxi h (firstSheetReverse n
      ((firstSheetSpaceEquiv x hx hxi).symm (firstSheetSpaceEquiv x hx hxi a))))‖ ≤ _
  rw [LinearEquiv.symm_apply_apply]
  change ‖firstSheetRationalEmbedding x hx
    (firstSheetEvaluationOperator x hxi h (firstSheetReverse n a))‖ ≤
      (1 + K) * ‖firstSheetRationalEmbedding x hx a‖
  exact (firstSheetEvaluationOperator_norm_le x hx hxi h hh hK hbound
    (firstSheetReverse n a)).trans_eq (by rw [firstSheetRationalEmbedding_reverse_norm])

theorem sheetSpaceMixedOperator_inner_coefficient {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) (h : ℂ → ℂ)
    (i r : Fin n) :
    inner ℂ (sheetKernelFamily x hx i)
      (sheetSpaceMixedOperator x hx hxi h (sheetCoefficientFamily x hx r)) =
      ((x i : ℂ) ^ (r.rev : ℕ) + h (x i : ℂ) * (x i : ℂ) ^ (r : ℕ)) /
        firstSheetDenominator Finset.univ x (x i : ℂ) := by
  have hc : sheetCoefficientFamily x hx r =
      firstSheetSpaceEquiv x hx hxi (Pi.single r 1) := rfl
  rw [hc]
  change inner ℂ (firstSheetKernelVector (x i) (hx i))
    (firstSheetRationalEmbedding x hx (firstSheetEvaluationOperator x hxi h
      (firstSheetReverse n ((firstSheetSpaceEquiv x hx hxi).symm
        (firstSheetSpaceEquiv x hx hxi (Pi.single r 1)))))) = _
  rw [LinearEquiv.symm_apply_apply, firstSheetRationalEmbedding_inner_kernel,
    firstSheetRational]
  have hv := firstSheetEvaluation_cancellation x hxi h (Pi.single r 1) i
  rw [firstSheetEvaluation_apply, firstSheetReverse_single,
    firstSheetNumerator_single, firstSheetNumerator_single] at hv
  rw [firstSheetReverse_single, hv]

end

end CatalanMeasure.Parametric
