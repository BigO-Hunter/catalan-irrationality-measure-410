module

public import Submission.CatalanMeasure.Parametric.RestrictedWeights
public import Submission.CatalanMeasure.Parametric.RestrictedQuadrature
public import Submission.CatalanMeasure.Parametric.PopulationFixedFields
public import Submission.CatalanMeasure.GenD.Analytic.Const

@[expose] public section

/-!
# Analytic layer: full-interval coefficient formula (design-generic)

Restatement of the design-generic content of `Parametric.FullIntervalFormula` (which imports the
P20 circle files through `FullIntervalWeights`): the common factor does not vanish off `0, 1`, and
the filtered Catalan coefficient is the full-interval quadrature on any even node set
of size `J ≥ n - g`.  `full_weight_formula` is the generic form of `twenty_full_weight_formula`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric Polynomial Polynomial.Chebyshev Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

theorem rowCommonFactor_eval_ne_zero_of (P : Parameters) (N : ℕ) {t : ℝ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (rowCommonFactor P N).eval t ≠ 0 := by
  simp only [rowCommonFactor, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1.symm))

theorem filteredCatalanCoeff_full_weights {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0 < N) (hr : r < P.n N) {J : ℕ} (hJ : P.n N - P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ)
    (hτ0 : ∀ a, τ a ≠ 0) (hτ1 : ∀ a, τ a ≠ 1) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k : ℝ) =
      ∑ a, (realPoly (rowP P N r)).eval (τ a) * restrictedWeight P N k τ a := by
  rw [filteredCatalanCoeff_restricted_quadrature hP hN hr hJ hτ]
  apply sum_congr rfl
  intro a _
  have he : (realPoly (rowP P N r)).eval (τ a) =
      (rowCommonFactor P N).eval (τ a) * (realPoly (rowResidualP P N r)).eval (τ a) := by
    rw [rowP_common_factor hP hN hr]
    simp [realPoly, rowCommonFactor]
  have hn := rowCommonFactor_eval_ne_zero_of P N (hτ0 a) (hτ1 a)
  rw [he, restrictedWeight]
  field_simp

theorem chebX_even_ne_zero {J : ℕ} (hJ : Even J) (a : Fin J) :
    CatalanMeasure.chebX J a ≠ 0 := by
  have hm : 0 < J := by have := a.isLt; omega
  have hr : (T ℝ (J : ℤ)).eval (CatalanMeasure.chebX J a) = 0 := by
    rw [CatalanMeasure.T_eq_nodal hm, eval_mul, eval_C, eval_prod]
    apply mul_eq_zero_of_right
    apply prod_eq_zero (mem_univ a)
    simp
  intro hz
  rw [hz] at hr
  have hte := T_eval_zero_of_even (R := ℝ) (n := (J : ℤ)) (by exact_mod_cast hJ)
  rw [hte] at hr
  have hn : (((J : ℤ) / 2).negOnePow : ℤ) ≠ 0 := Units.ne_zero _
  exact hn (by exact_mod_cast hr)

/-- Generic `twenty_full_weight_formula`: Chebyshev nodes of any even size `J ≥ n - g`. -/
theorem full_weight_formula {P : Parameters} (hP : Admissible P) {N r : ℕ} (hN : 0 < N)
    (hr : r < P.n N) {J : ℕ} (hJ : P.n N - P.g N ≤ J) (hJe : Even J) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k : ℝ) =
      ∑ a : Fin J, (realPoly (rowP P N r)).eval (CatalanMeasure.chebX J a) *
        restrictedWeight P N k (CatalanMeasure.chebX J) a :=
  filteredCatalanCoeff_full_weights hP hN hr hJ (CatalanMeasure.chebX_injective _)
    (fun a => chebX_even_ne_zero hJe a) (fun a => (CatalanMeasure.chebX_mem a).2.ne) k

end
end Analytic
end CatalanMeasure.GenD
