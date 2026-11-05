module
public import Submission.CatalanMeasure.Parametric.TwoAdicRawMinors
public import Submission.CatalanMeasure.Parametric.TwoAdicExceptionalScalars
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open Classical
open scoped BigOperators
noncomputable section

abbrev paramRawCoefficientIndex (P : Parameters) (N : ℕ) (t : Fin 3) :=
  Fin (if t = 0 then 1 else P.C N)

def paramRawCoefficientVector (P : Parameters) (N r j : ℕ) (t : Fin 3) (u : ℕ) : ℚ_[2] :=
  if t = 0 then paramSmoothingColumn P N r j
  else if t = 1 then ((Chebyshev.T ℤ (rowDistance P N r : ℤ)).coeff u : ℚ_[2])
  else ((Int.sign (rowOffset P N r) *
    (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2])

def paramRawCoefficientScalar (P : Parameters) (z : ℚ) (N j : ℕ) (t : Fin 3) (u : ℕ) : ℚ_[2] :=
  if t = 0 then 1
  else if t = 1 then paramExceptionScalar P z N u j
  else paramBoundaryScalar P N u j

def paramRawCoefficientMinor (P : Parameters) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k)) : ℚ_[2] :=
  Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
    paramRawCoefficientVector P N r.val (c k).val (τ k) (u k).val)

theorem paramRawColumnTerm_coefficient_expansion (P : Parameters) (z : ℚ) (N r j : ℕ) (t : Fin 3) :
    paramRawColumnTerm P z N r j t =
      ∑ u : paramRawCoefficientIndex P N t,
        paramRawCoefficientVector P N r j t u.val * paramRawCoefficientScalar P z N j t u.val := by
  by_cases h0 : t = 0
  · subst t
    simp [paramRawColumnTerm, paramRawCoefficientIndex, paramRawCoefficientVector, paramRawCoefficientScalar]
  · by_cases h1 : t = 1
    · subst t
      have hsum := Fin.sum_univ_eq_sum_range
        (fun u : ℕ => ((Chebyshev.T ℤ (rowDistance P N r : ℤ)).coeff u : ℚ_[2]) *
          paramExceptionScalar P z N u j) (P.C N)
      simpa [paramRawColumnTerm, paramRawCoefficientIndex, paramRawCoefficientVector,
        paramRawCoefficientScalar] using
        (paramExceptionColumn_eq_sum_exceptionScalar P z N r j).trans hsum.symm
    · have h2 : t = 2 := by omega
      subst t
      have hsum := Fin.sum_univ_eq_sum_range
        (fun u : ℕ => ((Int.sign (rowOffset P N r) *
          (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2]) *
            paramBoundaryScalar P N u j) (P.C N)
      simpa [paramRawColumnTerm, paramRawCoefficientIndex, paramRawCoefficientVector,
        paramRawCoefficientScalar] using
        (paramBoundaryColumn_eq_sum_boundaryScalar P N r j).trans hsum.symm

theorem paramRawColumnMinor_coefficient_expansion (P : Parameters) (z : ℚ) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3) :
    Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
      paramRawColumnTerm P z N r.val (c k).val (τ k)) =
      ∑ u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k),
        (∏ k : Fin (P.n N), paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val) *
          paramRawCoefficientMinor P N c τ u := by
  classical
  have hmatrix :
      (Matrix.of fun r k : Fin (P.n N) => paramRawColumnTerm P z N r.val (c k).val (τ k)) =
        (Matrix.of fun r k : Fin (P.n N) =>
          ∑ a : paramRawCoefficientIndex P N (τ k),
            paramRawCoefficientVector P N r.val (c k).val (τ k) a.val *
              paramRawCoefficientScalar P z N (c k).val (τ k) a.val) := by
    ext r k
    simp only [Matrix.of_apply, paramRawColumnTerm_coefficient_expansion]
  rw [hmatrix]
  calc
    _ = ∑ u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k),
        ∑ σ : Equiv.Perm (Fin (P.n N)), ((Equiv.Perm.sign σ : ℤ) : ℚ_[2]) *
          ∏ k : Fin (P.n N),
            paramRawCoefficientVector P N (σ k).val (c k).val (τ k) (u k).val *
              paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [paramRawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem paramRawCoefficientMinor_eq_zero_of_repeat_exception (P : Parameters) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k))
    {i j : Fin (P.n N)} (hne : i ≠ j) (hi : τ i = 1) (hj : τ j = 1)
    (hu : (u i).val = (u j).val) : paramRawCoefficientMinor P N c τ u = 0 := by
  unfold paramRawCoefficientMinor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, paramRawCoefficientVector, hi, hj, hu]

theorem paramRawCoefficientMinor_eq_zero_of_repeat_boundary (P : Parameters) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k))
    {i j : Fin (P.n N)} (hne : i ≠ j) (hi : τ i = 2) (hj : τ j = 2)
    (hu : (u i).val = (u j).val) : paramRawCoefficientMinor P N c τ u = 0 := by
  unfold paramRawCoefficientMinor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, paramRawCoefficientVector, hi, hj, hu]

theorem paramRawCoefficientMinor_exception_injOn (P : Parameters) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k))
    (hdet : paramRawCoefficientMinor P N c τ u ≠ 0) :
    Set.InjOn (fun k => (u k).val) {k | τ k = 1} := by
  intro i hi j hj hu
  by_contra hne
  exact hdet (paramRawCoefficientMinor_eq_zero_of_repeat_exception P N c τ u hne hi hj hu)

theorem paramRawCoefficientMinor_boundary_injOn (P : Parameters) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k))
    (hdet : paramRawCoefficientMinor P N c τ u ≠ 0) :
    Set.InjOn (fun k => (u k).val) {k | τ k = 2} := by
  intro i hi j hj hu
  by_contra hne
  exact hdet (paramRawCoefficientMinor_eq_zero_of_repeat_boundary P N c τ u hne hi hj hu)

theorem paramRawColumnMinor_coefficient_expansion_injective (P : Parameters) (z : ℚ) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3) :
    Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
      paramRawColumnTerm P z N r.val (c k).val (τ k)) =
      ∑ u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k) with
          Set.InjOn (fun k => (u k).val) {k | τ k = 1} ∧
          Set.InjOn (fun k => (u k).val) {k | τ k = 2},
        (∏ k : Fin (P.n N), paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val) *
          paramRawCoefficientMinor P N c τ u := by
  classical
  rw [paramRawColumnMinor_coefficient_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro u hu hout
  have hnot : ¬(Set.InjOn (fun k => (u k).val) {k | τ k = 1} ∧
      Set.InjOn (fun k => (u k).val) {k | τ k = 2}) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hout
  have hzero : paramRawCoefficientMinor P N c τ u = 0 := by
    by_contra hne
    exact hnot ⟨paramRawCoefficientMinor_exception_injOn P N c τ u hne,
      paramRawCoefficientMinor_boundary_injOn P N c τ u hne⟩
  rw [hzero, mul_zero]


end
end CatalanMeasure.Parametric
