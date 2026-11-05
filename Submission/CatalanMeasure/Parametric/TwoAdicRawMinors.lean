module
public import Submission.CatalanMeasure.Parametric.TwoAdicColumns
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section


def paramRawMatrixRat (P : Parameters) (z : ℚ) (N : ℕ) :
    Matrix (Fin (P.n N)) ↥(Finset.Ico (P.b N) (P.L N)) ℚ :=
  fun r j =>rawEntryRat P z N r.val j.val

def paramRawFilterInt (P : Parameters) (N : ℕ) :
    Matrix ↥(Finset.Ico (P.b N) (P.L N)) (Fin (P.n N)) ℤ :=
  fun j k =>∑ v ∈ Finset.range (P.q N+1),
    if j.val=P.b N+k.val+v then (-1:ℤ)^v*(P.q N).choose v else 0

theorem paramFilteredMatrixRat_eq_raw_mul_filter (P : Parameters) (z : ℚ) (N : ℕ) :
    (fun r k : Fin (P.n N) =>filteredEntryRat P z N r.val k.val)=
      paramRawMatrixRat P z N * (Matrix.of fun j k =>(paramRawFilterInt P N j k:ℚ)) :=by
  classical
  ext r k
  rw [Matrix.mul_apply]
  simp only [paramRawMatrixRat,paramRawFilterInt,Matrix.of_apply,Int.cast_sum,
    Int.cast_ite,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,
    Int.cast_zero,Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold filteredEntryRat
  apply Finset.sum_congr rfl
  intro v hv
  have hj : P.b N+k.val+v∈Finset.Ico (P.b N) (P.L N) :=
    Finset.mem_Ico.mpr ⟨by omega,rawColumn_lt_L k.isLt (by have :=Finset.mem_range.mp hv;omega)⟩
  rw [Finset.sum_coe_sort (Finset.Ico (P.b N) (P.L N))
    (fun j : ℕ =>rawEntryRat P z N r.val j *
      if j=P.b N+k.val+v then (-1:ℚ)^v*(P.q N).choose v else 0)]
  simp only [mul_ite,mul_zero]
  simp [hj,filterCoeffRat,mul_comm]

theorem paramDeterminantRat_eq_det_raw_mul_filter (P : Parameters) (z : ℚ) (N : ℕ) :
    determinantRat P z N =
      Matrix.det (paramRawMatrixRat P z N * (Matrix.of fun j k => (paramRawFilterInt P N j k : ℚ))) := by
  rw [determinantRat, paramFilteredMatrixRat_eq_raw_mul_filter]

def paramRawMinorRat (P : Parameters) (z : ℚ) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) : ℚ :=
  Matrix.det (Matrix.of fun r k : Fin (P.n N) => rawEntryRat P z N r.val (c k).val)

theorem paramRawMinorRat_eq_zero_of_not_injective (P : Parameters) (z : ℚ) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (hc : ¬Function.Injective c) : paramRawMinorRat P z N c = 0 := by
  classical
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨i, j, hij, hne⟩ := hc
  unfold paramRawMinorRat
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp only [Matrix.of_apply]
  rw [hij]

theorem paramDeterminantRat_eq_sum_raw_choices (P : Parameters) (z : ℚ) (N : ℕ) :
    determinantRat P z N =
      ∑ c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)),
        ((∏ k : Fin (P.n N), paramRawFilterInt P N (c k) k : ℤ) : ℚ) * paramRawMinorRat P z N c := by
  classical
  rw [paramDeterminantRat_eq_det_raw_mul_filter]
  calc
    _ = ∑ c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)),
        ∑ σ : Equiv.Perm (Fin (P.n N)), ((Equiv.Perm.sign σ : ℤ) : ℚ) *
          ∏ k : Fin (P.n N),
            paramRawMatrixRat P z N (σ k) (c k) * (paramRawFilterInt P N (c k) k : ℚ) := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Matrix.of_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [paramRawMinorRat, paramRawMatrixRat, paramRawFilterInt]
      rw [Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      simp only [Int.cast_prod, Finset.prod_mul_distrib, Matrix.of_apply]
      ring

theorem paramDeterminantRat_eq_sum_raw_minors (P : Parameters) (z : ℚ) (N : ℕ) :
    determinantRat P z N =
      ∑ c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)) with Function.Injective c,
        ((∏ k : Fin (P.n N), paramRawFilterInt P N (c k) k : ℤ) : ℚ) * paramRawMinorRat P z N c := by
  classical
  rw [paramDeterminantRat_eq_sum_raw_choices]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hcinj
  have hnot : ¬Function.Injective c := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcinj
  rw [paramRawMinorRat_eq_zero_of_not_injective P z N c hnot, mul_zero]


def paramRawColumnTerm (P : Parameters) (z : ℚ) (N r j : ℕ) (t : Fin 3) : ℚ_[2] :=
  if t = 0 then paramSmoothingColumn P N r j
  else if t = 1 then paramExceptionColumn P z N r j
  else paramBoundaryColumn P N r j

theorem paramRawColumnTerm_sum (P : Parameters) (z : ℚ) (N r j : ℕ) :
    (∑ t : Fin 3, paramRawColumnTerm P z N r j t) =
      paramSmoothingColumn P N r j + paramExceptionColumn P z N r j + paramBoundaryColumn P N r j := by
  simp [Fin.sum_univ_succ, paramRawColumnTerm, add_assoc]

theorem paramRawMinorRat_cast_two_adic (P : Parameters) (z : ℚ) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) :
    (paramRawMinorRat P z N c : ℚ_[2]) =
      Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
        (rawEntryRat P z N r.val (c k).val : ℚ_[2])) := by
  simp only [paramRawMinorRat, Matrix.det_apply', Matrix.of_apply, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_prod, Rat.cast_intCast]

theorem paramRawMinorRat_two_adic_column_expansion (P : Parameters) (hAdm : Admissible P) (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) :
    (paramRawMinorRat P z N c : ℚ_[2]) =
      ∑ τ : Fin (P.n N) → Fin 3,
        Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
          paramRawColumnTerm P z N r.val (c k).val (τ k)) := by
  classical
  have hmatrix :
      (Matrix.of fun r k : Fin (P.n N) => (rawEntryRat P z N r.val (c k).val : ℚ_[2])) =
        (Matrix.of fun r k : Fin (P.n N) =>
          ∑ t : Fin 3, paramRawColumnTerm P z N r.val (c k).val t) := by
    ext r k
    simp only [Matrix.of_apply, paramRawColumnTerm_sum]
    exact paramRawEntryRat_two_adic_decomposition P z hAdm hN r.isLt
      (Finset.mem_Ico.mp (c k).property).2
  rw [paramRawMinorRat_cast_two_adic, hmatrix]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]

theorem paramDeterminantRat_two_adic_column_expansion (P : Parameters) (hAdm : Admissible P) (z : ℚ) {N : ℕ} (hN : 0 < N) :
    (determinantRat P z N : ℚ_[2]) =
      ∑ c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)) with Function.Injective c,
        ((∏ k : Fin (P.n N), paramRawFilterInt P N (c k) k : ℤ) : ℚ_[2]) *
          ∑ τ : Fin (P.n N) → Fin 3,
            Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
              paramRawColumnTerm P z N r.val (c k).val (τ k)) := by
  classical
  rw [paramDeterminantRat_eq_sum_raw_minors]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro c hc
  rw [paramRawMinorRat_two_adic_column_expansion P hAdm z hN c]


end
end CatalanMeasure.Parametric
