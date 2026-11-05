module
public import Submission.CatalanMeasure.Parametric.TwoAdicColumns
public import Submission.OAI.NumberTheory.Catalan.Estimates.ExceptionalScalarBounds
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def paramExceptionScalar (P : Parameters) (q : ℚ) (N u j : ℕ) : ℚ_[2] :=
  (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
    ∑ v ∈ Finset.range (P.h N + 1),
      (((1 - X : ℤ[X]) ^ P.h N).coeff v : ℚ_[2]) *
        (centralCoeffKernel (((P.C N - 1 - u + v : ℕ) : ℤ) - j) : ℚ_[2])

def paramBoundaryScalar (P : Parameters) (N u j : ℕ) : ℚ_[2] :=
  ∑ v ∈ Finset.range (P.h N + 1),
    (((1 - X : ℤ[X]) ^ P.h N).coeff v : ℚ_[2]) *
      ((-smoothingMoment 0 1) * (if P.C N - 1 - u + v = j then 1 else 0) -
        (3 / 2 : ℚ_[2]) * (zetaRat (P.C N - 1 - u + v) j : ℚ_[2]))

theorem paramExceptionalScalar_index_lt_H (P : Parameters) {N u v : ℕ}
    (hu : u < P.C N) (hv : v < P.h N + 1) :
    P.C N - 1 - u + v < P.H N := by
  unfold Parameters.H at *
  omega

private theorem paramContract_rowFactor_reversed (P : Parameters) (N : ℕ) (F : ℤ[X]) (w : ℕ → ℚ_[2]) :
    (∑ i ∈ Finset.range (P.H N),
      ((((1 - X : ℤ[X]) ^ P.h N * reversedRow (P.C N) F).coeff i) : ℚ_[2]) *
        w i) =
      ∑ u ∈ Finset.range (P.C N), (F.coeff u : ℚ_[2]) *
        ∑ v ∈ Finset.range (P.h N + 1),
          (((1 - X : ℤ[X]) ^ P.h N).coeff v : ℚ_[2]) *
            w (P.C N - 1 - u + v) := by
  classical
  have hfactor : (1 - X : ℤ[X]) ^ P.h N =
      ∑ v ∈ Finset.range (P.h N + 1),
        Polynomial.C (((1 - X : ℤ[X]) ^ P.h N).coeff v) * X ^ v :=
    Polynomial.as_sum_range_C_mul_X_pow' _
      (lt_of_le_of_lt (rowFactor_natDegree_le P N) (Nat.lt_succ_self _))
  have hpoly : (1 - X : ℤ[X]) ^ P.h N * reversedRow (P.C N) F =
      ∑ u ∈ Finset.range (P.C N), ∑ v ∈ Finset.range (P.h N + 1),
        Polynomial.C (F.coeff u * ((1 - X : ℤ[X]) ^ P.h N).coeff v) *
          X ^ (P.C N - 1 - u + v) := by
    unfold reversedRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    calc
      _ = (∑ v ∈ Finset.range (P.h N + 1),
          Polynomial.C (((1 - X : ℤ[X]) ^ P.h N).coeff v) * X ^ v) *
            (Polynomial.C (F.coeff u) * X ^ (P.C N - 1 - u)) :=
        congrArg (fun Q : ℤ[X] => Q *
          (Polynomial.C (F.coeff u) * X ^ (P.C N - 1 - u))) hfactor
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [map_mul, pow_add]
        ring
  rw [hpoly]
  simp only [finsetSum_coeff, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hi := paramExceptionalScalar_index_lt_H P
    (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  simp [Finset.mem_range, hi, mul_assoc]

theorem paramExceptionColumn_eq_sum_exceptionScalar (P : Parameters) (q : ℚ) (N r j : ℕ) :
    paramExceptionColumn P q N r j =
      ∑ u ∈ Finset.range (P.C N),
        ((Chebyshev.T ℤ (rowDistance P N r : ℤ)).coeff u : ℚ_[2]) *
          paramExceptionScalar P q N u j := by
  unfold paramExceptionColumn rowP
  rw [paramContract_rowFactor_reversed, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  unfold paramExceptionScalar
  ring

theorem paramBoundaryColumn_eq_sum_boundaryScalar (P : Parameters) (N r j : ℕ) :
    paramBoundaryColumn P N r j =
      ∑ u ∈ Finset.range (P.C N),
        ((Int.sign (rowOffset P N r) *
          (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2]) *
            paramBoundaryScalar P N u j := by
  unfold paramBoundaryColumn rowD
  simp only [mul_assoc, coeff_C_mul, Int.cast_mul]
  rw [← Finset.mul_sum, paramContract_rowFactor_reversed, Finset.mul_sum]
  simp only [paramBoundaryScalar]


theorem paramExceptionScalar_norm_le (P : Parameters) (q : ℚ) {N u : ℕ} (j : ℕ)
    (hu : u < P.C N) :
    ‖paramExceptionScalar P q N u j‖ ≤
      ‖4 * (q : ℚ_[2]) - smoothingMoment 0 0‖ *
        (2 : ℝ) ^ ((P.H N : ℤ) - 1 - u - j) := by
  unfold paramExceptionScalar
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro v hv
  have hv' := Finset.mem_range.mp hv
  have hCH : P.H N=P.C N+P.h N :=rfl
  have hindex : (((P.C N - 1 - u + v : ℕ) : ℤ) - j) ≤
      (P.H N : ℤ) - 1 - u - j := by omega
  have hk := (centralCoeffKernel_norm_le
    (((P.C N - 1 - u + v : ℕ) : ℤ) - j)).trans
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hindex)
  rw [norm_mul]
  calc
    _ ≤ 1 * (2 : ℝ) ^ ((P.H N : ℤ) - 1 - u - j) :=
      mul_le_mul (Padic.norm_int_le_one _) hk (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem paramBoundaryScalar_norm_le (P : Parameters) {N u j : ℕ}
    (hu : u < P.C N) (hj : j < P.H N) :
    ‖paramBoundaryScalar P N u j‖ ≤
      max ‖-smoothingMoment 0 1‖ (2 * (2 : ℝ) ^ (2 * Nat.log 2 (P.H N))) := by
  have hthree : ‖(3 : ℚ_[2])‖ ≤ (1 : ℝ) := by
    simpa using Padic.norm_int_le_one (3 : ℤ)
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using Padic.norm_p (p := 2)
  have hratio : ‖(3 / 2 : ℚ_[2])‖ ≤ (2 : ℝ) := by
    rw [norm_div, htwo]
    calc
      _ ≤ 1 / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hthree (by norm_num)
      _ = _ := by norm_num
  unfold paramBoundaryScalar
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (le_trans (norm_nonneg _) (le_max_left _ _))
  intro v hv
  have hi := paramExceptionalScalar_index_lt_H P hu (Finset.mem_range.mp hv)
  have hz := zetaRat_norm_le (P.H N) (P.C N - 1 - u + v) j hi hj
  have hdelta : ‖(-smoothingMoment 0 1) *
      (if P.C N - 1 - u + v = j then (1 : ℚ_[2]) else 0)‖ ≤
      ‖-smoothingMoment 0 1‖ := by
    split_ifs <;> simp
  have hzeta : ‖(3 / 2 : ℚ_[2]) *
      (zetaRat (P.C N - 1 - u + v) j : ℚ_[2])‖ ≤
      2 * (2 : ℝ) ^ (2 * Nat.log 2 (P.H N)) := by
    rw [norm_mul]
    exact mul_le_mul hratio hz (norm_nonneg _) (by norm_num)
  have hinner : ‖(-smoothingMoment 0 1) *
      (if P.C N - 1 - u + v = j then (1 : ℚ_[2]) else 0) -
      (3 / 2 : ℚ_[2]) * (zetaRat (P.C N - 1 - u + v) j : ℚ_[2])‖ ≤
      max ‖-smoothingMoment 0 1‖ (2 * (2 : ℝ) ^ (2 * Nat.log 2 (P.H N))) := by
    have hsum := Padic.nonarchimedean
      ((-smoothingMoment 0 1) *
        (if P.C N - 1 - u + v = j then (1 : ℚ_[2]) else 0))
      (-((3 / 2 : ℚ_[2]) * (zetaRat (P.C N - 1 - u + v) j : ℚ_[2])))
    rw [← sub_eq_add_neg, norm_neg] at hsum
    exact hsum.trans (max_le_max hdelta hzeta)
  rw [norm_mul]
  calc
    _ ≤ 1 * max ‖-smoothingMoment 0 1‖
        (2 * (2 : ℝ) ^ (2 * Nat.log 2 (P.H N))) :=
      mul_le_mul (Padic.norm_int_le_one _) hinner (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _


end
end CatalanMeasure.Parametric
