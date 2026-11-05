module
public import Submission.CatalanMeasure.Parametric.CoefficientBounds
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

theorem reversedRow_shift (a c : ℕ) (F : ℤ[X]) (hF : F.natDegree < c) :
    OAI.InternalCatalan.reversedRow (a+c) F =
      X^a * OAI.InternalCatalan.reversedRow c F := by
  ext i
  rw [OAI.InternalCatalan.reversedRow_coeff, coeff_X_pow_mul']
  by_cases hi : a ≤ i
  · rw [ite_eq_left hi, OAI.InternalCatalan.reversedRow_coeff]
    by_cases hu : i < a+c
    · rw [ite_eq_left hu, ite_eq_left (by omega : i-a<c)]
      congr 1
      omega
    · rw [ite_eq_right hu, ite_eq_right (by omega : ¬ i-a<c)]
  · rw [ite_eq_right hi, ite_eq_left (by omega : i<a+c)]
    apply coeff_eq_zero_of_natDegree_lt
    omega

def rowResidualP (P : Parameters) (N r : ℕ) : ℤ[X] :=
  OAI.InternalCatalan.reversedRow (P.n N-P.g N)
    (Chebyshev.T ℤ (rowDistance P N r : ℤ))

theorem C_eq_A_add_residual {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N) :
    P.C N = P.A N + (P.n N-P.g N) := by
  have hg := two_g_lt_n hP hN
  unfold Parameters.C Parameters.L Parameters.A
  omega

/-- Every polynomial in a replaced column has this common factor. -/
theorem rowP_common_factor {P : Parameters} (hP : Admissible P) {N r : ℕ}
    (hN : 0<N) (hr : r<P.n N) :
    rowP P N r = (X^(P.A N) * (1-X)^(P.h N)) * rowResidualP P N r := by
  have hd := rowDistance_le hP hN hr
  have hg := two_g_lt_n hP hN
  have hF : (Chebyshev.T ℤ (rowDistance P N r : ℤ)).natDegree < P.n N-P.g N := by
    simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
    omega
  unfold rowP rowResidualP
  rw [C_eq_A_add_residual hP hN, reversedRow_shift _ _ _ hF]
  ring

theorem rowResidualP_natDegree_le (P : Parameters) (N r : ℕ) :
    (rowResidualP P N r).natDegree ≤ P.n N-P.g N-1 :=
  OAI.InternalCatalan.reversedRow_natDegree_le _ _

end
end CatalanMeasure.Parametric
