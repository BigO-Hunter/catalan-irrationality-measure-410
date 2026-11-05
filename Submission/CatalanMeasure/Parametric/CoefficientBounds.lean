module
public import Submission.CatalanMeasure.Parametric.RowExtraction
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open OAI.InternalCatalan
noncomputable section

theorem rowFactor_natDegree_le (P : Parameters) (N : ℕ) :
    ((1 - X : ℤ[X]) ^ P.h N).natDegree ≤ P.h N := by
  calc
    _ ≤ P.h N * (1 - X : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
    _ = P.h N := by rw [OAI.InternalCatalan.natDegree_one_sub_X, mul_one]

theorem rowP_natDegree_le {P : Parameters} (hP : Admissible P) {N : ℕ}
    (hN : 0 < N) (r : ℕ) : (rowP P N r).natDegree ≤ P.H N - 1 := by
  have hC := C_pos hP hN
  unfold rowP
  calc
    _ ≤ ((1 - X : ℤ[X]) ^ P.h N).natDegree +
        (reversedRow (P.C N) (Chebyshev.T ℤ (rowDistance P N r : ℤ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ P.h N + (P.C N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le P N) (reversedRow_natDegree_le _ _)
    _ ≤ P.H N - 1 := by unfold Parameters.H; omega

theorem rowD_natDegree_le {P : Parameters} (hP : Admissible P) {N : ℕ}
    (hN : 0 < N) (r : ℕ) : (rowD P N r).natDegree ≤ P.H N - 1 := by
  have hC := C_pos hP hN
  unfold rowD
  rw [mul_assoc]
  calc
    _ ≤ (((1 - X : ℤ[X]) ^ P.h N) *
        reversedRow (P.C N) (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((1 - X : ℤ[X]) ^ P.h N).natDegree +
        (reversedRow (P.C N) (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ P.h N + (P.C N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le P N) (reversedRow_natDegree_le _ _)
    _ ≤ P.H N - 1 := by unfold Parameters.H; omega

theorem rowP_coeff_eq_zero_of_lt {P : Parameters} (hP : Admissible P) {N r i : ℕ}
    (hN : 0 < N) (hr : r < P.n N) (hi : i < P.A N) : (rowP P N r).coeff i = 0 := by
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (P.A N) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance P N r) _
  · simp [Chebyshev.natDegree_T]
  · exact rowDistance_lt_C hP hN hr
  · exact lt_of_lt_of_le hj (A_le_reversed_min hP hN hr)

theorem rowD_eq_zero_of_distance_zero {P : Parameters} {N r : ℕ}
    (hd : rowDistance P N r = 0) : rowD P N r = 0 := by
  simp [rowD, hd]

theorem rowD_coeff_eq_zero_of_lt {P : Parameters} (hP : Admissible P) {N r i : ℕ}
    (hN : 0 < N) (hr : r < P.n N) (hi : i < P.A N + 1) : (rowD P N r).coeff i = 0 := by
  by_cases hd : rowDistance P N r = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ (P.A N + 1) _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance P N r - 1) _
    · simp [Chebyshev.natDegree_U]
    · have hdist := rowDistance_lt_C hP hN hr
      omega
    · have hb := A_le_reversed_min hP hN hr
      have hc := rowDistance_lt_C hP hN hr
      exact lt_of_lt_of_le hj (by omega)

theorem rowP_coeff_eq_zero_of_ge {P : Parameters} (hP : Admissible P) {N r i : ℕ}
    (hN : 0 < N) (hi : P.H N ≤ i) : (rowP P N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowP_natDegree_le hP hN r
  have hH : 0 < P.H N := by have := C_pos hP hN; unfold Parameters.H; omega
  omega

theorem rowD_coeff_eq_zero_of_ge {P : Parameters} (hP : Admissible P) {N r i : ℕ}
    (hN : 0 < N) (hi : P.H N ≤ i) : (rowD P N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowD_natDegree_le hP hN r
  have hH : 0 < P.H N := by have := C_pos hP hN; unfold Parameters.H; omega
  omega

end
end CatalanMeasure.Parametric
