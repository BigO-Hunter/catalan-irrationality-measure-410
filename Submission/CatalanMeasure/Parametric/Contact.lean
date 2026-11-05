module
public import Submission.CatalanMeasure.Parametric.CoefficientBounds
public import Submission.OAI.NumberTheory.Catalan.Determinants.TwoAdicSmoothedMinor
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem rowDistance_le_g {P : Parameters} {N r : ℕ} (hr : r≤P.g N) :
    rowDistance P N r≤P.g N := by unfold rowDistance rowOffset;omega

theorem rowP_left_contact {P : Parameters} (hP : Admissible P) {N r i : ℕ}
    (hN : 0<N) (hrg : r≤P.g N) (hi : i<P.L N-1) : (rowP P N r).coeff i=0 := by
  have hd := rowDistance_le_g hrg
  have hC := C_pos hP hN
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (P.L N-1) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance P N r) _
  · simp [Chebyshev.natDegree_T]
  · unfold Parameters.C at hC ⊢;omega
  · unfold Parameters.C at hC ⊢;omega

theorem rowD_left_contact {P : Parameters} (hP : Admissible P) {N r i : ℕ}
    (hN : 0<N) (hrg : r≤P.g N) (hi : i<P.L N) : (rowD P N r).coeff i=0 := by
  have hd := rowDistance_le_g hrg
  by_cases hz : rowDistance P N r=0
  · rw [rowD_eq_zero_of_distance_zero hz];simp
  have hC := C_pos hP hN
  unfold rowD
  apply coeff_mul_eq_zero_below_right _ _ (P.L N) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance P N r-1) _
  · simp [Chebyshev.natDegree_U]
  · unfold Parameters.C at hC ⊢;omega
  · unfold Parameters.C at hC ⊢;omega

/-- The contact identity cancels the zeta(2) term in every actual moment entry. -/
theorem row_contact {P : Parameters} (hP : Admissible P) {N r j : ℕ}
    (hN : 0<N) (hr : r<P.n N) (hj : j<P.L N) :
    (∑ i ∈ Finset.range (P.H N),((rowP P N r).coeff i:ℚ)*
      centralCoeffKernel ((j:ℤ)-i-1))=((rowD P N r).coeff j:ℚ) := by
  rcases le_or_gt r (P.g N) with hrg|hrg
  · rw [rowD_left_contact hP hN hrg hj,Int.cast_zero]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i<P.L N-1
    · rw [rowP_left_contact hP hN hrg hi,Int.cast_zero,zero_mul]
    · rw [centralCoeffKernel_of_neg (by omega : (j:ℤ)-i-1<0),mul_zero]
  · have hjC : j<P.C N := by unfold Parameters.C;omega
    have hjH : j<P.H N := by unfold Parameters.H;omega
    have hd := rowDistance_lt_C hP hN hr
    have hs : Int.sign (rowOffset P N r)=1 := by
      apply Int.sign_eq_one_of_pos
      unfold rowOffset
      omega
    have hbase : ∀ l<P.C N,PowerSeries.coeff l
        (contactSeries (reversedRow (P.C N) (Chebyshev.T ℤ (rowDistance P N r:ℤ)))) =
        PowerSeries.coeff l (intPolynomialSeries
          (reversedRow (P.C N) (Chebyshev.U ℤ ((rowDistance P N r:ℤ)-1)))) := by
      intro l hl
      exact reversedChebyshev_contact_series hd hl
    have hmul := series_coeff_mul_congr_below hbase
      (intPolynomialSeries ((1-X:ℤ[X])^(P.h N))) hjC
    rw [← contactSeries_mul,← intPolynomialSeries_mul] at hmul
    rw [contactSeries_coeff_eq_sum _ hjH,coeff_intPolynomialSeries] at hmul
    simpa only [rowP,rowD,hs,Polynomial.C_1,one_mul] using hmul

end
end CatalanMeasure.Parametric
