module
public import Submission.CatalanMeasure.Parametric.Contact
public import Submission.OAI.NumberTheory.Catalan.Polynomial.Rationality
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Matrix Finset OAI.InternalCatalan
noncomputable section

theorem row_contact_real {P : Parameters} (hP : Admissible P) {N r j : ℕ}
    (hN : 0<N) (hr : r<P.n N) (hj : j<P.L N) :
    (∑ i ∈ range (P.H N),((rowP P N r).coeff i:ℝ)*
      (centralCoeffKernel ((j:ℤ)-i-1):ℝ))=((rowD P N r).coeff j:ℝ) := by
  exact_mod_cast row_contact hP hN hr hj

theorem mixedMoment_rowP_evaluation {P : Parameters} (hP : Admissible P) {N r j : ℕ}
    (hN : 0<N) (hr : r<P.n N) (hj : j<P.L N) :
    mixedMoment (realPoly (rowP P N r)) (X^j) =
      (∑ i ∈ range (P.H N),((rowP P N r).coeff i:ℝ)*
        ((momentRat i j:ℝ)+4*catalan*(centralCoeffKernel ((i:ℤ)-j):ℝ))) +
      (3/2:ℝ)*zetaSeries 0 0*((rowD P N r).coeff j:ℝ) := by
  rw [mixedMoment_realPoly_X_pow_eq_sum_range (rowP P N r) (P.H N) j
    (fun i hi =>rowP_coeff_eq_zero_of_ge hP hN hi)]
  simp_rw [mixedMoment_X_pow_evaluation]
  calc
    _ = ∑ i ∈ range (P.H N), (((rowP P N r).coeff i:ℝ)*
        ((momentRat i j:ℝ)+4*catalan*(centralCoeffKernel ((i:ℤ)-j):ℝ)) +
        ((3/2:ℝ)*zetaSeries 0 0)*(((rowP P N r).coeff i:ℝ)*
          (centralCoeffKernel ((j:ℤ)-i-1):ℝ))) := by
            apply sum_congr rfl
            intro i _
            ring
    _ = _ := by rw [sum_add_distrib,← mul_sum,row_contact_real hP hN hr hj]

theorem zetaMoment_rowD_evaluation {P : Parameters} (hP : Admissible P) {N r j : ℕ}
    (hN : 0<N) (hj : j<P.L N) :
    zetaMoment (realPoly (rowD P N r)) (X^j) =
      (∑ i ∈ range (P.H N),((rowD P N r).coeff i:ℝ)*(zetaRat i j:ℝ)) +
      ((rowD P N r).coeff j:ℝ)*zetaSeries 0 0 := by
  have hjH : j<P.H N := by unfold Parameters.H Parameters.C;omega
  rw [zetaMoment_realPoly_X_pow_eq_sum_range (rowD P N r) (P.H N) j
    (fun i hi =>rowD_coeff_eq_zero_of_ge hP hN hi)]
  have hterms : (∑ i ∈ range (P.H N),((rowD P N r).coeff i:ℝ)*zetaSeries i j) =
      ∑ i ∈ range (P.H N),((rowD P N r).coeff i:ℝ)*
        ((zetaRat i j:ℝ)+if i=j then zetaSeries 0 0 else 0) := by
    apply sum_congr rfl
    intro i _
    rw [zetaSeries_eq_zetaRat_add i j]
  rw [hterms]
  simp_rw [mul_add]
  rw [sum_add_distrib]
  congr 1
  rw [sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro hj'
    exact (hj' (mem_range.mpr hjH)).elim

def realEntry (P : Parameters) (N r k : ℕ) : ℝ :=
  ∑ v ∈ range (P.q N+1),(filterCoeffRat P N v:ℝ)*
    (mixedMoment (realPoly (rowP P N r)) (X^(P.b N+k+v)) -
      (3/2:ℝ)*zetaMoment (realPoly (rowD P N r)) (X^(P.b N+k+v)))

theorem rawEntry_real_affine {P : Parameters} (hP : Admissible P) {N r j : ℕ}
    (hN : 0<N) (hr : r<P.n N) (hj : j<P.L N) :
    (rawEntryRat P 0 N r j:ℝ)+catalan*(rawCatalanCoeffRat P N r j:ℝ) =
      mixedMoment (realPoly (rowP P N r)) (X^j) -
        (3/2:ℝ)*zetaMoment (realPoly (rowD P N r)) (X^j) := by
  rw [mixedMoment_rowP_evaluation hP hN hr hj,zetaMoment_rowD_evaluation hP hN hj]
  simp only [rawEntryRat,rawCatalanCoeffRat,mul_zero,zero_mul,add_zero]
  push_cast
  simp_rw [mul_add,sum_add_distrib]
  rw [mul_sum]
  ring_nf
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [show (i:ℤ)-(j:ℤ)=-(j:ℤ)+i by ring] <;> ring

theorem filteredEntry_real_affine {P : Parameters} (hP : Admissible P) {N r k : ℕ}
    (hN : 0<N) (hr : r<P.n N) (hk : k<P.n N) :
    (filteredEntryRat P 0 N r k:ℝ)+catalan*(filteredCatalanCoeffRat P N r k:ℝ)=realEntry P N r k := by
  unfold filteredEntryRat filteredCatalanCoeffRat realEntry
  push_cast
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have hh := rawEntry_real_affine (j := P.b N+k+v) hP hN hr
    (rawColumn_lt_L (v := v) hk (by have :=mem_range.mp hv;omega))
  linear_combination (filterCoeffRat P N v:ℝ)*hh

theorem aeval_catalan_deltaPoly {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0<N) :
    aeval catalan (deltaPoly P N)=det (fun r k : Fin (P.n N) =>realEntry P N r.val k.val) := by
  have hh := AlgHom.map_det (aeval (R := ℚ) catalan)
    ((X:ℚ[X]) • (measureCatalanMatrix P N).map C + (measureBaseMatrix P N).map C)
  unfold deltaPoly
  rw [hh]
  congr 1
  ext r k
  rw [AlgHom.mapMatrix_apply,Matrix.map_apply,deltaPoly_matrix_entry]
  simp only [map_add,map_mul,aeval_X,aeval_C,eq_ratCast]
  rw [← filteredEntry_real_affine hP hN r.isLt k.isLt]
  ring

end
end CatalanMeasure.Parametric
