module
public import Submission.CatalanMeasure.Parametric.SparseRowCore
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem reversedRow_cut_shift (K t : ℕ) (F : ℤ[X])
    (ht : t<K) (hF : F.natDegree<K-t) :
    reversedRow K F=X^t*reversedRow (K-t) F := by
  ext i
  rw [reversedRow_coeff,coeff_X_pow_mul',reversedRow_coeff]
  by_cases hit : t ≤ i
  · rw [ite_eq_left hit]
    by_cases hiK : i<K
    · rw [ite_eq_left hiK,ite_eq_left (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hiK,ite_eq_right (by omega)]
  · rw [ite_eq_right hit,ite_eq_left (by omega)]
    apply coeff_eq_zero_of_natDegree_lt
    omega

theorem sparseRowCore_shift (P : Parameters) (N p d : ℕ)
    (hd : 0<d) (hcut : 2*p+d ≤ P.C N) :
    sparseRowCore P N p d=X^p*sparseRowCore P N (2*p) d := by
  have hF : (Chebyshev.U ℤ ((d:ℤ)-1)).natDegree<P.C N-p-p := by
    simp only [Chebyshev.natDegree_U,sub_add_cancel,Int.natAbs_natCast]
    omega
  have ht : p<P.C N-p := by omega
  have hh :=reversedRow_cut_shift (P.C N-p) p (Chebyshev.U ℤ ((d:ℤ)-1)) ht hF
  unfold sparseRowCore
  rw [hh]
  have hidx : P.C N-p-p=P.C N-2*p :=by omega
  rw [hidx]
  ring

end
end CatalanMeasure.Parametric
