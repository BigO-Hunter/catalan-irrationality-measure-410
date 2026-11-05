module
public import Submission.CatalanMeasure.Parametric.ChebyshevDifferences
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

def sparseRowCore (P : Parameters) (N p d : ℕ) : ℤ[X] :=
  C (2:ℤ)*((1-X)^(P.h N)*reversedRow (P.C N-p) (Chebyshev.U ℤ ((d:ℤ)-1)))

theorem sparseRowCore_coeff_below (P : Parameters) (N p d : ℕ)
    (hd : 0<d) (hcut : p+d≤P.C N) {i : ℕ} (hi : i<P.C N-p-d) :
    (sparseRowCore P N p d).coeff i=0 := by
  rw [sparseRowCore,coeff_C_mul]
  apply mul_eq_zero_of_right
  apply coeff_mul_eq_zero_below_right _ _ (P.C N-p-d) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt (P.C N-p) (d-1) _
  · simp only [Chebyshev.natDegree_U,sub_add_cancel,Int.natAbs_natCast]
    omega
  · omega
  · omega

theorem sparseRowCore_degree_le (P : Parameters) (N p d : ℕ) (hcut : p<P.C N) :
    (sparseRowCore P N p d).natDegree≤P.H N-p-1 := by
  have hdeg :=reversedRow_natDegree_le (P.C N-p) (Chebyshev.U ℤ ((d:ℤ)-1))
  have hf :=rowFactor_natDegree_le P N
  have hh : (((1-X:ℤ[X])^(P.h N))*
      reversedRow (P.C N-p) (Chebyshev.U ℤ ((d:ℤ)-1))).natDegree ≤
      ((1-X:ℤ[X])^(P.h N)).natDegree +
      (reversedRow (P.C N-p) (Chebyshev.U ℤ ((d:ℤ)-1))).natDegree := natDegree_mul_le
  have hc :=natDegree_C_mul_le (2:ℤ)
    (((1-X:ℤ[X])^(P.h N))*reversedRow (P.C N-p) (Chebyshev.U ℤ ((d:ℤ)-1)))
  change (sparseRowCore P N p d).natDegree≤
    (((1-X:ℤ[X])^(P.h N))*reversedRow (P.C N-p) (Chebyshev.U ℤ ((d:ℤ)-1))).natDegree at hc
  unfold Parameters.H
  omega

theorem sparseRowCore_coeff_above (P : Parameters) (N p d : ℕ) (hcut : p<P.C N)
    {i : ℕ} (hi : P.H N - p ≤ i) : (sparseRowCore P N p d).coeff i=0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hh :=sparseRowCore_degree_le P N p d hcut
  have hH : p<P.H N := by unfold Parameters.H;omega
  omega

theorem sparseRowCore_second_digit (P : Parameters) (N p d : ℕ)
    (hd : 0 < d) (hp : 0 < p) (hlo : 3*p+d ≤ P.C N) (hhi : P.H N ≤ 4*p)
    {i : ℕ} (hc : (sparseRowCore P N p d).coeff i ≠ 0) : 2*p ≤ i ∧ i < 3*p := by
  have hcut : p < P.C N := by omega
  have hl : P.C N-p-d ≤ i := by
    by_contra hh
    exact hc (sparseRowCore_coeff_below P N p d hd (by omega) (by omega))
  have hu : i < P.H N-p := by
    by_contra hh
    exact hc (sparseRowCore_coeff_above P N p d hcut (by omega))
  constructor <;> omega

theorem sparseRowCore_raw_digit_position (P : Parameters) (N p d j : ℕ)
    (hd : 0 < d) (hp : 0 < p) (hlo : 3*p+d ≤ P.C N)
    (hdg : d ≤ P.g N) (hwindow : P.H N ≤ 3*p+P.b N)
    (hjb : P.b N ≤ j) (hjL : j < P.L N)
    (hc : (sparseRowCore P N p d).coeff (2*p+j%p) ≠ 0) : j/p=1 ∨ j/p=2 := by
  have hcut : p < P.C N := by omega
  have hl : P.C N-p-d ≤ 2*p+j%p := by
    by_contra hh
    exact hc (sparseRowCore_coeff_below P N p d hd (by omega) (by omega))
  have hu : 2*p+j%p < P.H N-p := by
    by_contra hh
    exact hc (sparseRowCore_coeff_above P N p d hcut (by omega))
  have hdiv := Nat.mod_add_div j p
  have hCeq : P.C N=P.L N+P.g N := rfl
  have hHeq : P.H N=P.C N+P.h N := rfl
  by_cases hz : j/p=0
  · rw [hz,mul_zero,add_zero] at hdiv
    omega
  · have hqsmall : j/p < 3 := by
      by_contra hh
      have hq : 3 ≤ j/p := Nat.le_of_not_gt hh
      have hm := Nat.mul_le_mul_left p hq
      unfold Parameters.C at hl
      omega
    have hqpos : 0 < j/p := Nat.pos_of_ne_zero hz
    omega

end
end CatalanMeasure.Parametric
