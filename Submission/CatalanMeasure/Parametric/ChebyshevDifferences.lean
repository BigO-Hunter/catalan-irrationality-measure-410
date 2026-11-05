module
public import Submission.CatalanMeasure.Parametric.SparseDigitConstants
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

theorem chebyshev_T_difference (R : Type*) [CommRing R] (m : ℤ) (d : ℕ) :
    Chebyshev.T R (m+(d:ℤ))-Chebyshev.T R (m-(d:ℤ)) =
      2*(X^2-1)*Chebyshev.U R (m-1)*Chebyshev.U R ((d:ℤ)-1) := by
  induction d using Nat.twoStepInduction with
  | zero => simp [Chebyshev.U_neg_one]
  | one =>
    have h1 :=Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T R (m-1)
    have h2 :=Chebyshev.T_add_one R m
    simp only [show m-1+1=m by ring,show m-1+2=m+1 by ring] at h1
    simp only [Nat.cast_one,sub_self,Chebyshev.U_zero,mul_one]
    linear_combination (norm :=ring_nf) 2*h1-h2
  | more d ih0 ih1 =>
    have h1 :=Chebyshev.T_add_two R (m+(d:ℤ))
    have h2 :=Chebyshev.T_sub_two R (m-(d:ℤ))
    have h3 :=Chebyshev.U_add_two R ((d:ℤ)-1)
    push_cast at ih1 ⊢
    linear_combination (norm :=ring_nf)
      h1-h2+2*(X:R[X])*ih1-ih0-(2*(X^2-1)*Chebyshev.U R (m-1))*h3

theorem chebyshev_U_difference (R : Type*) [CommRing R] (m : ℤ) (d : ℕ) :
    Chebyshev.U R (m+(d:ℤ)-1)-Chebyshev.U R (m-(d:ℤ)-1) =
      2*Chebyshev.T R m*Chebyshev.U R ((d:ℤ)-1) := by
  induction d using Nat.twoStepInduction with
  | zero => simp [Chebyshev.U_neg_one]
  | one =>
    have hh :=Chebyshev.two_mul_T_eq_U_sub_U R (m-2)
    simp only [show m-2+2=m by ring] at hh
    simpa only [Nat.cast_one,add_sub_cancel_right,show m-1-1=m-2 by ring,
      sub_self,Chebyshev.U_zero,mul_one] using hh.symm
  | more d ih0 ih1 =>
    have h1 :=Chebyshev.U_add_two R (m+(d:ℤ)-1)
    have h2 :=Chebyshev.U_sub_two R (m-(d:ℤ)-1)
    have h3 :=Chebyshev.U_add_two R ((d:ℤ)-1)
    push_cast at ih1 ⊢
    linear_combination (norm :=ring_nf)
      h1-h2+2*(X:R[X])*ih1-ih0-(2*Chebyshev.T R m)*h3

end
end CatalanMeasure.Parametric
