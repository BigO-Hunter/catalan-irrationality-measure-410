module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.ChebyshevComposition
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable (R : Type*) [CommRing R]

theorem chebyshev_U_reflect (n j : Int) :
    U R (n-j-1)=U R (n-1)*T R j-T R n*U R (j-1) := by
  have h := chebyshev_U_add R n (-j)
  rw [T_neg,U_neg_sub_one] at h
  simpa only [mul_neg,sub_eq_add_neg] using h

theorem chebyshev_T_reflect (n j : Int) :
    T R (n-j)=T R n*T R j-(X^2-1)*U R (n-1)*U R (j-1) := by
  have h := chebyshev_T_add R n (-j)
  rw [T_neg,U_neg_sub_one] at h
  simpa only [mul_neg,sub_eq_add_neg] using h

theorem chebyshev_U_block (k n j : Int) :
    U R (k*n+j-1)=
      (U R (k-1)).comp (T R n)*U R (n-1)*T R j+
      (T R k).comp (T R n)*U R (j-1) := by
  rw [chebyshev_U_add,chebyshev_U_mul,T_mul]

theorem chebyshev_T_block (k n j : Int) :
    T R (k*n+j)=
      (T R k).comp (T R n)*T R j+
      (X^2-1)*(U R (k-1)).comp (T R n)*U R (n-1)*U R (j-1) := by
  rw [chebyshev_T_add,chebyshev_U_mul,T_mul]
  ring

/-- The full symmetric physical pair, on every signed block, has one common
native slot. The formula includes j=0 and needs no finite-characteristic inverse. -/
theorem physical_pair_U_plus (k n j : Int) :
    U R (k*n+j-1)+U R ((k+1)*n-j-1)=
      ((U R k).comp (T R n)+(U R (k-1)).comp (T R n))*
      (U R (n-1)*T R j+(1-T R n)*U R (j-1)) := by
  have h₁ := chebyshev_U_block R k n j
  have h₂ := chebyshev_U_block R (k+1) n (-j)
  simp only [T_neg,U_neg_sub_one,mul_neg] at h₂
  have h₃ := congr_arg (comp · (T R n)) (T_eq_U_sub_X_mul_U R k)
  have h₄ := congr_arg (comp · (T R n)) (T_eq_X_mul_U_sub_U R (k-1))
  simp only [sub_comp,mul_comp,X_comp] at h₃ h₄
  linear_combination (norm := ring_nf) h₁+h₂+U R (j-1)*(h₃-h₄)

/-- Antisymmetric physical pair, with the same unrestricted signed block index. -/
theorem physical_pair_U_minus (k n j : Int) :
    U R (k*n+j-1)-U R ((k+1)*n-j-1)=
      ((U R k).comp (T R n)-(U R (k-1)).comp (T R n))*
      ((1+T R n)*U R (j-1)-U R (n-1)*T R j) := by
  have h₁ := chebyshev_U_block R k n j
  have h₂ := chebyshev_U_block R (k+1) n (-j)
  simp only [T_neg,U_neg_sub_one,mul_neg] at h₂
  have h₃ := congr_arg (comp · (T R n)) (T_eq_U_sub_X_mul_U R k)
  have h₄ := congr_arg (comp · (T R n)) (T_eq_X_mul_U_sub_U R (k-1))
  simp only [sub_comp,mul_comp,X_comp] at h₃ h₄
  linear_combination (norm := ring_nf) h₁-h₂+U R (j-1)*(h₃+h₄)

#print axioms physical_pair_U_plus
#print axioms physical_pair_U_minus
/-- Polynomial Pell identity on every signed index, in every commutative ring. -/
theorem chebyshev_pell_signed (n : Int) :
    (T R n)^2-(X^2-1)*(U R (n-1))^2=1 := by
  have h := chebyshev_T_add R n (-n)
  rw [T_neg,U_neg_sub_one] at h
  simp only [add_neg_cancel,T_zero,mul_neg] at h
  linear_combination (norm := ring_nf) -h

theorem physical_pair_T_plus (k n j : Int) :
    U R (n-1)*(T R (k*n+j)+T R ((k+1)*n-j))=
      (1+T R n)*((U R k).comp (T R n)-(U R (k-1)).comp (T R n))*
      (U R (n-1)*T R j+(1-T R n)*U R (j-1)) := by
  have h₁ := chebyshev_T_block R k n j
  have h₂ := chebyshev_T_block R (k+1) n (-j)
  simp only [T_neg,U_neg_sub_one,mul_neg] at h₂
  have h₃ := congr_arg (comp · (T R n)) (T_eq_U_sub_X_mul_U R k)
  have h₄ := congr_arg (comp · (T R n)) (T_eq_X_mul_U_sub_U R (k-1))
  simp only [sub_comp,mul_comp,X_comp] at h₃ h₄
  have hp := chebyshev_pell_signed R n
  linear_combination (norm := ring_nf)
    U R (n-1)*(h₁+h₂)+U R (n-1)*T R j*(h₃+h₄)+
      ((U R k).comp (T R n)-(U R (k-1)).comp (T R n))*U R (j-1)*hp

theorem physical_pair_T_minus (k n j : Int) :
    U R (n-1)*(T R (k*n+j)-T R ((k+1)*n-j))=
      (T R n-1)*((U R k).comp (T R n)+(U R (k-1)).comp (T R n))*
      ((1+T R n)*U R (j-1)-U R (n-1)*T R j) := by
  have h₁ := chebyshev_T_block R k n j
  have h₂ := chebyshev_T_block R (k+1) n (-j)
  simp only [T_neg,U_neg_sub_one,mul_neg] at h₂
  have h₃ := congr_arg (comp · (T R n)) (T_eq_U_sub_X_mul_U R k)
  have h₄ := congr_arg (comp · (T R n)) (T_eq_X_mul_U_sub_U R (k-1))
  simp only [sub_comp,mul_comp,X_comp] at h₃ h₄
  have hp := chebyshev_pell_signed R n
  linear_combination (norm := ring_nf)
    U R (n-1)*(h₁-h₂)+U R (n-1)*T R j*(h₃-h₄)-
      ((U R k).comp (T R n)+(U R (k-1)).comp (T R n))*U R (j-1)*hp

#print axioms physical_pair_T_plus
#print axioms physical_pair_T_minus
end CatalanMeasure.GenD.Uniform.Prefix



