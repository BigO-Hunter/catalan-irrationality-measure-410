module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.ChebyshevAdd
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable (R : Type*) [CommRing R]

/-- Signed step recurrence in the physical row index. -/
theorem chebyshev_U_step (a n : Int) :
    U R (a+n-1)+U R (a-n-1)=2*T R n*U R (a-1) := by
  have hp := chebyshev_U_add R a n
  have hn := chebyshev_U_add R a (-n)
  rw [T_neg, U_neg_sub_one] at hn
  linear_combination (norm := ring_nf) hp+hn

/-- Universal composition, valid in every characteristic and at signed block
indices. In characteristic p this yields the p-block physical row factors. -/
theorem chebyshev_U_mul (m n : Int) :
    U R (m*n-1)=(U R (m-1)).comp (T R n)*U R (n-1) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := chebyshev_U_step R (((m : Int)+1)*n) n
    have h₂ := congr_arg (comp · (T R n)) (U_add_two R ((m : Int)-1))
    simp only [sub_comp,mul_comp,ofNat_comp,X_comp] at h₂
    linear_combination (norm := ring_nf)
      h₁ - U R (n-1)*h₂ + 2*T R n*ih1 - ih2
  | neg_add_one m ih1 ih2 =>
    have h₁ := chebyshev_U_step R (-(m : Int)*n) n
    have h₂ := congr_arg (comp · (T R n)) (U_add_two R (-(m : Int)-2))
    simp only [sub_comp,mul_comp,ofNat_comp,X_comp] at h₂
    linear_combination (norm := ring_nf)
      h₁ - U R (n-1)*h₂ + 2*T R n*ih1 - ih2

#print axioms chebyshev_U_mul
end CatalanMeasure.GenD.Uniform.Prefix

