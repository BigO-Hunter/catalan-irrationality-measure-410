module
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable (R : Type*) [CommRing R]

/-- Addition identity on every signed physical row index; no restriction to
positive blocks or a fixed number of p-blocks. -/
theorem chebyshev_T_add (m n : Int) :
    T R (m+n) = T R m*T R n+(X^2-1)*U R (m-1)*U R (n-1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp only [T_one, Int.reduceSub, U_zero, mul_one]
    have h := T_eq_X_mul_T_sub_pol_U R (m-1)
    linear_combination (norm := ring_nf) h
  | add_two n ih1 ih2 =>
    have hr := T_add_two R (m+n)
    have ht := T_add_two R n
    have hu := U_add_two R ((n : Int)-1)
    linear_combination (norm := ring_nf)
      hr+2*(X : Polynomial R)*ih1-ih2-T R m*ht-(X^2-1)*U R (m-1)*hu
  | neg_add_one n ih1 ih2 =>
    have hr := T_add_two R (m+(-(n : Int)-1))
    have ht := T_add_two R (-(n : Int)-1)
    have hu := U_add_two R (-(n : Int)-2)
    linear_combination (norm := ring_nf)
      hr+2*(X : Polynomial R)*ih1-ih2-T R m*ht-(X^2-1)*U R (m-1)*hu

/-- Companion U addition identity, with the actual negative-index convention. -/
theorem chebyshev_U_add (m n : Int) :
    U R (m+n-1) = U R (m-1)*T R n+T R m*U R (n-1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp only [T_one, Int.reduceSub, U_zero, mul_one]
    have h := U_eq_X_mul_U_add_T R (m-1)
    linear_combination (norm := ring_nf) h
  | add_two n ih1 ih2 =>
    have hr := U_add_two R (m+(n : Int)-1)
    have ht := T_add_two R n
    have hu := U_add_two R ((n : Int)-1)
    linear_combination (norm := ring_nf)
      hr+2*(X : Polynomial R)*ih1-ih2-U R (m-1)*ht-T R m*hu
  | neg_add_one n ih1 ih2 =>
    have hr := U_add_two R (m+(-(n : Int)-1)-1)
    have ht := T_add_two R (-(n : Int)-1)
    have hu := U_add_two R (-(n : Int)-2)
    linear_combination (norm := ring_nf)
      hr+2*(X : Polynomial R)*ih1-ih2-U R (m-1)*ht-T R m*hu

#print axioms chebyshev_T_add
#print axioms chebyshev_U_add
end CatalanMeasure.GenD.Uniform.Prefix

