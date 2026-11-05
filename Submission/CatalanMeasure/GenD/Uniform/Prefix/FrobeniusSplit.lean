module
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PStep
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

/-- The elementary shear turns a split at X^p into a split at X^p-1. -/
def splitShear (p : Nat) :
    (Polynomial.degreeLT R p × Polynomial.degreeLT R p) ≃ₗ[R]
      (Polynomial.degreeLT R p × Polynomial.degreeLT R p) where
  toFun x := (x.1+x.2,x.2)
  invFun x := (x.1-x.2,x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp [add_comm, add_left_comm, add_assoc]
  map_smul' a x := by ext <;> simp [smul_add]

/-- Every degree<2p slot has exactly one pair (F,E), both degree<p, with
Q=F+(X^p-1)E. This needs no characteristic or p-dependent case assumption. -/
def slotSplit (p : Nat) : Polynomial.degreeLT R (p+p) ≃ₗ[R]
    (Polynomial.degreeLT R p × Polynomial.degreeLT R p) :=
  (Polynomial.degreeLT.addLinearEquiv R p p).trans (splitShear p)

theorem slotSplit_identity (p : Nat) (Q : Polynomial.degreeLT R (p+p)) :
    (Q : Polynomial R) = ((slotSplit p Q).1 : Polynomial R) +
      (X^p-1)*((slotSplit p Q).2 : Polynomial R) := by
  have h := Polynomial.degreeLT.addLinearEquiv_symm_apply (R := R) (m := p) (n := p)
    (Polynomial.degreeLT.addLinearEquiv R p p Q)
  simp only [LinearEquiv.symm_apply_apply] at h
  change (Q : Polynomial R) =
    (((Polynomial.degreeLT.addLinearEquiv R p p Q).1 +
      (Polynomial.degreeLT.addLinearEquiv R p p Q).2 : Polynomial.degreeLT R p) : Polynomial R) +
      (X^p-1)*((Polynomial.degreeLT.addLinearEquiv R p p Q).2 : Polynomial R)
  rw [h, Submodule.coe_add]
  ring

theorem slotSplit_injective (p : Nat) : Function.Injective (slotSplit (R := R) p) :=
  (slotSplit p).injective

/-- Frobenius-normalize the complete h quotient, including h/p≥p. -/
theorem omega_frobenius {p : Nat} [Fact p.Prime] [CharP R p] (h : Nat) :
    (X-1 : Polynomial R)^h = (X^p-1)^(h/p)*(X-1)^(h%p) := by
  rw [filter_polynomial_split (p := p) h]
  exact mul_comm _ _

#print axioms slotSplit_identity
end
end CatalanMeasure.GenD.Uniform.Prefix