module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyCol
@[expose] public section
set_option Elab.async false

/-!
# Linear functionals on the HY+ atom space
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

section
variable (P N p) (Dn nQ : ℕ)

/-- Coordinate projections of the atom space. -/
def pjA (t : Fin Dn) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj t : (Fin Dn → ZMod p) →ₗ[ZMod p] ZMod p).comp
    (LinearMap.fst (ZMod p) (Fin Dn → ZMod p) ((Fin nQ → ZMod p) × (Fin Dn → ZMod p)))

def pjC (i : Fin nQ) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj i : (Fin nQ → ZMod p) →ₗ[ZMod p] ZMod p).comp
    ((LinearMap.fst (ZMod p) (Fin nQ → ZMod p) (Fin Dn → ZMod p)).comp
      (LinearMap.snd (ZMod p) (Fin Dn → ZMod p) ((Fin nQ → ZMod p) × (Fin Dn → ZMod p))))

def pjD (t : Fin Dn) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj t : (Fin Dn → ZMod p) →ₗ[ZMod p] ZMod p).comp
    ((LinearMap.snd (ZMod p) (Fin nQ → ZMod p) (Fin Dn → ZMod p)).comp
      (LinearMap.snd (ZMod p) (Fin Dn → ZMod p) ((Fin nQ → ZMod p) × (Fin Dn → ZMod p))))

/-- `a ↦ aco a.1 e`. -/
def acoL (e : ℕ) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  ∑ t : Fin Dn, (hLam P N p (t : ℕ)).coeff e • pjA p Dn nQ t

/-- `a ↦ cco a.2.2 e`. -/
def ccoL (e : ℕ) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  ∑ t : Fin Dn, (hmLam P N p (t : ℕ)).coeff e • pjD p Dn nQ t

/-- `a ↦ (Qpoly a.2.1).coeff m`. -/
def qcoL (a0 m : ℕ) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  ∑ i : Fin nQ, ((X - 1 : (ZMod p)[X]) ^ a0 * X ^ (i : ℕ)).coeff m • pjC p Dn nQ i

end

theorem acoL_apply (Dn nQ e : ℕ) (a : HyA p Dn nQ) : acoL P N p Dn nQ e a = aco P N p a.1 e := by
  simp only [acoL, aco, LinearMap.sum_apply, LinearMap.smul_apply, pjA, LinearMap.comp_apply,
    LinearMap.coe_proj, Function.eval, LinearMap.fst_apply, smul_eq_mul, finset_sum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem ccoL_apply (Dn nQ e : ℕ) (a : HyA p Dn nQ) : ccoL P N p Dn nQ e a = cco P N p a.2.2 e := by
  simp only [ccoL, cco, LinearMap.sum_apply, LinearMap.smul_apply, pjD, LinearMap.comp_apply,
    LinearMap.coe_proj, Function.eval, LinearMap.snd_apply, smul_eq_mul, finset_sum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem qcoL_apply (Dn nQ a0 m : ℕ) (a : HyA p Dn nQ) :
    qcoL p Dn nQ a0 m a = (Qpoly p a0 nQ a.2.1).coeff m := by
  simp only [qcoL, Qpoly, LinearMap.sum_apply, LinearMap.smul_apply, pjC, LinearMap.comp_apply,
    LinearMap.coe_proj, Function.eval, LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul,
    finset_sum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
