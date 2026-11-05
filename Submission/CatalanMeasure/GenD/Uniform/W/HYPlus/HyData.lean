module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HySys
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyFold
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PBasis
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax5
@[expose] public section
set_option Elab.async false

/-!
# HY+ atoms: the data map and the coefficient profile `w_e`
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The atom space: `(A, c, C)`. -/
abbrev HyA (p Dn nQ : ℕ) := (Fin Dn → ZMod p) × (Fin nQ → ZMod p) × (Fin Dn → ZMod p)

/-- `Q = Σ c_i (X-1)^a0 X^i`. -/
def Qpoly (p a0 nQ : ℕ) [Fact p.Prime] (c : Fin nQ → ZMod p) : (ZMod p)[X] :=
  ∑ i : Fin nQ, C (c i) * ((X - 1) ^ a0 * X ^ (i : ℕ))

/-- The period slot coefficients `B_t = Σ_i c_i sc_i t`. -/
def Bvec {Dn nQ : ℕ} (sc : Fin nQ → Fin Dn → ZMod p) (c : Fin nQ → ZMod p) : Fin Dn → ZMod p :=
  fun t => ∑ i, c i * sc i t

/-- The datum of an atom. -/
def xd {K Dn nQ : ℕ} (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (a : HyA p Dn nQ) : Fin (Dn + Dn) → Fin (K + K) → ZMod p :=
  fun d k => Fin.addCases
    (fun t => Fin.addCases (fun κ => a.1 t * u κ + Bvec sc a.2.1 t * v κ) (fun _ => 0) k)
    (fun t => Fin.addCases (fun _ => 0) (fun κ => a.2.2 t * y κ) k) d

theorem xd_add {K Dn nQ : ℕ} (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (a b : HyA p Dn nQ) : xd u v y sc (a + b) = xd u v y sc a + xd u v y sc b := by
  funext d k
  refine Fin.addCases (fun t => ?_) (fun t => ?_) d <;>
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) k <;>
    simp only [xd, Fin.addCases_left, Fin.addCases_right, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Bvec, add_zero] <;> first | (simp only [Finset.sum_add_distrib, add_mul]; ring) | ring

theorem xd_smul {K Dn nQ : ℕ} (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (r : ZMod p) (a : HyA p Dn nQ) : xd u v y sc (r • a) = r • xd u v y sc a := by
  funext d k
  refine Fin.addCases (fun t => ?_) (fun t => ?_) d <;>
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) k <;>
    simp only [xd, Fin.addCases_left, Fin.addCases_right, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, Bvec, mul_zero] <;>
      first | ring1 | (simp only [mul_assoc, ← Finset.mul_sum]; ring1)

/-- The atom map as a linear map. -/
def xi {K Dn nQ : ℕ} (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p) :
    HyA p Dn nQ →ₗ[ZMod p] (Fin (Dn + Dn) → Fin (K + K) → ZMod p) where
  toFun := xd u v y sc
  map_add' := xd_add u v y sc
  map_smul' := xd_smul u v y sc

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
