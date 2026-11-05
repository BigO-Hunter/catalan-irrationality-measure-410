module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyData
@[expose] public section
set_option Elab.async false

/-!
# The coefficient profile `w_e` of an HY+ atom
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Coefficient `a_e` of `λ_A = Σ A_t hLam_t`. -/
def aco (P : Parameters) (N p : ℕ) [Fact p.Prime] {Dn : ℕ} (A : Fin Dn → ZMod p) (e : ℕ) : ZMod p :=
  (∑ t : Fin Dn, C (A t) * hLam P N p (t : ℕ)).coeff e

/-- Coefficient `c_e` of `λ_C = Σ C_t hmLam_t`. -/
def cco (P : Parameters) (N p : ℕ) [Fact p.Prime] {Dn : ℕ} (C' : Fin Dn → ZMod p) (e : ℕ) : ZMod p :=
  (∑ t : Fin Dn, C (C' t) * hmLam P N p (t : ℕ)).coeff e

/-- Coefficient `b_e` of `X^p Q - Q`. -/
def bco (p a0 nQ : ℕ) [Fact p.Prime] (c : Fin nQ → ZMod p) (e : ℕ) : ZMod p :=
  (X ^ p * Qpoly p a0 nQ c - Qpoly p a0 nQ c).coeff e

/-- The slot polynomial family of `hySys`. -/
def hyLam (P : Parameters) (N p Dn : ℕ) [Fact p.Prime] : Fin (Dn + Dn) → (ZMod p)[X] :=
  Fin.append (fun t : Fin Dn => hLam P N p (t : ℕ)) (fun t : Fin Dn => hmLam P N p (t : ℕ))

theorem hySys_lam (hp2 : p ≠ 2) (K Dn : ℕ) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) :
    (hySys P N p hp2 K Dn k0 hD).lam = hyLam P N p Dn := rfl

theorem Qpoly_period (a0 nQ : ℕ) (c : Fin nQ → ZMod p) :
    X ^ p * Qpoly p a0 nQ c - Qpoly p a0 nQ c =
      ∑ i : Fin nQ, C (c i) * (X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ))) := by
  unfold Qpoly
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable (hp2 : p ≠ 2) {K Dn nQ : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
  (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
  (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
    X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))

include hsc in
theorem wv_xd_fl1 (a : HyA p Dn nQ) (e : ℕ) :
    fl1 K K (wv (hyLam P N p Dn) (xd u v y sc a) e) =
      aco P N p a.1 e • u + bco p a0 nQ a.2.1 e • v := by
  funext κ
  simp only [fl1_apply, wv, hyLam, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_add, Pi.add_apply,
    Fin.append_left, Fin.append_right, xd, Fin.addCases_left, Fin.addCases_right, Pi.add_apply,
    mul_zero, Finset.sum_const_zero, add_zero]
  have hb : ∑ t : Fin Dn, (hLam P N p (t : ℕ)).coeff e * Bvec sc a.2.1 t = bco p a0 nQ a.2.1 e := by
    unfold bco
    rw [Qpoly_period, finset_sum_coeff]
    simp only [coeff_C_mul, Bvec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsc i, finset_sum_coeff]
    simp only [coeff_C_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have ha : ∑ t : Fin Dn, (hLam P N p (t : ℕ)).coeff e * a.1 t = aco P N p a.1 e := by
    unfold aco
    rw [finset_sum_coeff]
    simp only [coeff_C_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ x : Fin Dn, (hLam P N p (x : ℕ)).coeff e * (a.1 x * u κ)) =
      (∑ x : Fin Dn, (hLam P N p (x : ℕ)).coeff e * a.1 x) * u κ by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring,
    show (∑ x : Fin Dn, (hLam P N p (x : ℕ)).coeff e * (Bvec sc a.2.1 x * v κ)) =
      (∑ x : Fin Dn, (hLam P N p (x : ℕ)).coeff e * Bvec sc a.2.1 x) * v κ by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, ha, hb]

include hsc in
theorem wv_xd_fl2 (a : HyA p Dn nQ) (e : ℕ) :
    fl2 K K (wv (hyLam P N p Dn) (xd u v y sc a) e) =
      cco P N p a.2.2 e • y := by
  funext κ
  simp only [fl2_apply, wv, hyLam, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_add, Pi.add_apply,
    Fin.append_left, Fin.append_right, xd, Fin.addCases_left, Fin.addCases_right,
    mul_zero, Finset.sum_const_zero, zero_add]
  unfold cco
  rw [finset_sum_coeff, Finset.sum_mul]
  simp only [coeff_C_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
