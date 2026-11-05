module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyWv
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyThree
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Period
@[expose] public section
set_option Elab.async false

/-!
# The response of an HY+ atom over the windows `s-1, s, s+1`
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem Qpoly_coeff_zero (a0 nQ : ℕ) (c : Fin nQ → ZMod p) (m : ℕ) (hm : a0 + nQ ≤ m) :
    (Qpoly p a0 nQ c).coeff m = 0 := by
  unfold Qpoly
  rw [finset_sum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := i.isLt
  refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ (by omega : a0 + (i : ℕ) < m))
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_mul_le.trans ?_
  have h1 : ((X - 1 : (ZMod p)[X]) ^ a0).natDegree ≤ a0 := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  have h2 : ((X : (ZMod p)[X]) ^ (i : ℕ)).natDegree ≤ i := by
    simp
  omega

theorem aco_zero (hp2 : p ≠ 2) {Dn : ℕ} (hD : Dn ≤ (p - 1) / 2) (A : Fin Dn → ZMod p) (e : ℕ)
    (he : P.h N + (p - 1) / 2 + Dn ≤ e) : aco P N p A e = 0 := by
  unfold aco
  rw [finset_sum_coeff]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt
    (lt_of_lt_of_le (hLam_natDegree_lt hp2 hD t) he), mul_zero]

theorem cco_zero (hp2 : p ≠ 2) {Dn : ℕ} (hD : Dn ≤ (p - 1) / 2) (A : Fin Dn → ZMod p) (e : ℕ)
    (he : P.h N + (p - 1) / 2 + Dn ≤ e) : cco P N p A e = 0 := by
  unfold cco
  rw [finset_sum_coeff]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt
    (lt_of_lt_of_le (hmLam_natDegree_lt hp2 hD t) he), mul_zero]

theorem bco_zero (a0 nQ : ℕ) (c : Fin nQ → ZMod p) (e : ℕ) (he : a0 + nQ + p ≤ e) :
    bco p a0 nQ c e = 0 := by
  unfold bco
  rw [lc_period, Qpoly_coeff_zero a0 nQ c (e - p) (by omega), Qpoly_coeff_zero a0 nQ c e (by omega)]
  simp

/-- The profile term of coefficient `e` in window `σ`. -/
def tmv (P : Parameters) (N p : ℕ) [Fact p.Prime] {K Dn nQ : ℕ} (k0 : ℤ) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (a : HyA p Dn nQ) (J : ℕ) (σ : ℤ) (e : ℕ) : ZMod p :=
  aco P N p a.1 e * (profHp p K k0).psi (P.H N) J σ u +
    bco p a0 nQ a.2.1 e * (profHp p K k0).psi (P.H N) J σ v +
    cco P N p a.2.2 e * (profHm p K k0).psi (P.H N) J σ y

variable (hp2 : p ≠ 2) {K Dn nQ : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
  (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
  (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
    X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))

include hsc in
theorem resp_xd (hN : True) (a : HyA p Dn nQ) (J ℓ : ℕ) :
    (hySys P N p hp2 K Dn k0 hD).resp J ℓ (xd u v y sc a) =
      ∑ e ∈ Finset.range (P.h N + (p - 1) / 2 + Dn),
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ℓ - e then
          tmv P N p k0 a0 u v y a J (((P.H N : ℤ) - 1 - ℓ - e) / p) e else 0 := by
  unfold SlotSystem.resp
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · show (profAdd (profHp p K k0) (profHm p K k0)).psi (P.H N) J _
        (wv (hyLam P N p Dn) (xd u v y sc a) e) = _
    rw [profAdd_psi, wv_xd_fl1 a0 u v y sc hsc a e, wv_xd_fl2 a0 u v y sc hsc a e]
    simp only [map_add, map_smul, smul_eq_mul, tmv]
  · rfl

include hsc in
theorem resp_atom (a : HyA p Dn nQ) (J ℓ η s : ℕ) (hp0 : 0 < p) (hℓ : ℓ < p) (hpη : p ≤ η)
    (hη2 : η < 2 * p) (hem : P.h N + (p - 1) / 2 + Dn ≤ η + p)
    (hQ : a0 + nQ + p ≤ P.h N + (p - 1) / 2 + Dn) (hHη : (P.H N : ℤ) - 1 = η + s * p) :
    (hySys P N p hp2 K Dn k0 hD).resp J ℓ (xd u v y sc a) =
      tmv P N p k0 a0 u v y a J (s : ℤ) (η - ℓ) +
        (if p ≤ η - ℓ then tmv P N p k0 a0 u v y a J ((s : ℤ) + 1) (η - ℓ - p) else 0) +
        tmv P N p k0 a0 u v y a J ((s : ℤ) - 1) (η - ℓ + p) := by
  rw [resp_xd hp2 k0 hD a0 u v y sc hsc trivial]
  exact resp_sum_three p η s ℓ _ hp0 hℓ hpη hη2 hem _ hHη
    (fun e σ => tmv P N p k0 a0 u v y a J σ e)
    (fun e σ he => by
      simp only [tmv]
      rw [aco_zero hp2 hD _ e he, cco_zero hp2 hD _ e he, bco_zero a0 nQ _ e (by omega)]
      simp)

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
