module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.ShiftBridge
@[expose] public section
set_option Elab.async false

/-!
# Degrees of the MT profile maps (hypotheses of `psi_shift`)

For blocks `κ = k0 + k` with `|κ| ≤ s` and `s ≥ 1`:
`deg Ty ≤ s`, `deg Gy ≤ s + 1` for both the T- maps (`tyMap`, `gyMap`) and the T+ period maps
(`tpTy`, `tpGy`).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem T_natDegree_le (hp2 : p ≠ 2) (κ : ℤ) : (Chebyshev.T (ZMod p) κ).natDegree = κ.natAbs := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  exact Chebyshev.natDegree_T (ZMod p) κ

theorem U_natDegree_le' (hp2 : p ≠ 2) (κ : ℤ) :
    (Chebyshev.U (ZMod p) (κ - 1)).natDegree = κ.natAbs - 1 := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  rw [Chebyshev.natDegree_U]
  simp

theorem sumT_natDegree_le (hp2 : p ≠ 2) {K s : ℕ} (k0 : ℤ) (hk : ∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s)
    (y : Fin K → ZMod p) :
    (∑ k : Fin K, C (y k) * Chebyshev.T (ZMod p) (k0 + (k : ℕ))).natDegree ≤ s := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [T_natDegree_le hp2]; exact hk k

theorem sumU_natDegree_le (hp2 : p ≠ 2) {K s : ℕ} (k0 : ℤ) (hk : ∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s)
    (y : Fin K → ZMod p) :
    (∑ k : Fin K, C (y k) * Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).natDegree ≤ s - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [U_natDegree_le' hp2]; have := hk k; omega

theorem tyMap_natDegree_le' (hp2 : p ≠ 2) {K s : ℕ} (k0 : ℤ)
    (hk : ∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s) (y : Fin K → ZMod p) :
    (tyMap p K k0 y).natDegree ≤ s := by
  rw [tyMap_apply]; exact sumT_natDegree_le hp2 k0 hk y

theorem gyMap_natDegree_le' (hp2 : p ≠ 2) {K s : ℕ} (hs : 1 ≤ s) (k0 : ℤ)
    (hk : ∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s) (y : Fin K → ZMod p) :
    (gyMap p K k0 y).natDegree ≤ s + 1 := by
  rw [gyMap_apply, uyMap_apply]
  have h1 := sumU_natDegree_le hp2 k0 hk y
  have h2 : (X ^ 2 - 1 : (ZMod p)[X]).natDegree ≤ 2 := by
    have : (X ^ 2 - 1 : (ZMod p)[X]).natDegree = 2 := natDegree_X_pow_sub_C (n := 2) (r := (1 : ZMod p))
    omega
  have := natDegree_mul_le (p := (X ^ 2 - 1 : (ZMod p)[X]))
    (q := ∑ k : Fin K, C (y k) * Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))
  omega

theorem tpTy_natDegree_le' (hp2 : p ≠ 2) {K s : ℕ} (hs : 1 ≤ s) (k0 : ℤ)
    (hk : ∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s) (y : Fin K → ZMod p) :
    (tpTy p K k0 y).natDegree ≤ s := by
  rw [tpTy_apply]
  have h1 := sumU_natDegree_le hp2 k0 hk y
  have h2 : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  have := natDegree_mul_le (p := (X - 1 : (ZMod p)[X]))
    (q := ∑ k : Fin K, C (y k) * Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))
  omega

theorem tpGy_natDegree_le' (hp2 : p ≠ 2) {K s : ℕ} (k0 : ℤ)
    (hk : ∀ k : Fin K, (k0 + (k : ℕ)).natAbs ≤ s) (y : Fin K → ZMod p) :
    (tpGy p K k0 y).natDegree ≤ s + 1 := by
  rw [tpGy_apply]
  have h1 := sumT_natDegree_le hp2 k0 hk y
  have h2 : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  have := natDegree_mul_le (p := (X - 1 : (ZMod p)[X]))
    (q := ∑ k : Fin K, C (y k) * Chebyshev.T (ZMod p) (k0 + (k : ℕ)))
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
