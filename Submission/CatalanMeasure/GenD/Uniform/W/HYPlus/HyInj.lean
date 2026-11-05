module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyExtract
@[expose] public section
set_option Elab.async false

/-!
# Injectivity of the atom map, divisibility and degree of the folded polynomial
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

section
variable {K Dn nQ : ℕ} (a0 : ℕ) (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
  (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
    X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))

include hsc in
theorem Bvec_zero (c : Fin nQ → ZMod p) (hB : Bvec sc c = 0) : c = 0 := by
  have h1 : ∑ t : Fin Dn, C (Bvec sc c t) * hLam P N p (t : ℕ) = X ^ p * Qpoly p a0 nQ c - Qpoly p a0 nQ c := by
    rw [Qpoly_period]
    simp only [Bvec, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsc i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hB] at h1
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at h1
  have h2 : (X ^ p - 1 : (ZMod p)[X]) * Qpoly p a0 nQ c = 0 := by
    rw [sub_mul, one_mul]; exact h1.symm
  have hXp : (X ^ p - 1 : (ZMod p)[X]) ≠ 0 := by simpa using X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos (1 : ZMod p)
  have h3 : Qpoly p a0 nQ c = 0 := (mul_eq_zero.mp h2).resolve_left hXp
  have h4 : Qpoly p a0 nQ c = (X - 1) ^ a0 * ∑ i : Fin nQ, C (c i) * X ^ (i : ℕ) := by
    unfold Qpoly; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hX1 : ((X - 1 : (ZMod p)[X]) ^ a0) ≠ 0 := pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : ZMod p))
  have h5 : ∑ i : Fin nQ, C (c i) * X ^ (i : ℕ) = 0 :=
    (mul_eq_zero.mp (h4 ▸ h3)).resolve_left hX1
  funext i
  have := congrArg (fun q => q.coeff (i : ℕ)) h5
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

include hsc in
theorem xi_injective (hind : LinearIndependent (ZMod p) ![u, v]) (hy0 : y ≠ 0) :
    Function.Injective (xi u v y sc) := by
  refine Thin.injective_of_zero _ fun a h0 => ?_
  have hxd : xd u v y sc a = 0 := h0
  have hAB : ∀ t, a.1 t = 0 ∧ Bvec sc a.2.1 t = 0 := by
    intro t
    have hz : a.1 t • u + Bvec sc a.2.1 t • v = 0 := by
      funext κ
      have := congrFun (congrFun hxd (Fin.castAdd Dn t)) (Fin.castAdd K κ)
      simpa [xd] using this
    have := Fintype.linearIndependent_iff.mp hind ![a.1 t, Bvec sc a.2.1 t] (by
      simpa [Fin.sum_univ_two] using hz)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  have hC : ∀ t, a.2.2 t = 0 := by
    intro t
    obtain ⟨κ, hκ⟩ : ∃ κ, y κ ≠ 0 := by
      by_contra hn; push_neg at hn; exact hy0 (funext hn)
    have := congrFun (congrFun hxd (Fin.natAdd Dn t)) (Fin.natAdd K κ)
    simp only [xd, Fin.addCases_right, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_right hκ
  have hc : a.2.1 = 0 := Bvec_zero a0 sc hsc _ (funext fun t => (hAB t).2)
  exact Prod.ext (funext fun t => (hAB t).1) (Prod.ext hc (funext hC))

end
end
end CatalanMeasure.GenD.Uniform.W.HYPlus
