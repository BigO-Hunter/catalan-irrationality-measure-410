module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MT
@[expose] public section
set_option Elab.async false

/-!
# Relaxed domain for the mixed T- and T+ system: one condition per missing row

A T- pair `a (e_{c+e} - e_{c-e})` and a T+ pair `b (e_{c+e} + e_{c-e})` about the same centre `c`
have the combined coefficients `a + b` at `c + e` and `b - a` at `c - e`.  If the row `c + e` is not
an actual row the only requirement is `a + b = 0` (one linear condition), not `a = b = 0`.  This
module proves the pair identities for data satisfying exactly these conditions (`RelaxOK`), the
corresponding injectivity, and the mixed slot system `mtSystem'` with the relaxed domain.
The number of conditions is the number of missing rows (`mixMiss`), as in `proof4/vfast.py`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem sum_ind_gen (m0 : ℤ) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (if (r : ℤ) - P.g N = m0 then (1 : ZMod p) else 0) *
      F ((r : ℤ) - P.g N) = if InRange P N m0 then F m0 else 0 := by
  by_cases hm : InRange P N m0
  · rw [if_pos hm]; exact sum_ind m0 hm F
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have : (r : ℤ) - P.g N ≠ m0 := by
      intro h
      apply hm
      rw [← h]
      refine ⟨by omega, by have := r.isLt; omega⟩
    rw [if_neg this]; simp

theorem gen_sum_tRows {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (tRows P N p K D k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ d : Fin D, ∑ k : Fin K, C (x d k) *
        ((if InRange P N (cen p K k0 k + ((d : ℕ) + 1)) then F (cen p K k0 k + ((d : ℕ) + 1)) else 0) -
          (if InRange P N (cen p K k0 k - ((d : ℕ) + 1)) then F (cen p K k0 k - ((d : ℕ) + 1)) else 0)) := by
  simp_rw [tRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := sum_ind_gen (P := P) (N := N) (p := p) (cen p K k0 k + ((d : ℕ) + 1)) F
  have h2 := sum_ind_gen (P := P) (N := N) (p := p) (cen p K k0 k - ((d : ℕ) + 1)) F
  unfold pairRow
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [← h1, ← h2, mul_sub, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem gen_sum_tpRows {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (tpRows P N p K D k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ d : Fin D, ∑ k : Fin K, C (x d k) *
        ((if InRange P N (cen p K k0 k + (d : ℕ)) then F (cen p K k0 k + (d : ℕ)) else 0) +
          (if InRange P N (cen p K k0 k - (d : ℕ)) then F (cen p K k0 k - (d : ℕ)) else 0)) := by
  simp_rw [tpRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := sum_ind_gen (P := P) (N := N) (p := p) (cen p K k0 k + (d : ℕ)) F
  have h2 := sum_ind_gen (P := P) (N := N) (p := p) (cen p K k0 k - (d : ℕ)) F
  unfold tpPairRow
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  rw [← h1, ← h2, mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The relaxed conditions: one linear condition per missing row. -/
def RelaxOK (P : Parameters) (N p : ℕ) {K D1 : ℕ} (k0 : ℤ) (a : Fin D1 → Fin K → ZMod p)
    (b : Fin (D1 + 1) → Fin K → ZMod p) : Prop :=
  (∀ (d : Fin D1) (k : Fin K), ¬ InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) →
      a d k + b d.succ k = 0) ∧
  (∀ (d : Fin D1) (k : Fin K), ¬ InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) →
      b d.succ k - a d k = 0) ∧
  (∀ (k : Fin K), ¬ InRange P N (cen p K k0 k) → b 0 k = 0)

/-- T- term identity (`U` part). -/
theorem tmU_term (hp2 : p ≠ 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N *
        (Chebyshev.U (ZMod p) (κ * p + (((d : ℕ) : ℤ) + 1) - 1) -
          Chebyshev.U (ZMod p) (κ * p - (((d : ℕ) : ℤ) + 1) - 1)) =
      Thin.lam P N p d * (Chebyshev.T (ZMod p) κ).comp (X ^ p) := by
  rw [U_pair_diff, T_block hp2 κ, Thin.lam]
  simp only [add_sub_cancel_right]
  ring

/-- T- term identity (`T` part). -/
theorem tmT_term (hp2 : p ≠ 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + (((d : ℕ) : ℤ) + 1)) -
          Chebyshev.T (ZMod p) (κ * p - (((d : ℕ) : ℤ) + 1))) =
      Thin.lam P N p d * ((X ^ 2 - 1 : (ZMod p)[X]).comp (X ^ p) *
        (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) := by
  rw [T_pair_diff, ← frob_X_sq (p := p) hp2]
  have hU := U_block hp2 κ
  have hU' : Chebyshev.U (ZMod p) (κ * p - 1) = (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p) *
      (X ^ 2 - 1) ^ ((p - 1) / 2) := hU
  have hh : Chebyshev.U (ZMod p) (((d : ℕ) : ℤ) + 1 - 1) = Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) := by
    simp
  rw [hh, hU', Thin.lam]
  ring

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
