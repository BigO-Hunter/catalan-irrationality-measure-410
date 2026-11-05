module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax
@[expose] public section
set_option Elab.async false

/-!
# Pair identities for the relaxed mixed T- and T+ data
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem comb_term (h2ne : (2 : ZMod p) ≠ 0) (a b : ZMod p) (x y : (ZMod p)[X]) (I1 I2 : Prop)
    [Decidable I1] [Decidable I2]
    (h1 : ¬ I1 → a + b = 0) (h2 : ¬ I2 → b - a = 0) :
    C a * ((if I1 then x else 0) - (if I2 then y else 0)) +
      C b * ((if I1 then x else 0) + (if I2 then y else 0)) =
    C a * (x - y) + C b * (x + y) := by
  by_cases e1 : I1 <;> by_cases e2 : I2
  · simp [e1, e2]
  · have hb : b = a := by linear_combination h2 e2
    simp only [e1, e2, if_true, if_false]
    rw [hb]; ring
  · have hb : b = -a := by linear_combination h1 e1
    simp only [e1, e2, if_true, if_false]
    rw [hb]; simp only [map_neg]; ring
  · have h3 : (2 : ZMod p) * a = 0 := by linear_combination h1 e1 - h2 e2
    have ha : a = 0 := (mul_eq_zero.mp h3).resolve_left h2ne
    have hb : b = 0 := by linear_combination h1 e1 - ha
    simp only [e1, e2, if_false]
    rw [ha, hb]; simp

theorem tyMap_comp {K : ℕ} (k0 : ℤ) (y : Fin K → ZMod p) :
    (tyMap p K k0 y).comp (X ^ p) =
      ∑ k : Fin K, C (y k) * (Chebyshev.T (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) := by
  rw [tyMap_apply, sum_comp']
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comp, C_comp]

theorem gyMap_comp {K : ℕ} (k0 : ℤ) (y : Fin K → ZMod p) :
    (gyMap p K k0 y).comp (X ^ p) =
      ∑ k : Fin K, C (y k) * ((X ^ 2 - 1 : (ZMod p)[X]).comp (X ^ p) *
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) := by
  rw [gyMap_apply, uyMap_apply, Polynomial.mul_comp, sum_comp', Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comp, C_comp]; ring

theorem tpTy_comp {K : ℕ} (k0 : ℤ) (y : Fin K → ZMod p) :
    (tpTy p K k0 y).comp (X ^ p) =
      ∑ k : Fin K, C (y k) * ((X ^ p - 1) *
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) := by
  rw [tpTy_apply, mul_comp, sub_comp, X_comp, one_comp, sum_comp', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comp, C_comp]; ring

theorem tpGy_comp {K : ℕ} (k0 : ℤ) (y : Fin K → ZMod p) :
    (tpGy p K k0 y).comp (X ^ p) =
      ∑ k : Fin K, C (y k) * ((X ^ p - 1) *
        (Chebyshev.T (ZMod p) (k0 + (k : ℕ))).comp (X ^ p)) := by
  rw [tpGy_apply, mul_comp, sub_comp, X_comp, one_comp, sum_comp', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comp, C_comp]; ring

/-- Pair identity (`U` part) for relaxed data. -/
theorem mix_repU {K D1 : ℕ} (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (hr : RelaxOK P N p k0 a b) :
    (X - 1) ^ P.h N * (intrinsicU P N p (tRows P N p K D1 k0 a) +
        intrinsicU P N p (tpRows P N p K (D1 + 1) k0 b)) =
      ∑ d : Fin D1, Thin.lam P N p (d : ℕ) * (tyMap p K k0 (a d)).comp (X ^ p) +
        ∑ d : Fin (D1 + 1), tpLam P N p (d : ℕ) * (tpTy p K k0 (b d)).comp (X ^ p) := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  obtain ⟨hr1, hr2, hr3⟩ := hr
  have g1 := gen_sum_tRows (P := P) (N := N) k0 a (fun m => Chebyshev.U (ZMod p) (m - 1))
  have g2 := gen_sum_tpRows (P := P) (N := N) k0 b (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (tRows P N p K D1 k0 a r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from g1,
    show (∑ r : Fin (P.n N), C (tpRows P N p K (D1 + 1) k0 b r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from g2]
  rw [Fin.sum_univ_succ (f := fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ) *
      (tpTy p K k0 (b d)).comp (X ^ p))]
  rw [Fin.sum_univ_succ (f := fun d : Fin (D1 + 1) => ∑ k : Fin K, C (b d k) *
      ((if InRange P N (cen p K k0 k + ((d : ℕ) : ℤ)) then
          Chebyshev.U (ZMod p) (cen p K k0 k + ((d : ℕ) : ℤ) - 1) else 0) +
        (if InRange P N (cen p K k0 k - ((d : ℕ) : ℤ)) then
          Chebyshev.U (ZMod p) (cen p K k0 k - ((d : ℕ) : ℤ) - 1) else 0)))]
  simp only [tyMap_comp, tpTy_comp, Fin.val_succ, Fin.val_zero, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, add_zero, sub_zero, Finset.mul_sum]
  -- split both sides as `Σ_d Σ_k (pair term) + Σ_k (centre term)`
  have hL : ∀ (d : Fin D1) (k : Fin K),
      (X - 1 : (ZMod p)[X]) ^ P.h N * (C (a d k) *
        ((if InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.U (ZMod p) (cen p K k0 k + (((d : ℕ) : ℤ) + 1) - 1) else 0) -
          (if InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.U (ZMod p) (cen p K k0 k - (((d : ℕ) : ℤ) + 1) - 1) else 0)) +
        C (b d.succ k) *
        ((if InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.U (ZMod p) (cen p K k0 k + (((d : ℕ) : ℤ) + 1) - 1) else 0) +
          (if InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.U (ZMod p) (cen p K k0 k - (((d : ℕ) : ℤ) + 1) - 1) else 0))) =
      Thin.lam P N p (d : ℕ) * (C (a d k) * (Chebyshev.T (ZMod p) (k0 + (k : ℕ))).comp (X ^ p)) +
        tpLam P N p ((d : ℕ) + 1) * (C (b d.succ k) * ((X ^ p - 1) *
          (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p))) := by
    intro d k
    rw [comb_term h2ne (a d k) (b d.succ k) _ _ _ _ (hr1 d k) (hr2 d k)]
    have e1 := tmU_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
    have e2 := tpU_term (P := P) (N := N) hp2 hph ((k0 : ℤ) + (k : ℕ)) ((d : ℕ) + 1)
    simp only [cen, Nat.cast_add, Nat.cast_one] at e2 ⊢
    linear_combination C (a d k) * e1 + C (b d.succ k) * e2
  have hC : ∀ k : Fin K, (X - 1 : (ZMod p)[X]) ^ P.h N * (C (b 0 k) *
      ((if InRange P N (cen p K k0 k) then Chebyshev.U (ZMod p) (cen p K k0 k - 1) else 0) +
        (if InRange P N (cen p K k0 k) then Chebyshev.U (ZMod p) (cen p K k0 k - 1) else 0))) =
      tpLam P N p 0 * (C (b 0 k) * ((X ^ p - 1) *
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p))) := by
    intro k
    by_cases hk : InRange P N (cen p K k0 k)
    · have e := tpU_term (P := P) (N := N) hp2 hph ((k0 : ℤ) + (k : ℕ)) 0
      simp only [Nat.cast_zero, add_zero, sub_zero] at e
      simp only [hk, if_true]
      simp only [cen] at e ⊢
      linear_combination C (b 0 k) * e
    · rw [hr3 k hk]; simp
  rw [mul_add, mul_add]
  simp only [Finset.mul_sum]
  rw [add_left_comm]
  conv_rhs => rw [add_left_comm]
  simp only [← Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => hC k
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_add, hL d k]

/-- Pair identity (`T` part) for relaxed data. -/
theorem mix_repT {K D1 : ℕ} (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (k0 : ℤ)
    (a : Fin D1 → Fin K → ZMod p) (b : Fin (D1 + 1) → Fin K → ZMod p)
    (hr : RelaxOK P N p k0 a b) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * (intrinsicT P N p (tRows P N p K D1 k0 a) +
        intrinsicT P N p (tpRows P N p K (D1 + 1) k0 b)) =
      ∑ d : Fin D1, Thin.lam P N p (d : ℕ) * (gyMap p K k0 (a d)).comp (X ^ p) +
        ∑ d : Fin (D1 + 1), tpLam P N p (d : ℕ) * (tpGy p K k0 (b d)).comp (X ^ p) := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  obtain ⟨hr1, hr2, hr3⟩ := hr
  have g1 := gen_sum_tRows (P := P) (N := N) k0 a (fun m => Chebyshev.T (ZMod p) m)
  have g2 := gen_sum_tpRows (P := P) (N := N) k0 b (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (tRows P N p K D1 k0 a r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from g1,
    show (∑ r : Fin (P.n N), C (tpRows P N p K (D1 + 1) k0 b r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from g2]
  rw [Fin.sum_univ_succ (f := fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ) *
      (tpGy p K k0 (b d)).comp (X ^ p))]
  rw [Fin.sum_univ_succ (f := fun d : Fin (D1 + 1) => ∑ k : Fin K, C (b d k) *
      ((if InRange P N (cen p K k0 k + ((d : ℕ) : ℤ)) then
          Chebyshev.T (ZMod p) (cen p K k0 k + ((d : ℕ) : ℤ)) else 0) +
        (if InRange P N (cen p K k0 k - ((d : ℕ) : ℤ)) then
          Chebyshev.T (ZMod p) (cen p K k0 k - ((d : ℕ) : ℤ)) else 0)))]
  simp only [gyMap_comp, tpGy_comp, Fin.val_succ, Fin.val_zero, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, add_zero, sub_zero, Finset.mul_sum]
  -- split both sides as `Σ_d Σ_k (pair term) + Σ_k (centre term)`
  have hL : ∀ (d : Fin D1) (k : Fin K),
      (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * (C (a d k) *
        ((if InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.T (ZMod p) (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) else 0) -
          (if InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.T (ZMod p) (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) else 0)) +
        C (b d.succ k) *
        ((if InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.T (ZMod p) (cen p K k0 k + (((d : ℕ) : ℤ) + 1)) else 0) +
          (if InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) then
            Chebyshev.T (ZMod p) (cen p K k0 k - (((d : ℕ) : ℤ) + 1)) else 0))) =
      Thin.lam P N p (d : ℕ) * (C (a d k) * ((X ^ 2 - 1 : (ZMod p)[X]).comp (X ^ p) *
          (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p))) +
        tpLam P N p ((d : ℕ) + 1) * (C (b d.succ k) * ((X ^ p - 1) *
          (Chebyshev.T (ZMod p) (k0 + (k : ℕ))).comp (X ^ p))) := by
    intro d k
    rw [comb_term h2ne (a d k) (b d.succ k) _ _ _ _ (hr1 d k) (hr2 d k)]
    have e1 := tmT_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
    have e2 := tpT_term (P := P) (N := N) hp2 hph ((k0 : ℤ) + (k : ℕ)) ((d : ℕ) + 1)
    simp only [cen, Nat.cast_add, Nat.cast_one] at e2 ⊢
    linear_combination C (a d k) * e1 + C (b d.succ k) * e2
  have hC : ∀ k : Fin K, (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * (C (b 0 k) *
      ((if InRange P N (cen p K k0 k) then Chebyshev.T (ZMod p) (cen p K k0 k) else 0) +
        (if InRange P N (cen p K k0 k) then Chebyshev.T (ZMod p) (cen p K k0 k) else 0))) =
      tpLam P N p 0 * (C (b 0 k) * ((X ^ p - 1) *
        (Chebyshev.T (ZMod p) (k0 + (k : ℕ))).comp (X ^ p))) := by
    intro k
    by_cases hk : InRange P N (cen p K k0 k)
    · have e := tpT_term (P := P) (N := N) hp2 hph ((k0 : ℤ) + (k : ℕ)) 0
      simp only [Nat.cast_zero, add_zero, sub_zero] at e
      simp only [hk, if_true]
      simp only [cen] at e ⊢
      linear_combination C (b 0 k) * e
    · rw [hr3 k hk]; simp
  rw [mul_add, mul_add]
  simp only [Finset.mul_sum]
  rw [add_left_comm]
  conv_rhs => rw [add_left_comm]
  simp only [← Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => hC k
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_add, hL d k]

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
