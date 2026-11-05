module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HmPair
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax2
@[expose] public section
set_option Elab.async false

/-!
# Relaxed H+ / H- pair data: the pair identities
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- One linear condition per missing row: `a` = H+ data, `b` = H- data. -/
def HCons (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (a b : Fin D → Fin K → ZMod p) : Prop :=
  (∀ (t : Fin D) (k : Fin K), ¬ InRange P N (hlo p K k0 k t) → b t k + a t k = 0) ∧
  (∀ (t : Fin D) (k : Fin K), ¬ InRange P N (hhi p K k0 k t) → a t k - b t k = 0)

theorem hy_repU {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (a b : Fin D → Fin K → ZMod p)
    (hc : HCons P N p k0 a b) :
    (X - 1) ^ P.h N * (intrinsicU P N p (sRows P N p K D 1 k0 a) +
        intrinsicU P N p (sRows P N p K D (-1) k0 b)) =
      ∑ t : Fin D, hLam P N p (t : ℕ) * (hTy p K k0 (a t)).comp (X ^ p) +
        ∑ t : Fin D, hmLam P N p (t : ℕ) * (hmTy p K k0 (b t)).comp (X ^ p) := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have gA := gen_sum_sRows (P := P) (N := N) (1 : ZMod p) k0 a (fun m => Chebyshev.U (ZMod p) (m - 1))
  have gB := gen_sum_sRows (P := P) (N := N) (-1 : ZMod p) k0 b (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (sRows P N p K D 1 k0 a r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from gA,
    show (∑ r : Fin (P.n N), C (sRows P N p K D (-1) k0 b r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from gB]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, hTy_apply, hmTy_apply, sum_comp', sum_comp',
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hL := comb_term h2ne (b t k) (a t k)
    (Chebyshev.U (ZMod p) (hlo p K k0 k t - 1)) (Chebyshev.U (ZMod p) (hhi p K k0 k t - 1))
    (InRange P N (hlo p K k0 k t)) (InRange P N (hhi p K k0 k t)) (hc.1 t k) (hc.2 t k)
  have e1 := hU_pair hp2 ((k0 : ℤ) + (k : ℕ)) (t : ℕ)
  have e2 := hmU_pair hp2 ((k0 : ℤ) + (k : ℕ)) (t : ℕ)
  have e1' : Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) +
      Chebyshev.U (ZMod p) (hhi p K k0 k t - 1) =
      ((Chebyshev.U (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) +
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) := by
    unfold hlo hhi cen; exact e1
  have e2' : Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) -
      Chebyshev.U (ZMod p) (hhi p K k0 k t - 1) =
      ((Chebyshev.U (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) -
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) - Chebyshev.U (ZMod p) (hh p + t)) := by
    unfold hlo hhi cen; exact e2
  simp only [map_one, map_neg, one_mul, neg_one_mul, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.add_comp, Polynomial.sub_comp] at *
  unfold hLam hmLam
  have key : (X - 1 : (ZMod p)[X]) ^ P.h N * (C (a t k) * ((if InRange P N (hlo p K k0 k t) then
        Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) else 0) +
      (if InRange P N (hhi p K k0 k t) then Chebyshev.U (ZMod p) (hhi p K k0 k t - 1) else 0)) +
      C (b t k) * ((if InRange P N (hlo p K k0 k t) then
        Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) else 0) +
      -(if InRange P N (hhi p K k0 k t) then Chebyshev.U (ZMod p) (hhi p K k0 k t - 1) else 0))) = 
      (X - 1) ^ P.h N * (C (b t k) * (Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) - Chebyshev.U (ZMod p) (hhi p K k0 k t - 1)) +
        C (a t k) * (Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) + Chebyshev.U (ZMod p) (hhi p K k0 k t - 1))) := by
    rw [← hL]; congr 1; ring
  rw [key, e1', e2']; ring

theorem hy_repT {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (a b : Fin D → Fin K → ZMod p)
    (hc : HCons P N p k0 a b) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * (intrinsicT P N p (sRows P N p K D 1 k0 a) +
        intrinsicT P N p (sRows P N p K D (-1) k0 b)) =
      ∑ t : Fin D, hLam P N p (t : ℕ) * (hGy p K k0 (a t)).comp (X ^ p) +
        ∑ t : Fin D, hmLam P N p (t : ℕ) * (hmGy p K k0 (b t)).comp (X ^ p) := by
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have gA := gen_sum_sRows (P := P) (N := N) (1 : ZMod p) k0 a (fun m => Chebyshev.T (ZMod p) m)
  have gB := gen_sum_sRows (P := P) (N := N) (-1 : ZMod p) k0 b (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (sRows P N p K D 1 k0 a r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from gA,
    show (∑ r : Fin (P.n N), C (sRows P N p K D (-1) k0 b r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from gB]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, hGy_apply, hmGy_apply, sum_comp', sum_comp',
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hL := comb_term h2ne (b t k) (a t k)
    (Chebyshev.T (ZMod p) (hlo p K k0 k t)) (Chebyshev.T (ZMod p) (hhi p K k0 k t))
    (InRange P N (hlo p K k0 k t)) (InRange P N (hhi p K k0 k t)) (hc.1 t k) (hc.2 t k)
  have e1 := hT_pair hp2 ((k0 : ℤ) + (k : ℕ)) (t : ℕ)
  have e2 := hmT_pair hp2 ((k0 : ℤ) + (k : ℕ)) (t : ℕ)
  have e1' : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
      (Chebyshev.T (ZMod p) (hlo p K k0 k t) + Chebyshev.T (ZMod p) (hhi p K k0 k t)) =
      (1 + X ^ p) * ((Chebyshev.U (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) -
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) := by
    unfold hlo hhi cen; exact e1
  have e2' : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
      (Chebyshev.T (ZMod p) (hlo p K k0 k t) - Chebyshev.T (ZMod p) (hhi p K k0 k t)) =
      (X ^ p - 1) * ((Chebyshev.U (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) +
        (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) - Chebyshev.U (ZMod p) (hh p + t)) := by
    unfold hlo hhi cen; exact e2
  simp only [map_one, map_neg, one_mul, neg_one_mul, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.add_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp] at *
  unfold hLam hmLam
  have key : (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) *
      (C (a t k) * ((if InRange P N (hlo p K k0 k t) then
        Chebyshev.T (ZMod p) (hlo p K k0 k t) else 0) +
      (if InRange P N (hhi p K k0 k t) then Chebyshev.T (ZMod p) (hhi p K k0 k t) else 0)) +
      C (b t k) * ((if InRange P N (hlo p K k0 k t) then
        Chebyshev.T (ZMod p) (hlo p K k0 k t) else 0) +
      -(if InRange P N (hhi p K k0 k t) then Chebyshev.T (ZMod p) (hhi p K k0 k t) else 0))) =
      (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) *
        (C (b t k) * (Chebyshev.T (ZMod p) (hlo p K k0 k t) - Chebyshev.T (ZMod p) (hhi p K k0 k t)) +
        C (a t k) * (Chebyshev.T (ZMod p) (hlo p K k0 k t) + Chebyshev.T (ZMod p) (hhi p K k0 k t))) := by
    rw [← hL]; congr 1; ring
  rw [key]
  linear_combination ((X - 1) ^ P.h N * C (a t k)) * e1' + ((X - 1) ^ P.h N * C (b t k)) * e2'

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
