module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZRows
@[expose] public section
set_option Elab.async false

/-!
# Lemma T for the combined rows (one-sided pairs allowed)

`(X-1)^h intrinsicU c` and `(X-1)^h (X²-1)^hp intrinsicT c` of `c = zRows S A` are the slot
sums `Σ zpLam_d · (profile of S_d)(X^p) + Σ zaLam_d · (profile of A_d)(X^p)`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The antisymmetric slot polynomial `2 (X-1)^h U_{d-1}`. -/
def zaLam (P : Parameters) (N p : ℕ) (d : ℕ) : (ZMod p)[X] :=
  2 * (X - 1) ^ P.h N * Chebyshev.U (ZMod p) ((d : ℤ) - 1)

theorem zaLam_natDegree_le (hp2 : p ≠ 2) (d : ℕ) : (zaLam P N p d).natDegree ≤ P.h N + d := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  unfold zaLam
  have h1 : (2 * (X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
    refine natDegree_mul_le.trans ?_
    have a : (2 : (ZMod p)[X]).natDegree ≤ 0 := by compute_degree
    have b : ((X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
      refine natDegree_pow_le.trans ?_
      have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
      nlinarith
    omega
  have h2 : (Chebyshev.U (ZMod p) ((d : ℤ) - 1)).natDegree ≤ d := by
    rcases d with _ | d
    · simp
    · have : (((d + 1 : ℕ) : ℤ) - 1) = (d : ℤ) := by push_cast; ring
      rw [this, Chebyshev.natDegree_U_natCast]; omega
  have := natDegree_mul_le (p := (2 * (X - 1) ^ P.h N : (ZMod p)[X]))
    (q := Chebyshev.U (ZMod p) ((d : ℤ) - 1))
  omega

theorem zaU_term (hp2 : p ≠ 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N *
        (Chebyshev.U (ZMod p) (κ * p + (d : ℤ) - 1) - Chebyshev.U (ZMod p) (κ * p - (d : ℤ) - 1)) =
      zaLam P N p d * (Chebyshev.T (ZMod p) κ).comp (X ^ p) := by
  rw [U_pair_diff, T_block hp2 κ, zaLam]; ring

theorem zaT_term (hp2 : p ≠ 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + (d : ℤ)) - Chebyshev.T (ZMod p) (κ * p - (d : ℤ))) =
      zaLam P N p d * ((X ^ 2 - 1 : (ZMod p)[X]) * (Chebyshev.U (ZMod p) (κ - 1))).comp (X ^ p) := by
  have e := T_pair_diff (ZMod p) (κ * p) (d : ℤ)
  have hU := U_block hp2 κ
  have hf := frob_X_sq (p := p) hp2
  rw [e, hU, zaLam, Polynomial.mul_comp, ← hf]
  ring

theorem intrinsicU_zRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (S A : Fin D → Fin K → ZMod p)
    (hc : ZCons P N p k0 S A) :
    (X - 1) ^ P.h N * intrinsicU P N p (zRows P N p K D k0 S A) =
      ∑ d : Fin D, zpLam P N p (d : ℕ) * (uyMap p K k0 (S d)).comp (X ^ p) +
        ∑ d : Fin D, zaLam P N p (d : ℕ) * (tyMap p K k0 (A d)).comp (X ^ p) := by
  have h := sum_zRows (P := P) (N := N) k0 S A hc (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (zRows P N p K D k0 S A r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from h]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [uyMap_apply, tyMap_apply, sum_comp', sum_comp', Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := zpU_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  have e2 := zaU_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  simp only [cen, Polynomial.C_mul_comp]
  linear_combination C (S d k) * e1 + C (A d k) * e2

theorem intrinsicT_zRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ) (S A : Fin D → Fin K → ZMod p)
    (hc : ZCons P N p k0 S A) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p (zRows P N p K D k0 S A) =
      ∑ d : Fin D, zpLam P N p (d : ℕ) * (tyMap p K k0 (S d)).comp (X ^ p) +
        ∑ d : Fin D, zaLam P N p (d : ℕ) * (gyMap p K k0 (A d)).comp (X ^ p) := by
  have h := sum_zRows (P := P) (N := N) k0 S A hc (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (zRows P N p K D k0 S A r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from h]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [tyMap_apply, gyMap_apply, uyMap_apply]
  simp only [Polynomial.mul_comp, sum_comp', Polynomial.C_mul_comp, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := zpT_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  have e2 := zaT_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  simp only [cen, Polynomial.mul_comp, Polynomial.C_comp] at e1 e2 ⊢
  linear_combination C (S d k) * e1 + C (A d k) * e2

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
