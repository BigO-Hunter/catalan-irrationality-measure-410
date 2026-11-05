module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.TpSystem
@[expose] public section
set_option Elab.async false

/-!
# T+ pairs as a slot system, plain (non-period) form

For `h + (p-1)/2 < p` (Theorem Z regime) the T+ slot polynomial is
`lam d = 2 (X-1)^h (X²-1)^((p-1)/2) T_d`, of degree `≤ h + p - 1 + d < 2p`
(zone2 sec. 1: `π = 2 (x-1)^h w Σ S_d T_d`), with profile maps
`Ty y = Σ y_k U_{k0+k-1}`, `Gy y = Σ y_k T_{k0+k}` (polynomials in `Y = X^p`):

    (X-1)^h intrinsicU c = Σ lam_d · Ty(x_d)(X^p),
    (X-1)^h (X²-1)^hp intrinsicT c = Σ lam_d · Gy(x_d)(X^p).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The plain T+ slot polynomial. -/
def zpLam (P : Parameters) (N p : ℕ) (d : ℕ) : (ZMod p)[X] :=
  2 * (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (d : ℤ)

theorem zpLam_natDegree_le (hp2 : p ≠ 2) (d : ℕ) :
    (zpLam P N p d).natDegree ≤ P.h N + (p - 1) + d := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have h1 : (2 * (X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
    refine natDegree_mul_le.trans ?_
    have a : (2 : (ZMod p)[X]).natDegree ≤ 0 := by compute_degree
    have b : ((X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
      refine natDegree_pow_le.trans ?_
      have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
      nlinarith
    omega
  have h2 : ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).natDegree ≤ p - 1 := by
    refine natDegree_pow_le.trans ?_
    have : (X ^ 2 - 1 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
    have := Nat.mul_le_mul_left ((p - 1) / 2) this
    omega
  have h3 : (Chebyshev.T (ZMod p) (d : ℤ)).natDegree ≤ d := by
    rw [Chebyshev.natDegree_T]; simp
  unfold zpLam
  have := natDegree_mul_le (p := (2 * (X - 1) ^ P.h N : (ZMod p)[X]))
    (q := (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2))
  have := natDegree_mul_le (p := (2 * (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) : (ZMod p)[X]))
    (q := Chebyshev.T (ZMod p) (d : ℤ))
  omega

theorem zpU_term (hp2 : p ≠ 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N *
        (Chebyshev.U (ZMod p) (κ * p + (d : ℤ) - 1) + Chebyshev.U (ZMod p) (κ * p - (d : ℤ) - 1)) =
      zpLam P N p d * (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p) := by
  rw [U_pair_sum, U_block hp2 κ, zpLam]; ring

theorem zpT_term (hp2 : p ≠ 2) (κ : ℤ) (d : ℕ) :
    (X - 1 : (ZMod p)[X]) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + (d : ℤ)) + Chebyshev.T (ZMod p) (κ * p - (d : ℤ))) =
      zpLam P N p d * (Chebyshev.T (ZMod p) κ).comp (X ^ p) := by
  rw [T_pair_sum, T_block hp2 κ, zpLam]; ring

theorem intrinsicU_zpRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ d k, ¬ TpGood P N p k0 d k → x d k = 0) :
    (X - 1) ^ P.h N * intrinsicU P N p (tpRows P N p K D k0 x) =
      ∑ d : Fin D, zpLam P N p (d : ℕ) * (uyMap p K k0 (x d)).comp (X ^ p) := by
  have h := sum_tpPairRows (P := P) (N := N) k0 x hx
    (fun m => Chebyshev.U (ZMod p) (m - 1))
  unfold intrinsicU
  rw [show (∑ r : Fin (P.n N), C (tpRows P N p K D k0 x r) *
      Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [uyMap_apply, sum_comp', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := zpU_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  simp only [cen, Polynomial.C_mul_comp]
  linear_combination C (x d k) * e

theorem intrinsicT_zpRows {K D : ℕ} (hp2 : p ≠ 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ d k, ¬ TpGood P N p k0 d k → x d k = 0) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p (tpRows P N p K D k0 x) =
      ∑ d : Fin D, zpLam P N p (d : ℕ) * (tyMap p K k0 (x d)).comp (X ^ p) := by
  have h := sum_tpPairRows (P := P) (N := N) k0 x hx
    (fun m => Chebyshev.T (ZMod p) m)
  unfold intrinsicT
  rw [show (∑ r : Fin (P.n N), C (tpRows P N p K D k0 x r) *
      Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [tyMap_apply, sum_comp', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := zpT_term (P := P) (N := N) hp2 ((k0 : ℤ) + (k : ℕ)) (d : ℕ)
  simp only [cen, Polynomial.C_mul_comp]
  linear_combination C (x d k) * e

/-- The plain T+ pair slot system. -/
def zpSystem (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (K D : ℕ) (k0 : ℤ) (hD : D ≤ (p - 1) / 2 + 1) : SlotSystem P N p where
  K := K
  D := D
  emax := P.h N + (p - 1) + D
  prof := ⟨uyMap p K k0, tyMap p K k0⟩
  lam := fun d => zpLam P N p d
  rows := tpRows P N p K D k0
  dom := badDom p K D (tpBad P N p K D k0)
  deg := fun d => by
    have h1 := zpLam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
    have h2 := d.isLt
    omega
  repU := fun x hx => intrinsicU_zpRows hp2 k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tpBad, hg]))
  repT := fun x hx => intrinsicT_zpRows hp2 k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tpBad, hg]))
  inj := fun x hx h0 => tpRows_injective_on hp2 hD k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tpBad, hg])) h0

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
