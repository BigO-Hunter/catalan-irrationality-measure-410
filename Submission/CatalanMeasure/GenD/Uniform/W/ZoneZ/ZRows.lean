module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Add
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.TpPlain
@[expose] public section
set_option Elab.async false

/-!
# Combined T+/T- pair rows with one-sided (virtual) pairs

A pair `(d,k)` carries data `(S,A)`: coefficient `S + A` on row `c_k + d` and `S - A` on row
`c_k - d` (so `2S` at `d = 0`).  A member that is not an actual row forces a relation
(`S + A = 0` resp. `S - A = 0`): one condition per missing member, not two.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The antisymmetric pair row `e_{c+d} - e_{c-d}` with offset `d` (no shift). -/
def aPairRow (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) :
    Fin (P.n N) → ZMod p := fun r =>
  (if (r : ℤ) - P.g N = cen p K k0 k + (d : ℕ) then (1 : ZMod p) else 0) -
    (if (r : ℤ) - P.g N = cen p K k0 k - (d : ℕ) then (1 : ZMod p) else 0)

def aRows (P : Parameters) (N p K D : ℕ) (k0 : ℤ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  ∑ d : Fin D, ∑ k : Fin K, (coordLin p K D d k).smulRight (aPairRow P N p k0 d k)

theorem aRows_apply (K D : ℕ) (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (r : Fin (P.n N)) :
    aRows P N p K D k0 x r = ∑ d : Fin D, ∑ k : Fin K, x d k * aPairRow P N p k0 d k r := by
  simp [aRows, LinearMap.sum_apply, coordLin]

/-- Sum against an indicator row. -/
theorem sum_ind' (m0 : ℤ) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (if (r : ℤ) - P.g N = m0 then (1 : ZMod p) else 0) *
      F ((r : ℤ) - P.g N) = if InRange P N m0 then F m0 else 0 := by
  by_cases hm : InRange P N m0
  · rw [if_pos hm]; exact sum_ind m0 hm F
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have : ¬ ((r : ℤ) - P.g N = m0) := by
      intro h
      apply hm
      unfold InRange
      have := r.isLt
      omega
    simp [this]

/-- Virtual-pair consistency of the data `(S, A)`. -/
def ZCons (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (S A : Fin D → Fin K → ZMod p) : Prop :=
  ∀ (d : Fin D) (k : Fin K),
    (¬ InRange P N (cen p K k0 k + (d : ℕ)) → S d k + A d k = 0) ∧
    (¬ InRange P N (cen p K k0 k - (d : ℕ)) → S d k - A d k = 0)

/-- Rows of the combined data. -/
def zRows (P : Parameters) (N p K D : ℕ) (k0 : ℤ) (S A : Fin D → Fin K → ZMod p) :
    Fin (P.n N) → ZMod p := tpRows P N p K D k0 S + aRows P N p K D k0 A

theorem sum_pair_comb {K D : ℕ} (k0 : ℤ) (S A : ZMod p) (d : Fin D) (k : Fin K)
    (h1 : ¬ InRange P N (cen p K k0 k + (d : ℕ)) → S + A = 0)
    (h2 : ¬ InRange P N (cen p K k0 k - (d : ℕ)) → S - A = 0) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (S * tpPairRow P N p k0 d k r + A * aPairRow P N p k0 d k r) *
        F ((r : ℤ) - P.g N) =
      C S * (F (cen p K k0 k + (d : ℕ)) + F (cen p K k0 k - (d : ℕ))) +
        C A * (F (cen p K k0 k + (d : ℕ)) - F (cen p K k0 k - (d : ℕ))) := by
  have e : ∀ r : Fin (P.n N), C (S * tpPairRow P N p k0 d k r + A * aPairRow P N p k0 d k r) *
      F ((r : ℤ) - P.g N) =
      C (S + A) * (C (if (r : ℤ) - P.g N = cen p K k0 k + (d : ℕ) then (1 : ZMod p) else 0) *
        F ((r : ℤ) - P.g N)) +
      C (S - A) * (C (if (r : ℤ) - P.g N = cen p K k0 k - (d : ℕ) then (1 : ZMod p) else 0) *
        F ((r : ℤ) - P.g N)) := by
    intro r
    unfold tpPairRow aPairRow
    simp only [map_add, map_sub, map_mul]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_ind', sum_ind']
  have key : C S * (F (cen p K k0 k + (d : ℕ)) + F (cen p K k0 k - (d : ℕ))) +
      C A * (F (cen p K k0 k + (d : ℕ)) - F (cen p K k0 k - (d : ℕ))) =
      C (S + A) * F (cen p K k0 k + (d : ℕ)) + C (S - A) * F (cen p K k0 k - (d : ℕ)) := by
    simp only [map_add, map_sub]; ring
  rw [key]
  by_cases hp : InRange P N (cen p K k0 k + (d : ℕ)) <;>
    by_cases hm : InRange P N (cen p K k0 k - (d : ℕ))
  · simp [hp, hm]
  · simp [hp, hm, h2 hm]
  · simp [hp, hm, h1 hp]
  · simp [hp, hm, h1 hp, h2 hm]

theorem sum_zRows {K D : ℕ} (k0 : ℤ) (S A : Fin D → Fin K → ZMod p) (hc : ZCons P N p k0 S A)
    (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (zRows P N p K D k0 S A r) * F ((r : ℤ) - P.g N) =
      ∑ d : Fin D, ∑ k : Fin K, (C (S d k) * (F (cen p K k0 k + (d : ℕ)) + F (cen p K k0 k - (d : ℕ))) +
        C (A d k) * (F (cen p K k0 k + (d : ℕ)) - F (cen p K k0 k - (d : ℕ)))) := by
  have hrow : ∀ r, zRows P N p K D k0 S A r =
      ∑ d : Fin D, ∑ k : Fin K, (S d k * tpPairRow P N p k0 d k r + A d k * aPairRow P N p k0 d k r) := by
    intro r
    simp only [zRows, Pi.add_apply, tpRows_apply, aRows_apply, Finset.sum_add_distrib]
  simp_rw [hrow, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_pair_comb k0 (S d k) (A d k) d k (hc d k).1 (hc d k).2 F

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
