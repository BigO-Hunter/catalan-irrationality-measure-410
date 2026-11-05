module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HmProf
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax
@[expose] public section
set_option Elab.async false

/-!
# Signed half-centred pair rows `e_lo + ε e_hi` (ε = 1: H+, ε = -1: H-)
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The signed pair row. -/
def sPairRow (P : Parameters) (N p : ℕ) {K D : ℕ} (ε : ZMod p) (k0 : ℤ) (t : Fin D) (k : Fin K) :
    Fin (P.n N) → ZMod p := fun r =>
  (if (r : ℤ) - P.g N = hlo p K k0 k t then (1 : ZMod p) else 0) +
    ε * (if (r : ℤ) - P.g N = hhi p K k0 k t then (1 : ZMod p) else 0)

def sRows (P : Parameters) (N p K D : ℕ) (ε : ZMod p) (k0 : ℤ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  ∑ t : Fin D, ∑ k : Fin K, (coordLin p K D t k).smulRight (sPairRow P N p ε k0 t k)

theorem sRows_apply (K D : ℕ) (ε : ZMod p) (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (r : Fin (P.n N)) :
    sRows P N p K D ε k0 x r = ∑ t : Fin D, ∑ k : Fin K, x t k * sPairRow P N p ε k0 t k r := by
  simp [sRows, LinearMap.sum_apply, coordLin]

theorem gen_sum_sRows {K D : ℕ} (ε : ZMod p) (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (sRows P N p K D ε k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ t : Fin D, ∑ k : Fin K, C (x t k) *
        ((if InRange P N (hlo p K k0 k t) then F (hlo p K k0 k t) else 0) +
          C ε * (if InRange P N (hhi p K k0 k t) then F (hhi p K k0 k t) else 0)) := by
  simp_rw [sRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := sum_ind_gen (P := P) (N := N) (p := p) (hlo p K k0 k t) F
  have h2 := sum_ind_gen (P := P) (N := N) (p := p) (hhi p K k0 k t) F
  unfold sPairRow
  simp only [map_add, map_mul, add_mul, Finset.sum_add_distrib]
  rw [← h1, ← h2, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem sPairRow_lo (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (ε : ZMod p) (k0 : ℤ)
    (t t2 : Fin D) (k k2 : Fin K) (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = hlo p K k0 k t) :
    sPairRow P N p ε k0 t2 k2 r = if (t2 = t ∧ k2 = k) then 1 else 0 := by
  unfold sPairRow
  by_cases h : t2 = t ∧ k2 = k
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos hr, if_neg (by rw [hr]; exact hlo_ne_hhi t2 k2 k0)]
    simp
  · have a1 : ¬ ((r : ℤ) - P.g N = hlo p K k0 k2 t2) := fun h' =>
      h ((hpos_aux hp2 hD k0 t t2 k k2).1 (by rw [← h', hr]))
    have a2 : ¬ ((r : ℤ) - P.g N = hhi p K k0 k2 t2) := fun h' =>
      (hpos_aux hp2 hD k0 t t2 k k2).2.2.1 (by rw [← h', hr])
    rw [if_neg a1, if_neg a2, if_neg h]; simp

theorem sPairRow_hi (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (ε : ZMod p) (k0 : ℤ)
    (t t2 : Fin D) (k k2 : Fin K) (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = hhi p K k0 k t) :
    sPairRow P N p ε k0 t2 k2 r = if (t2 = t ∧ k2 = k) then ε else 0 := by
  unfold sPairRow
  by_cases h : t2 = t ∧ k2 = k
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos hr, if_neg (by rw [hr]; exact (hlo_ne_hhi t2 k2 k0).symm)]
    simp
  · have a1 : ¬ ((r : ℤ) - P.g N = hlo p K k0 k2 t2) := fun h' =>
      (hpos_aux hp2 hD k0 t t2 k k2).2.2.2 (h'.symm.trans hr)
    have a2 : ¬ ((r : ℤ) - P.g N = hhi p K k0 k2 t2) := fun h' =>
      h ((hpos_aux hp2 hD k0 t t2 k k2).2.1 (by rw [← h', hr]))
    rw [if_neg a1, if_neg a2, if_neg h]; simp

theorem sum_pt {K D : ℕ} (x : Fin D → Fin K → ZMod p) (t : Fin D) (k : Fin K) (c : ZMod p) :
    ∑ t2 : Fin D, ∑ k2 : Fin K, x t2 k2 * (if (t2 = t ∧ k2 = k) then c else 0) = c * x t k := by
  rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp [mul_comm]

theorem sRows_eval_lo (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (ε : ZMod p) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (t : Fin D) (k : Fin K) (r : Fin (P.n N))
    (hr : (r : ℤ) - P.g N = hlo p K k0 k t) : sRows P N p K D ε k0 x r = x t k := by
  rw [sRows_apply]
  simp_rw [sPairRow_lo (P := P) (N := N) hp2 hD ε k0 t _ k _ r hr]
  rw [sum_pt, one_mul]

theorem sRows_eval_hi (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (ε : ZMod p) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (t : Fin D) (k : Fin K) (r : Fin (P.n N))
    (hr : (r : ℤ) - P.g N = hhi p K k0 k t) : sRows P N p K D ε k0 x r = ε * x t k := by
  rw [sRows_apply]
  simp_rw [sPairRow_hi (P := P) (N := N) hp2 hD ε k0 t _ k _ r hr]
  rw [sum_pt]

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
