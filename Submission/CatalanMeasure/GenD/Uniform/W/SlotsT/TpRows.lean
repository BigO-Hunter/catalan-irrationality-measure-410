module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.All
@[expose] public section
set_option Elab.async false

/-!
# T+ pair rows (symmetric centred pairs) in the G row index

A *T+ pair* of block `k` and offset `d ≥ 0` is `e_{c_k + d} + e_{c_k - d}` with centre
`c_k = (k0 + k) p`; for `d = 0` it is `2 e_{c_k}`.  Both members must be actual rows
(`TpGood`), otherwise its coefficient is forced to `0`.  Compare `Thin.PairRows` (T- pairs).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Both members of the T+ pair `(d, k)` are actual rows. -/
def TpGood (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) : Prop :=
  InRange P N (cen p K k0 k + (d : ℕ)) ∧ InRange P N (cen p K k0 k - (d : ℕ))

instance (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) :
    Decidable (TpGood P N p k0 d k) := by
  unfold TpGood; infer_instance

/-- The T+ pair row `e_{c+d} + e_{c-d}`. -/
def tpPairRow (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) :
    Fin (P.n N) → ZMod p := fun r =>
  (if (r : ℤ) - P.g N = cen p K k0 k + (d : ℕ) then (1 : ZMod p) else 0) +
    (if (r : ℤ) - P.g N = cen p K k0 k - (d : ℕ) then (1 : ZMod p) else 0)

/-- Rows of a T+ pair profile family. -/
def tpRows (P : Parameters) (N p K D : ℕ) (k0 : ℤ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  ∑ d : Fin D, ∑ k : Fin K,
    (coordLin p K D d k).smulRight (tpPairRow P N p k0 d k)

theorem tpRows_apply (K D : ℕ) (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (r : Fin (P.n N)) :
    tpRows P N p K D k0 x r = ∑ d : Fin D, ∑ k : Fin K, x d k * tpPairRow P N p k0 d k r := by
  simp [tpRows, LinearMap.sum_apply, coordLin]

theorem sum_tpPairRow {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) (hg : TpGood P N p k0 d k)
    (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (tpPairRow P N p k0 d k r) * F ((r : ℤ) - P.g N) =
      F (cen p K k0 k + (d : ℕ)) + F (cen p K k0 k - (d : ℕ)) := by
  unfold tpPairRow
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  rw [sum_ind _ hg.1, sum_ind _ hg.2]

theorem sum_tpPairRows {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ d k, ¬ TpGood P N p k0 d k → x d k = 0) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (tpRows P N p K D k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ d : Fin D, ∑ k : Fin K, C (x d k) *
        (F (cen p K k0 k + (d : ℕ)) + F (cen p K k0 k - (d : ℕ))) := by
  simp_rw [tpRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hg : TpGood P N p k0 d k
  · rw [← sum_tpPairRow k0 d k hg F, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  · rw [hx d k hg]
    simp

/-- The row `c_k + d` determines the coefficient `x d k` (up to the factor `2` at `d = 0`). -/
theorem tpPair_eval {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) (r : Fin (P.n N))
    (hr : (r : ℤ) - P.g N = cen p K k0 k + (d : ℕ)) :
    tpRows P N p K D k0 x r = (if (d : ℕ) = 0 then 2 else 1) * x d k := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hpo := p_odd_half hp2
  have hdl := d.isLt
  have hp1 : (0 : ℤ) < p := by omega
  -- the only contributing pair is `(d, k)`
  have key : ∀ (d2 : Fin D) (k2 : Fin K), (d2 ≠ d ∨ k2 ≠ k) →
      tpPairRow P N p k0 d2 k2 r = 0 := by
    intro d2 k2 hne
    unfold tpPairRow
    have hd2l := d2.isLt
    have hn1 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 + (d2 : ℕ)) := by
      intro h
      unfold cen at h hr
      have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = ((d2 : ℕ) : ℤ) - (d : ℕ) := by nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      rcases hne with h7 | h7
      · exact h7 (Fin.ext (by omega))
      · exact h7 (Fin.ext (by omega))
    have hn2 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 - (d2 : ℕ)) := by
      intro h
      unfold cen at h hr
      have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = -((d2 : ℕ) : ℤ) - (d : ℕ) := by nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      rcases hne with h7 | h7
      · exact h7 (Fin.ext (by omega))
      · exact h7 (Fin.ext (by omega))
    rw [if_neg hn1, if_neg hn2]; simp
  rw [tpRows_apply, Finset.sum_eq_single d]
  · rw [Finset.sum_eq_single k]
    · unfold tpPairRow
      rw [if_pos hr]
      by_cases hd0 : (d : ℕ) = 0
      · rw [if_pos hd0, if_pos (by rw [hr]; simp [hd0])]; ring
      · rw [if_neg hd0, if_neg (by rw [hr]; omega)]; ring
    · intro k2 _ hk2
      rw [key d k2 (Or.inr hk2)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro d2 _ hd2
    refine Finset.sum_eq_zero fun k2 _ => ?_
    rw [key d2 k2 (Or.inl hd2)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Injectivity on the virtual-pair-free subspace. -/
theorem tpRows_injective_on {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ d k, ¬ TpGood P N p k0 d k → x d k = 0)
    (h0 : tpRows P N p K D k0 x = 0) : x = 0 := by
  funext d k
  by_cases hg : TpGood P N p k0 d k
  · obtain ⟨⟨h1, h2⟩, _⟩ := hg
    have hr : (cen p K k0 k + (d : ℕ) + P.g N).toNat < P.n N := by omega
    have := tpPair_eval (P := P) (N := N) hp2 hD k0 x d k ⟨_, hr⟩ (by simp only; omega)
    rw [h0] at this
    have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
    have hne : (if (d : ℕ) = 0 then (2 : ZMod p) else 1) ≠ 0 := by
      split_ifs
      · exact h2ne
      · exact one_ne_zero
    have := this.symm
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left hne
  · exact hx d k hg

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
