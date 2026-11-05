module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.TPairs
@[expose] public section
set_option Elab.async false

/-!
# Half-centred H+ pairs in the G row index

The H+ pair of block `k` (centre `c_k = (k0+k) p`) and index `t < D` is
`e_{c_k + h - t} + e_{c_k + h + 1 + t}` with `h = (p-1)/2`; in the source notation this is
`e_{kp+j} + e_{(k+1)p-j}` with `j = h - t`.  Both members must be actual rows (`HGood`),
otherwise the coefficient is forced to `0`.

* `hRows`: linear map from profile data `x : Fin D → F_p^K` to rows;
* `hRows_injective_on`: injective on the virtual-pair-free subspace for `D ≤ (p-1)/2`;
* `sum_hPairRows`: `Σ_r c_r F(r-g) = Σ x (F(lo) + F(hi))`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Half the prime, as an integer. -/
def hh (p : ℕ) : ℤ := (((p - 1) / 2 : ℕ) : ℤ)

/-- Lower member of the H+ pair `(t, k)`. -/
def hlo (p K : ℕ) (k0 : ℤ) (k : Fin K) (t : ℕ) : ℤ := cen p K k0 k + hh p - t

/-- Upper member of the H+ pair `(t, k)`. -/
def hhi (p K : ℕ) (k0 : ℤ) (k : Fin K) (t : ℕ) : ℤ := cen p K k0 k + hh p + 1 + t

/-- Both members are actual rows. -/
def HGood (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (t : Fin D) (k : Fin K) : Prop :=
  InRange P N (hlo p K k0 k t) ∧ InRange P N (hhi p K k0 k t)

instance (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (t : Fin D) (k : Fin K) :
    Decidable (HGood P N p k0 t k) := by
  unfold HGood; infer_instance

/-- The H+ pair row. -/
def hPairRow (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (t : Fin D) (k : Fin K) :
    Fin (P.n N) → ZMod p := fun r =>
  (if (r : ℤ) - P.g N = hlo p K k0 k t then (1 : ZMod p) else 0) +
    (if (r : ℤ) - P.g N = hhi p K k0 k t then (1 : ZMod p) else 0)

/-- Rows of an H+ pair profile family. -/
def hRows (P : Parameters) (N p K D : ℕ) (k0 : ℤ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  ∑ t : Fin D, ∑ k : Fin K, (coordLin p K D t k).smulRight (hPairRow P N p k0 t k)

theorem hRows_apply (K D : ℕ) (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (r : Fin (P.n N)) :
    hRows P N p K D k0 x r = ∑ t : Fin D, ∑ k : Fin K, x t k * hPairRow P N p k0 t k r := by
  simp [hRows, LinearMap.sum_apply, coordLin]

theorem sum_hPairRow {K D : ℕ} (k0 : ℤ) (t : Fin D) (k : Fin K) (hg : HGood P N p k0 t k)
    (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (hPairRow P N p k0 t k r) * F ((r : ℤ) - P.g N) =
      F (hlo p K k0 k t) + F (hhi p K k0 k t) := by
  unfold hPairRow
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  rw [sum_ind _ hg.1, sum_ind _ hg.2]

theorem sum_hPairRows {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ t k, ¬ HGood P N p k0 t k → x t k = 0) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (hRows P N p K D k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ t : Fin D, ∑ k : Fin K, C (x t k) * (F (hlo p K k0 k t) + F (hhi p K k0 k t)) := by
  simp_rw [hRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hg : HGood P N p k0 t k
  · rw [← sum_hPairRow k0 t k hg F, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  · rw [hx t k hg]
    simp

/-- Positions of distinct pairs never coincide (`D ≤ (p-1)/2`). -/
theorem hpos_aux (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (t t2 : Fin D) (k k2 : Fin K) :
    (hlo p K k0 k2 t2 = hlo p K k0 k t → t2 = t ∧ k2 = k) ∧
    (hhi p K k0 k2 t2 = hhi p K k0 k t → t2 = t ∧ k2 = k) ∧
    hhi p K k0 k2 t2 ≠ hlo p K k0 k t ∧ hlo p K k0 k2 t2 ≠ hhi p K k0 k t := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hp1 : (0 : ℤ) < p := by omega
  have ht := t.isLt
  have ht2 := t2.isLt
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold hlo cen at h
    have h5 : (((k2 : ℕ) : ℤ) - (k : ℕ)) * p = ((t2 : ℕ) : ℤ) - (t : ℕ) := by
      linear_combination h
    have h6 := no_mult _ _ hp1 (by unfold hh at *; omega) (by unfold hh at *; omega) h5
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · unfold hhi cen at h
    have h5 : (((k2 : ℕ) : ℤ) - (k : ℕ)) * p = ((t : ℕ) : ℤ) - (t2 : ℕ) := by
      linear_combination h
    have h6 := no_mult _ _ hp1 (by unfold hh at *; omega) (by unfold hh at *; omega) h5
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · unfold hhi hlo cen at h
    have h5 : (((k2 : ℕ) : ℤ) - (k : ℕ)) * p = -(((t : ℕ) : ℤ) + (t2 : ℕ) + 1) := by
      linear_combination h
    have h6 := no_mult _ _ hp1 (by unfold hh at *; omega) (by unfold hh at *; omega) h5
    omega
  · unfold hhi hlo cen at h
    have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = -(((t : ℕ) : ℤ) + (t2 : ℕ) + 1) := by
      linear_combination -h
    have h6 := no_mult _ _ hp1 (by unfold hh at *; omega) (by unfold hh at *; omega) h5
    omega

theorem hlo_ne_hhi {K D : ℕ} (t : Fin D) (k : Fin K) (k0 : ℤ) : hlo p K k0 k t ≠ hhi p K k0 k t := by
  unfold hlo hhi; omega

/-- Evaluation at the lower member. -/
theorem hpair_eval_lo (hp2 : p ≠ 2) {K D : ℕ} (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (t : Fin D) (k : Fin K) (r : Fin (P.n N))
    (hr : (r : ℤ) - P.g N = hlo p K k0 k t) : hRows P N p K D k0 x r = x t k := by
  rw [hRows_apply, Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single k]
    · unfold hPairRow
      rw [if_pos hr, if_neg (by rw [hr]; exact hlo_ne_hhi t k k0)]
      simp
    · intro k2 _ hk2
      unfold hPairRow
      have a1 : ¬ ((r : ℤ) - P.g N = hlo p K k0 k2 t) := fun h =>
        hk2 ((hpos_aux hp2 hD k0 t t k k2).1 (by rw [← h, hr])).2
      have a2 : ¬ ((r : ℤ) - P.g N = hhi p K k0 k2 t) := fun h =>
        (hpos_aux hp2 hD k0 t t k k2).2.2.1 (by rw [← h, hr])
      rw [if_neg a1, if_neg a2]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro t2 _ ht2
    refine Finset.sum_eq_zero fun k2 _ => ?_
    unfold hPairRow
    have a1 : ¬ ((r : ℤ) - P.g N = hlo p K k0 k2 t2) := fun h =>
      ht2 ((hpos_aux hp2 hD k0 t t2 k k2).1 (by rw [← h, hr])).1
    have a2 : ¬ ((r : ℤ) - P.g N = hhi p K k0 k2 t2) := fun h =>
      (hpos_aux hp2 hD k0 t t2 k k2).2.2.1 (by rw [← h, hr])
    rw [if_neg a1, if_neg a2]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Injectivity on the virtual-pair-free subspace. -/
theorem hRows_injective_on {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ t k, ¬ HGood P N p k0 t k → x t k = 0)
    (h0 : hRows P N p K D k0 x = 0) : x = 0 := by
  funext t k
  by_cases hg : HGood P N p k0 t k
  · obtain ⟨⟨h1, h2⟩, _⟩ := hg
    have hr : (hlo p K k0 k t + P.g N).toNat < P.n N := by omega
    have := hpair_eval_lo (P := P) (N := N) hp2 hD k0 x t k ⟨_, hr⟩ (by simp only; omega)
    rw [h0] at this
    simpa using this.symm
  · exact hx t k hg

#print axioms hRows_injective_on
#print axioms sum_hPairRows
end
end CatalanMeasure.GenD.Uniform.W.Slots
