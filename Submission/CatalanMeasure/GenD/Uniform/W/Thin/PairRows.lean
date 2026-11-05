module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponse
public import Submission.CatalanMeasure.GenD.Interface
@[expose] public section
set_option Elab.async false

/-!
# Centred pair rows (T-type slots) in the G row index

The G row `r : Fin n` is the Laurent exponent `m = r - g`.  A *T-pair* of block `k` and offset
`d + 1` is `e_{c_k + (d+1)} - e_{c_k - (d+1)}` with centre `c_k = (k0 + k) p`; both members must
be actual rows (`Good`), otherwise its coefficient is forced to `0` (a virtual-row condition).

* `tRows`: the linear map from profile data `x : Fin D → Fin K → F_p` to rows;
* `tRows_injective_on`: injectivity on the virtual-row-free subspace, for offsets `≤ (p-1)/2`;
* `sum_pairRows`: any `Σ_r c_r F(r - g)` of a pair vector is `Σ x (F(c+d') - F(c-d'))`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The centre (Laurent exponent) of block `k`. -/
def cen (p K : ℕ) (k0 : ℤ) (k : Fin K) : ℤ := (k0 + (k : ℕ)) * p

/-- Laurent exponent `m` is an actual row. -/
def InRange (P : Parameters) (N : ℕ) (m : ℤ) : Prop :=
  -(P.g N : ℤ) ≤ m ∧ m < (P.n N : ℤ) - P.g N

instance (P : Parameters) (N : ℕ) (m : ℤ) : Decidable (InRange P N m) := by
  unfold InRange; infer_instance

/-- Both members of the pair `(d, k)` are actual rows. -/
def Good (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) : Prop :=
  InRange P N (cen p K k0 k + ((d : ℕ) + 1)) ∧ InRange P N (cen p K k0 k - ((d : ℕ) + 1))

instance (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) :
    Decidable (Good P N p k0 d k) := by
  unfold Good; infer_instance

/-- The T-pair row `e_{c+d'} - e_{c-d'}`. -/
def pairRow (P : Parameters) (N p : ℕ) {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) :
    Fin (P.n N) → ZMod p := fun r =>
  (if (r : ℤ) - P.g N = cen p K k0 k + ((d : ℕ) + 1) then (1 : ZMod p) else 0) -
    (if (r : ℤ) - P.g N = cen p K k0 k - ((d : ℕ) + 1) then (1 : ZMod p) else 0)

/-- Coordinate `x d k` as a linear functional. -/
def coordLin (p K D : ℕ) (d : Fin D) (k : Fin K) : (Fin D → Fin K → ZMod p) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
    (LinearMap.proj d : (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))

/-- Rows of a T-pair profile family. -/
def tRows (P : Parameters) (N p K D : ℕ) (k0 : ℤ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  ∑ d : Fin D, ∑ k : Fin K,
    (coordLin p K D d k).smulRight (pairRow P N p k0 d k)

theorem tRows_apply (K D : ℕ) (k0 : ℤ) (x : Fin D → Fin K → ZMod p) (r : Fin (P.n N)) :
    tRows P N p K D k0 x r = ∑ d : Fin D, ∑ k : Fin K, x d k * pairRow P N p k0 d k r := by
  simp [tRows, LinearMap.sum_apply, coordLin]

theorem sum_ind (m0 : ℤ) (hm : InRange P N m0) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (if (r : ℤ) - P.g N = m0 then (1 : ZMod p) else 0) *
      F ((r : ℤ) - P.g N) = F m0 := by
  obtain ⟨h1, h2⟩ := hm
  have hr : (m0 + P.g N).toNat < P.n N := by omega
  rw [Finset.sum_eq_single ⟨(m0 + P.g N).toNat, hr⟩]
  · have : ((⟨(m0 + P.g N).toNat, hr⟩ : Fin (P.n N)) : ℤ) - P.g N = m0 := by
      simp only; omega
    rw [this]; simp
  · intro r _ hne
    have : (r : ℤ) - P.g N ≠ m0 := by
      intro h; apply hne; apply Fin.ext; simp only; omega
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_pairRow {K D : ℕ} (k0 : ℤ) (d : Fin D) (k : Fin K) (hg : Good P N p k0 d k)
    (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (pairRow P N p k0 d k r) * F ((r : ℤ) - P.g N) =
      F (cen p K k0 k + ((d : ℕ) + 1)) - F (cen p K k0 k - ((d : ℕ) + 1)) := by
  unfold pairRow
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [sum_ind _ hg.1, sum_ind _ hg.2]

/-- Pair-row sums, for coefficients vanishing on virtual pairs. -/
theorem sum_pairRows {K D : ℕ} (k0 : ℤ) (x : Fin D → Fin K → ZMod p)
    (hx : ∀ d k, ¬ Good P N p k0 d k → x d k = 0) (F : ℤ → (ZMod p)[X]) :
    ∑ r : Fin (P.n N), C (tRows P N p K D k0 x r) * F ((r : ℤ) - P.g N) =
      ∑ d : Fin D, ∑ k : Fin K, C (x d k) *
        (F (cen p K k0 k + ((d : ℕ) + 1)) - F (cen p K k0 k - ((d : ℕ) + 1))) := by
  simp_rw [tRows_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hg : Good P N p k0 d k
  · rw [← sum_pairRow k0 d k hg F, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  · rw [hx d k hg]
    simp

theorem no_mult (t u : ℤ) (hp : (0 : ℤ) < p) (h1 : -(p : ℤ) < u) (h2 : u < p)
    (h : t * p = u) : t = 0 ∧ u = 0 := by
  have : t = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h3 | h3
    · nlinarith
    · nlinarith
  subst this
  simp at h
  exact ⟨rfl, h.symm⟩

/-- A row `c_k + d'` with `1 ≤ d' ≤ (p-1)/2` determines `(k, d')`. -/
theorem pair_eval {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) (r : Fin (P.n N))
    (hr : (r : ℤ) - P.g N = cen p K k0 k + ((d : ℕ) + 1)) :
    tRows P N p K D k0 x r = x d k := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hdl := d.isLt
  have hp1 : (0 : ℤ) < p := by omega
  rw [tRows_apply, Finset.sum_eq_single d]
  · rw [Finset.sum_eq_single k]
    · unfold pairRow
      rw [if_pos hr, if_neg]
      · simp
      · intro h
        rw [hr] at h
        omega
    · intro k2 _ hk2
      unfold pairRow
      have hn1 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 + ((d : ℕ) + 1)) := by
        intro h
        unfold cen at h hr
        have h4 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = 0 := by nlinarith
        have h5 := (no_mult _ 0 hp1 (by omega) (by omega) h4).1
        exact hk2 (Fin.ext (by omega))
      have hn2 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 - ((d : ℕ) + 1)) := by
        intro h
        unfold cen at h hr
        have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = -2 * ((d : ℕ) + 1) := by nlinarith
        have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
        omega
      rw [if_neg hn1, if_neg hn2]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro d2 _ hd2
    refine Finset.sum_eq_zero fun k2 _ => ?_
    unfold pairRow
    have hd2l := d2.isLt
    have hn1 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 + ((d2 : ℕ) + 1)) := by
      intro h
      unfold cen at h hr
      have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = ((d2 : ℕ) : ℤ) - (d : ℕ) := by nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      apply hd2
      apply Fin.ext
      omega
    have hn2 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 - ((d2 : ℕ) + 1)) := by
      intro h
      unfold cen at h hr
      have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = -(((d : ℕ) : ℤ) + 1) - ((d2 : ℕ) + 1) := by
        nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      omega
    rw [if_neg hn1, if_neg hn2]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Injectivity on the virtual-pair-free subspace. -/
theorem tRows_injective_on {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (hx : ∀ d k, ¬ Good P N p k0 d k → x d k = 0)
    (h0 : tRows P N p K D k0 x = 0) : x = 0 := by
  funext d k
  by_cases hg : Good P N p k0 d k
  · obtain ⟨⟨h1, h2⟩, _⟩ := hg
    have hr : (cen p K k0 k + ((d : ℕ) + 1) + P.g N).toNat < P.n N := by omega
    have := pair_eval (P := P) (N := N) hp2 hD k0 x d k ⟨_, hr⟩ (by simp only; omega)
    rw [h0] at this
    simpa using this.symm
  · exact hx d k hg

#print axioms tRows_injective_on
#print axioms sum_pairRows
end
end CatalanMeasure.GenD.Uniform.W.Thin
