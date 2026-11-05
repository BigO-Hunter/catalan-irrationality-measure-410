module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.TilingPoly
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.EndpointCutoff
@[expose] public section
set_option Elab.async false

/-!
# Virtual rows: the endpoint blocks of the tiling

For tiling coordinates `t` with rows `ĉ = physicalTilingEquiv t`:

* `bottom_identity` : `QA_0 - QC_0 + u_0 w = Σ_{i<p} ĉ_i U_{p-1-i}` (= `bottomEndpoint`), so the rows below
  `ja` vanish iff `deg (QA_0 - QC_0 + u_0 w) < p - ja`;
* `top_identity` : `QA_{b-1} + QC_{b-1} = Σ_{i=1}^{p} ĉ_{(b-1)p+i} U_{i-1}` (= `topEndpoint`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Polynomial Polynomial.Chebyshev Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

theorem Up1 (hp2 : p ≠ 2) : U Fp ((p : ℤ) - 1) = nativeCenter (p := p) := by
  rw [CatalanMeasure.Parametric.chebyshev_U_prime hp2]; rfl

/-- The bottom-block test family. -/
def Fbot (p : ℕ) [Fact p.Prime] (i : ℕ) : (ZMod p)[X] :=
  if i ≤ p then U (ZMod p) ((p : ℤ) - 1 - i) else 0

theorem Fbot_zero (hp2 : p ≠ 2) : Fbot p 0 = nativeCenter (p := p) := by
  simp [Fbot, Up1 hp2]

theorem Fbot_p : Fbot p p = 0 := by simp [Fbot]

theorem Fbot_big {i : ℕ} (h : p < i) : Fbot p i = 0 := by
  simp [Fbot, not_le.mpr h]

theorem bottom_identity (hp2 : p ≠ 2) {b : ℕ} (hb : 0 < b)
    (t : TilingCoordinates (K := Fp) b ((p - 1) / 2)) :
    QA t ⟨0, hb⟩ - QC t ⟨0, hb⟩ + t.2 0 • nativeCenter (p := p) =
      bottomEndpoint p (fun i : Fin p => physicalTilingEquiv b ((p - 1) / 2) p
        (native_half_identity hp2) (native_two_ne_zero hp2) t
        ⟨i.val, by have := i.isLt; have := Nat.le_mul_of_pos_left p hb; omega⟩) := by
  have hpe := native_half_identity hp2
  have hbp : p ≤ b * p := Nat.le_mul_of_pos_left p hb
  have hs := tiling_sum (K := Fp) (M := Fp[X]) b ((p - 1) / 2) p hpe (native_two_ne_zero hp2) t (Fbot p)
  -- the left side
  have hL : ∑ i : Fin (b * p + 1), (physicalTilingEquiv b ((p - 1) / 2) p hpe
        (native_two_ne_zero hp2) t i) • Fbot p i = bottomEndpoint p (fun i : Fin p =>
        physicalTilingEquiv b ((p - 1) / 2) p hpe (native_two_ne_zero hp2) t
        ⟨i.val, by have := i.isLt; omega⟩) := by
    set ĉ := physicalTilingEquiv b ((p - 1) / 2) p hpe (native_two_ne_zero hp2) t with hĉ
    let c' : ℕ → Fp := fun i => if h : i < b * p + 1 then ĉ ⟨i, h⟩ else 0
    have e1 : ∑ i : Fin (b * p + 1), ĉ i • Fbot p i = ∑ i ∈ range (b * p + 1), c' i • Fbot p i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => c' i • Fbot p i) (b * p + 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : c' (i : ℕ) = ĉ i := by simp only [c', dif_pos i.isLt]
      rw [this]
    have e2 : ∑ i ∈ range (b * p + 1), c' i • Fbot p i = ∑ i ∈ range p, c' i • Fbot p i := by
      symm
      apply Finset.sum_subset (range_subset_range.mpr (by omega))
      intro i hi hni
      rw [Finset.mem_range] at hi hni
      by_cases hip : i = p
      · subst hip; simp [Fbot_p]
      · rw [Fbot_big (by omega), smul_zero]
    have e3 : ∑ i ∈ range p, c' i • Fbot p i =
        ∑ i : Fin p, ĉ ⟨i.val, by have := i.isLt; omega⟩ • U Fp ((p : ℤ) - 1 - (i : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => c' i • Fbot p i) p]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : i.val < b * p + 1 := by have := i.isLt; omega
      have h2 : (i : ℕ) ≤ b * p := by have := i.isLt; omega
      simp [c', h1, Fbot, i.isLt.le, h2]
    unfold bottomEndpoint
    rw [e1, e2, e3]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
    have hi := i.isLt
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
    congr 2
    omega
  rw [← hL, hs]
  have hhp : ∀ j : Fin ((p - 1) / 2), (j : ℕ) + 1 ≤ p := fun j => by have := j.isLt; omega
  have hA : ∀ j : Fin ((p - 1) / 2), Fbot p (0 * p + ((j : ℕ) + 1)) =
      U Fp ((p : ℤ) - (j : ℕ) - 2) := fun j => by
    have := hhp j
    simp only [zero_mul, zero_add, Fbot, if_pos this]
    congr 1; push_cast; ring
  have hB : ∀ j : Fin ((p - 1) / 2), Fbot p (0 * p + (p - ((j : ℕ) + 1))) = U Fp ((j : ℕ) : ℤ) := fun j => by
    have := hhp j
    simp only [zero_mul, zero_add, Fbot, if_pos (Nat.sub_le p _)]
    congr 1; rw [Nat.cast_sub this]; push_cast; ring
  have hk : ∀ k : Fin b, k ≠ ⟨0, hb⟩ →
      (∑ j : Fin ((p - 1) / 2),
        (t.1.1 (finProdFinEquiv (k, j)) • (Fbot p (k * p + (j + 1)) + Fbot p (k * p + (p - (j + 1)))) +
         t.1.2 (finProdFinEquiv (k, j)) • (Fbot p (k * p + (j + 1)) - Fbot p (k * p + (p - (j + 1)))))) = 0 ∧
      t.2 k.succ • (Fbot p (k * p) + Fbot p ((k + 1) * p)) = 0 := by
    intro k hk0
    have hk1 : 1 ≤ (k : ℕ) := by
      rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
      · exact absurd (Fin.ext h) hk0
      · exact h
    have hkp : p ≤ k * p := Nat.le_mul_of_pos_left p hk1
    refine ⟨Finset.sum_eq_zero fun j _ => ?_, ?_⟩
    · have hj := j.isLt
      rw [Fbot_big (by omega), Fbot_big (by omega)]; simp
    · have e2 : Fbot p ((k + 1) * p) = 0 := Fbot_big (by
        have := (Fact.out : p.Prime).pos; rw [Nat.add_mul, one_mul]; omega)
      have e1 : Fbot p (k * p) = 0 := by
        by_cases h : k * p = p
        · rw [h]; exact Fbot_p
        · exact Fbot_big (by omega)
      rw [e1, e2]; simp
  rw [Finset.sum_eq_single ⟨0, hb⟩ (fun k _ hk0 => (hk k hk0).1) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single ⟨0, hb⟩ (fun k _ hk0 => (hk k hk0).2) (fun h => absurd (Finset.mem_univ _) h)]
  have hedge : Fbot p ((0 : ℕ) * p) + Fbot p (((0 : ℕ) + 1) * p) = nativeCenter (p := p) := by
    rw [zero_mul, Fbot_zero hp2, zero_add, one_mul, Fbot_p, add_zero]
  rw [hedge, Fbot_zero hp2]
  simp only [QA, QC]
  have hj : ∀ j : Fin ((p - 1) / 2),
      t.1.1 (finProdFinEquiv ((⟨0, hb⟩ : Fin b), j)) • (Fbot p (0 * p + (j + 1)) + Fbot p (0 * p + (p - (j + 1)))) +
        t.1.2 (finProdFinEquiv ((⟨0, hb⟩ : Fin b), j)) • (Fbot p (0 * p + (j + 1)) - Fbot p (0 * p + (p - (j + 1)))) =
      t.1.1 (finProdFinEquiv ((⟨0, hb⟩ : Fin b), j)) • nativePlus (p := p) ((j : ℤ) + 1) -
        t.1.2 (finProdFinEquiv ((⟨0, hb⟩ : Fin b), j)) • nativeMinus (p := p) ((j : ℤ) + 1) := by
    intro j
    rw [hA j, hB j]
    have hP : nativePlus (p := p) ((j : ℤ) + 1) = U Fp ((j : ℕ) : ℤ) + U Fp ((p : ℤ) - (j : ℕ) - 2) := by
      unfold nativePlus; congr 2 <;> ring_nf
    have hM : nativeMinus (p := p) ((j : ℤ) + 1) = U Fp ((j : ℕ) : ℤ) - U Fp ((p : ℤ) - (j : ℕ) - 2) := by
      unfold nativeMinus; congr 2 <;> ring_nf
    rw [hP, hM]
    simp only [smul_add, smul_sub]
    abel
  simp only [zero_mul, zero_add] at hj
  simp only [zero_mul, zero_add, Fin.val_mk]
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib]
  simp only [Fin.succ_mk]
  abel

/-- The top-block test family (block starts at `m = (b-1) p`). -/
def Ftop (p m : ℕ) [Fact p.Prime] (i : ℕ) : (ZMod p)[X] :=
  if m ≤ i then U (ZMod p) ((i : ℤ) - m - 1) else 0

theorem Ftop_lt {m i : ℕ} (h : i < m) : Ftop p m i = 0 := by simp [Ftop, not_le.mpr h]
theorem Ftop_m (m : ℕ) : Ftop p m m = 0 := by simp [Ftop]

theorem top_identity (hp2 : p ≠ 2) {b : ℕ} (hb : 0 < b)
    (t : TilingCoordinates (K := Fp) b ((p - 1) / 2)) :
    QA t ⟨b - 1, by omega⟩ + QC t ⟨b - 1, by omega⟩ =
      topEndpoint p (fun i : Fin (p + 1) => physicalTilingEquiv b ((p - 1) / 2) p
        (native_half_identity hp2) (native_two_ne_zero hp2) t
        ⟨(b - 1) * p + i.val, by
          have := i.isLt
          have : (b - 1) * p + p = b * p := by
            have : b = (b - 1) + 1 := by omega
            conv_rhs => rw [this]
            ring
          omega⟩) := by
  have hpe := native_half_identity hp2
  have hmp : (b - 1) * p + p = b * p := by
    have : b = (b - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  set m := (b - 1) * p with hm
  have hs := tiling_sum (K := Fp) (M := Fp[X]) b ((p - 1) / 2) p hpe (native_two_ne_zero hp2) t (Ftop p m)
  have hL : ∑ i : Fin (b * p + 1), (physicalTilingEquiv b ((p - 1) / 2) p hpe
        (native_two_ne_zero hp2) t i) • Ftop p m i = topEndpoint p (fun i : Fin (p + 1) =>
        physicalTilingEquiv b ((p - 1) / 2) p hpe (native_two_ne_zero hp2) t
        ⟨m + i.val, by have := i.isLt; omega⟩) := by
    set ĉ := physicalTilingEquiv b ((p - 1) / 2) p hpe (native_two_ne_zero hp2) t with hĉ
    let c' : ℕ → Fp := fun i => if h : i < b * p + 1 then ĉ ⟨i, h⟩ else 0
    have e1 : ∑ i : Fin (b * p + 1), ĉ i • Ftop p m i = ∑ i ∈ range (b * p + 1), c' i • Ftop p m i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => c' i • Ftop p m i) (b * p + 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : c' (i : ℕ) = ĉ i := by simp only [c', dif_pos i.isLt]
      rw [this]
    have e2 : ∑ i ∈ range (b * p + 1), c' i • Ftop p m i =
        ∑ i ∈ range p, c' (m + 1 + i) • Ftop p m (m + 1 + i) := by
      have : b * p + 1 = (m + 1) + p := by omega
      rw [this, Finset.sum_range_add]
      have h0 : ∑ i ∈ range (m + 1), c' i • Ftop p m i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_range] at hi
        by_cases him : i = m
        · rw [him, Ftop_m, smul_zero]
        · rw [Ftop_lt (by omega), smul_zero]
      rw [h0, zero_add]
    have e3 : ∑ i ∈ range p, c' (m + 1 + i) • Ftop p m (m + 1 + i) =
        ∑ i : Fin p, ĉ ⟨m + (i.val + 1), by have := i.isLt; omega⟩ • U Fp (i.val : ℤ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => c' (m + 1 + i) • Ftop p m (m + 1 + i)) p]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : m + 1 + i.val < b * p + 1 := by have := i.isLt; omega
      have h2 : m ≤ m + 1 + i.val := by omega
      have e : m + 1 + i.val = m + (i.val + 1) := by omega
      simp only [c', dif_pos h1, Ftop, if_pos h2]
      congr 2
      · congr 1
      · push_cast; ring
    unfold topEndpoint
    rw [e1, e2, e3]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.val_succ]
  rw [← hL, hs]
  have hhp : ∀ j : Fin ((p - 1) / 2), (j : ℕ) + 1 ≤ p := fun j => by have := j.isLt; omega
  have hkl : ∀ k : Fin b, k ≠ ⟨b - 1, by omega⟩ → (k : ℕ) + 1 ≤ b - 1 := fun k hk => by
    have h1 := k.isLt
    have : (k : ℕ) ≠ b - 1 := fun h => hk (Fin.ext h)
    omega
  have hk : ∀ k : Fin b, k ≠ ⟨b - 1, by omega⟩ →
      (∑ j : Fin ((p - 1) / 2),
        (t.1.1 (finProdFinEquiv (k, j)) • (Ftop p m (k * p + (j + 1)) + Ftop p m (k * p + (p - (j + 1)))) +
         t.1.2 (finProdFinEquiv (k, j)) • (Ftop p m (k * p + (j + 1)) - Ftop p m (k * p + (p - (j + 1)))))) = 0 ∧
      t.2 k.succ • (Ftop p m (k * p) + Ftop p m ((k + 1) * p)) = 0 := by
    intro k hk0
    have h1 := hkl k hk0
    have hkp : ((k : ℕ) + 1) * p ≤ m := Nat.mul_le_mul_right p h1
    rw [Nat.add_mul, one_mul] at hkp
    refine ⟨Finset.sum_eq_zero fun j _ => ?_, ?_⟩
    · have hj := j.isLt
      rw [Ftop_lt (by omega), Ftop_lt (by omega)]; simp
    · have e1 : Ftop p m (k * p) = 0 := Ftop_lt (by have := (Fact.out : p.Prime).pos; omega)
      have e2 : Ftop p m ((k + 1) * p) = 0 := by
        by_cases h : ((k : ℕ) + 1) * p = m
        · rw [h]; exact Ftop_m m
        · exact Ftop_lt (by rw [Nat.add_mul, one_mul] at *; omega)
      rw [e1, e2]; simp
  rw [Finset.sum_eq_single ⟨b - 1, by omega⟩ (fun k _ hk0 => (hk k hk0).1) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single ⟨b - 1, by omega⟩ (fun k _ hk0 => (hk k hk0).2) (fun h => absurd (Finset.mem_univ _) h)]
  have hF0 : Ftop p m 0 = 0 := by
    by_cases h : m = 0
    · rw [← h]; exact Ftop_m m
    · exact Ftop_lt (by omega)
  have hedge : Ftop p m (((b - 1 : ℕ)) * p) + Ftop p m (((b - 1 : ℕ) + 1) * p) = nativeCenter (p := p) := by
    rw [← hm, Ftop_m]
    have : ((b - 1 : ℕ) + 1) * p = m + p := by rw [Nat.add_mul, one_mul]
    rw [this]
    simp only [Ftop, le_add_iff_nonneg_right, zero_le, if_true, zero_add]
    rw [← Up1 hp2]; congr 1; push_cast; ring
  simp only [Fin.val_mk]
  rw [hF0, hedge, smul_zero, add_zero]
  simp only [QA, QC]
  have hj : ∀ j : Fin ((p - 1) / 2),
      t.1.1 (finProdFinEquiv ((⟨b - 1, by omega⟩ : Fin b), j)) •
          (Ftop p m ((b - 1) * p + (j + 1)) + Ftop p m ((b - 1) * p + (p - (j + 1)))) +
        t.1.2 (finProdFinEquiv ((⟨b - 1, by omega⟩ : Fin b), j)) •
          (Ftop p m ((b - 1) * p + (j + 1)) - Ftop p m ((b - 1) * p + (p - (j + 1)))) =
      t.1.1 (finProdFinEquiv ((⟨b - 1, by omega⟩ : Fin b), j)) • nativePlus (p := p) ((j : ℤ) + 1) +
        t.1.2 (finProdFinEquiv ((⟨b - 1, by omega⟩ : Fin b), j)) • nativeMinus (p := p) ((j : ℤ) + 1) := by
    intro j
    have hj1 := hhp j
    have hA : Ftop p m ((b - 1) * p + ((j : ℕ) + 1)) = U Fp ((j : ℕ) : ℤ) := by
      rw [← hm]; simp only [Ftop, le_add_iff_nonneg_right, zero_le, if_true]; congr 1; push_cast; ring
    have hB : Ftop p m ((b - 1) * p + (p - ((j : ℕ) + 1))) = U Fp ((p : ℤ) - (j : ℕ) - 2) := by
      rw [← hm]; simp only [Ftop, le_add_iff_nonneg_right, zero_le, if_true]
      congr 1; rw [Nat.cast_add, Nat.cast_sub hj1]; push_cast; ring
    rw [hA, hB]
    have hP : nativePlus (p := p) ((j : ℤ) + 1) = U Fp ((j : ℕ) : ℤ) + U Fp ((p : ℤ) - (j : ℕ) - 2) := by
      unfold nativePlus; congr 2 <;> ring_nf
    have hM : nativeMinus (p := p) ((j : ℤ) + 1) = U Fp ((j : ℕ) : ℤ) - U Fp ((p : ℤ) - (j : ℕ) - 2) := by
      unfold nativeMinus; congr 2 <;> ring_nf
    rw [hP, hM]
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib]
  abel

end
end CatalanMeasure.GenD.Uniform.W.Charts4
