module

public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTPlus
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.HPGen

@[expose] public section
set_option Elab.async false

/-!
# Generic cell lemmas for Theorem MT (1) (lane G5f)

For a fixed digit `s`, block window `(k0, K)` and offsets `(D1, e0)` the three MT (1) values
`mtVal2` (T- and T+), `mtPlusVal` (T+) and `mtMinusVal` (T-) are bounded below by a closed form:
the digit set `mtJJ` has at most `c` elements (`mtJJ_card_le`), and only the blocks outside `[a, b)`
can carry missing rows (`bad_card_le`).  A cell then only has to discharge linear side conditions
by `omega`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

/-! ### Ranges of the block index -/

theorem hpKmin_le_of (P : Parameters) (N p a : ℕ) (hp : 0 < p) (h : a * p ≤ P.g N + p - 1) :
    hpKmin P N p ≤ -(a : ℤ) - 1 := by
  unfold hpKmin
  have : a ≤ (P.g N + p - 1) / p := (Nat.le_div_iff_mul_le hp).mpr h
  omega

theorem le_hpKmax_of (P : Parameters) (N p e : ℕ) (hp : 0 < p) (h : e * p ≤ P.n N - P.g N) :
    (e : ℤ) + 1 ≤ hpKmax P N p := by
  unfold hpKmax
  have : e ≤ (P.n N - P.g N) / p := (Nat.le_div_iff_mul_le hp).mpr h
  omega

theorem mtKmax_ge_of (P : Parameters) (N p a e K : ℕ) (hp : 0 < p) (h1 : a * p ≤ P.g N + p - 1)
    (h2 : e * p ≤ P.n N - P.g N) (hK : K ≤ a + e + 3) : K ≤ mtKmax P N p := by
  have := hpKmin_le_of P N p a hp h1
  have := le_hpKmax_of P N p e hp h2
  unfold mtKmax
  omega

/-! ### Values lie below `mtLB3` -/

theorem mtVal2_le_mtLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) [Fact p.Prime]
    (s K D1 e0 : ℕ) (k0 : ℤ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0)
    (h1 : k0 ≤ hpKmax P N p) (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    mtVal2 P N p s K D1 e0 k0 ≤ (mtLB3 P hP).kap N p := by
  have h2 : mtVal2 P N p s K D1 e0 k0 ≤ mtKap2 P N p := by
    unfold mtKap2
    rw [dif_pos (Fact.out : p.Prime)]
    exact le_mtSup P N p (fun s K k0 D1 e0 => mtVal2 P N p s K D1 e0 k0) s K k0 D1 e0 hs h0 h1 hK hD he
  exact h2.trans (mtBothLB2_le_mtLB3 P hP N p)

theorem mtMinusVal_le_mtLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) [Fact p.Prime]
    (s K D1 e0 : ℕ) (k0 : ℤ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0)
    (h1 : k0 ≤ hpKmax P N p) (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    mtMinusVal P N p s K k0 D1 e0 ≤ (mtLB3 P hP).kap N p := by
  have h2 : mtMinusVal P N p s K k0 D1 e0 ≤ mtMinusKap P N p := by
    unfold mtMinusKap
    rw [dif_pos (Fact.out : p.Prime)]
    exact le_mtSup P N p (fun s K k0 D1 e0 => mtMinusVal P N p s K k0 D1 e0) s K k0 D1 e0 hs h0 h1 hK hD he
  exact h2.trans (mtMinusLB_le_mtLB3 P hP N p)

theorem mtPlusVal_le_mtLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) [Fact p.Prime]
    (s K D1 e0 : ℕ) (k0 : ℤ) (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0)
    (h1 : k0 ≤ hpKmax P N p) (hK : K ≤ mtKmax P N p) (hD : D1 ≤ (p - 1) / 2) (he : e0 ≤ D1) :
    mtPlusVal P N p s K D1 e0 k0 ≤ (mtLB3 P hP).kap N p := by
  have h2 : mtPlusVal P N p s K D1 e0 k0 ≤ mtPlusKap P N p := by
    unfold mtPlusKap
    rw [dif_pos (Fact.out : p.Prime)]
    exact le_mtSup P N p (fun s K k0 D1 e0 => mtPlusVal P N p s K D1 e0 k0) s K k0 D1 e0 hs h0 h1 hK hD he
  exact h2.trans (mtPlusLB_le_mtLB3 P hP N p)

/-! ### The digit set -/

theorem mtJJ_card_le {P : Parameters} {N p s D1 e0 lm1 c : ℕ}
    (hA : lm1 * p + (hpEta P N p s - e0) < P.b N)
    (hB : P.L N - 1 < (lm1 + 1 + c) * p + (hpEta P N p s - (P.h N + D1 - 1))) :
    (mtJJ P N p s D1 e0).card ≤ c := by
  have hsub : mtJJ P N p s D1 e0 ⊆ Finset.Ico (lm1 + 1) (lm1 + 1 + c) := by
    intro J hJ
    unfold mtJJ at hJ
    rw [Finset.mem_filter] at hJ
    obtain ⟨-, hJ⟩ := hJ
    have h1 : P.b N ≤ J * p + (hpEta P N p s - e0) :=
      (le_max_right _ _).trans (hJ.trans (min_le_left _ _))
    have h2 : J * p + (hpEta P N p s - (P.h N + D1 - 1)) ≤ P.L N - 1 :=
      (le_max_left _ _).trans (hJ.trans (min_le_right _ _))
    rw [Finset.mem_Ico]
    constructor
    · by_contra hc
      have := Nat.mul_le_mul_right p (show J ≤ lm1 by omega)
      omega
    · by_contra hc
      have := Nat.mul_le_mul_right p (show lm1 + 1 + c ≤ J by omega)
      omega
  calc (mtJJ P N p s D1 e0).card ≤ (Finset.Ico (lm1 + 1) (lm1 + 1 + c)).card :=
        Finset.card_le_card hsub
    _ = c := by simp

theorem mtJJ_card_le0 {P : Parameters} {N p s D1 e0 c : ℕ}
    (hB : P.L N - 1 < c * p + (hpEta P N p s - (P.h N + D1 - 1))) :
    (mtJJ P N p s D1 e0).card ≤ c := by
  have hsub : mtJJ P N p s D1 e0 ⊆ Finset.range c := by
    intro J hJ
    unfold mtJJ at hJ
    rw [Finset.mem_filter] at hJ
    obtain ⟨-, hJ⟩ := hJ
    have h2 : J * p + (hpEta P N p s - (P.h N + D1 - 1)) ≤ P.L N - 1 :=
      (le_max_left _ _).trans (hJ.trans (min_le_right _ _))
    rw [Finset.mem_range]
    by_contra hc
    have := Nat.mul_le_mul_right p (show c ≤ J by omega)
    omega
  calc (mtJJ P N p s D1 e0).card ≤ (Finset.range c).card := Finset.card_le_card hsub
    _ = c := by simp

/-! ### Missing rows -/

theorem out_card_le {K : ℕ} (a b : ℕ) :
    (Finset.univ.filter (fun k : Fin K => k.val < a ∨ b ≤ k.val)).card ≤ a + (K - b) := by
  have h : (Finset.univ.filter (fun k : Fin K => k.val < a ∨ b ≤ k.val)).card ≤
      (Finset.range a ∪ Finset.Ico b K).card := by
    refine Finset.card_le_card_of_injOn (fun k : Fin K => k.val) ?_ ?_
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk
      simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ico, Set.mem_union,
        Set.mem_Iio, Set.mem_Ico]
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr ⟨hk, k.isLt⟩
    · intro i _ j _ hij
      exact Fin.ext hij
  refine h.trans ((Finset.card_union_le _ _).trans ?_)
  simp

theorem bad_card_le {D K : ℕ} (G : Fin D → Fin K → Prop) [∀ d k, Decidable (G d k)] (a b : ℕ)
    (h : ∀ (d : Fin D) (k : Fin K), a ≤ k.val → k.val < b → G d k) :
    (Finset.univ.filter (fun dk : Fin D × Fin K => ¬ G dk.1 dk.2)).card ≤ D * (a + (K - b)) := by
  have hsub : (Finset.univ.filter (fun dk : Fin D × Fin K => ¬ G dk.1 dk.2)) ⊆
      (Finset.univ : Finset (Fin D)) ×ˢ
        (Finset.univ.filter (fun k : Fin K => k.val < a ∨ b ≤ k.val)) := by
    intro dk hdk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hdk
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
    by_contra hc
    push_neg at hc
    exact hdk (h dk.1 dk.2 hc.1 hc.2)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = D * _ := by simp
    _ ≤ D * (a + (K - b)) := Nat.mul_le_mul_left _ (out_card_le a b)

theorem bad0_card_le {K : ℕ} (G : Fin K → Prop) [∀ k, Decidable (G k)] (a b : ℕ)
    (h : ∀ k : Fin K, a ≤ k.val → k.val < b → G k) :
    (Finset.univ.filter (fun k : Fin K => ¬ G k)).card ≤ a + (K - b) := by
  refine le_trans (Finset.card_le_card ?_) (out_card_le (K := K) a b)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_contra hc
  push_neg at hc
  exact hk (h k hc.1 hc.2)

/-- Rows of the in-blocks `[a, b)` with offsets up to `D1` are actual rows. -/
theorem inrange_of_blocks {P : Parameters} {N p K : ℕ} {k0 : ℤ} {D1 a b : ℕ}
    (hL : -(P.g N : ℤ) ≤ (k0 + a) * p - D1) (hR : (k0 + b - 1) * p + D1 < (P.n N : ℤ) - P.g N)
    (k : Fin K) (ha : a ≤ k.val) (hb : k.val < b) (t : ℤ) (ht0 : 0 ≤ t) (htD : t ≤ D1) :
    InRange P N (cen p K k0 k + t) ∧ InRange P N (cen p K k0 k - t) := by
  unfold InRange cen
  have hp : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  have h1 : ((a : ℤ)) ≤ (k.val : ℤ) := by exact_mod_cast ha
  have h2 : (k.val : ℤ) ≤ (b : ℤ) - 1 := by have : k.val + 1 ≤ b := hb; omega
  have m1 : (k0 + a) * (p : ℤ) ≤ (k0 + k.val) * p :=
    mul_le_mul_of_nonneg_right (by linarith) hp
  have m2 : (k0 + k.val) * (p : ℤ) ≤ (k0 + b - 1) * p :=
    mul_le_mul_of_nonneg_right (by linarith) hp
  constructor <;> constructor <;> nlinarith

/-- The number of missing rows of the mixed system. -/
theorem mixMiss_le {P : Parameters} {N p K D1 a b t : ℕ} {k0 : ℤ}
    (hL : -(P.g N : ℤ) ≤ (k0 + a) * p - D1) (hR : (k0 + b - 1) * p + D1 < (P.n N : ℤ) - P.g N)
    (ht : a + (K - b) ≤ t) : mixMiss P N p K D1 k0 ≤ t * (2 * D1 + 1) := by
  have hP : (mmP P N p K D1 k0).card ≤ D1 * (a + (K - b)) := by
    unfold mmP
    refine bad_card_le (fun (d : Fin D1) (k : Fin K) => InRange P N (cen p K k0 k + (((d : ℕ) : ℤ) + 1)))
      a b ?_
    intro d k ha hb
    exact (inrange_of_blocks hL hR k ha hb _ (by omega) (by have := d.isLt; omega)).1
  have hM : (mmM P N p K D1 k0).card ≤ D1 * (a + (K - b)) := by
    unfold mmM
    refine bad_card_le (fun (d : Fin D1) (k : Fin K) => InRange P N (cen p K k0 k - (((d : ℕ) : ℤ) + 1)))
      a b ?_
    intro d k ha hb
    exact (inrange_of_blocks hL hR k ha hb _ (by omega) (by have := d.isLt; omega)).2
  have h0 : (mm0 P N p K k0).card ≤ a + (K - b) := by
    unfold mm0
    refine bad0_card_le (fun k : Fin K => InRange P N (cen p K k0 k)) a b ?_
    intro k ha hb
    have := (inrange_of_blocks (D1 := D1) hL hR k ha hb 0 le_rfl (by omega)).1
    simpa using this
  unfold mixMiss
  have e1 : D1 * (a + (K - b)) ≤ D1 * t := Nat.mul_le_mul_left _ ht
  have : t * (2 * D1 + 1) = D1 * t + D1 * t + t := by ring
  omega

theorem tpVirt_le {P : Parameters} {N p K D1 a b t : ℕ} [Fact p.Prime] {k0 : ℤ}
    (hL : -(P.g N : ℤ) ≤ (k0 + a) * p - D1) (hR : (k0 + b - 1) * p + D1 < (P.n N : ℤ) - P.g N)
    (ht : a + (K - b) ≤ t) : tpVirt P N p K (D1 + 1) k0 ≤ (D1 + 1) * t := by
  unfold tpVirt tpBad
  refine (bad_card_le (fun (d : Fin (D1 + 1)) (k : Fin K) => TpGood P N p k0 d k) a b ?_).trans
    (Nat.mul_le_mul_left _ ht)
  intro d k ha hb
  have := inrange_of_blocks hL hR k ha hb (d : ℕ) (by omega) (by have := d.isLt; omega)
  exact ⟨by simpa using this.1, by simpa using this.2⟩

theorem virtCount_le {P : Parameters} {N p K D1 a b t : ℕ} {k0 : ℤ}
    (hL : -(P.g N : ℤ) ≤ (k0 + a) * p - D1) (hR : (k0 + b - 1) * p + D1 < (P.n N : ℤ) - P.g N)
    (ht : a + (K - b) ≤ t) : virtCount P N p K D1 k0 ≤ D1 * t := by
  unfold virtCount
  refine (bad_card_le (fun (d : Fin D1) (k : Fin K) => Good P N p k0 d k) a b ?_).trans
    (Nat.mul_le_mul_left _ ht)
  intro d k ha hb
  have := inrange_of_blocks hL hR k ha hb ((d : ℕ) + 1) (by omega) (by have := d.isLt; omega)
  exact ⟨by simpa using this.1, by simpa using this.2⟩

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger3
