module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.LB
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.MTGen

@[expose] public section
set_option Elab.async false

/-!
# Generic closed forms for the MT (b) glue cells (lane G5g)

* `mixMiss_le_top`: when every block but the top one has all its rows, the missing rows of the top block
  are bounded by `(D1 - r1) + u + 1` (rows `>= n - g` only).
* `cov1_gen`, `cov2_gen`: digit coverage of the raw columns from linear inequalities.
* `glue_ge`: the closed form for `mtGlueVal1` below `glueCellLB`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.MTGlue CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Only the top block can have a row `>= n - g`. -/
theorem top_key {P : Parameters} {N p K D1 : ℕ} {k0 : ℤ}
    (hlow : ∀ k : Fin K, -(P.g N : ℤ) ≤ cen p K k0 k - D1)
    (hmid : ∀ k : Fin K, k.val + 1 < K → cen p K k0 k + D1 < (P.n N : ℤ) - P.g N)
    (k : Fin K) (t : ℤ) (ht : -(D1 : ℤ) ≤ t) (ht' : t ≤ D1)
    (hx : ¬ InRange P N (cen p K k0 k + t)) : k.val + 1 = K := by
  by_contra hne
  have hk := k.isLt
  have h1 := hmid k (by omega)
  have h2 := hlow k
  apply hx
  unfold InRange
  constructor <;> omega

theorem mixMiss_le_top {P : Parameters} {N p K D1 r1 u : ℕ} {k0 : ℤ} (hK : 0 < K)
    (hlow : ∀ k : Fin K, -(P.g N : ℤ) ≤ cen p K k0 k - D1)
    (hmid : ∀ k : Fin K, k.val + 1 < K → cen p K k0 k + D1 < (P.n N : ℤ) - P.g N)
    (hr : r1 = 0 ∨ (r1 : ℤ) ≤ (P.n N : ℤ) - P.g N - cen p K k0 ⟨K - 1, by omega⟩ - 1)
    (hu : cen p K k0 ⟨K - 1, by omega⟩ - ((P.n N : ℤ) - P.g N) ≤ u) :
    mixMiss P N p K D1 k0 ≤ (D1 - r1) + u + 1 := by
  unfold mixMiss mmP mmM mm0
  have hct : ∀ k : Fin K, k.val + 1 = K → cen p K k0 k = cen p K k0 ⟨K - 1, by omega⟩ := by
    intro k hk
    congr 1; exact Fin.ext (by simp; omega)
  have hP : (Finset.univ.filter fun dk : Fin D1 × Fin K =>
      ¬ InRange P N (cen p K k0 dk.2 + (((dk.1 : ℕ) : ℤ) + 1))).card ≤ D1 - r1 := by
    have key : ∀ x : Fin D1 × Fin K, ¬ InRange P N (cen p K k0 x.2 + (((x.1 : ℕ) : ℤ) + 1)) →
        x.2.val + 1 = K ∧ r1 ≤ x.1.val := by
      intro x hx
      have hd := x.1.isLt
      have hkk := top_key hlow hmid x.2 _ (by omega) (by omega) hx
      refine ⟨hkk, ?_⟩
      have h3 := hct x.2 hkk
      have hl := hlow x.2
      rw [h3] at hl
      unfold InRange at hx
      rw [h3] at hx
      by_contra hcon
      apply hx
      constructor <;> omega
    have : (Finset.univ.filter fun dk : Fin D1 × Fin K =>
        ¬ InRange P N (cen p K k0 dk.2 + (((dk.1 : ℕ) : ℤ) + 1))).card ≤ (Finset.range (D1 - r1)).card := by
      refine Finset.card_le_card_of_injOn (fun dk => dk.1.val - r1) ?_ ?_
      · intro dk hdk
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hdk
        have hd := dk.1.isLt
        have := key dk hdk
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        obtain ⟨ha1, ha2⟩ := key a ha
        obtain ⟨hb1, hb2⟩ := key b hb
        have := a.2.isLt; have := b.2.isLt
        refine Prod.ext (Fin.ext (by simp only at hab; omega)) (Fin.ext (by omega))
    simpa using this
  have hM : (Finset.univ.filter fun dk : Fin D1 × Fin K =>
      ¬ InRange P N (cen p K k0 dk.2 - (((dk.1 : ℕ) : ℤ) + 1))).card ≤ u := by
    have key : ∀ x : Fin D1 × Fin K, ¬ InRange P N (cen p K k0 x.2 - (((x.1 : ℕ) : ℤ) + 1)) →
        x.2.val + 1 = K ∧ x.1.val < u := by
      intro x hx
      have hd := x.1.isLt
      have hkk := top_key hlow hmid x.2 (-(((x.1 : ℕ) : ℤ) + 1)) (by omega) (by omega)
        (by simpa [sub_eq_add_neg] using hx)
      refine ⟨hkk, ?_⟩
      have h3 := hct x.2 hkk
      have hl := hlow x.2
      rw [h3] at hl
      unfold InRange at hx
      rw [h3] at hx
      by_contra hcon
      apply hx
      constructor <;> omega
    have : (Finset.univ.filter fun dk : Fin D1 × Fin K =>
        ¬ InRange P N (cen p K k0 dk.2 - (((dk.1 : ℕ) : ℤ) + 1))).card ≤ (Finset.range u).card := by
      refine Finset.card_le_card_of_injOn (fun dk => dk.1.val) ?_ ?_
      · intro dk hdk
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hdk
        simp only [Finset.coe_range, Set.mem_Iio]
        exact (key dk hdk).2
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        have := a.2.isLt; have := b.2.isLt
        have h1 := (key a ha).1; have h2 := (key b hb).1
        exact Prod.ext (Fin.ext hab) (Fin.ext (by omega))
    simpa using this
  have h0 : (Finset.univ.filter fun k : Fin K => ¬ InRange P N (cen p K k0 k)).card ≤ 1 := by
    have key : ∀ x : Fin K, ¬ InRange P N (cen p K k0 x) → x.val + 1 = K := by
      intro x hx
      exact top_key (D1 := D1) hlow hmid x 0 (by omega) (by omega) (by simpa using hx)
    have : (Finset.univ.filter fun k : Fin K => ¬ InRange P N (cen p K k0 k)).card ≤
        (Finset.range 1).card := by
      refine Finset.card_le_card_of_injOn (fun k => 0) ?_ ?_
      · intro k hk; simp
      · intro a ha b hb _
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        exact Fin.ext (by have := key a ha; have := key b hb; omega)
    simpa using this
  omega

/-- Coverage, upper digit `hi`, lower digit `lo` (conditional on `T <= j % p`). -/
theorem cov1_gen {P : Parameters} {N p lo hi T : ℕ} (hp : 0 < p) (hlo : lo * p ≤ P.b N)
    (hhi : P.L N ≤ (hi + 2) * p) (hT : P.L N ≤ (hi + 1) * p + T) :
    ∀ j, P.b N ≤ j → j < P.L N → T ≤ j % p → j / p ∈ Finset.Icc lo hi := by
  intro j h1 h2 h3
  refine Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hp).mpr (hlo.trans h1), ?_⟩
  by_contra hc
  have hm : hi + 1 ≤ j / p := by omega
  have hm2 : j / p < hi + 2 := (Nat.div_lt_iff_lt_mul hp).mpr (lt_of_lt_of_le h2 hhi)
  have hm3 : j / p = hi + 1 := by omega
  have hd := Nat.div_add_mod j p
  rw [hm3] at hd
  have e : p * (hi + 1) = (hi + 1) * p := Nat.mul_comm _ _
  omega

theorem cov2_gen {P : Parameters} {N p lo' hi elo eta : ℕ} (hp : 0 < p) (hhi : P.L N ≤ (hi + 1) * p)
    (hlo : eta + lo' * p < P.b N + elo + p) :
    ∀ j, P.b N ≤ j → j < P.L N → j % p + elo + p ≤ eta → j / p ∈ Finset.Icc (lo' + 1) hi := by
  intro j h1 h2 h3
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · by_contra hc
    have hm : j / p ≤ lo' := by omega
    have hmul : p * (j / p) ≤ p * lo' := Nat.mul_le_mul_left p hm
    have hd := Nat.div_add_mod j p
    have e : p * lo' = lo' * p := Nat.mul_comm _ _
    omega
  · have : j / p < hi + 1 := (Nat.div_lt_iff_lt_mul hp).mpr (lt_of_lt_of_le h2 hhi)
    omega

/-- The closed form for a glue cell. -/
theorem glue_ge {P : Parameters} (hP : Admissible P) {N p : ℕ} (hp : p.Prime) (c : GlueCell)
    (hcop : Nat.Coprime p c.modulus) {D1 elo r1 u : ℕ} (hw : GlueWin P N p c D1 elo)
    (hlow : ∀ k : Fin c.K, -(P.g N : ℤ) ≤ cen p c.K c.k0 k - D1)
    (hmid : ∀ k : Fin c.K, k.val + 1 < c.K → cen p c.K c.k0 k + D1 < (P.n N : ℤ) - P.g N)
    (hr : r1 = 0 ∨ (r1 : ℤ) ≤ (P.n N : ℤ) - P.g N - cen p c.K c.k0 ⟨c.K - 1, by have := c.hky; omega⟩ - 1)
    (hu : cen p c.K c.k0 ⟨c.K - 1, by have := c.hky; omega⟩ - ((P.n N : ℤ) - P.g N) ≤ u) :
    (D1 + (D1 + 1)) - ((P.H N - 1 - c.s * p - p + 1) + elo) - ((D1 - r1) + u + 1) -
      (p - P.q N - (P.h N + (p - 1) / 2 - p)) ≤ (glueCellLB P hP c).kap N p := by
  have h := mtGlueVal1_le_glueCellLB P hP c hp hcop hw
  have hm := mixMiss_le_top (P := P) (N := N) (p := p) (K := c.K) (D1 := D1) (r1 := r1) (u := u)
    (k0 := c.k0) (by have := c.hky; omega) hlow hmid hr hu
  refine le_trans ?_ h
  unfold mtGlueVal1
  omega

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
