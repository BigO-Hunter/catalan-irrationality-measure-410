module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyLB

@[expose] public section
set_option Elab.async false

/-!
# Certified windows for Family M (HY+, `s = 10`) (lane G5g)

Window `Dn = g - (p-1)/2`, `K = 9`, `k0 = -1`.  On `6.9 N < p <= 7.06 N`:
* `hyMiss <= Dn - r` (only the hi side of the top block can fall outside the rows),
* the edge set is empty (digits `J <= 9` are good; the `J = 10` digits satisfy `L + emax <= eta + 10 p + 1`),
so `hyVal = p - 6N` for `p <= 7N` and `64 N - 9 p` for `p >= 7N` up to `O(1)`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

/-- Missing rows: only the hi side of the top block can be missing. -/
theorem hyMiss_le_top {P : Parameters} {N p K Dn r : ℕ} [Fact p.Prime] {k0 : ℤ}
    (hlo' : ∀ (t : Fin Dn) (k : Fin K), InRange P N (hlo p K k0 k t))
    (hhi' : ∀ (t : Fin Dn) (k : Fin K), (k.val + 1 < K ∨ t.val < r) → InRange P N (hhi p K k0 k t)) :
    hyMiss P N p K Dn k0 ≤ Dn - r := by
  unfold hyMiss
  have h0 : (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro tk _; exact not_not.mpr (hlo' tk.1 tk.2)
  rw [h0, zero_add]
  have : (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)).card ≤
      (Finset.range (Dn - r)).card := by
    refine Finset.card_le_card_of_injOn (fun tk => tk.1.val - r) ?_ ?_
    · intro tk htk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at htk
      have hn : ¬ (tk.2.val + 1 < K ∨ tk.1.val < r) := fun h => htk (hhi' tk.1 tk.2 h)
      have := tk.1.isLt
      simp only [Finset.coe_range, Set.mem_Iio]
      push_neg at hn
      omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      have hna : ¬ (a.2.val + 1 < K ∨ a.1.val < r) := fun h => ha (hhi' a.1 a.2 h)
      have hnb : ¬ (b.2.val + 1 < K ∨ b.1.val < r) := fun h => hb (hhi' b.1 b.2 h)
      push_neg at hna hnb
      have := a.2.isLt; have := b.2.isLt
      refine Prod.ext (Fin.ext (by simp only at hab; omega)) (Fin.ext (by omega))
  simpa using this

/-- The edge set is empty for `s = 10` under the displayed inequalities. -/
theorem edgeSet_empty10 {P : Parameters} {N p a0 nQ η Dn : ℕ}
    (hb : p ≤ P.b N) (hη : η < P.b N) (hLe : P.L N + (P.h N + (p - 1) / 2 + Dn) ≤ η + 10 * p + 1)
    (hL : P.L N ≤ 11 * p) (hq : a0 + nQ + p = P.h N + (p - 1) / 2 + Dn) :
    edgeSet P N p a0 nQ 10 η Dn = ∅ := by
  unfold edgeSet
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨l, J⟩ hmem ⟨h1, h2, hbad⟩
  simp only [Finset.mem_product, Finset.mem_range] at hmem h1 h2
  have hl : l < p := hmem.1
  unfold HyBad at hbad
  rcases Nat.lt_or_ge J 11 with hJ | hJ
  · interval_cases J <;> omega
  · have := Nat.mul_le_mul_right p hJ
    omega

/-- Nullity bound `hyTermG` at `s = 10` is below `mLB'`. -/
theorem hyTermG10_le (hP : Admissible design) {N p Dn : ℕ} (hDn : Dn < p) :
    hyTermG design N p 10 9 ZHY10 Dn ≤ (mLB' design hP).kap N p := by
  have h1 : hyTermG design N p 10 9 ZHY10 Dn ≤ hyKapS design N p 10 9 ZHY10 :=
    Finset.le_sup (f := fun Dn => hyTermG design N p 10 9 ZHY10 Dn) (Finset.mem_range.mpr hDn)
  have h2 : hyKapS design N p 10 9 ZHY10 ≤ hyKap design N p :=
    le_max_of_le_right (le_max_left _ _)
  have h3 : (mLB' design hP).kap N p = hyKap design N p := by
    simp [mLB', NullityLB.ofWindow]
  rw [h3]; exact h1.trans h2

theorem not_dvd_ZHY10 {N p : ℕ} (hN : ZHY10 ≤ N) (hp : N < p) : ¬ p ∣ ZHY10 := fun h =>
  absurd (Nat.le_of_dvd ZHY10_pos h) (by omega)

/-- Lower bound for the HY+ value at the window `Dn = g - (p-1)/2`, as a sum of explicit terms. -/
theorem mval_core {N p : ℕ} [Fact p.Prime] (hZ : ZHY10 ≤ N) (hN : 1000 ≤ N) (h1 : 69 * N < 10 * p)
    (h2 : 100 * p ≤ 706 * N) :
    (2 * (5 * N - (p - 1) / 2) + (8 * N - p)) -
      ((5 * N - (p - 1) / 2) - (53 * N - 7 * p - (p - 1) / 2 - 1) + (78 * N - 11 * p) +
        (10 * p - 70 * N) + (p - 6 * N)) ≤ (mLB' design adm).kap N p := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hnum : HYNum design N p 10 (5 * N - (p - 1) / 2) := by
    unfold HYNum hyEta hyEmax hyA0
    des_unfold
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hnd : ¬ p ∣ ZHY10 := not_dvd_ZHY10 hZ (by omega)
  have hterm : hyTermG design N p 10 9 ZHY10 (5 * N - (p - 1) / 2) =
      hyVal design N p 10 9 (5 * N - (p - 1) / 2) (-1) := by
    unfold hyTermG
    rw [dif_pos (Fact.out : p.Prime)]
    rw [if_pos ⟨hp2, hnum, by des_unfold; omega, hnd⟩]
  have hle := hyTermG10_le adm (N := N) (p := p) (Dn := 5 * N - (p - 1) / 2) (by omega)
  rw [hterm] at hle
  refine le_trans ?_ hle
  have hm : hyMiss design N p 9 (5 * N - (p - 1) / 2) (-1) ≤
      (5 * N - (p - 1) / 2) - (53 * N - 7 * p - (p - 1) / 2 - 1) := by
    refine hyMiss_le_top ?_ ?_
    · intro t k
      have hk := k.isLt
      have c1 : (-1 : ℤ) * p ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
        have : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have c2 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 7 * p := by
        have : ((k : ℕ) : ℤ) ≤ 8 := by exact_mod_cast (by omega : (k : ℕ) ≤ 8)
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have ht := t.isLt
      unfold InRange hlo cen hh
      des_unfold
      push_cast
      omega
    · intro t k hk'
      have hk := k.isLt
      have c1 : (-1 : ℤ) * p ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
        have : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have c2 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 7 * p := by
        have : ((k : ℕ) : ℤ) ≤ 8 := by exact_mod_cast (by omega : (k : ℕ) ≤ 8)
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have ht := t.isLt
      unfold InRange hhi cen hh
      des_unfold
      push_cast
      rcases hk' with hk'' | hk''
      · have : ((k : ℕ) : ℤ) ≤ 7 := by exact_mod_cast (by omega : (k : ℕ) ≤ 7)
        have c3 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 6 * p := by
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        omega
      · omega
  have he : (edgeSet design N p (hyA0 design N p) (hyNQ design N p (5 * N - (p - 1) / 2)) 10
      (hyEta design N p 10) (5 * N - (p - 1) / 2)) = ∅ := by
    refine edgeSet_empty10 ?_ ?_ ?_ ?_ ?_
    · des_unfold; omega
    · unfold hyEta; des_unfold; omega
    · unfold hyEta; des_unfold; omega
    · des_unfold; omega
    · unfold hyNQ hyEmax hyA0; des_unfold; omega
  unfold hyVal hyConds
  rw [he, Finset.card_empty]
  have hNQ : hyNQ design N p (5 * N - (p - 1) / 2) = 8 * N - p := by
    unfold hyNQ hyEmax hyA0; des_unfold; omega
  have hE : hyEta design N p 10 + 1 - p = 78 * N - 11 * p := by unfold hyEta; des_unfold; omega
  have hEm : hyEmax design N p (5 * N - (p - 1) / 2) - (hyEta design N p 10 + 1) = 10 * p - 70 * N := by
    unfold hyEta hyEmax; des_unfold; omega
  have hF : hyF design N p = p - 6 * N := by unfold hyF; des_unfold; omega
  rw [hNQ, hE, hEm, hF]
  omega

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
