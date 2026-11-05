module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY11

@[expose] public section
set_option Elab.async false

/-!
# Certified windows for HY+ at `s = 9` (lane G6)

Window `Dn = (150 N + 1 - 19 p) / 2` (so that `emax = eta + 1`, `Em = 0`), `K = 8`, `k0 = -1`,
on `53/7 N < p <= 54/7 N`:
* `nQ = E = 78 N - 10 p`, `F = p - 6 N`,
* missing rows: only the lo side of the bottom block, `t >= 5N - p + (p-1)/2 + 1`: `miss <= 70 N - 9 p`,
* edges: `J = 9` with `l < 70 N - 9 p` and `J = 1` with `9N - p <= l < 78N - 10p`:
  `|edges| <= (70 N - 9 p) + (69 N - 9 p)`,
so `hyVal = 7 p - 53 N` for `9 p <= 69 N` and `16 N - 2 p` for `9 p >= 69 N`, up to `O(1)`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

/-- Missing rows when only the lo side of the bottom block is affected. -/
theorem hyMiss_le_bot {P : Parameters} {N p K Dn rlo : ℕ} [Fact p.Prime] {k0 : ℤ}
    (hlo' : ∀ (t : Fin Dn) (k : Fin K), (0 < k.val ∨ t.val < rlo) → InRange P N (hlo p K k0 k t))
    (hhi' : ∀ (t : Fin Dn) (k : Fin K), InRange P N (hhi p K k0 k t)) :
    hyMiss P N p K Dn k0 ≤ Dn - rlo := by
  unfold hyMiss
  have h0 : (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro tk _; exact not_not.mpr (hhi' tk.1 tk.2)
  rw [h0, add_zero]
  have : (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)).card ≤
      (Finset.range (Dn - rlo)).card := by
    refine Finset.card_le_card_of_injOn (fun tk => tk.1.val - rlo) ?_ ?_
    · intro tk htk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at htk
      have hn : ¬ (0 < tk.2.val ∨ tk.1.val < rlo) := fun h => htk (hlo' tk.1 tk.2 h)
      have := tk.1.isLt
      simp only [Finset.coe_range, Set.mem_Iio]
      push_neg at hn
      omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      have hna : ¬ (0 < a.2.val ∨ a.1.val < rlo) := fun h => ha (hlo' a.1 a.2 h)
      have hnb : ¬ (0 < b.2.val ∨ b.1.val < rlo) := fun h => hb (hlo' b.1 b.2 h)
      push_neg at hna hnb
      refine Prod.ext (Fin.ext (by simp only at hab; omega)) (Fin.ext (by omega))
  simpa using this

/-- Shape of the edge set for `s = 9`. -/
theorem edge_shape9 {N p l J : ℕ} (hodd : p % 2 = 1) (h1 : 53 * N < 7 * p) (h2 : 7 * p ≤ 54 * N)
    (hl : l < p)
    (hm : (l, J) ∈ edgeSet design N p (hyA0 design N p)
      (hyNQ design N p ((150 * N + 1 - 19 * p) / 2)) 9 (hyEta design N p 9) ((150 * N + 1 - 19 * p) / 2)) :
    (J = 9 ∧ 9 * p + l < 70 * N) ∨ (J = 1 ∧ 9 * N ≤ p + l ∧ l + p < 78 * N - 9 * p) := by
  unfold edgeSet at hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨_, hb1, hb2, hbad⟩ := hm
  unfold HyBad at hbad
  unfold hyEta hyA0 hyNQ hyEmax at hbad
  des_unfold at hbad hb1 hb2
  rcases Nat.lt_or_ge J 10 with hJ | hJ
  · interval_cases J <;> omega
  · have := Nat.mul_le_mul_right p hJ
    omega

theorem edgeCard9 {N p : ℕ} (hodd : p % 2 = 1) (h1 : 53 * N < 7 * p) (h2 : 7 * p ≤ 54 * N) :
    (edgeSet design N p (hyA0 design N p) (hyNQ design N p ((150 * N + 1 - 19 * p) / 2)) 9
      (hyEta design N p 9) ((150 * N + 1 - 19 * p) / 2)).card ≤
      (70 * N - 9 * p) + (69 * N - 9 * p) := by
  have hsub : edgeSet design N p (hyA0 design N p) (hyNQ design N p ((150 * N + 1 - 19 * p) / 2)) 9
      (hyEta design N p 9) ((150 * N + 1 - 19 * p) / 2) ⊆
      (Finset.range (70 * N - 9 * p)).image (fun l => (l, 9)) ∪
        (Finset.Ico (9 * N - p) (78 * N - 10 * p)).image (fun l => (l, 1)) := by
    rintro ⟨l, J⟩ hm
    have hl : l < p := by
      unfold edgeSet at hm
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      exact hm.1.1
    rcases edge_shape9 hodd h1 h2 hl hm with ⟨rfl, h⟩ | ⟨rfl, ha, hb⟩
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
      left; exact ⟨l, by omega, rfl⟩
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico]
      right; exact ⟨l, ⟨by omega, by omega⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ?_ ?_
  · exact Finset.card_image_le.trans (by simp)
  · refine Finset.card_image_le.trans ?_
    simp only [Nat.card_Ico]
    omega

theorem hyTermG9_le (hP : Admissible design) {N p Dn : ℕ} (hDn : Dn < p) :
    hyTermG design N p 9 8 ZHY9 Dn ≤ (mLB' design hP).kap N p := by
  have h1 : hyTermG design N p 9 8 ZHY9 Dn ≤ hyKapS design N p 9 8 ZHY9 :=
    Finset.le_sup (f := fun Dn => hyTermG design N p 9 8 ZHY9 Dn) (Finset.mem_range.mpr hDn)
  have h2 : hyKapS design N p 9 8 ZHY9 ≤ hyKap design N p := le_max_left _ _
  have h3 : (mLB' design hP).kap N p = hyKap design N p := by
    simp [mLB', NullityLB.ofWindow]
  rw [h3]; exact h1.trans h2

theorem not_dvd_ZHY9 {N p : ℕ} (hN : ZHY9 ≤ N) (hp : N < p) : ¬ p ∣ ZHY9 := fun h =>
  absurd (Nat.le_of_dvd ZHY9_pos h) (by omega)

/-- Lower bound for the HY+ value at the window `Dn = (150 N + 1 - 19 p)/2`, `s = 9`. -/
theorem hy9_core {N p : ℕ} [Fact p.Prime] (hZ : ZHY9 ≤ N) (hN : 1000 ≤ N) (h1 : 53 * N < 7 * p)
    (h2 : 7 * p ≤ 54 * N) :
    (2 * ((150 * N + 1 - 19 * p) / 2) + (78 * N - 10 * p)) -
      ((70 * N - 9 * p) + (78 * N - 10 * p) + 0 + (p - 6 * N) + ((70 * N - 9 * p) + (69 * N - 9 * p))) ≤
      (mLB' design adm).kap N p := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hnum : HYNum design N p 9 ((150 * N + 1 - 19 * p) / 2) := by
    unfold HYNum hyEta hyEmax hyA0
    des_unfold
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hnd : ¬ p ∣ ZHY9 := not_dvd_ZHY9 hZ (by omega)
  have hterm : hyTermG design N p 9 8 ZHY9 ((150 * N + 1 - 19 * p) / 2) =
      hyVal design N p 9 8 ((150 * N + 1 - 19 * p) / 2) (-1) := by
    unfold hyTermG
    rw [dif_pos (Fact.out : p.Prime)]
    rw [if_pos ⟨hp2, hnum, by des_unfold; omega, hnd⟩]
  have hle := hyTermG9_le adm (N := N) (p := p) (Dn := (150 * N + 1 - 19 * p) / 2) (by omega)
  rw [hterm] at hle
  refine le_trans ?_ hle
  have hm : hyMiss design N p 8 ((150 * N + 1 - 19 * p) / 2) (-1) ≤ 70 * N - 9 * p := by
    have key : hyMiss design N p 8 ((150 * N + 1 - 19 * p) / 2) (-1) ≤
        (150 * N + 1 - 19 * p) / 2 - (5 * N + (p - 1) / 2 + 1 - p) := by
      refine hyMiss_le_bot ?_ ?_
      · intro t k hk'
        have hk := k.isLt
        have c1 : (-1 : ℤ) * p ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
          have : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        have c2 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 6 * p := by
          have : ((k : ℕ) : ℤ) ≤ 7 := by exact_mod_cast (by omega : (k : ℕ) ≤ 7)
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        have ht := t.isLt
        unfold InRange hlo cen hh
        des_unfold
        push_cast
        rcases hk' with hk'' | hk''
        · have c0 : (0 : ℤ) ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
            have : (1 : ℤ) ≤ (k : ℕ) := by exact_mod_cast hk''
            nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
          omega
        · omega
      · intro t k
        have hk := k.isLt
        have c2 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 6 * p := by
          have : ((k : ℕ) : ℤ) ≤ 7 := by exact_mod_cast (by omega : (k : ℕ) ≤ 7)
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        have c1 : (-1 : ℤ) * p ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
          have : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        have ht := t.isLt
        unfold InRange hhi cen hh
        des_unfold
        push_cast
        omega
    omega
  have he := edgeCard9 (N := N) (p := p) hodd h1 h2
  unfold hyVal hyConds
  have hNQ : hyNQ design N p ((150 * N + 1 - 19 * p) / 2) = 78 * N - 10 * p := by
    unfold hyNQ hyEmax hyA0; des_unfold; omega
  have hE : hyEta design N p 9 + 1 - p = 78 * N - 10 * p := by unfold hyEta; des_unfold; omega
  have hEm : hyEmax design N p ((150 * N + 1 - 19 * p) / 2) - (hyEta design N p 9 + 1) = 0 := by
    unfold hyEta hyEmax; des_unfold; omega
  have hF : hyF design N p = p - 6 * N := by unfold hyF; des_unfold; omega
  rw [hNQ] at he
  rw [hNQ, hE, hEm, hF]
  omega

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
