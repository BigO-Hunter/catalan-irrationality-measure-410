module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.MWins
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyLB

@[expose] public section
set_option Elab.async false

/-!
# Certified windows for HY+ at `s = 11` (lane G6)

Window `Dn = g - (p-1)/2`, `K = 10`, `k0 = -1`, on `6.2728 N < p <= 6.4 N`:
* the top block (`k = 9`, centre `8p`) is the only one with rows outside the range:
  `hi` for every `t`, `lo` for `t <= 8p + (p-1)/2 - 53 N`; so `hyMiss <= Dn + (8p + (p-1)/2 + 1 - 53 N)`,
* the edge set is empty (`J <= 11`, tight at `J = 10, 11`),
so `hyVal = p - 6N` for `11 p <= 70 N` and `64 N - 10 p` for `11 p >= 70 N` up to `O(1)`
(idealised content `17/440`; the part `6.25 .. 69/11` with a nonempty edge set is not taken).
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

/-- Missing rows when only the top block is affected on both sides. -/
theorem hyMiss_le_top2 {P : Parameters} {N p K Dn rlo : ℕ} [Fact p.Prime] {k0 : ℤ}
    (hlo' : ∀ (t : Fin Dn) (k : Fin K), (k.val + 1 < K ∨ rlo ≤ t.val) → InRange P N (hlo p K k0 k t))
    (hhi' : ∀ (t : Fin Dn) (k : Fin K), k.val + 1 < K → InRange P N (hhi p K k0 k t)) :
    hyMiss P N p K Dn k0 ≤ rlo + Dn := by
  unfold hyMiss
  have h1 : (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)).card ≤
      (Finset.range rlo).card := by
    refine Finset.card_le_card_of_injOn (fun tk => tk.1.val) ?_ ?_
    · intro tk htk
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at htk
      have hn : ¬ (tk.2.val + 1 < K ∨ rlo ≤ tk.1.val) := fun h => htk (hlo' tk.1 tk.2 h)
      push_neg at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      have hna : ¬ (a.2.val + 1 < K ∨ rlo ≤ a.1.val) := fun h => ha (hlo' a.1 a.2 h)
      have hnb : ¬ (b.2.val + 1 < K ∨ rlo ≤ b.1.val) := fun h => hb (hlo' b.1 b.2 h)
      push_neg at hna hnb
      have := a.2.isLt; have := b.2.isLt
      refine Prod.ext (Fin.ext (by simpa using hab)) (Fin.ext (by omega))
  have h2 : (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)).card ≤
      (Finset.range Dn).card := by
    refine Finset.card_le_card_of_injOn (fun tk => tk.1.val) ?_ ?_
    · intro tk htk
      simp only [Finset.coe_range, Set.mem_Iio]
      exact tk.1.isLt
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      have hna : ¬ (a.2.val + 1 < K) := fun h => ha (hhi' a.1 a.2 h)
      have hnb : ¬ (b.2.val + 1 < K) := fun h => hb (hhi' b.1 b.2 h)
      push_neg at hna hnb
      have := a.2.isLt; have := b.2.isLt
      refine Prod.ext (Fin.ext (by simpa using hab)) (Fin.ext (by omega))
  simp only [Finset.card_range] at h1 h2
  omega

/-- The edge set is empty for `s = 11`. -/
theorem edgeSet_empty11 {N p : ℕ} (h1 : 69 * N < 11 * p) (h2 : 5 * p ≤ 32 * N) :
    edgeSet design N p (hyA0 design N p) (hyNQ design N p (5 * N - (p - 1) / 2)) 11
      (hyEta design N p 11) (5 * N - (p - 1) / 2) = ∅ := by
  unfold edgeSet
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨l, J⟩ hmem ⟨hb1, hb2, hbad⟩
  simp only [Finset.mem_product, Finset.mem_range] at hmem hb1 hb2
  have hl : l < p := hmem.1
  unfold HyBad at hbad
  unfold hyEta hyA0 hyNQ hyEmax at hbad
  des_unfold at hbad hb1 hb2
  rcases Nat.lt_or_ge J 12 with hJ | hJ
  · interval_cases J <;> omega
  · have := Nat.mul_le_mul_right p hJ
    omega

theorem hyTermG11_le (hP : Admissible design) {N p Dn : ℕ} (hDn : Dn < p) :
    hyTermG design N p 11 10 ZHY11 Dn ≤ (mLB' design hP).kap N p := by
  have h1 : hyTermG design N p 11 10 ZHY11 Dn ≤ hyKapS design N p 11 10 ZHY11 :=
    Finset.le_sup (f := fun Dn => hyTermG design N p 11 10 ZHY11 Dn) (Finset.mem_range.mpr hDn)
  have h2 : hyKapS design N p 11 10 ZHY11 ≤ hyKap design N p :=
    le_max_of_le_right (le_max_right _ _)
  have h3 : (mLB' design hP).kap N p = hyKap design N p := by
    simp [mLB', NullityLB.ofWindow]
  rw [h3]; exact h1.trans h2

theorem not_dvd_ZHY11 {N p : ℕ} (hN : ZHY11 ≤ N) (hp : N < p) : ¬ p ∣ ZHY11 := fun h =>
  absurd (Nat.le_of_dvd ZHY11_pos h) (by omega)

/-- Lower bound for the HY+ value at the window `Dn = g - (p-1)/2`, `s = 11`. -/
theorem hy11_core {N p : ℕ} [Fact p.Prime] (hZ : ZHY11 ≤ N) (hN : 1000 ≤ N) (h1 : 69 * N < 11 * p)
    (h2 : 5 * p ≤ 32 * N) :
    (2 * (5 * N - (p - 1) / 2) + (8 * N - p)) -
      (((5 * N - (p - 1) / 2) + (8 * p + (p - 1) / 2 + 1 - 53 * N)) + (78 * N - 12 * p) +
        (11 * p - 70 * N) + (p - 6 * N)) ≤ (mLB' design adm).kap N p := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hnum : HYNum design N p 11 (5 * N - (p - 1) / 2) := by
    unfold HYNum hyEta hyEmax hyA0
    des_unfold
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hnd : ¬ p ∣ ZHY11 := not_dvd_ZHY11 hZ (by omega)
  have hterm : hyTermG design N p 11 10 ZHY11 (5 * N - (p - 1) / 2) =
      hyVal design N p 11 10 (5 * N - (p - 1) / 2) (-1) := by
    unfold hyTermG
    rw [dif_pos (Fact.out : p.Prime)]
    rw [if_pos ⟨hp2, hnum, by des_unfold; omega, hnd⟩]
  have hle := hyTermG11_le adm (N := N) (p := p) (Dn := 5 * N - (p - 1) / 2) (by omega)
  rw [hterm] at hle
  refine le_trans ?_ hle
  have hm : hyMiss design N p 10 (5 * N - (p - 1) / 2) (-1) ≤
      (8 * p + (p - 1) / 2 + 1 - 53 * N) + (5 * N - (p - 1) / 2) := by
    refine hyMiss_le_top2 ?_ ?_
    · intro t k hk'
      have hk := k.isLt
      have c1 : (-1 : ℤ) * p ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
        have : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have c2 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 8 * p := by
        have : ((k : ℕ) : ℤ) ≤ 9 := by exact_mod_cast (by omega : (k : ℕ) ≤ 9)
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have ht := t.isLt
      unfold InRange hlo cen hh
      des_unfold
      push_cast
      rcases hk' with hk'' | hk''
      · have c3 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 7 * p := by
          have : ((k : ℕ) : ℤ) ≤ 8 := by exact_mod_cast (by omega : (k : ℕ) ≤ 8)
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        omega
      · omega
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
      omega
  have he : (edgeSet design N p (hyA0 design N p) (hyNQ design N p (5 * N - (p - 1) / 2)) 11
      (hyEta design N p 11) (5 * N - (p - 1) / 2)) = ∅ := edgeSet_empty11 h1 h2
  unfold hyVal hyConds
  rw [he, Finset.card_empty]
  have hNQ : hyNQ design N p (5 * N - (p - 1) / 2) = 8 * N - p := by
    unfold hyNQ hyEmax hyA0; des_unfold; omega
  have hE : hyEta design N p 11 + 1 - p = 78 * N - 12 * p := by unfold hyEta; des_unfold; omega
  have hEm : hyEmax design N p (5 * N - (p - 1) / 2) - (hyEta design N p 11 + 1) = 11 * p - 70 * N := by
    unfold hyEta hyEmax; des_unfold; omega
  have hF : hyF design N p = p - 6 * N := by unfold hyF; des_unfold; omega
  rw [hNQ, hE, hEm, hF]
  omega

theorem hy11_cell2 {N p : ℕ} (hp : p.Prime) (hZ : ZHY11 ≤ N) (hN : 1000 ≤ N) (h1 : 69 * N < 11 * p)
    (h2 : 11 * p ≤ 70 * N) :
    (-6 : ℤ) * N + 1 * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := hy11_core hZ hN h1 (by omega)
  omega

theorem hy11_cell3 {N p : ℕ} (hp : p.Prime) (hZ : ZHY11 ≤ N) (hN : 1000 ≤ N) (h1 : 70 * N < 11 * p)
    (h2 : 5 * p ≤ 32 * N) :
    (64 : ℤ) * N + (-10) * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := hy11_core (p := p) hZ hN (by omega) h2
  omega

/-- The two `s = 11` windows. -/
def hy11Wins : List KapWindow :=
  [cw (69 / 11 : ℝ) (70 / 11 : ℝ) (-6 : ℝ) (1 : ℝ),
   cw (70 / 11 : ℝ) (32 / 5 : ℝ) (64 : ℝ) (-10 : ℝ)]

theorem hy11Wins_cert : ∀ w ∈ hy11Wins, WinCert (mLB' design adm) w := by
  intro w hw
  simp only [hy11Wins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact wincert_cw (mLB' design adm) (na := 69) (da := 11) (nb := 70) (db := 11) (A := -6) (B := 1)
      (d := 1) (N0 := ZHY11 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY11 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact hy11_cell2 hp hZ h1000 h1 h2
  · exact wincert_cw (mLB' design adm) (na := 70) (da := 11) (nb := 32) (db := 5) (A := 64) (B := -10)
      (d := 1) (N0 := ZHY11 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY11 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact hy11_cell3 hp hZ h1000 h1 h2

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
