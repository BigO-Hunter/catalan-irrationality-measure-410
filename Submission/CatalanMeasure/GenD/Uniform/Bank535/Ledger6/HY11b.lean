module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.HY11

@[expose] public section
set_option Elab.async false

/-!
# HY+ `s = 11`: the window with a nonempty edge set, `K = 12 x - 75` on `(6.25, 69/11]` (lane G6)

For `p <= 69 N / 11` the edge set is the single digit `J = 1`, `9N - p <= l <= eta - p`,
of size `69 N - 11 p`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

theorem edge_shape11 {N p l J : ℕ} (hodd : p % 2 = 1) (h1 : 25 * N < 4 * p) (h2 : 5 * p ≤ 32 * N)
    (hl : l < p)
    (hm : (l, J) ∈ edgeSet design N p (hyA0 design N p) (hyNQ design N p (5 * N - (p - 1) / 2)) 11
      (hyEta design N p 11) (5 * N - (p - 1) / 2)) :
    J = 1 ∧ 9 * N ≤ p + l ∧ l + p < 78 * N - 11 * p := by
  unfold edgeSet at hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨_, hb1, hb2, hbad⟩ := hm
  unfold HyBad at hbad
  unfold hyEta hyA0 hyNQ hyEmax at hbad
  des_unfold at hbad hb1 hb2
  rcases Nat.lt_or_ge J 12 with hJ | hJ
  · interval_cases J <;> omega
  · have := Nat.mul_le_mul_right p hJ
    omega

theorem edgeCard11 {N p : ℕ} (hodd : p % 2 = 1) (h1 : 25 * N < 4 * p) (h2 : 5 * p ≤ 32 * N) :
    (edgeSet design N p (hyA0 design N p) (hyNQ design N p (5 * N - (p - 1) / 2)) 11
      (hyEta design N p 11) (5 * N - (p - 1) / 2)).card ≤ 69 * N - 11 * p := by
  have hsub : edgeSet design N p (hyA0 design N p) (hyNQ design N p (5 * N - (p - 1) / 2)) 11
      (hyEta design N p 11) (5 * N - (p - 1) / 2) ⊆
      (Finset.Ico (9 * N - p) (78 * N - 12 * p)).image (fun l => (l, 1)) := by
    rintro ⟨l, J⟩ hm
    have hl : l < p := by
      unfold edgeSet at hm
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      exact hm.1.1
    obtain ⟨rfl, ha, hb⟩ := edge_shape11 hodd h1 h2 hl hm
    simp only [Finset.mem_image, Finset.mem_Ico]
    exact ⟨l, ⟨by omega, by omega⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp only [Nat.card_Ico]
  omega

/-- Lower bound for the HY+ value at the window `Dn = g - (p-1)/2`, `s = 11`. -/
theorem hy11b_core {N p : ℕ} [Fact p.Prime] (hZ : ZHY11 ≤ N) (hN : 1000 ≤ N) (h1 : 25 * N < 4 * p)
    (h2 : 5 * p ≤ 32 * N) :
    (2 * (5 * N - (p - 1) / 2) + (8 * N - p)) -
      (((5 * N - (p - 1) / 2) + (8 * p + (p - 1) / 2 + 1 - 53 * N)) + (78 * N - 12 * p) +
        (11 * p - 70 * N) + (p - 6 * N) + (69 * N - 11 * p)) ≤ (mLB' design adm).kap N p := by
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
  have he := edgeCard11 (N := N) (p := p) hodd h1 h2
  unfold hyVal hyConds
  have hNQ : hyNQ design N p (5 * N - (p - 1) / 2) = 8 * N - p := by
    unfold hyNQ hyEmax hyA0; des_unfold; omega
  have hE : hyEta design N p 11 + 1 - p = 78 * N - 12 * p := by unfold hyEta; des_unfold; omega
  have hEm : hyEmax design N p (5 * N - (p - 1) / 2) - (hyEta design N p 11 + 1) = 11 * p - 70 * N := by
    unfold hyEta hyEmax; des_unfold; omega
  have hF : hyF design N p = p - 6 * N := by unfold hyF; des_unfold; omega
  rw [hNQ] at he
  rw [hNQ, hE, hEm, hF]
  omega


theorem hy11b_cell {N p : ℕ} (hp : p.Prime) (hZ : ZHY11 ≤ N) (hN : 1000 ≤ N) (h1 : 25 * N < 4 * p)
    (h2 : 11 * p ≤ 69 * N) :
    (-75 : ℤ) * N + 12 * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := hy11b_core hZ hN h1 (by omega)
  omega

def hy11bWins : List KapWindow := [cw (25 / 4 : ℝ) (69 / 11 : ℝ) (-75 : ℝ) (12 : ℝ)]

theorem hy11bWins_cert : ∀ w ∈ hy11bWins, WinCert (mLB' design adm) w := by
  intro w hw
  simp only [hy11bWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl
  exact wincert_cw (mLB' design adm) (na := 25) (da := 4) (nb := 69) (db := 11) (A := -75) (B := 12)
      (d := 1) (N0 := ZHY11 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY11 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact hy11b_cell hp hZ h1000 h1 h2

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
