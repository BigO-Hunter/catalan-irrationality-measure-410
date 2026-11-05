module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger6.Merge7

@[expose] public section
set_option Elab.async false

/-!
# HY+ `s = 10`: flank window `K = 64 - 9 x` on `(106/15, 78/11]` (lane G6)

Same window as `Ledger4.MWins` (`Dn = g - (p-1)/2`, `K = 9`), but above `7.0667` the top block also loses
its lo rows (`t <= 7p + (p-1)/2 - 53 N`), so `hyMiss <= Dn + rlo`; the limit `78/11` is the numerical
hypothesis `p <= eta`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger6
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

/-- Lower bound for the HY+ value at the window `Dn = g - (p-1)/2`, `s = 10`, above `7.0667`. -/
theorem hy10_core {N p : ℕ} [Fact p.Prime] (hZ : ZHY10 ≤ N) (hN : 1000 ≤ N) (h1 : 106 * N < 15 * p)
    (h2 : 11 * p ≤ 78 * N) :
    (2 * (5 * N - (p - 1) / 2) + (8 * N - p)) -
      (((5 * N - (p - 1) / 2) + (7 * p + (p - 1) / 2 + 1 - 53 * N)) + (78 * N - 11 * p) +
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
      (7 * p + (p - 1) / 2 + 1 - 53 * N) + (5 * N - (p - 1) / 2) := by
    refine hyMiss_le_top2 ?_ ?_
    · intro t k hk'
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
      rcases hk' with hk'' | hk''
      · have c3 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 6 * p := by
          have : ((k : ℕ) : ℤ) ≤ 7 := by exact_mod_cast (by omega : (k : ℕ) ≤ 7)
          nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
        omega
      · omega
    · intro t k hk'
      have hk := k.isLt
      have c1 : (-1 : ℤ) * p ≤ ((-1 : ℤ) + (k : ℕ)) * p := by
        have : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have c3 : ((-1 : ℤ) + (k : ℕ)) * p ≤ 6 * p := by
        have : ((k : ℕ) : ℤ) ≤ 7 := by exact_mod_cast (by omega : (k : ℕ) ≤ 7)
        nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
      have ht := t.isLt
      unfold InRange hhi cen hh
      des_unfold
      push_cast
      omega
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

theorem hy10_cell {N p : ℕ} (hp : p.Prime) (hZ : ZHY10 ≤ N) (hN : 1000 ≤ N) (h1 : 106 * N < 15 * p)
    (h2 : 11 * p ≤ 78 * N) :
    (64 : ℤ) * N + (-9) * p ≤ 1 * (((mLB' design adm).kap N p : ℕ) + 2 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := hy10_core hZ hN h1 h2
  omega

def hy10Wins : List KapWindow := [cw (106 / 15 : ℝ) (78 / 11 : ℝ) (64 : ℝ) (-9 : ℝ)]

theorem hy10Wins_cert : ∀ w ∈ hy10Wins, WinCert (mLB' design adm) w := by
  intro w hw
  simp only [hy10Wins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl
  exact wincert_cw (mLB' design adm) (na := 106) (da := 15) (nb := 78) (db := 11) (A := 64) (B := -9)
      (d := 1) (N0 := ZHY10 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => by
        have hZ : ZHY10 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
        have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
        clear hN
        exact hy10_cell hp hZ h1000 h1 h2

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger6
