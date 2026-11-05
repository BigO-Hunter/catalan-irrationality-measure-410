module

public import Submission.CatalanMeasure.GenD.Uniform.W.Tier3.HP2LB
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger2.CellsHP2
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win

@[expose] public section
set_option Elab.async false

/-!
# HP2 window cells (lane G6): `s = 9`, blocks `(-1, 6)`, period slot at the window pair `(8, 9)`

* `hp2A_cell` : `K = 19x/2 - 73` on `(148/19 + 1e-4, 39/5 - 1e-4]` with `ilo = 78 N - 10 p = e0`;
* `hp2B_cell` : `K = 83 - 21x/2` on `(7.8001, 7.8946]` with `ilo = 0`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger7
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Tier3
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4 CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

theorem hp2A_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 77896 * N < 10000 * p)
    (h2 : 10000 * p ≤ 77999 * N) :
    (-146 : ℤ) * N + (19) * p ≤ 2 * ((hp2Kap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hp2Kap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6)
    (ilo := (78 * N - 10 * p)) (cH := 8) (cP := 7) (mH := 1) (mP := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 5 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (Or.inr (by unfold hpEta; des_unfold; omega))
    (by
      refine le_trans (interval_card (lo := 1) (hi := 8) ?_) (by norm_num)
      intro x hx
      simp only [hpJJ, Finset.mem_filter] at hx
      unfold hpDD hpJstar hpElo hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 9 ≤ x by omega)
        omega)
    (by
      refine le_trans (interval_card (lo := 1) (hi := 7) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 8 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hp2Kap design N p = K at key ⊢
  unfold perPmax perD0 hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem hp2B_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 78001 * N < 10000 * p)
    (h2 : 10000 * p ≤ 78946 * N) :
    (166 : ℤ) * N + (-21) * p ≤ 2 * ((hp2Kap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hp2Kap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6)
    (ilo := 0) (cH := 8) (cP := 7) (mH := 1) (mP := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 5 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (Or.inr (by unfold hpEta; des_unfold; omega))
    (by
      refine le_trans (interval_card (lo := 1) (hi := 8) ?_) (by norm_num)
      intro x hx
      simp only [hpJJ, Finset.mem_filter] at hx
      unfold hpDD hpJstar hpElo hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 9 ≤ x by omega)
        omega)
    (by
      refine le_trans (interval_card (lo := 1) (hi := 7) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 8 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hp2Kap design N p = K at key ⊢
  unfold perPmax perD0 hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger7
