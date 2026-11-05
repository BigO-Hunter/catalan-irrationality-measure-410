module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger2.HPSGen

@[expose] public section
set_option Elab.async false

/-!
# Cell certificates with exact breakpoints for H', P and the H' + P sum (lane G5e)

Each `*_cell` is an affine lower bound `A N + B p <= d (kap + 2)` of `hpKap`, `perKap` or `hpsKap`
(`kap` the maximum over digits and blocks) on a window `(a N, b N]` of odd `p`, for `N >= 100000`,
for a fixed digit `s`, block range `(k0, k1)` and support start `ilo`.  The windows run up to
`1/10000` of the exact breakpoints of the piecewise-affine value (zero crossings and the
switching points `26/3`, `70/9`, `39/5` of the minima in `hpDD`, `hpElo`), so no plateau is left
uncovered; the `S*` cells use the H' + P sum.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger2
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

theorem P1a_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 67779 * N < 10000 * p)
    (h2 : 1000 * p ≤ 6857 * N) :
    (-61 : ℤ) * N + (9) * p ≤ 1 * ((perKap design N p : ℕ) : ℤ) + 2 := by
  have hp0 : 0 < p := by omega
  have key := perKap_ge (P := design) (N := N) (p := p) (s := 10) (k0 := -1) (k1 := 7)
    (ilo := 69 * N - 10 * p) (c := 8) (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 6 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 2) (hi := 9) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 10 ≤ x by omega)
        omega)
    (by unfold hpK; omega)
  generalize hK : perKap design N p = K at key ⊢
  unfold perPmax perD0 hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem P1b_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 68573 * N < 10000 * p)
    (h2 : 10000 * p ≤ 68999 * N) :
    (-13 : ℤ) * N + (2) * p ≤ 1 * ((perKap design N p : ℕ) : ℤ) + 2 := by
  have hp0 : 0 < p := by omega
  have key := perKap_ge (P := design) (N := N) (p := p) (s := 10) (k0 := -1) (k1 := 7)
    (ilo := 69 * N - 10 * p) (c := 8) (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 6 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 2) (hi := 9) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 10 ≤ x by omega)
        omega)
    (by unfold hpK; omega)
  generalize hK : perKap design N p = K at key ⊢
  unfold perPmax perD0 hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem P1c_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 69001 * N < 10000 * p)
    (h2 : 10000 * p ≤ 69999 * N) :
    (56 : ℤ) * N + (-8) * p ≤ 1 * ((perKap design N p : ℕ) : ℤ) + 2 := by
  have hp0 : 0 < p := by omega
  have key := perKap_ge (P := design) (N := N) (p := p) (s := 10) (k0 := -1) (k1 := 7)
    (ilo := 0) (c := 8) (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 6 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 2) (hi := 9) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 10 ≤ x by omega)
        omega)
    (by unfold hpK; omega)
  generalize hK : perKap design N p = K at key ⊢
  unfold perPmax perD0 hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem P2a_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 76251 * N < 10000 * p)
    (h2 : 5000 * p ≤ 38331 * N) :
    (-61 : ℤ) * N + (8) * p ≤ 1 * ((perKap design N p : ℕ) : ℤ) + 2 := by
  have hp0 : 0 < p := by omega
  have key := perKap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6)
    (ilo := 69 * N - 9 * p) (c := 7) (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 5 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 2) (hi := 8) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 9 ≤ x by omega)
        omega)
    (by unfold hpK; omega)
  generalize hK : perKap design N p = K at key ⊢
  unfold perPmax perD0 hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem P2b_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 76671 * N < 10000 * p)
    (h2 : 10000 * p ≤ 76839 * N) :
    (8 : ℤ) * N + (-1) * p ≤ 1 * ((perKap design N p : ℕ) : ℤ) + 2 := by
  have hp0 : 0 < p := by omega
  have key := perKap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6)
    (ilo := 0) (c := 7) (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 5 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 2) (hi := 8) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 9 ≤ x by omega)
        omega)
    (by unfold hpK; omega)
  generalize hK : perKap design N p = K at key ⊢
  unfold perPmax perD0 hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem Sb_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 19211 * N < 2500 * p)
    (h2 : 90000 * p ≤ 699991 * N) :
    (-130 : ℤ) * N + (17) * p ≤ 2 * ((hpsKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := Ledger2.hpsKap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6)
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
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
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
      refine le_trans (interval_card (lo := 2) (hi := 8) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 9 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpsKap design N p = K at key ⊢
  unfold perPmax perD0 hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem Sc_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 700009 * N < 90000 * p)
    (h2 : 10000 * p ≤ 77999 * N) :
    (150 : ℤ) * N + (-19) * p ≤ 2 * ((hpsKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := Ledger2.hpsKap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6)
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
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
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
      refine le_trans (interval_card (lo := 2) (hi := 8) ?_) (by norm_num)
      intro x hx
      simp only [perJJ, Finset.mem_filter] at hx
      unfold perPmax perD0 hpJstar hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 1 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 9 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpsKap design N p = K at key ⊢
  unfold perPmax perD0 hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem H3c_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 78001 * N < 10000 * p)
    (h2 : 5000 * p ≤ 39471 * N) :
    (150 : ℤ) * N + (-19) * p ≤ 2 * ((hpKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hpKap_ge (P := design) (N := N) (p := p) (s := 9) (k0 := -1) (k1 := 6) (c := 8)
    (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 5 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
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
    (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpKap design N p = K at key ⊢
  unfold hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem P2c_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 78001 * N < 10000 * p)
    (h2 : 10000 * p ≤ 79999 * N) :
    (8 : ℤ) * N + (-1) * p ≤ 1 * ((perKap design N p : ℕ) : ℤ) + 2 := by
  have hp0 : 0 < p := by omega
  have key := perKap_ge (P := design) (N := N) (p := p) (s := 8) (k0 := -1) (k1 := 6)
    (ilo := 0) (c := 7) (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 5 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by unfold hpEta; des_unfold; omega)
    (by
      unfold perOK perPmax perD0 hpJstar hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
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
    (by unfold hpK; omega)
  generalize hK : perKap design N p = K at key ⊢
  unfold perPmax perD0 hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem H2a_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 21471 * N < 2500 * p)
    (h2 : 30000 * p ≤ 259997 * N) :
    (-146 : ℤ) * N + (17) * p ≤ 2 * ((hpKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hpKap_ge (P := design) (N := N) (p := p) (s := 8) (k0 := -1) (k1 := 5) (c := 7)
    (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 4 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 1) (hi := 7) ?_) (by norm_num)
      intro x hx
      simp only [hpJJ, Finset.mem_filter] at hx
      unfold hpDD hpJstar hpElo hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 8 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpKap design N p = K at key ⊢
  unfold hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem H2b_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 260003 * N < 30000 * p)
    (h2 : 10000 * p ≤ 87499 * N) :
    (10 : ℤ) * N + (-1) * p ≤ 2 * ((hpKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hpKap_ge (P := design) (N := N) (p := p) (s := 8) (k0 := -1) (k1 := 5) (c := 7)
    (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 4 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 1) (hi := 7) ?_) (by norm_num)
      intro x hx
      simp only [hpJJ, Finset.mem_filter] at hx
      unfold hpDD hpJstar hpElo hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 8 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpKap design N p = K at key ⊢
  unfold hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem H2c_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 87501 * N < 10000 * p)
    (h2 : 10000 * p ≤ 88229 * N) :
    (150 : ℤ) * N + (-17) * p ≤ 2 * ((hpKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hpKap_ge (P := design) (N := N) (p := p) (s := 8) (k0 := -1) (k1 := 5) (c := 7)
    (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 4 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 1) (hi := 7) ?_) (by norm_num)
      intro x hx
      simp only [hpJJ, Finset.mem_filter] at hx
      unfold hpDD hpJstar hpElo hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 8 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpKap design N p = K at key ⊢
  unfold hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

theorem H1_cell {N p : ℕ} (hN : 100000 ≤ N) (hp1 : p % 2 = 1) (h1 : 49289 * N < 5000 * p)
    (h2 : 10000 * p ≤ 99999 * N) :
    (10 : ℤ) * N + (-1) * p ≤ 2 * ((hpKap design N p : ℕ) : ℤ) + 4 := by
  have hp0 : 0 < p := by omega
  have key := hpKap_ge (P := design) (N := N) (p := p) (s := 7) (k0 := -1) (k1 := 4) (c := 6)
    (m0 := 1)
    ((Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega))
    (hpKmin_le_neg1 _ _ _)
    (by omega)
    (by
      unfold hpKmax
      have : 3 ≤ (design.n N - design.g N) / p :=
        (Nat.le_div_iff_mul_le hp0).mpr (by des_unfold; omega)
      omega)
    (by
      unfold hpOK hpD hpDD hpJstar hpElo hpEta hh
      des_unfold
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)
    (by
      refine le_trans (interval_card (lo := 1) (hi := 6) ?_) (by norm_num)
      intro x hx
      simp only [hpJJ, Finset.mem_filter] at hx
      unfold hpDD hpJstar hpElo hpEta hh at hx
      des_unfold at hx
      constructor
      · by_contra hc
        have := Nat.mul_le_mul_right p (show x ≤ 0 by omega)
        omega
      · by_contra hc
        have := Nat.mul_le_mul_right p (show 7 ≤ x by omega)
        omega)
    (by unfold hpK; omega) (by unfold hpK; omega)
  generalize hK : hpKap design N p = K at key ⊢
  unfold hpD hpElo hpDD hpJstar hpEta hh at key
  des_unfold at key
  omega

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger2
