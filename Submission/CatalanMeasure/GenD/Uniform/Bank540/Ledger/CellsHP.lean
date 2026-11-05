module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.HPGen

@[expose] public section
set_option Elab.async false

/-!
# Cell certificates for the H' and P families at D58 (lane G5c)

Each `*_cell` is an exact affine lower bound `A N + B p <= d (kap + 2)` of `hpKap` / `perKap`
on a window `(a N, b N]` of odd `p`, for a fixed digit `s` and block range `(k0, k1)`, from the
integer formulas of `hpVal` / `perVal`.  The digit set `JJ` is confined to an interval of digits
(`interval_card`); everything else is `omega` after unfolding the design.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

macro "des_unfold" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h, D58.Odd.design] $[$loc]?)

theorem hpKmin_le_neg1 (P : Parameters) (N p : ℕ) : hpKmin P N p ≤ -1 := by
  unfold hpKmin
  have h := Int.natCast_nonneg ((P.g N + p - 1) / p)
  omega

theorem H1_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1233 * N < 125 * p)
    (h2 : 200 * p ≤ 1999 * N) :
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

theorem H2a_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 8593 * N < 1000 * p)
    (h2 : 1000 * p ≤ 8661 * N) :
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

theorem H2b_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1084 * N < 125 * p)
    (h2 : 125 * p ≤ 1093 * N) :
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

theorem H2c_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1751 * N < 200 * p)
    (h2 : 50 * p ≤ 441 * N) :
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

theorem H3a_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 7689 * N < 1000 * p)
    (h2 : 500 * p ≤ 3887 * N) :
    (-146 : ℤ) * N + (19) * p ≤ 2 * ((hpKap design N p : ℕ) : ℤ) + 4 := by
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

theorem H3b_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1561 * N < 200 * p)
    (h2 : 100 * p ≤ 789 * N) :
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

theorem P1a_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1357 * N < 200 * p)
    (h2 : 200 * p ≤ 1371 * N) :
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

theorem P1b_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 6863 * N < 1000 * p)
    (h2 : 200 * p ≤ 1379 * N) :
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

theorem P1c_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1381 * N < 200 * p)
    (h2 : 200 * p ≤ 1399 * N) :
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

theorem P2a_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 763 * N < 100 * p)
    (h2 : 500 * p ≤ 3831 * N) :
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

theorem P2b_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 959 * N < 125 * p)
    (h2 : 500 * p ≤ 3887 * N) :
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

theorem P2c_cell {N p : ℕ} (hN : 100 ≤ N) (hp1 : p % 2 = 1) (h1 : 1561 * N < 200 * p)
    (h2 : 200 * p ≤ 1599 * N) :
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

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
