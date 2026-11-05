module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Growth
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.CellsFam
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPSLB

@[expose] public section
set_option Elab.async false

/-!
# The partial D58 ledger instance (lane G5c)

`ledgerLB` is the pointwise maximum of the accepted families: `thinLB2sum` (banked T, U, S, U6g,
the T-raw tail, and the H' + P sum), `hpLB`, `perLB`, family A (`aLB`) and the Frobenius-product
cell `frobLB`.  `ledgerWins` is the piecewise-affine envelope of the exact Lean counts (banked
cells, tail, A, Frobenius, twelve H'/P cells), each window certified by `w0, w1, ...`;
`partial_growth` is the resulting denominator growth with the exact integrated gain
`partialGain`.  Remaining families (MT, M, Theorem Z, ...) plug in as further windows.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.SlotsA CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.W.FrobInst
noncomputable section

/-- All families in the ledger. -/
def ledgerLB : NullityLB design :=
  NullityLB.supList design [Slots.thinLB2sum design adm, Slots.hpLB design adm,
    Slots.perLB design adm, SlotsA.aLB design adm, frobLB]

theorem lift_fam (N p : ℕ) : famKap design N p ≤ ledgerLB.kap N p :=
  (Thin.banked_le_thinLB design adm N p).trans
    ((Slots.thinLB_le_thinLB2sum design adm N p).trans
      (NullityLB.le_supList_kap (by simp [ledgerLB]) N p))

theorem lift_tail (N p : ℕ) : (tTailLB design adm).kap N p ≤ ledgerLB.kap N p :=
  (Thin.tTail_le_thinLB design adm N p).trans
    ((Slots.thinLB_le_thinLB2sum design adm N p).trans
      (NullityLB.le_supList_kap (by simp [ledgerLB]) N p))

theorem lift_hp (N p : ℕ) : hpKap design N p ≤ ledgerLB.kap N p :=
  NullityLB.le_supList_kap (A := Slots.hpLB design adm) (by simp [ledgerLB]) N p

theorem lift_per (N p : ℕ) : perKap design N p ≤ ledgerLB.kap N p :=
  NullityLB.le_supList_kap (A := Slots.perLB design adm) (by simp [ledgerLB]) N p

theorem lift_A (N p : ℕ) : (aLB design adm).kap N p ≤ ledgerLB.kap N p :=
  NullityLB.le_supList_kap (by simp [ledgerLB]) N p

theorem lift_frob (N p : ℕ) : frobLB.kap N p ≤ ledgerLB.kap N p :=
  NullityLB.le_supList_kap (by simp [ledgerLB]) N p

theorem win_lo {a : ℝ} {na da : ℕ} (hd : 0 < da) (ha : a * da = na) {N p : ℕ}
    (h : a * N < p) : na * N < da * p := by
  have hdr : (0 : ℝ) < da := by exact_mod_cast hd
  have : (na : ℝ) * N < da * p := by rw [← ha]; nlinarith
  exact_mod_cast this

theorem win_hi {b : ℝ} {nb db : ℕ} (hd : 0 < db) (hb : b * db = nb) {N p : ℕ}
    (h : (p : ℝ) ≤ b * N) : db * p ≤ nb * N := by
  have hdr : (0 : ℝ) < db := by exact_mod_cast hd
  have : (db : ℝ) * p ≤ nb * N := by rw [← hb]; nlinarith
  exact_mod_cast this

theorem floor_cert {x : ℝ} {k : ℕ} (h : ⌊x⌋₊ ≤ k + 1) : x - 2 ≤ k := by
  rcases lt_or_ge x 0 with hx | hx
  · have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  · have h1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) ≤ k + 1 := by exact_mod_cast h
    linarith

theorem w0 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (1357 / 200 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (1371 / 200 : ℝ) * N) :
    (N : ℝ) * (cw (1357 / 200 : ℝ) (1371 / 200 : ℝ) (-61 : ℝ) (9 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (1357 / 200 : ℝ) (1371 / 200 : ℝ) (-61 : ℝ) (9 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 1357 * N < 200 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 200 * p ≤ 1371 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (1357 / 200 : ℝ) (1371 / 200 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := P1a_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (1357 / 200 : ℝ)) (b := (1371 / 200 : ℝ)) (A := -61) (B := 9) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w1 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (6863 / 1000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (1379 / 200 : ℝ) * N) :
    (N : ℝ) * (cw (6863 / 1000 : ℝ) (1379 / 200 : ℝ) (-13 : ℝ) (2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (6863 / 1000 : ℝ) (1379 / 200 : ℝ) (-13 : ℝ) (2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 6863 * N < 1000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 200 * p ≤ 1379 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (6863 / 1000 : ℝ) (1379 / 200 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := P1b_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (6863 / 1000 : ℝ)) (b := (1379 / 200 : ℝ)) (A := -13) (B := 2) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w2 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (1381 / 200 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (1399 / 200 : ℝ) * N) :
    (N : ℝ) * (cw (1381 / 200 : ℝ) (1399 / 200 : ℝ) (56 : ℝ) (-8 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (1381 / 200 : ℝ) (1399 / 200 : ℝ) (56 : ℝ) (-8 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 1381 * N < 200 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 200 * p ≤ 1399 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (1381 / 200 : ℝ) (1399 / 200 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := P1c_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (1381 / 200 : ℝ)) (b := (1399 / 200 : ℝ)) (A := 56) (B := -8) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w3 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (763 / 100 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (3831 / 500 : ℝ) * N) :
    (N : ℝ) * (cw (763 / 100 : ℝ) (3831 / 500 : ℝ) (-61 : ℝ) (8 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (763 / 100 : ℝ) (3831 / 500 : ℝ) (-61 : ℝ) (8 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 763 * N < 100 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 500 * p ≤ 3831 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (763 / 100 : ℝ) (3831 / 500 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := P2a_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (763 / 100 : ℝ)) (b := (3831 / 500 : ℝ)) (A := -61) (B := 8) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w4 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (959 / 125 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (54 / 7 : ℝ) * N) :
    (N : ℝ) * (cw (959 / 125 : ℝ) (54 / 7 : ℝ) (8 : ℝ) (-1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (959 / 125 : ℝ) (54 / 7 : ℝ) (8 : ℝ) (-1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 959 * N < 125 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 7 * p ≤ 54 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (959 / 125 : ℝ) (54 / 7 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := P2b_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (959 / 125 : ℝ)) (b := (54 / 7 : ℝ)) (A := 8) (B := -1) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w5 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (54 / 7 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (3887 / 500 : ℝ) * N) :
    (N : ℝ) * (cw (54 / 7 : ℝ) (3887 / 500 : ℝ) (-73 : ℝ) (19 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (54 / 7 : ℝ) (3887 / 500 : ℝ) (-73 : ℝ) (19 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 54 * N < 7 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 500 * p ≤ 3887 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (54 / 7 : ℝ) (3887 / 500 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := H3a_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (54 / 7 : ℝ)) (b := (3887 / 500 : ℝ)) (A := -146) (B := 19) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w6 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (1561 / 200 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (134 / 17 : ℝ) * N) :
    (N : ℝ) * (cw (1561 / 200 : ℝ) (134 / 17 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (1561 / 200 : ℝ) (134 / 17 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 1561 * N < 200 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 17 * p ≤ 134 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (1561 / 200 : ℝ) (134 / 17 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := H3b_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (1561 / 200 : ℝ)) (b := (134 / 17 : ℝ)) (A := 150) (B := -19) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w7 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (134 / 17 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (1599 / 200 : ℝ) * N) :
    (N : ℝ) * (cw (134 / 17 : ℝ) (1599 / 200 : ℝ) (8 : ℝ) (-1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (134 / 17 : ℝ) (1599 / 200 : ℝ) (8 : ℝ) (-1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 134 * N < 17 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 200 * p ≤ 1599 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (134 / 17 : ℝ) (1599 / 200 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := P2c_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (134 / 17 : ℝ)) (b := (1599 / 200 : ℝ)) (A := 8) (B := -1) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w8 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (8593 / 1000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (8661 / 1000 : ℝ) * N) :
    (N : ℝ) * (cw (8593 / 1000 : ℝ) (8661 / 1000 : ℝ) (-73 : ℝ) (17 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (8593 / 1000 : ℝ) (8661 / 1000 : ℝ) (-73 : ℝ) (17 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 8593 * N < 1000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1000 * p ≤ 8661 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (8593 / 1000 : ℝ) (8661 / 1000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := H2a_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (8593 / 1000 : ℝ)) (b := (8661 / 1000 : ℝ)) (A := -146) (B := 17) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w9 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (1084 / 125 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (1093 / 125 : ℝ) * N) :
    (N : ℝ) * (cw (1084 / 125 : ℝ) (1093 / 125 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (1084 / 125 : ℝ) (1093 / 125 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 1084 * N < 125 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 125 * p ≤ 1093 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (1084 / 125 : ℝ) (1093 / 125 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := H2b_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (1084 / 125 : ℝ)) (b := (1093 / 125 : ℝ)) (A := 10) (B := -1) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w10 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (1751 / 200 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (441 / 50 : ℝ) * N) :
    (N : ℝ) * (cw (1751 / 200 : ℝ) (441 / 50 : ℝ) (75 : ℝ) (-17 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (1751 / 200 : ℝ) (441 / 50 : ℝ) (75 : ℝ) (-17 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 1751 * N < 200 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 50 * p ≤ 441 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (1751 / 200 : ℝ) (441 / 50 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := H2c_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (1751 / 200 : ℝ)) (b := (441 / 50 : ℝ)) (A := 150) (B := -17) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w11 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (1233 / 125 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (1999 / 200 : ℝ) * N) :
    (N : ℝ) * (cw (1233 / 125 : ℝ) (1999 / 200 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (1233 / 125 : ℝ) (1999 / 200 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 1233 * N < 125 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 200 * p ≤ 1999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (1233 / 125 : ℝ) (1999 / 200 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := H1_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (1233 / 125 : ℝ)) (b := (1999 / 200 : ℝ)) (A := 10) (B := -1) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w12 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (59 / 5 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (12 : ℝ) * N) :
    (N : ℝ) * (cw (59 / 5 : ℝ) (12 : ℝ) (-59 : ℝ) (5 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (59 / 5 : ℝ) (12 : ℝ) (-59 : ℝ) (5 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 59 * N < 5 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1 * p ≤ 12 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (59 / 5 : ℝ) (12 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := A_cell (N := N) (p := p) hN (by omega) (by omega)
  have hle : ((aLB design adm).kap N p : ℕ) ≤ ledgerLB.kap N p := lift_A N p
  have hle' : (((aLB design adm).kap N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (59 / 5 : ℝ)) (b := (12 : ℝ)) (A := -59) (B := 5) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w13 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (12 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (13 : ℝ) * N) :
    (N : ℝ) * (cw (12 : ℝ) (13 : ℝ) (-5 : ℝ) (1 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (12 : ℝ) (13 : ℝ) (-5 : ℝ) (1 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 12 * N < 1 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1 * p ≤ 13 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (12 : ℝ) (13 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell0 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (12 : ℝ) (13 : ℝ) (-5 : ℝ) (1 / 2 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (-5 : ℝ) (1 / 2 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w14 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (13 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (146 / 11 : ℝ) * N) :
    (N : ℝ) * (cw (13 : ℝ) (146 / 11 : ℝ) (73 : ℝ) (-11 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (13 : ℝ) (146 / 11 : ℝ) (73 : ℝ) (-11 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 13 * N < 1 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 11 * p ≤ 146 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (13 : ℝ) (146 / 11 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell1 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (13 : ℝ) (146 / 11 : ℝ) (73 : ℝ) (-11 / 2 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (73 : ℝ) (-11 / 2 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w15 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (16 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (118 / 7 : ℝ) * N) :
    (N : ℝ) * (cw (16 : ℝ) (118 / 7 : ℝ) (-16 : ℝ) (1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (16 : ℝ) (118 / 7 : ℝ) (-16 : ℝ) (1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 16 * N < 1 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 7 * p ≤ 118 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (16 : ℝ) (118 / 7 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := tail_cell (N := N) (p := p) hN (by omega) (by omega)
  have hle : ((tTailLB design adm).kap N p : ℕ) ≤ ledgerLB.kap N p := lift_tail N p
  have hle' : (((tTailLB design adm).kap N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (16 : ℝ)) (b := (118 / 7 : ℝ)) (A := -16) (B := 1) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem w16 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (118 / 7 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (69 / 4 : ℝ) * N) :
    (N : ℝ) * (cw (118 / 7 : ℝ) (69 / 4 : ℝ) (-75 : ℝ) (9 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (118 / 7 : ℝ) (69 / 4 : ℝ) (-75 : ℝ) (9 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 118 * N < 7 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 4 * p ≤ 69 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (118 / 7 : ℝ) (69 / 4 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell2 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (118 / 7 : ℝ) (69 / 4 : ℝ) (-75 : ℝ) (9 / 2 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (-75 : ℝ) (9 / 2 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w17 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (69 / 4 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (35 / 2 : ℝ) * N) :
    (N : ℝ) * (cw (69 / 4 : ℝ) (35 / 2 : ℝ) (-6 : ℝ) (1 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (69 / 4 : ℝ) (35 / 2 : ℝ) (-6 : ℝ) (1 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 69 * N < 4 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2 * p ≤ 35 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (69 / 4 : ℝ) (35 / 2 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell3 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (69 / 4 : ℝ) (35 / 2 : ℝ) (-6 : ℝ) (1 / 2 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (-6 : ℝ) (1 / 2 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w18 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (35 / 2 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (128 / 7 : ℝ) * N) :
    (N : ℝ) * (cw (35 / 2 : ℝ) (128 / 7 : ℝ) (64 : ℝ) (-7 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (35 / 2 : ℝ) (128 / 7 : ℝ) (64 : ℝ) (-7 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 35 * N < 2 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 7 * p ≤ 128 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (35 / 2 : ℝ) (128 / 7 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell4 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (35 / 2 : ℝ) (128 / 7 : ℝ) (64 : ℝ) (-7 / 2 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (64 : ℝ) (-7 / 2 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w19 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (64 / 3 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (23 : ℝ) * N) :
    (N : ℝ) * (cw (64 / 3 : ℝ) (23 : ℝ) (-64 : ℝ) (3 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (64 / 3 : ℝ) (23 : ℝ) (-64 : ℝ) (3 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 64 * N < 3 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1 * p ≤ 23 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (64 / 3 : ℝ) (23 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell5 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (64 / 3 : ℝ) (23 : ℝ) (-64 : ℝ) (3 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (-64 : ℝ) (3 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w20 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (23 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (24 : ℝ) * N) :
    (N : ℝ) * (cw (23 : ℝ) (24 : ℝ) (5 : ℝ) (0 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (23 : ℝ) (24 : ℝ) (5 : ℝ) (0 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 23 * N < 1 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1 * p ≤ 24 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (23 : ℝ) (24 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell6 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (23 : ℝ) (24 : ℝ) (5 : ℝ) (0 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (5 : ℝ) (0 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w21 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (24 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (26 : ℝ) * N) :
    (N : ℝ) * (cw (24 : ℝ) (26 : ℝ) (53 : ℝ) (-2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (24 : ℝ) (26 : ℝ) (53 : ℝ) (-2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 24 * N < 1 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1 * p ≤ 26 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (24 : ℝ) (26 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hfl := floor_cert (D58.cell7 hN0 hp1 (by omega) (by omega))
  have hle : (famKap design N p : ℝ) ≤ (ledgerLB.kap N p : ℝ) := by
    exact_mod_cast lift_fam N p
  have hev : (N : ℝ) * (cw (24 : ℝ) (26 : ℝ) (53 : ℝ) (-2 : ℝ)).K.eval ((p : ℝ) / N) =
      (N : ℝ) * (PL.Prof.mk (53 : ℝ) (-2 : ℝ) []).eval ((p : ℝ) / N) := rfl
  rw [hev]
  linarith

theorem w22 {N p : ℕ} (hN : 100 ≤ N) (hp : p.Prime) (h1 : (26 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (53 / 2 : ℝ) * N) :
    (N : ℝ) * (cw (26 : ℝ) (53 / 2 : ℝ) (53 : ℝ) (-2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (26 : ℝ) (53 / 2 : ℝ) (53 : ℝ) (-2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 26 * N < 1 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2 * p ≤ 53 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (26 : ℝ) (53 / 2 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := frob_cell (N := N) (p := p) (by omega) (by omega)
  have hle : (frobLB.kap N p : ℕ) ≤ ledgerLB.kap N p := lift_frob N p
  have hle' : ((frobLB.kap N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (26 : ℝ)) (b := (53 / 2 : ℝ)) (A := 53) (B := -2) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

/-- The certified windows: the piecewise-affine envelope of the families in Lean. -/
def ledgerWins : List KapWindow :=
  [cw (1357 / 200 : ℝ) (1371 / 200 : ℝ) (-61 : ℝ) (9 : ℝ),
   cw (6863 / 1000 : ℝ) (1379 / 200 : ℝ) (-13 : ℝ) (2 : ℝ),
   cw (1381 / 200 : ℝ) (1399 / 200 : ℝ) (56 : ℝ) (-8 : ℝ),
   cw (763 / 100 : ℝ) (3831 / 500 : ℝ) (-61 : ℝ) (8 : ℝ),
   cw (959 / 125 : ℝ) (54 / 7 : ℝ) (8 : ℝ) (-1 : ℝ),
   cw (54 / 7 : ℝ) (3887 / 500 : ℝ) (-73 : ℝ) (19 / 2 : ℝ),
   cw (1561 / 200 : ℝ) (134 / 17 : ℝ) (75 : ℝ) (-19 / 2 : ℝ),
   cw (134 / 17 : ℝ) (1599 / 200 : ℝ) (8 : ℝ) (-1 : ℝ),
   cw (8593 / 1000 : ℝ) (8661 / 1000 : ℝ) (-73 : ℝ) (17 / 2 : ℝ),
   cw (1084 / 125 : ℝ) (1093 / 125 : ℝ) (5 : ℝ) (-1 / 2 : ℝ),
   cw (1751 / 200 : ℝ) (441 / 50 : ℝ) (75 : ℝ) (-17 / 2 : ℝ),
   cw (1233 / 125 : ℝ) (1999 / 200 : ℝ) (5 : ℝ) (-1 / 2 : ℝ),
   cw (59 / 5 : ℝ) (12 : ℝ) (-59 : ℝ) (5 : ℝ),
   cw (12 : ℝ) (13 : ℝ) (-5 : ℝ) (1 / 2 : ℝ),
   cw (13 : ℝ) (146 / 11 : ℝ) (73 : ℝ) (-11 / 2 : ℝ),
   cw (16 : ℝ) (118 / 7 : ℝ) (-16 : ℝ) (1 : ℝ),
   cw (118 / 7 : ℝ) (69 / 4 : ℝ) (-75 : ℝ) (9 / 2 : ℝ),
   cw (69 / 4 : ℝ) (35 / 2 : ℝ) (-6 : ℝ) (1 / 2 : ℝ),
   cw (35 / 2 : ℝ) (128 / 7 : ℝ) (64 : ℝ) (-7 / 2 : ℝ),
   cw (64 / 3 : ℝ) (23 : ℝ) (-64 : ℝ) (3 : ℝ),
   cw (23 : ℝ) (24 : ℝ) (5 : ℝ) (0 : ℝ),
   cw (24 : ℝ) (26 : ℝ) (53 : ℝ) (-2 : ℝ),
   cw (26 : ℝ) (53 / 2 : ℝ) (53 : ℝ) (-2 : ℝ)]

/-- The integrated gain of the partial ledger. -/
def partialGain : ℝ := 314974644491 / 15708000000

theorem ledgerWins_area : (ledgerWins.map (KapWindow.area 58)).sum = partialGain := by
  simp only [ledgerWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area,
    partialGain]
  norm_num

theorem ledgerWins_pos : ∀ w ∈ ledgerWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [ledgerWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem ledgerWins_ord : ledgerWins.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [ledgerWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem ledgerWins_rec : ∀ w ∈ ledgerWins, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  simp only [ledgerWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;> simp only [cw] <;> norm_num

theorem ledgerWins_cert : ∀ w ∈ ledgerWins, ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime →
    w.a * N < p → (p : ℝ) ≤ w.b * N →
      (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
      (N : ℝ) * w.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  intro w hw
  simp only [ledgerWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w0 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w1 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w2 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w3 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w4 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w5 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w6 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w7 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w8 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w9 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w10 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w11 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w12 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w13 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w14 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w15 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w16 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w17 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w18 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w19 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w20 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w21 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100] with N hN p hp h1 h2
    exact w22 hN hp h1 h2

/-- **Partial ledger.**  `log D_N <= (24733/4 + (2673/8) log 2 - partialGain + eps) N^2`. -/
theorem partial_growth {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible ledgerLB 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - partialGain + ε) * (N : ℝ) ^ 2 :=
  ledger_growth ledgerLB ledgerWins partialGain ledgerWins_area ledgerWins_pos ledgerWins_ord
    ledgerWins_rec ledgerWins_cert hε

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
