module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger2.CellsHP2

@[expose] public section
set_option Elab.async false

/-!
# The refined partial ledger (lane G5e)

Same families as `Ledger.ledgerLB`; the H'/P part of `ledgerWins` is replaced by the exact-breakpoint
cells of `Ledger2.CellsHP2` (plateau, H' + P sum cells, windows within `1/10000` of the breakpoints).
`partial_growth2` is the resulting denominator growth with the exact gain `gain2`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger2
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.SlotsA CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.W.FrobInst CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

theorem lift_hps (N p : ℕ) : hpsKap design N p ≤ ledgerLB.kap N p :=
  (Slots.hpsLB_le_thinLB2sum design adm N p).trans
    (NullityLB.le_supList_kap (A := Slots.thinLB2sum design adm) (by simp [ledgerLB]) N p)

theorem v0 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (67779 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (6857 / 1000 : ℝ) * N) :
    (N : ℝ) * (cw (67779 / 10000 : ℝ) (6857 / 1000 : ℝ) (-61 : ℝ) (9 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (67779 / 10000 : ℝ) (6857 / 1000 : ℝ) (-61 : ℝ) (9 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 67779 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1000 * p ≤ 6857 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (67779 / 10000 : ℝ) (6857 / 1000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.P1a_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (67779 / 10000 : ℝ)) (b := (6857 / 1000 : ℝ)) (A := -61) (B := 9) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v1 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (68573 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (68999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (68573 / 10000 : ℝ) (68999 / 10000 : ℝ) (-13 : ℝ) (2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (68573 / 10000 : ℝ) (68999 / 10000 : ℝ) (-13 : ℝ) (2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 68573 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 68999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (68573 / 10000 : ℝ) (68999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.P1b_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (68573 / 10000 : ℝ)) (b := (68999 / 10000 : ℝ)) (A := -13) (B := 2) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v2 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (69001 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (69999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (69001 / 10000 : ℝ) (69999 / 10000 : ℝ) (56 : ℝ) (-8 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (69001 / 10000 : ℝ) (69999 / 10000 : ℝ) (56 : ℝ) (-8 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 69001 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 69999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (69001 / 10000 : ℝ) (69999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.P1c_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (69001 / 10000 : ℝ)) (b := (69999 / 10000 : ℝ)) (A := 56) (B := -8) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v3 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (76251 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (38331 / 5000 : ℝ) * N) :
    (N : ℝ) * (cw (76251 / 10000 : ℝ) (38331 / 5000 : ℝ) (-61 : ℝ) (8 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (76251 / 10000 : ℝ) (38331 / 5000 : ℝ) (-61 : ℝ) (8 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 76251 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 5000 * p ≤ 38331 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (76251 / 10000 : ℝ) (38331 / 5000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.P2a_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (76251 / 10000 : ℝ)) (b := (38331 / 5000 : ℝ)) (A := -61) (B := 8) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v4 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (76671 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (76839 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (76671 / 10000 : ℝ) (76839 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (76671 / 10000 : ℝ) (76839 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 76671 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 76839 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (76671 / 10000 : ℝ) (76839 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.P2b_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (76671 / 10000 : ℝ)) (b := (76839 / 10000 : ℝ)) (A := 8) (B := -1) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v5 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (19211 / 2500 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (699991 / 90000 : ℝ) * N) :
    (N : ℝ) * (cw (19211 / 2500 : ℝ) (699991 / 90000 : ℝ) (-65 : ℝ) (17 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (19211 / 2500 : ℝ) (699991 / 90000 : ℝ) (-65 : ℝ) (17 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 19211 * N < 2500 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 90000 * p ≤ 699991 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (19211 / 2500 : ℝ) (699991 / 90000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.Sb_cell hN hp1 (by omega) (by omega)
  have hle : (hpsKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hps N p
  have hle' : ((hpsKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (19211 / 2500 : ℝ)) (b := (699991 / 90000 : ℝ)) (A := -130) (B := 17) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v6 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (700009 / 90000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (77999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (700009 / 90000 : ℝ) (77999 / 10000 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (700009 / 90000 : ℝ) (77999 / 10000 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 700009 * N < 90000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 77999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (700009 / 90000 : ℝ) (77999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.Sc_cell hN hp1 (by omega) (by omega)
  have hle : (hpsKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hps N p
  have hle' : ((hpsKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (700009 / 90000 : ℝ)) (b := (77999 / 10000 : ℝ)) (A := 150) (B := -19) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v7 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (78001 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (134 / 17 : ℝ) * N) :
    (N : ℝ) * (cw (78001 / 10000 : ℝ) (134 / 17 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (78001 / 10000 : ℝ) (134 / 17 : ℝ) (75 : ℝ) (-19 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 78001 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 17 * p ≤ 134 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (78001 / 10000 : ℝ) (134 / 17 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.H3c_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (78001 / 10000 : ℝ)) (b := (134 / 17 : ℝ)) (A := 150) (B := -19) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v8 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (134 / 17 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (79999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (134 / 17 : ℝ) (79999 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (134 / 17 : ℝ) (79999 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 134 * N < 17 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 79999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (134 / 17 : ℝ) (79999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.P2c_cell hN hp1 (by omega) (by omega)
  have hle : (perKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_per N p
  have hle' : ((perKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (134 / 17 : ℝ)) (b := (79999 / 10000 : ℝ)) (A := 8) (B := -1) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v9 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (21471 / 2500 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (259997 / 30000 : ℝ) * N) :
    (N : ℝ) * (cw (21471 / 2500 : ℝ) (259997 / 30000 : ℝ) (-73 : ℝ) (17 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (21471 / 2500 : ℝ) (259997 / 30000 : ℝ) (-73 : ℝ) (17 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 21471 * N < 2500 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 30000 * p ≤ 259997 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (21471 / 2500 : ℝ) (259997 / 30000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.H2a_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (21471 / 2500 : ℝ)) (b := (259997 / 30000 : ℝ)) (A := -146) (B := 17) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v10 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (260003 / 30000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (87499 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (260003 / 30000 : ℝ) (87499 / 10000 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (260003 / 30000 : ℝ) (87499 / 10000 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 260003 * N < 30000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 87499 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (260003 / 30000 : ℝ) (87499 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.H2b_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (260003 / 30000 : ℝ)) (b := (87499 / 10000 : ℝ)) (A := 10) (B := -1) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v11 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (87501 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (88229 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (87501 / 10000 : ℝ) (88229 / 10000 : ℝ) (75 : ℝ) (-17 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (87501 / 10000 : ℝ) (88229 / 10000 : ℝ) (75 : ℝ) (-17 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 87501 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 88229 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (87501 / 10000 : ℝ) (88229 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.H2c_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (87501 / 10000 : ℝ)) (b := (88229 / 10000 : ℝ)) (A := 150) (B := -17) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v12 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (49289 / 5000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (99999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (49289 / 5000 : ℝ) (99999 / 10000 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
    (N : ℝ) * (cw (49289 / 5000 : ℝ) (99999 / 10000 : ℝ) (5 : ℝ) (-1 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have hN0 : 0 < N := by omega
  have h1' : 49289 * N < 5000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 99999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (49289 / 5000 : ℝ) (99999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := Ledger2.H1_cell hN hp1 (by omega) (by omega)
  have hle : (hpKap design N p : ℕ) ≤ ledgerLB.kap N p := lift_hp N p
  have hle' : ((hpKap design N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (49289 / 5000 : ℝ)) (b := (99999 / 10000 : ℝ)) (A := 10) (B := -1) (d := 2) (by norm_num : 0 < 2) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v13 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (59 / 5 : ℝ) * N < p)
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
  have hN' : 100 ≤ N := by omega
  have hc := A_cell (N := N) (p := p) hN' (by omega) (by omega)
  have hle : ((aLB design adm).kap N p : ℕ) ≤ ledgerLB.kap N p := lift_A N p
  have hle' : (((aLB design adm).kap N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (59 / 5 : ℝ)) (b := (12 : ℝ)) (A := -59) (B := 5) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v14 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (12 : ℝ) * N < p)
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

theorem v15 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (13 : ℝ) * N < p)
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

theorem v16 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (16 : ℝ) * N < p)
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
  have hN' : 100 ≤ N := by omega
  have hc := tail_cell (N := N) (p := p) hN' (by omega) (by omega)
  have hle : ((tTailLB design adm).kap N p : ℕ) ≤ ledgerLB.kap N p := lift_tail N p
  have hle' : (((tTailLB design adm).kap N p : ℕ) : ℤ) ≤ ((ledgerLB.kap N p : ℕ) : ℤ) := by exact_mod_cast hle
  exact cw_kap_cert (a := (16 : ℝ)) (b := (118 / 7 : ℝ)) (A := -16) (B := 1) (d := 1) (by norm_num : 0 < 1) (by norm_num)
    (by norm_num) hN0 (by push_cast; linarith)

theorem v17 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (118 / 7 : ℝ) * N < p)
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

theorem v18 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (69 / 4 : ℝ) * N < p)
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

theorem v19 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (35 / 2 : ℝ) * N < p)
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

theorem v20 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (64 / 3 : ℝ) * N < p)
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

theorem v21 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (23 : ℝ) * N < p)
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

theorem v22 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (24 : ℝ) * N < p)
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

theorem v23 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (26 : ℝ) * N < p)
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

/-- The certified windows of the refined ledger. -/
def wins2 : List KapWindow :=
  [cw (67779 / 10000 : ℝ) (6857 / 1000 : ℝ) (-61 : ℝ) (9 : ℝ),
   cw (68573 / 10000 : ℝ) (68999 / 10000 : ℝ) (-13 : ℝ) (2 : ℝ),
   cw (69001 / 10000 : ℝ) (69999 / 10000 : ℝ) (56 : ℝ) (-8 : ℝ),
   cw (76251 / 10000 : ℝ) (38331 / 5000 : ℝ) (-61 : ℝ) (8 : ℝ),
   cw (76671 / 10000 : ℝ) (76839 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ),
   cw (19211 / 2500 : ℝ) (699991 / 90000 : ℝ) (-65 : ℝ) (17 / 2 : ℝ),
   cw (700009 / 90000 : ℝ) (77999 / 10000 : ℝ) (75 : ℝ) (-19 / 2 : ℝ),
   cw (78001 / 10000 : ℝ) (134 / 17 : ℝ) (75 : ℝ) (-19 / 2 : ℝ),
   cw (134 / 17 : ℝ) (79999 / 10000 : ℝ) (8 : ℝ) (-1 : ℝ),
   cw (21471 / 2500 : ℝ) (259997 / 30000 : ℝ) (-73 : ℝ) (17 / 2 : ℝ),
   cw (260003 / 30000 : ℝ) (87499 / 10000 : ℝ) (5 : ℝ) (-1 / 2 : ℝ),
   cw (87501 / 10000 : ℝ) (88229 / 10000 : ℝ) (75 : ℝ) (-17 / 2 : ℝ),
   cw (49289 / 5000 : ℝ) (99999 / 10000 : ℝ) (5 : ℝ) (-1 / 2 : ℝ),
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

/-- The integrated gain of the refined ledger. -/
def gain2 : ℝ := 7906089003959 / 392700000000

theorem wins2_area : (wins2.map (KapWindow.area 58)).sum = gain2 := by
  simp only [wins2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area, gain2]
  norm_num

theorem wins2_pos : ∀ w ∈ wins2, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [wins2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem wins2_ord : wins2.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [wins2, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem wins2_rec : ∀ w ∈ wins2, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  simp only [wins2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;> simp only [cw] <;> norm_num

theorem wins2_cert : ∀ w ∈ wins2, ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime →
    w.a * N < p → (p : ℝ) ≤ w.b * N →
      (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ (ledgerLB.kap N p : ℝ) ∧
      (N : ℝ) * w.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  intro w hw
  simp only [wins2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v0 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v1 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v2 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v3 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v4 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v5 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v6 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v7 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v8 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v9 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v10 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v11 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v12 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v13 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v14 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v15 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v16 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v17 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v18 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v19 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v20 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v21 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v22 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact v23 hN hp h1 h2

/-- **Refined partial ledger.**  `log D_N <= (24733/4 + (2673/8) log 2 - gain2 + eps) N^2`. -/
theorem partial_growth2 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible ledgerLB 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain2 + ε) * (N : ℝ) ^ 2 :=
  ledger_growth ledgerLB wins2 gain2 wins2_area wins2_pos wins2_ord
    wins2_rec wins2_cert hε

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger2
