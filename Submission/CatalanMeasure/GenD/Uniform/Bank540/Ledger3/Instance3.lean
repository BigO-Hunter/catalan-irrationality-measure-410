module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Cells1
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Cells2
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Fam

@[expose] public section
set_option Elab.async false

/-!
# Certified MT (1) windows and the ledger `Ledger2 + MT(1)` (lane G5f)

`mtWins` : 11 windows in the region `x in (3.9, 5.1)` certified against `mtLB3` (`WinCert`),
with exact area `mtGain`; `partial_growth3` is the denominator growth of the families
`[ledgerLB, mtLB3]` on `mtWins ++ wins2`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.W.SlotsT CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger2
noncomputable section

theorem mtv0 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (42943 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (5403 / 1250 : ℝ) * N) :
    (N : ℝ) * (cw (42943 / 10000 : ℝ) (5403 / 1250 : ℝ) (-73 : ℝ) (17 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (42943 / 10000 : ℝ) (5403 / 1250 : ℝ) (-73 : ℝ) (17 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 42943 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 1250 * p ≤ 5403 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (42943 / 10000 : ℝ) (5403 / 1250 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell0 hN hp1 h1' h2'
  exact cw_kap_cert (a := (42943 / 10000 : ℝ)) (b := (5403 / 1250 : ℝ)) (A := -73000) (B := 17000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv1 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (43227 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (10833 / 2500 : ℝ) * N) :
    (N : ℝ) * (cw (43227 / 10000 : ℝ) (10833 / 2500 : ℝ) (-140 : ℝ) (65 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (43227 / 10000 : ℝ) (10833 / 2500 : ℝ) (-140 : ℝ) (65 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 43227 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2500 * p ≤ 10833 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (43227 / 10000 : ℝ) (10833 / 2500 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell1 hN hp1 h1' h2'
  exact cw_kap_cert (a := (43227 / 10000 : ℝ)) (b := (10833 / 2500 : ℝ)) (A := -140000) (B := 32500) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv2 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (8667 / 2000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (8727 / 2000 : ℝ) * N) :
    (N : ℝ) * (cw (8667 / 2000 : ℝ) (8727 / 2000 : ℝ) (16 : ℝ) (-7 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (8667 / 2000 : ℝ) (8727 / 2000 : ℝ) (16 : ℝ) (-7 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 8667 * N < 2000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2000 * p ≤ 8727 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (8667 / 2000 : ℝ) (8727 / 2000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell2 hN hp1 h1' h2'
  exact cw_kap_cert (a := (8667 / 2000 : ℝ)) (b := (8727 / 2000 : ℝ)) (A := 16000) (B := -3500) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv3 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (21819 / 5000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (21851 / 5000 : ℝ) * N) :
    (N : ℝ) * (cw (21819 / 5000 : ℝ) (21851 / 5000 : ℝ) (112 : ℝ) (-51 / 2 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (21819 / 5000 : ℝ) (21851 / 5000 : ℝ) (112 : ℝ) (-51 / 2 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 21819 * N < 5000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 5000 * p ≤ 21851 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (21819 / 5000 : ℝ) (21851 / 5000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell3 hN hp1 h1' h2'
  exact cw_kap_cert (a := (21819 / 5000 : ℝ)) (b := (21851 / 5000 : ℝ)) (A := 112000) (B := -25500) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv4 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (8741 / 2000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (43999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (8741 / 2000 : ℝ) (43999 / 10000 : ℝ) (53 : ℝ) (-12 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (8741 / 2000 : ℝ) (43999 / 10000 : ℝ) (53 : ℝ) (-12 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 8741 * N < 2000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 43999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (8741 / 2000 : ℝ) (43999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell4 hN hp1 h1' h2'
  exact cw_kap_cert (a := (8741 / 2000 : ℝ)) (b := (43999 / 10000 : ℝ)) (A := 53000) (B := -12000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv5 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (44001 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (11029 / 2500 : ℝ) * N) :
    (N : ℝ) * (cw (44001 / 10000 : ℝ) (11029 / 2500 : ℝ) (75 : ℝ) (-17 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (44001 / 10000 : ℝ) (11029 / 2500 : ℝ) (75 : ℝ) (-17 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 44001 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2500 * p ≤ 11029 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (44001 / 10000 : ℝ) (11029 / 2500 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell5 hN hp1 h1' h2'
  exact cw_kap_cert (a := (44001 / 10000 : ℝ)) (b := (11029 / 2500 : ℝ)) (A := 75000) (B := -17000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv6 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (11429 / 2500 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (45999 / 10000 : ℝ) * N) :
    (N : ℝ) * (cw (11429 / 2500 : ℝ) (45999 / 10000 : ℝ) (-64 : ℝ) (14 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (11429 / 2500 : ℝ) (45999 / 10000 : ℝ) (-64 : ℝ) (14 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 11429 * N < 2500 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 10000 * p ≤ 45999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (11429 / 2500 : ℝ) (45999 / 10000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell6 hN hp1 h1' h2'
  exact cw_kap_cert (a := (11429 / 2500 : ℝ)) (b := (45999 / 10000 : ℝ)) (A := -64000) (B := 14000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv7 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (46001 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (9333 / 2000 : ℝ) * N) :
    (N : ℝ) * (cw (46001 / 10000 : ℝ) (9333 / 2000 : ℝ) (5 : ℝ) (-1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (46001 / 10000 : ℝ) (9333 / 2000 : ℝ) (5 : ℝ) (-1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 46001 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2000 * p ≤ 9333 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (46001 / 10000 : ℝ) (9333 / 2000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell7 hN hp1 h1' h2'
  exact cw_kap_cert (a := (46001 / 10000 : ℝ)) (b := (9333 / 2000 : ℝ)) (A := 5000) (B := -1000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv8 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (11667 / 2500 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (23437 / 5000 : ℝ) * N) :
    (N : ℝ) * (cw (11667 / 2500 : ℝ) (23437 / 5000 : ℝ) (75 : ℝ) (-16 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (11667 / 2500 : ℝ) (23437 / 5000 : ℝ) (75 : ℝ) (-16 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 11667 * N < 2500 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 5000 * p ≤ 23437 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (11667 / 2500 : ℝ) (23437 / 5000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell8 hN hp1 h1' h2'
  exact cw_kap_cert (a := (11667 / 2500 : ℝ)) (b := (23437 / 5000 : ℝ)) (A := 75000) (B := -16000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv9 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (3077 / 625 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (12321 / 2500 : ℝ) * N) :
    (N : ℝ) * (cw (3077 / 625 : ℝ) (12321 / 2500 : ℝ) (-64 : ℝ) (13 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (3077 / 625 : ℝ) (12321 / 2500 : ℝ) (-64 : ℝ) (13 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 3077 * N < 625 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 2500 * p ≤ 12321 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (3077 / 625 : ℝ) (12321 / 2500 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell9 hN hp1 h1' h2'
  exact cw_kap_cert (a := (3077 / 625 : ℝ)) (b := (12321 / 2500 : ℝ)) (A := -64000) (B := 13000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

theorem mtv10 {N p : ℕ} (hN : 100000 ≤ N) (hp : p.Prime) (h1 : (49287 / 10000 : ℝ) * N < p)
    (h2 : (p : ℝ) ≤ (24999 / 5000 : ℝ) * N) :
    (N : ℝ) * (cw (49287 / 10000 : ℝ) (24999 / 5000 : ℝ) (5 : ℝ) (-1 : ℝ)).K.eval ((p : ℝ) / N) - 2 ≤ ((mtLB3 design adm).kap N p : ℝ) ∧
    (N : ℝ) * (cw (49287 / 10000 : ℝ) (24999 / 5000 : ℝ) (5 : ℝ) (-1 : ℝ)).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  haveI := Fact.mk hp
  have hN0 : 0 < N := by omega
  have h1' : 49287 * N < 10000 * p := win_lo (by norm_num) (by norm_num) h1
  have h2' : 5000 * p ≤ 24999 * N := win_hi (by norm_num) (by norm_num) h2
  have hp1 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hpool := pool_cert (49287 / 10000 : ℝ) (24999 / 5000 : ℝ) hN0 (by omega : 2 * p ≤ 59 * N)
  refine ⟨?_, hpool⟩
  have hc := mtcell10 hN hp1 h1' h2'
  exact cw_kap_cert (a := (49287 / 10000 : ℝ)) (b := (24999 / 5000 : ℝ)) (A := 5000) (B := -1000) (d := 1000) (by norm_num)
    (by norm_num) (by norm_num) hN0 (by push_cast; linarith)

/-- The certified MT (1) windows. -/
def mtWins : List KapWindow :=
  [cw (42943 / 10000 : ℝ) (5403 / 1250 : ℝ) (-73 : ℝ) (17 : ℝ),
   cw (43227 / 10000 : ℝ) (10833 / 2500 : ℝ) (-140 : ℝ) (65 / 2 : ℝ),
   cw (8667 / 2000 : ℝ) (8727 / 2000 : ℝ) (16 : ℝ) (-7 / 2 : ℝ),
   cw (21819 / 5000 : ℝ) (21851 / 5000 : ℝ) (112 : ℝ) (-51 / 2 : ℝ),
   cw (8741 / 2000 : ℝ) (43999 / 10000 : ℝ) (53 : ℝ) (-12 : ℝ),
   cw (44001 / 10000 : ℝ) (11029 / 2500 : ℝ) (75 : ℝ) (-17 : ℝ),
   cw (11429 / 2500 : ℝ) (45999 / 10000 : ℝ) (-64 : ℝ) (14 : ℝ),
   cw (46001 / 10000 : ℝ) (9333 / 2000 : ℝ) (5 : ℝ) (-1 : ℝ),
   cw (11667 / 2500 : ℝ) (23437 / 5000 : ℝ) (75 : ℝ) (-16 : ℝ),
   cw (3077 / 625 : ℝ) (12321 / 2500 : ℝ) (-64 : ℝ) (13 : ℝ),
   cw (49287 / 10000 : ℝ) (24999 / 5000 : ℝ) (5 : ℝ) (-1 : ℝ)]

/-- Their exact integrated gain. -/
def mtGain : ℝ := (35863749 / 400000000 : ℝ)
theorem mtWins_area : (mtWins.map (KapWindow.area 58)).sum = mtGain := by
  simp only [mtWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area, mtGain]
  norm_num

theorem mtWins_pos : ∀ w ∈ mtWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [mtWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem mtWins_ord : mtWins.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [mtWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem mtWins_rec : ∀ w ∈ mtWins, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  simp only [mtWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;> simp only [cw] <;> norm_num

theorem mtWins_lt : ∀ w ∈ mtWins, w.b ≤ 6 := by
  intro w hw
  simp only [mtWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem mtWins_cert : ∀ w ∈ mtWins, WinCert (mtLB3 design adm) w := by
  intro w hw
  simp only [mtWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv0 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv1 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv2 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv3 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv4 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv5 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv6 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv7 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv8 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv9 hN hp h1 h2
  · filter_upwards [eventually_ge_atTop 100000] with N hN p hp h1 h2
    exact mtv10 hN hp h1 h2

/-- The families of the ledger so far. -/
def fams3 : List (NullityLB design) := [ledgerLB, mtLB3 design adm]

/-- The windows of the ledger so far (MT (1) below `x = 6`, Ledger2 above). -/
def wins3 : List KapWindow := mtWins ++ wins2

/-- Total gain of `wins3`. -/
def gain3 : ℝ := mtGain + gain2

theorem wins2_ge : ∀ t ∈ wins2, (6 : ℝ) ≤ t.a := by
  intro t ht
  simp only [wins2, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem wins3_area : (wins3.map (KapWindow.area 58)).sum = gain3 := by
  simp only [wins3, List.map_append, List.sum_append, mtWins_area, wins2_area, gain3]

theorem wins3_pos : ∀ w ∈ wins3, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact mtWins_pos w h
  · exact wins2_pos w h

theorem wins3_ord : wins3.Pairwise (fun s t => s.b ≤ t.a) := by
  unfold wins3
  rw [List.pairwise_append]
  exact ⟨mtWins_ord, wins2_ord, fun s hs t ht => (mtWins_lt s hs).trans (wins2_ge t ht)⟩

theorem wins3_rec : ∀ w ∈ wins3, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact mtWins_rec w h
  · exact wins2_rec w h

theorem wins3_cert : ∀ w ∈ wins3, ∃ lb ∈ fams3, WinCert lb w := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact ⟨mtLB3 design adm, by simp [fams3], mtWins_cert w h⟩
  · exact ⟨ledgerLB, by simp [fams3], wins2_cert w h⟩

/-- **Partial growth, Ledger2 + MT (1).**  `log D_N <= (24733/4 + (2673/8) log 2 - gain3 + eps) N^2`. -/
theorem partial_growth3 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams3) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain3 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams3 wins3 gain3 wins3_area wins3_pos wins3_ord wins3_rec wins3_cert hε

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger3
