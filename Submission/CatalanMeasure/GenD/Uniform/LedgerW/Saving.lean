module

public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.PriceGrowth

@[expose] public section

/-!
# The compatible saving from a nullity profile and a pool profile (lane G4)

For an arbitrary `NullityLB` the odd price is `min (pool, 2n - kap)`, so the saving relative to
the pool is `(kap - (2n - pool))_+`.  This module proves the linear lower bound used by the
window certificates: `kap + pool - 2n <= saving` (`kap <= n` always, since `kap <= nullity`),
and records that the recycling-safe bound agrees with the original off the recycling band.
-/

namespace CatalanMeasure.GenD.Uniform.LedgerW

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Arithmetic

noncomputable section

/-- A nullity lower bound never exceeds `n`. -/
theorem kap_le_n (P : Parameters) (lb : NullityLB P) {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) : lb.kap N p ≤ P.n N := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (lb.ok N p hN hp hp2 hH).trans (Nat.sub_le _ _)

/-- Natural-number form of the saving inequality. -/
theorem saving_ge_nat (P : Parameters) (lb : NullityLB P) (N p : ℕ)
    (hk : lb.kap N p ≤ 2 * P.n N) :
    lb.kap N p + safeOddLoss P N p ≤ saving P lb N p + 2 * P.n N := by
  have h := saving_eq_excess P lb N p hk
  have hp := safeOddLoss_le_twice P N p
  omega

/-- The saving dominates `kap + pool - 2n`. -/
theorem saving_ge_real (P : Parameters) (lb : NullityLB P) {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) :
    (lb.kap N p : ℝ) + (safeOddLoss P N p : ℝ) - 2 * (P.n N : ℝ) ≤ (saving P lb N p : ℝ) := by
  have hk := kap_le_n P lb hN hp hp2 hH
  have h := saving_ge_nat P lb N p (by omega)
  have h' : ((lb.kap N p + safeOddLoss P N p : ℕ) : ℝ) ≤
      ((saving P lb N p + 2 * P.n N : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith only [h']

/-- Off the recycling band the recycling-safe bound is the original. -/
theorem recyclingSafeLB_kap_of_not_band (P : Parameters) (lb : NullityLB P) {N p : ℕ}
    (h : ¬ (N < p ∧ p ≤ 2 * N)) : (recyclingSafeLB P lb).kap N p = lb.kap N p := by
  simp [recyclingSafeLB, h]

/-- One window certificate: eventual linear lower bounds for `kap` (up to a charge) and for the
pool give the saving certificate `N F(p/N) - 1 <= saving + sl + charge`, where
`F = K + G - 2 n0`. -/
theorem saving_window_cert (P : Parameters) (lb : NullityLB P) {N p : ℕ} (hN : 0 < N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (K G c : ℝ) (hc : 0 ≤ c)
    (chg : ℕ) (hK : (N : ℝ) * K - c ≤ (lb.kap N p : ℝ) + chg)
    (hG : (N : ℝ) * G - c ≤ (safeOddLoss P N p : ℝ)) :
    (N : ℝ) * (K + G - 2 * (P.n0 : ℝ)) - 1 ≤
      (saving P lb N p : ℝ) + (⌈2 * c⌉₊ : ℝ) + chg := by
  have h := saving_ge_real P lb hN hp hp2 hH
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := by simp [Parameters.n]
  have hceil : 2 * c ≤ (⌈2 * c⌉₊ : ℝ) := Nat.le_ceil _
  have hnn : (0 : ℝ) ≤ (chg : ℝ) := Nat.cast_nonneg _
  nlinarith only [h, hK, hG, hn, hceil, hnn]

end

end CatalanMeasure.GenD.Uniform.LedgerW
