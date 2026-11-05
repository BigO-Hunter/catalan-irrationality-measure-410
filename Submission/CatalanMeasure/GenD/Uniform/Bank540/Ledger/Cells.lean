module

public import Submission.CatalanMeasure.GenD.Uniform.LedgerW.Field
public import Submission.CatalanMeasure.GenD.D58.Normalizer

@[expose] public section
set_option Elab.async false

/-!
# Affine cell windows for the D58 denominator ledger (lane G5c)

A *cell* is a `LedgerW.KapWindow` with an affine nullity profile `K = c0 + c1 x` and the constant
pool minorant `G = 116 = 2 n0` (valid for `x ≤ 29.5`).  Every cell certificate is a cleared
integer inequality `A N + B p ≤ d (kap + 2)`; `cw_kap_cert` turns it into the real certificate
`N K(p/N) - 2 ≤ kap` of `D_growth_of_nullityLB`, and `pool_cert` gives the pool side.
`ledger_growth` is the design-specific instance of `D_growth_field` with `f58`, `kappa0 = 116`,
zero exceptional charge, and the conclusion in the form `24733/4 + (2673/8) log 2 - gain`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

/-- The displaced design `(58,9,3,5,3)`. -/
abbrev design : Parameters := D58.Odd.design

/-- A window with affine `K = c0 + c1 x` and pool minorant `116`. -/
def cw (a b c0 c1 : ℝ) : KapWindow := ⟨a, b, ⟨c0, c1, []⟩, ⟨116, 0, []⟩⟩

theorem cw_area (a b c0 c1 : ℝ) :
    (cw a b c0 c1).area 58 = c0 * (b - a) + c1 * ((b ^ 2 - a ^ 2) / 2) := by
  unfold KapWindow.area cw
  simp only [PL.Prof.area, PL.hingeInt_nil]
  ring

theorem design_n0 : ((design.n0 : ℕ) : ℝ) = 58 := by
  norm_num [design, D58.Odd.design]

/-- Cleared certificate of the `K` side. -/
theorem cw_kap_cert {a b c0 c1 : ℝ} {A B : ℤ} {d : ℕ} (hd : 0 < d) (hc0 : c0 * d = A)
    (hc1 : c1 * d = B) {N p k : ℕ} (hN : 0 < N)
    (h : A * (N : ℤ) + B * (p : ℤ) ≤ (d : ℤ) * ((k : ℤ) + 2)) :
    (N : ℝ) * (cw a b c0 c1).K.eval ((p : ℝ) / N) - 2 ≤ (k : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hev : (N : ℝ) * (cw a b c0 c1).K.eval ((p : ℝ) / N) = c0 * N + c1 * p := by
    simp only [cw, PL.Prof.eval, PL.hinges_nil]
    field_simp
    ring
  rw [hev]
  have hh : (A : ℝ) * N + B * p ≤ (d : ℝ) * ((k : ℝ) + 2) := by exact_mod_cast h
  have h2 : (c0 * N + c1 * p) * d ≤ d * ((k : ℝ) + 2) := by
    have : (c0 * N + c1 * p) * d = (A : ℝ) * N + B * p := by
      rw [← hc0, ← hc1]; ring
    rw [this]; exact hh
  have h3 : c0 * N + c1 * p ≤ (k : ℝ) + 2 := by nlinarith
  linarith

/-- The pool minorant: `safeOddLoss ≥ 116 N` for `x ≤ 29.5`. -/
theorem pool_nat {N p : ℕ} (hN : 0 < N) (h : 2 * p ≤ 59 * N) :
    116 * N ≤ safeOddLoss design N p := by
  have hna : ¬ UpperAvailable design N p := by
    intro hu
    have := hu.2.1
    rw [Odd.design_H] at this
    omega
  rw [safeOddLoss_eq_lower _ _ _ hna, Odd.lower_eq (by omega)]
  unfold Odd.lossNat
  rw [if_pos h]

theorem pool_cert (a b : ℝ) {N p : ℕ} (hN : 0 < N) (h : 2 * p ≤ 59 * N) :
    (N : ℝ) * (cw a b 0 0).G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ) := by
  have h1 := pool_nat hN h
  have h2 : (116 * N : ℝ) ≤ (safeOddLoss design N p : ℝ) := by exact_mod_cast h1
  simp only [cw, PL.Prof.eval, PL.hinges_nil]
  linarith

theorem hloss_safe (N p : ℕ) (hN : 0 < N) (hp : p ≤ design.H N) :
    (safeOddLoss design N p : ℝ) ≤ N * D58.Odd.f58.eval ((p : ℝ) / N) := by
  have h := safeOddLoss_le_old design N p hp (fun h => Odd.side_of hN h)
  have h' : (safeOddLoss design N p : ℝ) ≤ (OddProfile.oddLossNat design N p : ℝ) := by
    exact_mod_cast h
  exact h'.trans (hloss_d58 hN hp).le

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
