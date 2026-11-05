module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Gate3

@[expose] public section
set_option Elab.async false

/-!
# Generic affine window certificate (lane G5g)

`wincert_cw`: an affine window `cw a b c0 c1` is certified against any `lb` as soon as the cleared
inequality `A N + B p <= d (lb.kap N p + 2)` holds for all large `N` and all primes `p` of the window.
`WinCert.shrink` restricts a certified window to a sub-interval with the same profiles.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
noncomputable section

theorem wincert_cw (lb : NullityLB design) {a b c0 c1 : ℝ} {na da nb db : ℕ} {A B : ℤ} {d N0 : ℕ}
    (hd : 0 < d) (hda : 0 < da) (hdb : 0 < db) (ha : a * da = na) (hb : b * db = nb)
    (hc0 : c0 * d = A) (hc1 : c1 * d = B) (hb59 : 2 * nb ≤ 59 * db)
    (hcell : ∀ N p : ℕ, N0 ≤ N → p.Prime → na * N < da * p → db * p ≤ nb * N →
      A * (N : ℤ) + B * (p : ℤ) ≤ (d : ℤ) * (((lb.kap N p : ℕ) : ℤ) + 2)) :
    WinCert lb (cw a b c0 c1) := by
  filter_upwards [eventually_ge_atTop (N0 + 1)] with N hN p hp h1 h2
  have hN0 : 0 < N := by omega
  have h1' : na * N < da * p := win_lo hda ha h1
  have h2' : db * p ≤ nb * N := win_hi hdb hb h2
  have hpool := pool_cert a b (p := p) hN0 (by nlinarith)
  refine ⟨?_, hpool⟩
  exact cw_kap_cert (a := a) (b := b) hd hc0 hc1 hN0 (hcell N p (by omega) hp h1' h2')

theorem WinCert.shrink {lb : NullityLB design} {a b c0 c1 a' b' : ℝ}
    (h : WinCert lb (cw a b c0 c1)) (ha : a ≤ a') (hb : b' ≤ b) : WinCert lb (cw a' b' c0 c1) := by
  filter_upwards [h] with N hN p hp h1 h2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  change a' * N < p at h1
  change (p : ℝ) ≤ b' * N at h2
  exact hN p hp (lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha hN0) h1)
    (le_trans h2 (mul_le_mul_of_nonneg_right hb hN0))

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
