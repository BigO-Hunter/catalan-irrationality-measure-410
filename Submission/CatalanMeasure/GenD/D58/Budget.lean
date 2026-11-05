module

public import Submission.CatalanMeasure.GenD.Budget
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# D58 = (58,9,3,5,3): common scalar data for the bank instances of `GenD.Budget`

The bank instance used by the release is `K590` (`D58.Budget590`); the choice of K is data only.

Unit convention (R1): Lean works in the design's own `N` (`n = 58 N`).  The qualified ledgers
(`witness-final/q/n58_qual.out`) are in reference units `n0 = 20`
(`n = 20 N'`, `N' = (29/10) N`).  With `t = 29/10`:  `ρ ↦ tρ`, `η, χ ↦ t²η, t²χ`, `δ ↦ tδ`,
`d0 ↦ t d0`, `κ ↦ κ/t`; caps, `c2`, `c07`, `c26` are dimensionless; the cover constant `w` scales like
`ρ`, and `ρ = n0 c2 + w`.  `x` is invariant (`xval_scale`).

Finding: with the existing criterion (recycling window `(p, 2p]`) the Lean-unit `κ = B/ρ` is below 2
(`not_pay_two`); the window must be widened to `(p, θ p]`, `θ ≥ 21/10` (`pay_own`).

Provenance: all data V (Arb/Fraction-qualified, not Lean-reviewed): `witness-final/notes.md`,
config `q/cfg_final_n58.json`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Budget Real
noncomputable section

/-! ### common data -/
def c07 : ℝ := 41 / 58
def c26 : ℝ := 76 / 29
def lo : ℝ := 6931471803 / 10 ^ 10
def hi : ℝ := 6931471808 / 10 ^ 10
def nearCap : ℝ := -77 / 100
def n1 : ℝ := 67761 / 100000
def F1 : ℝ := -248835 / 100000
/-- `λ · (2g/n) = 1.68493357 · 5/29` -/
def Lm : ℝ := 168493357 / 10 ^ 8 * (5 / 29)
def wcap : ℝ := 18203 / 1000
def t : ℝ := 29 / 10
def chiRef : ℝ := 4551 / 2000
def deltaRef : ℝ := 1 / 10 ^ 7
def d0ref : ℝ := 530 / 29
def d0 : ℝ := 53
def delta : ℝ := t * deltaRef
def chi : ℝ := t ^ 2 * chiRef

theorem d0_eq : d0 = t * d0ref := by norm_num [d0, d0ref, t]

theorem log2_bounds : lo ≤ Real.log 2 ∧ Real.log 2 ≤ hi := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> [skip; skip] <;> norm_num [lo, hi] at h1 h2 ⊢ <;> linarith


end
end D58
end CatalanMeasure.GenD
