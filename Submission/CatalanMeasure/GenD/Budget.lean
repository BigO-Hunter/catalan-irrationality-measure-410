module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Design-generic scalar budgets (module 3 of the G-displacement Lean plan)

Pure real algebra, no design constants.  The logarithm of 2 enters as a real `ℓ` with
rational bounds `lo ≤ ℓ ≤ hi`; the instance supplies `lo, hi` (for `Real.log 2` the Mathlib
`d9` interval) and all ledger constants (`c07 = 1 - (b+q+g)/n`, `c26 = 3 - (b+q+2g)/n`,
caps, costs).

* `quad_nonpos`: `A + s a - 2 ℓ a^2 ≤ 0` from the discriminant `s^2 + 8 ℓ A ≤ 0`.
* `second_budget`, `first_budget`: the two energy budgets for every admissible `a` (and `t`).
  The residual coefficient `res = (n-g)/n` cancels from both sides.
* `Pay`: the hypotheses of the recycled-polynomial criterion in the design's own unit `N`
  (`n = n0 N`), with the recycling window `(p, θ p]`; `θ = 2` is the existing criterion.
* `ChebGate`: the legacy Chebyshev gate `3ρ max(d0/(η+χ), 4) < 3B - 1`.
* `xval`: the ledger value `x = d0 ρ / (η + χ - 4 d0 δ)`, invariant under the unit change
  `(ρ, η, χ, δ, d0) ↦ (tρ, t²η, t²χ, tδ, t d0)`.
-/

namespace CatalanMeasure.GenD
namespace Budget

/-- A concave quadratic with non-positive discriminant is non-positive. -/
theorem quad_nonpos {ℓ A s a : ℝ} (hℓ : 0 < ℓ) (hd : s ^ 2 + 8 * ℓ * A ≤ 0) :
    A + s * a - 2 * ℓ * a ^ 2 ≤ 0 := by
  have h : 8 * ℓ * (A + s * a - 2 * ℓ * a ^ 2) ≤ 0 := by
    nlinarith only [hd, sq_nonneg (4 * ℓ * a - s)]
  by_contra hc
  push Not at hc
  have h8 : (0 : ℝ) < 8 * ℓ := by positivity
  have := mul_pos h8 hc
  linarith only [this, h]

/-- Second-trial budget. `Nn` = norm cap, `M` = field cap, `r` = residual cap, `nc` = near cap,
`T` = target, `cost` = second cost. -/
theorem second_budget {ℓ lo hi c07 c26 res Nn M r nc T cost m a t : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ ℓ) (hh : ℓ ≤ hi) (h07 : 0 ≤ c07) (h26 : 0 ≤ c26)
    (hobj : Nn + M + T - c07 * lo ≤ -m)
    (hdisc : (c26 * hi - M + r - cost) ^ 2 ≤ 8 * lo * m)
    (hnear : hi - r + nc ≤ 0) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + t - t ^ 2) * ℓ + Nn + (1 - a) * M
        + a * (1 - a) * ℓ + (a - t) * r + t * nc + res * a ≤
      -T + ℓ / 2 + (cost + res) * a := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hlo hl
  have hE : (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + t - t ^ 2) * ℓ + Nn + (1 - a) * M
        + a * (1 - a) * ℓ + (a - t) * r + t * nc + res * a -
      (-T + ℓ / 2 + (cost + res) * a) =
      (Nn + M + T - c07 * ℓ) + a * (c26 * ℓ - M + r - cost) - 2 * ℓ * a ^ 2
        + t * (ℓ - r + nc) - ℓ * t ^ 2 := by ring
  have h1 : Nn + M + T - c07 * ℓ ≤ -m := by
    nlinarith only [hobj, mul_nonneg h07 (sub_nonneg.2 hl)]
  have h2 : c26 * ℓ - M + r - cost ≤ c26 * hi - M + r - cost := by
    nlinarith only [mul_nonneg h26 (sub_nonneg.2 hh)]
  have h3 : a * (c26 * ℓ - M + r - cost) ≤ a * (c26 * hi - M + r - cost) :=
    mul_le_mul_of_nonneg_left h2 ha
  have h4 : -m + (c26 * hi - M + r - cost) * a - 2 * lo * a ^ 2 ≤ 0 :=
    quad_nonpos (A := -m) hlo (by nlinarith only [hdisc])
  have h5 : -(2 * ℓ * a ^ 2) ≤ -(2 * lo * a ^ 2) := by
    nlinarith only [mul_nonneg (sub_nonneg.2 hl) (sq_nonneg a)]
  have h6 : t * (ℓ - r + nc) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (by linarith only [hh, hnear])
  have h7 : 0 ≤ ℓ * t ^ 2 := by positivity
  nlinarith only [hE, h1, h3, h4, h5, h6, h7]

/-- First-trial budget, for every real `a`. `n1, F1` = first norm and field caps, `Lm` = the lambda
weight times lambda, `cost1` = first cost. -/
theorem first_budget {ℓ lo hi c07 c26 res n1 F1 Lm T cost1 m a : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ ℓ) (hh : ℓ ≤ hi) (h07 : 0 ≤ c07) (h26 : 0 ≤ c26)
    (hobj : n1 + F1 + T - c07 * lo ≤ -m) (hm : 0 ≤ m)
    (hdisc : (c26 * hi - F1 + Lm - cost1) ^ 2 ≤ 8 * lo * m)
    (hneg : cost1 ≤ c26 * lo - F1 + Lm) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * ℓ + n1 + (1 - a) * F1
        + a * (1 - a) * ℓ + a * Lm + res * a ≤
      -T + ℓ / 2 + (cost1 + res) * a := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hlo hl
  have hE : (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * ℓ + n1 + (1 - a) * F1
        + a * (1 - a) * ℓ + a * Lm + res * a - (-T + ℓ / 2 + (cost1 + res) * a) =
      (n1 + F1 + T - c07 * ℓ) + a * (c26 * ℓ - F1 + Lm - cost1) - 2 * ℓ * a ^ 2 := by ring
  have h1 : n1 + F1 + T - c07 * ℓ ≤ -m := by
    nlinarith only [hobj, mul_nonneg h07 (sub_nonneg.2 hl)]
  rcases le_or_gt 0 a with ha | ha
  · have h2 : c26 * ℓ - F1 + Lm - cost1 ≤ c26 * hi - F1 + Lm - cost1 := by
      nlinarith only [mul_nonneg h26 (sub_nonneg.2 hh)]
    have h3 : a * (c26 * ℓ - F1 + Lm - cost1) ≤ a * (c26 * hi - F1 + Lm - cost1) :=
      mul_le_mul_of_nonneg_left h2 ha
    have h4 : -m + (c26 * hi - F1 + Lm - cost1) * a - 2 * lo * a ^ 2 ≤ 0 :=
      quad_nonpos (A := -m) hlo (by nlinarith only [hdisc])
    have h5 : -(2 * ℓ * a ^ 2) ≤ -(2 * lo * a ^ 2) := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hl) (sq_nonneg a)]
    nlinarith only [hE, h1, h3, h4, h5]
  · have h2 : 0 ≤ c26 * ℓ - F1 + Lm - cost1 := by
      nlinarith only [hneg, mul_nonneg h26 (sub_nonneg.2 hl)]
    have h3 : a * (c26 * ℓ - F1 + Lm - cost1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le h2
    have h7 : 0 ≤ ℓ * a ^ 2 := by positivity
    nlinarith only [hE, h1, h3, h7, hm]

/-- Curvature `-ℓ` version of `quad_nonpos` (no `a (1 - a) ℓ` term in the energy). -/
theorem quad_nonpos' {ℓ A s a : ℝ} (hℓ : 0 < ℓ) (hd : s ^ 2 + 4 * ℓ * A ≤ 0) :
    A + s * a - ℓ * a ^ 2 ≤ 0 := by
  have h : 4 * ℓ * (A + s * a - ℓ * a ^ 2) ≤ 0 := by
    nlinarith only [hd, sq_nonneg (2 * ℓ * a - s)]
  by_contra hc
  push Not at hc
  have h8 : (0 : ℝ) < 4 * ℓ := by positivity
  have := mul_pos h8 hc
  linarith only [this, h]

/-- Second-trial budget for the endpoint column field (energy without the `α log (1 + s)` term,
hence without `a (1 - a) ℓ`): leading coefficient `-ℓ`, discriminant with `4 ℓ m`, and the
linear coefficient `(c26 - 1) ℓ`. -/
theorem second_budget' {ℓ lo hi c07 c26 res Nn M r nc T cost m a t : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ ℓ) (hh : ℓ ≤ hi) (h07 : 0 ≤ c07) (h26 : 0 ≤ c26 - 1)
    (hobj : Nn + M + T - c07 * lo ≤ -m)
    (hdisc : ((c26 - 1) * hi - M + r - cost) ^ 2 ≤ 4 * lo * m)
    (hnear : hi - r + nc ≤ 0) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + t - t ^ 2) * ℓ + Nn + (1 - a) * M
        + (a - t) * r + t * nc + res * a ≤
      -T + ℓ / 2 + (cost + res) * a := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hlo hl
  have hE : (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + t - t ^ 2) * ℓ + Nn + (1 - a) * M
        + (a - t) * r + t * nc + res * a -
      (-T + ℓ / 2 + (cost + res) * a) =
      (Nn + M + T - c07 * ℓ) + a * ((c26 - 1) * ℓ - M + r - cost) - ℓ * a ^ 2
        + t * (ℓ - r + nc) - ℓ * t ^ 2 := by ring
  have h1 : Nn + M + T - c07 * ℓ ≤ -m := by
    nlinarith only [hobj, mul_nonneg h07 (sub_nonneg.2 hl)]
  have h2 : (c26 - 1) * ℓ - M + r - cost ≤ (c26 - 1) * hi - M + r - cost := by
    nlinarith only [mul_nonneg h26 (sub_nonneg.2 hh)]
  have h3 : a * ((c26 - 1) * ℓ - M + r - cost) ≤ a * ((c26 - 1) * hi - M + r - cost) :=
    mul_le_mul_of_nonneg_left h2 ha
  have h4 : -m + ((c26 - 1) * hi - M + r - cost) * a - lo * a ^ 2 ≤ 0 :=
    quad_nonpos' (A := -m) hlo (by nlinarith only [hdisc])
  have h5 : -(ℓ * a ^ 2) ≤ -(lo * a ^ 2) := by
    nlinarith only [mul_nonneg (sub_nonneg.2 hl) (sq_nonneg a)]
  have h6 : t * (ℓ - r + nc) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (by linarith only [hh, hnear])
  have h7 : 0 ≤ ℓ * t ^ 2 := by positivity
  nlinarith only [hE, h1, h3, h4, h5, h6, h7]

/-- Second-trial budget for the endpoint column field, large marked fraction `a ≥ α1 > 0`: the
constant term `Nn + M + T - c07 ℓ ≤ u` (`u ≥ 0` may be positive, e.g. after a target shift) is
absorbed into the linear coefficient, `u ≤ (u / α1) a`, at the price `u / α1` in the cost. -/
theorem second_budget'_large {ℓ lo hi c07 c26 res Nn M r nc T cost u α1 a t : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ ℓ) (hh : ℓ ≤ hi) (h07 : 0 ≤ c07) (h26 : 0 ≤ c26 - 1)
    (hα : 0 < α1) (hu : 0 ≤ u)
    (hobj : Nn + M + T - c07 * lo ≤ u)
    (hcost : ((c26 - 1) * hi - M + r - cost) - lo * α1 + u / α1 ≤ 0)
    (hnear : hi - r + nc ≤ 0) (haα : α1 ≤ a) (ht : 0 ≤ t) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + t - t ^ 2) * ℓ + Nn + (1 - a) * M
        + (a - t) * r + t * nc + res * a ≤
      -T + ℓ / 2 + (cost + res) * a := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hlo hl
  have ha : 0 ≤ a := le_trans hα.le haα
  have hE : (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + t - t ^ 2) * ℓ + Nn + (1 - a) * M
        + (a - t) * r + t * nc + res * a -
      (-T + ℓ / 2 + (cost + res) * a) =
      (Nn + M + T - c07 * ℓ) + a * ((c26 - 1) * ℓ - M + r - cost) - ℓ * a ^ 2
        + t * (ℓ - r + nc) - ℓ * t ^ 2 := by ring
  have h1 : Nn + M + T - c07 * ℓ ≤ u := by
    nlinarith only [hobj, mul_nonneg h07 (sub_nonneg.2 hl)]
  have h1' : u ≤ a * (u / α1) := by
    have : u = α1 * (u / α1) := by field_simp
    have h2 : 0 ≤ u / α1 := div_nonneg hu hα.le
    nlinarith only [this, h2, haα]
  have h2 : (c26 - 1) * ℓ - M + r - cost ≤ (c26 - 1) * hi - M + r - cost := by
    nlinarith only [mul_nonneg h26 (sub_nonneg.2 hh)]
  have h3 : a * ((c26 - 1) * ℓ - M + r - cost) ≤ a * ((c26 - 1) * hi - M + r - cost) :=
    mul_le_mul_of_nonneg_left h2 ha
  have h5 : ℓ * a ^ 2 ≥ lo * α1 * a := by
    have : lo * α1 ≤ ℓ * a := mul_le_mul hl haα hα.le hℓ.le
    nlinarith only [this, ha, sq_nonneg a]
  have h6 : t * (ℓ - r + nc) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (by linarith only [hh, hnear])
  have h7 : 0 ≤ ℓ * t ^ 2 := by positivity
  have h8 : a * (((c26 - 1) * hi - M + r - cost) - lo * α1 + u / α1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hcost
  nlinarith only [hE, h1, h1', h3, h5, h6, h7, h8]

/-- First-trial budget for the endpoint column field (no `a (1 - a) ℓ` term). -/
theorem first_budget' {ℓ lo hi c07 c26 res n1 F1 Lm T cost1 m a : ℝ}
    (hlo : 0 < lo) (hl : lo ≤ ℓ) (hh : ℓ ≤ hi) (h07 : 0 ≤ c07) (h26 : 0 ≤ c26 - 1)
    (hobj : n1 + F1 + T - c07 * lo ≤ -m) (hm : 0 ≤ m)
    (hdisc : ((c26 - 1) * hi - F1 + Lm - cost1) ^ 2 ≤ 4 * lo * m)
    (hneg : cost1 ≤ (c26 - 1) * lo - F1 + Lm) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * ℓ + n1 + (1 - a) * F1
        + a * Lm + res * a ≤
      -T + ℓ / 2 + (cost1 + res) * a := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hlo hl
  have hE : (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * ℓ + n1 + (1 - a) * F1
        + a * Lm + res * a - (-T + ℓ / 2 + (cost1 + res) * a) =
      (n1 + F1 + T - c07 * ℓ) + a * ((c26 - 1) * ℓ - F1 + Lm - cost1) - ℓ * a ^ 2 := by ring
  have h1 : n1 + F1 + T - c07 * ℓ ≤ -m := by
    nlinarith only [hobj, mul_nonneg h07 (sub_nonneg.2 hl)]
  rcases le_or_gt 0 a with ha | ha
  · have h2 : (c26 - 1) * ℓ - F1 + Lm - cost1 ≤ (c26 - 1) * hi - F1 + Lm - cost1 := by
      nlinarith only [mul_nonneg h26 (sub_nonneg.2 hh)]
    have h3 : a * ((c26 - 1) * ℓ - F1 + Lm - cost1) ≤ a * ((c26 - 1) * hi - F1 + Lm - cost1) :=
      mul_le_mul_of_nonneg_left h2 ha
    have h4 : -m + ((c26 - 1) * hi - F1 + Lm - cost1) * a - lo * a ^ 2 ≤ 0 :=
      quad_nonpos' (A := -m) hlo (by nlinarith only [hdisc])
    have h5 : -(ℓ * a ^ 2) ≤ -(lo * a ^ 2) := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hl) (sq_nonneg a)]
    nlinarith only [hE, h1, h3, h4, h5]
  · have h2 : 0 ≤ (c26 - 1) * ℓ - F1 + Lm - cost1 := by
      nlinarith only [hneg, mul_nonneg h26 (sub_nonneg.2 hl)]
    have h3 : a * ((c26 - 1) * ℓ - F1 + Lm - cost1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le h2
    have h7 : 0 ≤ ℓ * a ^ 2 := by positivity
    nlinarith only [hE, h1, h3, h7, hm]

/-- Hypotheses of the recycled-polynomial criterion in the design's own unit, with recycling
window `(p, θ p]` (`θ = 2` is `irrationality_measure_of_recycled_polynomials_square_pnt`). -/
def Pay (θ d0 ρ η χ κ δ B : ℝ) : Prop :=
  ρ * κ = B ∧ 0 < η + χ ∧ 0 < ρ ∧ θ < κ * (θ - 1) ∧ 0 < δ ∧
    1 < 2 * (1 - δ * (2 * κ - 1)) ∧ η + χ < 2 * d0 ∧ d0 + 4 * d0 * δ * κ < (η + χ) * κ

/-- The legacy Chebyshev gate. -/
def ChebGate (d0 ρ η χ B : ℝ) : Prop := 3 * ρ * max (d0 / (η + χ)) 4 < 3 * B - 1

/-- The ledger value `x`: the smallest `B` allowed by `d0 + 4 d0 δ κ < (η+χ) κ`, `κ = B/ρ`. -/
noncomputable def xval (d0 ρ η χ δ : ℝ) : ℝ := d0 * ρ / (η + χ - 4 * d0 * δ)

/-- `x` is invariant under the unit change `N ↦ N/t`. -/
theorem xval_scale {t d0 ρ η χ δ : ℝ} (ht : 0 < t) :
    xval (t * d0) (t * ρ) (t ^ 2 * η) (t ^ 2 * χ) (t * δ) = xval d0 ρ η χ δ := by
  unfold xval
  by_cases h : η + χ - 4 * d0 * δ = 0
  · have : t ^ 2 * η + t ^ 2 * χ - 4 * (t * d0) * (t * δ) = 0 := by
      have : t ^ 2 * η + t ^ 2 * χ - 4 * (t * d0) * (t * δ) = t ^ 2 * (η + χ - 4 * d0 * δ) := by
        ring
      rw [this, h, mul_zero]
    rw [h, this]; simp
  · have h2 : t ^ 2 * η + t ^ 2 * χ - 4 * (t * d0) * (t * δ) ≠ 0 := by
      have : t ^ 2 * η + t ^ 2 * χ - 4 * (t * d0) * (t * δ) = t ^ 2 * (η + χ - 4 * d0 * δ) := by
        ring
      rw [this]; exact mul_ne_zero (by positivity) h
    have ht0 : t ≠ 0 := ht.ne'
    field_simp

/-- `pay` gives `B > x` (when `η + χ > 4 d0 δ`). -/
theorem lt_B_of_pay {d0 ρ η χ κ δ B : ℝ} (hρ : 0 < ρ) (hB : ρ * κ = B)
    (hd : 0 < η + χ - 4 * d0 * δ) (hpay : d0 + 4 * d0 * δ * κ < (η + χ) * κ) :
    xval d0 ρ η χ δ < B := by
  unfold xval
  rw [div_lt_iff₀ hd, ← hB]
  nlinarith only [mul_lt_mul_of_pos_left hpay hρ]

end Budget
end CatalanMeasure.GenD
