module

public import Submission.CatalanMeasure.GenD.D58.Budget
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# D58 = (58,9,3,5,3): scalar budgets of the bank `K590` (B = 590, witness `gi`)

Instance of `GenD.Budget` (reference-unit ledger `w590/q/k160_gi_qual.out`,
unit convention of `D58.Budget`); the data are those of the K = 160 witness `gi`
(34 real tails and 41 complex points at `eps = 1/100`), qualified at `B = 590`:
`x = 275547530000 / 467666483 = 589.19666...`, `B - x = 0.80334`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Budget Real
noncomputable section

namespace K590
def normCap : ℝ := 1547241039 / 2000000000
def fieldCap : ℝ := -253949899 / 100000000
def residualCap : ℝ := -315531 / 5000000
def target : ℝ := 563964709 / 250000000
def secondCost : ℝ := 214443 / 50000
def firstCost : ℝ := 409661 / 100000
def rhoRef : ℝ := 519901 / 5000
def etaRef : ℝ := 4748967 / 5000000
def B : ℝ := 590
def rho : ℝ := 58 * secondCost + (29 / 10) * wcap
def eta : ℝ := t ^ 2 * etaRef
def kappaRef : ℝ := B / rhoRef
def kappa : ℝ := B / rho

theorem rhoRef_eq : rhoRef = 20 * secondCost + wcap := by norm_num [rhoRef, secondCost, wcap]
theorem rho_eq : rho = t * rhoRef := by norm_num [rho, rhoRef, secondCost, wcap, t]
theorem rho_kappa : rho * kappa = B := by
  have : rho ≠ 0 := by norm_num [rho, secondCost, wcap]
  unfold kappa; field_simp

theorem x_ref : xval d0ref rhoRef etaRef chiRef deltaRef = 275547530000 / 467666483 := by
  norm_num [xval, d0ref, rhoRef, etaRef, chiRef, deltaRef]

theorem x_own : xval d0 rho eta chi delta = 275547530000 / 467666483 := by
  rw [d0_eq, rho_eq, eta, chi, delta, xval_scale (by norm_num [t])]
  exact x_ref

theorem x_bank : 275547530000 / 467666483 < B ∧ B - 275547530000 / 467666483 > 1 / 3 := by
  constructor <;> norm_num [B]

theorem pay_ref : Pay 2 d0ref rhoRef etaRef chiRef kappaRef deltaRef B := by
  unfold Pay kappaRef
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [B, d0ref, rhoRef, etaRef, chiRef, deltaRef]

theorem cheb_ref : ChebGate d0ref rhoRef etaRef chiRef B := by
  unfold ChebGate
  rw [max_eq_left (by norm_num [d0ref, etaRef, chiRef] : (4 : ℝ) ≤ d0ref / (etaRef + chiRef))]
  norm_num [B, d0ref, rhoRef, etaRef, chiRef]

theorem second_budget_log2 {a tt : ℝ} (ha : 0 ≤ a) (htt : 0 ≤ tt) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + tt - tt ^ 2) * Real.log 2 + normCap
        + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 + (a - tt) * residualCap
        + tt * nearCap + (9 / 10 : ℝ) * a ≤
      -target + Real.log 2 / 2 + (secondCost + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact second_budget (m := -(normCap + fieldCap + target - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c26, hi, lo, normCap, fieldCap, target, c07, residualCap, secondCost])
    (by norm_num [hi, residualCap, nearCap]) ha htt

theorem first_budget_log2 (a : ℝ) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * Real.log 2 + n1 + (1 - a) * F1
        + a * (1 - a) * Real.log 2 + a * Lm + (9 / 10 : ℝ) * a ≤
      -target + Real.log 2 / 2 + (firstCost + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact first_budget (m := -(n1 + F1 + target - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c07, lo, n1, F1, target])
    (by norm_num [c26, hi, lo, n1, F1, target, c07, Lm, firstCost])
    (by norm_num [c26, lo, F1, Lm, firstCost])

/-! ### ρ-saving S1: costs for the endpoint column field (budgets without `a (1 - a) log 2`) -/

/-- Second cost for the energy without the `α log (1 + s)` term:
`≥ (47/29) hi + 2.53949899 - 0.0631062 - 2 √(lo m') = 3.5968919…`. -/
def secondCost' : ℝ := 3596893 / 1000000
/-- First cost for the endpoint column field, `≥ 3.5495414…`. -/
def firstCost' : ℝ := 3549542 / 1000000

/-- Column cost `ρ' = 58 · max(c₁', c₂'') + Ψ` with `c₂'' = secondCost'` (the `max` is
`secondCost'`, see `firstCost'_le_secondCost'`), as a function of the weight-plus-binomial
exponent `Ψ`. -/
def rhoEnd (Ψ : ℝ) : ℝ := 58 * max firstCost' secondCost' + Ψ

theorem firstCost'_le_secondCost' : firstCost' ≤ secondCost' := by
  norm_num [firstCost', secondCost']

theorem rhoEnd_eq (Ψ : ℝ) : rhoEnd Ψ = 58 * secondCost' + Ψ := by
  unfold rhoEnd; rw [max_eq_right firstCost'_le_secondCost']

theorem rhoEnd_val (Ψ : ℝ) : rhoEnd Ψ = 208619794 / 1000000 + Ψ := by
  rw [rhoEnd_eq]; norm_num [secondCost']

/-- The Theorem A cost at `α₁ = 1/16` (`g = 8.334`, `G = g/58²`) is covered by `secondCost'`. -/
theorem secondCost'_ge_alpha1 :
    c26 * hi - fieldCap + residualCap - hi - lo * (1 / 16) +
        ((8334 / 1000) / 58 ^ 2 - -(normCap + fieldCap + target - c07 * lo)) / (1 / 16) ≤
      secondCost' := by
  norm_num [c26, hi, lo, fieldCap, residualCap, normCap, target, c07, secondCost']

theorem rhoEnd_at_Psi0 (Ψ : ℝ) (hΨ : Ψ = 879663 / 10000) :
    rhoEnd Ψ ≤ 2965861 / 10000 := by
  rw [rhoEnd_val, hΨ]; norm_num

theorem second_budget'_log2 {a tt : ℝ} (ha : 0 ≤ a) (htt : 0 ≤ tt) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + tt - tt ^ 2) * Real.log 2 + normCap
        + (1 - a) * fieldCap + (a - tt) * residualCap
        + tt * nearCap + (9 / 10 : ℝ) * a ≤
      -target + Real.log 2 / 2 + (secondCost' + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact second_budget' (m := -(normCap + fieldCap + target - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c26, hi, lo, normCap, fieldCap, target, c07, residualCap, secondCost'])
    (by norm_num [hi, residualCap, nearCap]) ha htt

theorem first_budget'_log2 (a : ℝ) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * Real.log 2 + n1 + (1 - a) * F1
        + a * Lm + (9 / 10 : ℝ) * a ≤
      -target + Real.log 2 / 2 + (firstCost' + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact first_budget' (m := -(n1 + F1 + target - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c07, lo, n1, F1, target])
    (by norm_num [c26, hi, lo, n1, F1, target, c07, Lm, firstCost'])
    (by norm_num [c26, lo, F1, Lm, firstCost'])

/-! ### Theorem A: the End budgets at the shifted target `target0` -/

/-- The Theorem A target `target0 = target + A / 58²`, `A = 8.29824` (the gain consumed by
`Signed.gain_ok410`: `A = 58² (target0 - target)`). -/
def target0 : ℝ := target + 829824 / 336400000

theorem target0_sub : 58 ^ 2 * (target0 - target) = 829824 / 100000 := by
  norm_num [target0]

/-- Second budget at `target0` for the marked fraction `a ≥ α₁ = 1/16`: cost `secondCost'`
(the constant `target0 - target` costs `16 (target0 - target)` in the linear coefficient, covered
by `secondCost'_ge_alpha1`, which has the larger shift `8.334 / 58²`). -/
theorem second_budget'_log2_target0 {a tt : ℝ} (ha : 1 / 16 ≤ a) (htt : 0 ≤ tt) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2 + tt - tt ^ 2) * Real.log 2 + normCap
        + (1 - a) * fieldCap + (a - tt) * residualCap
        + tt * nearCap + (9 / 10 : ℝ) * a ≤
      -target0 + Real.log 2 / 2 + (secondCost' + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact second_budget'_large (u := normCap + fieldCap + target0 - c07 * lo) (res := 9 / 10)
    (α1 := 1 / 16) (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26])
    (by norm_num) (by norm_num [normCap, fieldCap, target0, target, c07, lo]) le_rfl
    (by norm_num [c26, hi, lo, normCap, fieldCap, target0, target, c07, residualCap, secondCost'])
    (by norm_num [hi, residualCap, nearCap]) ha htt

/-- First budget at `target0`, every `a`, with cost `secondCost'` (the cost of `rhoEnd`; the first
trial is below it, `firstCost'_le_secondCost'`, but `firstCost'` itself does not fit at
`target0`). -/
theorem first_budget'_log2_target0 (a : ℝ) :
    (-(c07 - 1 / 2) + (c26 - 1) * a - a ^ 2) * Real.log 2 + n1 + (1 - a) * F1
        + a * Lm + (9 / 10 : ℝ) * a ≤
      -target0 + Real.log 2 / 2 + (secondCost' + 9 / 10) * a := by
  obtain ⟨hl, hh⟩ := log2_bounds
  exact first_budget' (m := -(n1 + F1 + target0 - c07 * lo)) (res := 9 / 10)
    (by norm_num [lo]) hl hh (by norm_num [c07]) (by norm_num [c26]) (by norm_num)
    (by norm_num [c07, lo, n1, F1, target0, target])
    (by norm_num [c26, hi, lo, n1, F1, target0, target, c07, Lm, secondCost'])
    (by norm_num [c26, lo, F1, Lm, secondCost'])

end K590

end
end D58
end CatalanMeasure.GenD
