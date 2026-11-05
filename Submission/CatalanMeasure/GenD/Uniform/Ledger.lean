module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Ledger

/-- The exact constrained real selector budget, including the boundary regime. -/
noncomputable def B2 (n s : Real) : Real :=
  if s ≤ 2*n then n*s/2+s^2/8 else n*s-n^2/2

/-- The selector quadratic after substituting H-b=n+s. -/
noncomputable def selectorQuadratic (n C s m l : Real) : Real :=
  (3/2)*m^2+(1/2)*l^2-(n+s+C)*m-C*l+C*n

/-- Monotonicity to the boundary and completion of the square prove the clamped
budget for every admissible selector. No interior-minimizer hypothesis is used. -/
theorem selector_quadratic_lower {n C s m l : Real}
    (hm : 0 ≤ m) (hl : 0 ≤ l) (hml : m+l ≤ n) (hCn : n ≤ C) :
    -B2 n s ≤ selectorQuadratic n C s m l := by
  have hu : 0 ≤ n-m-l := by linarith
  have hc : 0 ≤ C-n+m := by linarith
  have hprod := mul_nonneg hu hc
  have hreduce : selectorQuadratic n C s m l =
      selectorQuadratic n C s m (n-m) +
        (n-m-l)*(C-n+m)+(n-m-l)^2/2 := by unfold selectorQuadratic; ring
  unfold B2
  split_ifs with hs
  · have hboundary : selectorQuadratic n C s m (n-m) + (n*s/2+s^2/8) =
        2*(m-(2*n+s)/4)^2 := by unfold selectorQuadratic; ring
    nlinarith only [hreduce, hboundary, hprod, sq_nonneg (n-m-l),
      sq_nonneg (m-(2*n+s)/4)]
  · have hsm : 0 ≤ s-2*n := by linarith
    have hnm : 0 ≤ n-m := by linarith
    have hp := mul_nonneg hsm hnm
    have hboundary : selectorQuadratic n C s m (n-m) + (n*s-n^2/2) =
        2*(n-m)^2+(s-2*n)*(n-m) := by unfold selectorQuadratic; ring
    nlinarith only [hreduce, hboundary, hp, hprod, sq_nonneg (n-m), sq_nonneg (n-m-l)]

/-- An actual feasible minimizer; this proves sharpness of the real budget. -/
noncomputable def minimizingM (n s : Real) : Real := if s ≤ 2*n then (2*n+s)/4 else n

theorem minimizingM_feasible {n s : Real} (hn : 0 ≤ n) (hs : 0 ≤ s) :
    0 ≤ minimizingM n s ∧ minimizingM n s ≤ n := by
  unfold minimizingM
  split_ifs with h <;> constructor <;> linarith

theorem minimizingM_value (n C s : Real) :
    selectorQuadratic n C s (minimizingM n s) (n-minimizingM n s) = -B2 n s := by
  unfold minimizingM B2 selectorQuadratic
  split_ifs <;> ring

theorem B2_nonneg {n s : Real} (hn : 0 ≤ n) (hs : 0 ≤ s) : 0 ≤ B2 n s := by
  unfold B2
  split_ifs with h
  · positivity
  · have hsn : 0 ≤ s-n/2 := by linarith
    have hm := mul_nonneg hn hsn
    nlinarith only [hm]

/-- The older unconstrained square budget is safe but can be strictly larger. -/
theorem B2_le_unconstrained (n s : Real) : B2 n s ≤ n*s/2+s^2/8 := by
  unfold B2
  split_ifs with h
  · exact le_rfl
  · nlinarith only [sq_nonneg (s-2*n)]

/-- Combining a raw pool and a rank price is a minimum, never additive savings. -/
noncomputable def compatiblePrice (n pool rankGain : Real) : Real := min pool (2*n-rankGain)

noncomputable def compatibleSaving (n pool rankGain : Real) : Real :=
  max 0 (rankGain-(2*n-pool))

theorem compatiblePrice_eq_pool_sub_saving (n pool rankGain : Real) :
    compatiblePrice n pool rankGain = pool-compatibleSaving n pool rankGain := by
  unfold compatiblePrice compatibleSaving
  by_cases h : pool ≤ 2*n-rankGain
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · have hh : 2*n-rankGain ≤ pool := le_of_not_ge h
    rw [min_eq_right hh, max_eq_right (by linarith)]
    ring

theorem compatiblePrice_nonneg {n pool rankGain : Real}
    (hp : 0 ≤ pool) (hr : rankGain ≤ 2*n) : 0 ≤ compatiblePrice n pool rankGain :=
  le_min hp (sub_nonneg.mpr hr)

theorem compatiblePrice_le_pool (n pool rankGain : Real) :
    compatiblePrice n pool rankGain ≤ pool := min_le_left _ _

#print axioms selector_quadratic_lower
#print axioms minimizingM_value
end CatalanMeasure.GenD.Uniform.Ledger