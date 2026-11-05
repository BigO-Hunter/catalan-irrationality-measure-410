module

public import Submission.CatalanMeasure.GenD.PL
public import Submission.CatalanMeasure.Parametric.UpperPrimeValuation
public import Submission.CatalanMeasure.Parametric.LowerPrimePool
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.OddPrimeEvenStartingZero

@[expose] public section

/-!
# Odd-prime profile for an arbitrary design (module 7 of the G-displacement Lean plan)

Design-free.  For `Parameters` `P` and a prime `p` with `H < p²`, `p ≤ H`:
`-(oddLossNat P N p) ≤ v_p(det)`, where `oddLossNat` is `lowerPrimeLoss` for `2p ≤ H` and
`upperPrimeLoss` otherwise (the existing generic valuation theorems; the upper regime needs the
four linear side conditions `UpperSide`, discharged by `omega` in the instance).

The real profile: for a piecewise-linear `f : PL.Prof` with `loss ≤ N f(p/N)` on the two regimes,
`-(N f(p/N)) ≤ v_p(det)`.  The instance proves the two regime inequalities segment by segment
with `loss_eq_segment`, whose hypotheses are named linear facts (`omega`) and the evaluation of
`hingeSlope` / `hingeIntercept` (`norm_num`).  `prime_sum_tendsto_from_zero` is the weighted
prime-sum limit over `(0, M N]` for a profile that is constant on `[0,1]`.
-/

namespace CatalanMeasure.GenD
namespace OddProfile

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators

noncomputable section

/-- The odd-prime loss: lower pool for `2p ≤ H`, upper pool otherwise. -/
def oddLossNat (P : Parameters) (N p : ℕ) : ℕ :=
  if 2 * p ≤ P.H N then lowerPrimeLoss P N p else upperPrimeLoss P N p

/-- Side conditions of the upper regime. -/
structure UpperSide (P : Parameters) (N p : ℕ) : Prop where
  hA : P.A N ≤ p
  hLH : P.L N < P.H N
  hbp : P.b N < p
  hJL : P.H N - p ≤ P.L N

/-- Explicit form of the lower loss (truncated subtractions as in the definitions). -/
theorem lowerPrimeLoss_eq (P : Parameters) (N p : ℕ) :
    lowerPrimeLoss P N p = 2 * P.n N -
      (min (min p (P.L N - p)) (P.A N) - max (P.b N) (P.H N - 2 * p) - P.q N) := rfl

/-- Retained size of the upper pool. -/
def upperR (P : Parameters) (N p : ℕ) : ℕ :=
  (P.L N - P.b N) - (min (P.A N) (P.L N - p) - P.b N) -
    (min p (P.L N) - max (P.b N) (P.H N - p))

/-- Paired size of the upper pool. -/
def upperPd (P : Parameters) (N p : ℕ) : ℕ := min (P.A N) (P.L N - p) - P.b N

/-- Exceptional size of the upper pool. -/
def upperE (P : Parameters) (N p : ℕ) : ℕ := min (P.b N) (P.H N - p) - (P.L N - p)

/-- Explicit form of the upper loss. -/
theorem upperPrimeLoss_eq (P : Parameters) (N p : ℕ) :
    upperPrimeLoss P N p = min (2 * P.n N) (min (P.n N + upperR P N p)
      (2 * upperR P N p + upperPd P N p + upperE P N p)) := by
  unfold upperPrimeLoss
  simp only [paramUpperRetainedSize, paramUpperPairedSize, paramUpperExceptionalSize,
    Fintype.card_coe, paramUpperRetainedSet_card, paramUpperPairHighSet_card,
    paramUpperExceptionalSet_card, upperR, upperPd, upperE]

/-- The valuation bound with the piecewise loss, for every admissible design. -/
theorem odd_valuation (P : Parameters) (hAdm : Admissible P) {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hp2 : p ≠ 2) (hHsq : P.H N < p ^ 2) (hpH : p ≤ P.H N)
    (hside : P.H N ≤ 2 * p → UpperSide P N p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -(oddLossNat P N p : ℤ) ≤ padicValRat p (determinantRat P z N) := by
  unfold oddLossNat
  by_cases hhalf : 2 * p ≤ P.H N
  · simp only [hhalf, ↓reduceIte]
    have hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0 :=
      (rational_residue_mul (a := (p : ℚ)) (by simp) hz).1
    exact determinantRat_lower_prime_valuation hAdm hp2 hN hHsq z hzp
  · simp only [hhalf, ↓reduceIte]
    have hs := hside (by omega)
    exact determinantRat_upper_prime_valuation P hAdm hp2 hN hHsq hpH (by omega)
      hs.hA hs.hLH hs.hbp hs.hJL z hz

/-- The real-profile form: `-(N f(p/N)) ≤ v_p(det)` once the profile dominates the loss on each
regime. -/
theorem odd_valuation_profile (P : Parameters) (hAdm : Admissible P) (f : PL.Prof)
    (hlow : ∀ N p : ℕ, 0 < N → 2 * p ≤ P.H N →
      (lowerPrimeLoss P N p : ℝ) ≤ N * f.eval ((p : ℝ) / N))
    (hup : ∀ N p : ℕ, 0 < N → ¬ 2 * p ≤ P.H N → p ≤ P.H N →
      (upperPrimeLoss P N p : ℝ) ≤ N * f.eval ((p : ℝ) / N))
    {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hp2 : p ≠ 2) (hHsq : P.H N < p ^ 2) (hpH : p ≤ P.H N)
    (hside : P.H N ≤ 2 * p → UpperSide P N p) (z : ℚ) (hz : (z.den : ZMod p) ≠ 0) :
    -((N : ℝ) * f.eval ((p : ℝ) / N)) ≤ (padicValRat p (determinantRat P z N) : ℝ) := by
  have h1 := odd_valuation P hAdm hN hp2 hHsq hpH hside z hz
  have h2 : -(oddLossNat P N p : ℝ) ≤ (padicValRat p (determinantRat P z N) : ℝ) := by
    exact_mod_cast h1
  have h3 : (oddLossNat P N p : ℝ) ≤ N * f.eval ((p : ℝ) / N) := by
    unfold oddLossNat
    by_cases hhalf : 2 * p ≤ P.H N
    · simp only [hhalf, ↓reduceIte]; exact hlow N p hN hhalf
    · simp only [hhalf, ↓reduceIte]; exact hup N p hN hhalf hpH
  linarith

/-- One affine segment: if the natural-number loss equals `c N + s p` and `u ≤ p/N ≤ v` lies
between two kinks of `f`, then the loss is exactly `N f(p/N)`.  Thresholds are the fractions
`u1/w1` and `u2/w2`. -/
theorem loss_eq_segment (f : PL.Prof) {N p L : ℕ} (hN : 0 < N) (c s : ℤ)
    (hL : (L : ℤ) = c * N + s * p) {u1 w1 u2 w2 : ℕ} (hw1 : 0 < w1) (hw2 : 0 < w2)
    (h1 : u1 * N ≤ w1 * p) (h2 : w2 * p ≤ u2 * N)
    (hker : ∀ wt ∈ f.L, wt.2 ≤ (u1 : ℝ) / w1 ∨ (u2 : ℝ) / w2 ≤ wt.2)
    (hs : f.c1 + PL.hingeSlope f.L ((u1 : ℝ) / w1) = s)
    (hc : f.c0 - PL.hingeIntercept f.L ((u1 : ℝ) / w1) = c) :
    (L : ℝ) = N * f.eval ((p : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1R : (0 : ℝ) < w1 := by exact_mod_cast hw1
  have hw2R : (0 : ℝ) < w2 := by exact_mod_cast hw2
  have h1R : (u1 : ℝ) * N ≤ w1 * p := by exact_mod_cast h1
  have h2R : (w2 : ℝ) * p ≤ u2 * N := by exact_mod_cast h2
  have hx1 : (u1 : ℝ) / w1 ≤ (p : ℝ) / N := by
    rw [div_le_div_iff₀ hw1R hNR]; linarith
  have hx2 : (p : ℝ) / N ≤ (u2 : ℝ) / w2 := by
    rw [div_le_div_iff₀ hNR hw2R]; linarith
  have hev := PL.Prof.eval_affine f ⟨hx1, hx2⟩ hker
  rw [hs, hc] at hev
  have hLR : (L : ℝ) = c * N + s * p := by exact_mod_cast hL
  rw [hev, hLR]
  field_simp
  ring

/-- Weighted prime sum over `(0, M N]` for a continuous profile that is constant on `[0,1]`. -/
theorem prime_sum_tendsto_from_zero {F : ℝ → ℝ} (hF : Continuous F) (κ : ℝ)
    (hsmall : ∀ x : ℝ, x ≤ 1 → F x = κ) {M : ℕ} (hM : 1 < M) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ Finset.Ioc 0 (M * N) with p.Prime, F ((p : ℝ) / N) * Real.log (p : ℝ)) / N)
      atTop (𝓝 (κ + ∫ x in (1 : ℝ)..M, F x)) := by
  have hM' : (1 : ℝ) < M := by exact_mod_cast hM
  have hzero : ∀ R : ℝ, 0 < R →
      weightedPrimeIntervalSum F 0 1 R = κ * (Chebyshev.theta R / R) := by
    intro R hR
    have hc : weightedPrimeIntervalSum F 0 1 R = weightedPrimeIntervalSum (fun _ => κ) 0 1 R := by
      unfold weightedPrimeIntervalSum
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      have hh : p ≤ ⌊(1 : ℝ) * R⌋₊ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have hr : (p : ℝ) ≤ 1 * R := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 1 * R)).mp hh
      rw [hsmall _ ((div_le_iff₀ hR).mpr hr)]
    rw [hc, weightedPrimeIntervalSum_const]
    simp only [primeIntervalSum, Chebyshev.theta, zero_mul, Nat.floor_zero, one_mul]
  have hfirst := (theta_scaled_tendsto theta_ratio_tendsto_one
    (by norm_num : (0 : ℝ) < 1)).const_mul κ
  have hlast := continuous_weightedPrime_tendsto (F := F) (by norm_num : (0 : ℝ) < 1) hM'
    hF.continuousOn theta_ratio_tendsto_one
  have hh := hfirst.add hlast
  have hall : Tendsto (weightedPrimeIntervalSum F 0 M) atTop (𝓝 (κ + ∫ x in (1 : ℝ)..M, F x)) := by
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hh2 := weightedPrimeIntervalSum_add_adjacent F (by norm_num : (0 : ℝ) ≤ 1) hM'.le hR.le
    rw [hzero R hR] at hh2
    simp only [one_mul] at hh2 ⊢
    rw [hh2.symm]
  have hcomp := hall.comp tendsto_natCast_atTop_atTop
  apply hcomp.congr
  intro N
  have hf : ⌊(M : ℝ) * N⌋₊ = M * N := by
    rw [show (M : ℝ) * N = ((M * N : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  simp only [Function.comp_apply, weightedPrimeIntervalSum, zero_mul, Nat.floor_zero, hf]

end
end OddProfile
end CatalanMeasure.GenD
