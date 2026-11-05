module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# A prime in `(X, 3X]` not dividing `b`

If every prime in `(X, 3X]` divided `b`, their product would divide `b`, so
`θ(3X) - θ(X) ≤ log b`.  Chebyshev's bounds `θ(x) ≤ x log 4` and
`θ(x) ≥ (x - 1) log 2 - log (x + 2) - 2 √x log x` (both in Mathlib) make the left side
at least `X log 2 - o(X)`.  So once `log b ≤ X / 4` and `X` is large, such a prime exists.
-/

open Real Chebyshev Finset Filter Asymptotics

namespace CatalanMeasure

/-- The primes in `(⌊x⌋₊, ⌊y⌋₊]`. -/
noncomputable def windowPrimes (x y : ℝ) : Finset ℕ :=
  (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime

theorem theta_sub_eq_sum_window {x y : ℝ} (hxy : x ≤ y) :
    θ y - θ x = ∑ p ∈ windowPrimes x y, log p := by
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hI : Finset.Icc 0 ⌊y⌋₊ = Finset.Icc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [theta_eq_sum_Icc, theta_eq_sum_Icc, windowPrimes, hI, Finset.filter_union,
    Finset.sum_union]
  · ring
  · rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp hp'
    omega

/-- The sublinear error terms in Chebyshev's lower bound. -/
noncomputable def chebError (X : ℝ) : ℝ :=
  2 * √(3 * X) * log (3 * X) + log (3 * X + 2) + log 2

theorem chebError_isLittleO : chebError =o[atTop] (fun X : ℝ => X) := by
  -- `log =o √` and `√ * √ = id` give `√x log x =o x`; then compose with `x ↦ 3x`.
  have hlog : (fun x : ℝ => log x) =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hsq : (fun x : ℝ => √x * log x) =o[atTop] (fun x : ℝ => √x * x ^ (1 / 2 : ℝ)) :=
    (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO hlog
  have hsq' : (fun x : ℝ => √x * log x) =o[atTop] (fun x : ℝ => x) := by
    refine hsq.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hx]
  have h3 : Tendsto (fun X : ℝ => 3 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hT1 : (fun X : ℝ => 2 * √(3 * X) * log (3 * X)) =o[atTop] (fun X : ℝ => X) := by
    have h : (fun X : ℝ => √(3 * X) * log (3 * X)) =o[atTop] (fun X : ℝ => 3 * X) := by
      simpa [Function.comp_def] using hsq'.comp_tendsto h3
    have h' : (fun X : ℝ => √(3 * X) * log (3 * X)) =o[atTop] (fun X : ℝ => X) :=
      h.trans_isBigO (isBigO_const_mul_self 3 (fun X : ℝ => X) atTop)
    simpa [mul_assoc] using h'.const_mul_left 2
  have hT2 : (fun X : ℝ => log (3 * X + 2)) =o[atTop] (fun X : ℝ => X) := by
    have h32 : Tendsto (fun X : ℝ => 3 * X + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 h3
    have h : (fun X : ℝ => log (3 * X + 2)) =o[atTop] (fun X : ℝ => 3 * X + 2) := by
      simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.comp_tendsto h32
    refine h.trans_isBigO (IsBigO.of_bound 5 ?_)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  have hT3 : (fun _ : ℝ => log (2 : ℝ)) =o[atTop] (fun X : ℝ => X) := by
    exact isLittleO_const_id_atTop (log (2 : ℝ))
  have h := (hT1.add hT2).add hT3
  refine h.congr' ?_ EventuallyEq.rfl
  exact Eventually.of_forall (fun X => by simp [chebError])

theorem eventually_chebError_le : ∀ᶠ X : ℝ in atTop, chebError X ≤ X / 10 := by
  have h := (chebError_isLittleO.def (by norm_num : (0 : ℝ) < 1 / 10))
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with X hX hX0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hX0] at hX
  linarith [le_abs_self (chebError X)]

/-- **Prime window.** If `X ≥ 1`, the Chebyshev error is at most `X / 10`, and
`log b ≤ X / 4`, then some prime `p` with `X < p ≤ 3X` does not divide `b`. -/
theorem exists_prime_window_not_dvd {b : ℕ} (hb : 0 < b) {X : ℝ} (hX : 1 ≤ X)
    (herr : chebError X ≤ X / 10) (hlogb : log b ≤ X / 4) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ (p : ℝ) ≤ 3 * X ∧ ¬ p ∣ b := by
  by_contra hcon
  push Not at hcon
  -- every prime of the window divides `b`
  have hdiv : ∀ p ∈ windowPrimes X (3 * X), p ∣ b := by
    intro p hp
    simp only [windowPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
    apply hcon p hprime
    · exact (Nat.floor_lt (by linarith)).mp hlo
    · exact (Nat.le_floor_iff (by linarith)).mp hhi
  have hprod : (∏ p ∈ windowPrimes X (3 * X), p) ∣ b :=
    Finset.prod_primes_dvd b
      (fun p hp => (Finset.mem_filter.mp hp).2.prime) hdiv
  have hprod_le : (∏ p ∈ windowPrimes X (3 * X), p) ≤ b := Nat.le_of_dvd hb hprod
  have hpos : ∀ p ∈ windowPrimes X (3 * X), (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hsum_le : ∑ p ∈ windowPrimes X (3 * X), log (p : ℝ) ≤ log b := by
    rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
    apply Real.log_le_log
    · exact Finset.prod_pos hpos
    · rw [← Nat.cast_prod]
      exact_mod_cast hprod_le
  -- Chebyshev bounds
  have h3 : (1 : ℝ) ≤ 3 * X := by linarith
  have hlow := theta_ge' h3
  have hup := theta_le_log4_mul_x (by linarith : (0 : ℝ) ≤ X)
  have hwin := theta_sub_eq_sum_window (by linarith : X ≤ 3 * X)
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 : (0.5 : ℝ) ≤ log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have key : X * log 2 - chebError X ≤ X / 4 := by
    unfold chebError
    rw [hlog4] at hup
    linarith [hsum_le, hlow, hup, hwin, hlogb]
  have hXlog : X * 0.5 ≤ X * log 2 := mul_le_mul_of_nonneg_left hlog2 hX0
  linarith

end CatalanMeasure
