module

public import Submission.CatalanMeasure.Criterion
public import Submission.OAI.NumberTheory.Catalan.PrimeLimits.ImportedPNTCoreBridge

@[expose] public section

/-!
# The measure criterion with a prime-number-theorem window

`CatalanMeasure.Criterion` finds a prime `p ∤ b` in `(X, 3X]` from Chebyshev's bounds, which
costs a factor `3` in the exponent.  With the prime number theorem `θ(x) ~ x` (available in
OpenAI's workspace through the patched PrimeNumberTheoremAnd, `theta_ratio_tendsto_one`), the
window `(X, (1 + ε) X]` works for every `ε > 0`, and the exponent becomes
`(1 + ε) ρ (max (d / η) (c / ε) + 1) + 1` for any `c > 1`.
-/

open Real Filter Chebyshev Polynomial
open scoped Topology

namespace CatalanMeasure

/-- If every prime in `(X, Y]` divides `b`, then `θ Y - θ X ≤ log b`. -/
theorem theta_window_le_log {b : ℕ} (hb : 0 < b) {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hall : ∀ p : ℕ, p.Prime → X < p → (p : ℝ) ≤ Y → p ∣ b) :
    θ Y - θ X ≤ log b := by
  rw [theta_sub_eq_sum_window hXY]
  have hdiv : ∀ p ∈ windowPrimes X Y, p ∣ b := by
    intro p hp
    simp only [windowPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
    apply hall p hprime
    · exact (Nat.floor_lt hX).mp hlo
    · exact (Nat.le_floor_iff (by linarith)).mp hhi
  have hprod : (∏ p ∈ windowPrimes X Y, p) ∣ b :=
    Finset.prod_primes_dvd b (fun p hp => (Finset.mem_filter.mp hp).2.prime) hdiv
  have hprod_le : (∏ p ∈ windowPrimes X Y, p) ≤ b := Nat.le_of_dvd hb hprod
  have hpos : ∀ p ∈ windowPrimes X Y, (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
  apply Real.log_le_log
  · exact Finset.prod_pos hpos
  · rw [← Nat.cast_prod]
    exact_mod_cast hprod_le

/-- **Prime window from the prime number theorem.**  For `ε > 0` and `c > 1`, once `X` is large,
every `b ≥ 1` with `log b ≤ ε X / c` has a prime `p ∤ b` in `(X, (1 + ε) X]`. -/
theorem eventually_prime_window_not_dvd {ε c : ℝ} (hε : 0 < ε) (hc : 1 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℕ, 0 < b → log b ≤ ε * X / c →
      ∃ p : ℕ, p.Prime ∧ X < p ∧ (p : ℝ) ≤ (1 + ε) * X ∧ ¬ p ∣ b := by
  have hc0 : 0 < c := by linarith
  set δ : ℝ := ε * (c - 1) / (2 * c * (2 + ε)) with hδdef
  have hδ0 : 0 < δ := by
    have : 0 < c - 1 := by linarith
    positivity
  have hδ : δ * (2 + ε) = ε * (c - 1) / (2 * c) := by
    rw [hδdef]
    field_simp
  have hθ := OAI.Zeta5.W12.ImportedPNTCoreBridge.theta_ratio_tendsto_one
  have hlo : ∀ᶠ x : ℝ in atTop, 1 - δ < θ x / x := (tendsto_order.mp hθ).1 _ (by linarith)
  have hhi : ∀ᶠ x : ℝ in atTop, θ x / x < 1 + δ := (tendsto_order.mp hθ).2 _ (by linarith)
  have hscale : Tendsto (fun X : ℝ => (1 + ε) * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  filter_upwards [hhi, hscale.eventually hlo, eventually_gt_atTop (0 : ℝ)] with X hX1 hX2 hX0
  intro b hb hlogb
  by_contra hcon
  push Not at hcon
  have hY : X ≤ (1 + ε) * X := by nlinarith
  have hw := theta_window_le_log hb hX0.le hY hcon
  have h1 : (1 - δ) * ((1 + ε) * X) < θ ((1 + ε) * X) :=
    (lt_div_iff₀ (by positivity)).mp hX2
  have h2 : θ X < (1 + δ) * X := (div_lt_iff₀ hX0).mp hX1
  have hδX : δ * (2 + ε) * X = ε * (c - 1) / (2 * c) * X := by rw [hδ]
  have hkey : ε * X / c ≤ ε * X - ε * (c - 1) / (2 * c) * X := by
    have hεX : 0 < ε * X := mul_pos hε hX0
    have : ε * X - ε * (c - 1) / (2 * c) * X - ε * X / c = ε * X * (c - 1) / (2 * c) := by
      field_simp
      ring
    have h3 : 0 ≤ ε * X * (c - 1) / (2 * c) := by
      have : 0 ≤ c - 1 := by linarith
      positivity
    linarith
  nlinarith [mul_pos hε hX0]

/-- **Irrationality-measure criterion, prime number theorem version.** -/
theorem irrationality_measure_of_polynomials_pnt (G : ℝ) (d : ℕ) {η ρ ε c : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hε : 0 < ε) (hc : 1 < c) (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ p, (Q p).natDegree ≤ d * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ∣ b →
        aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ, |x - G| ≤ exp (-(ρ * p)) →
        |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((1 + ε) * ρ * max ((d : ℝ) / η) (c / ε))) < |G - a / b| := by
  have hc0 : 0 < c := by linarith
  set κ : ℝ := max ((d : ℝ) / η) (c / ε) with hκ
  have hκε : c / ε ≤ κ := le_max_right _ _
  have hκd : (d : ℝ) / η ≤ κ := le_max_left _ _
  have hκ0 : 0 < κ := by
    have : 0 < c / ε := by positivity
    linarith
  have hεκ : c ≤ ε * κ := by
    have h := mul_le_mul_of_nonneg_left hκε hε.le
    rw [mul_div_cancel₀ _ hε.ne'] at h
    linarith
  have hlogb : Tendsto (fun b : ℕ => κ * log b) atTop atTop :=
    Tendsto.const_mul_atTop hκ0 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ b : ℕ in atTop,
      (∀ b' : ℕ, 0 < b' → log b' ≤ ε * (κ * log b) / c →
        ∃ p : ℕ, p.Prime ∧ κ * log b < p ∧ (p : ℝ) ≤ (1 + ε) * (κ * log b) ∧ ¬ p ∣ b') ∧
      max (P₀ : ℝ) 1 ≤ κ * log b :=
    (hlogb.eventually (eventually_prime_window_not_dvd hε hc)).and
      (hlogb.eventually (eventually_ge_atTop _))
  filter_upwards [hev, eventually_ge_atTop 2] with b hb hb2 a
  obtain ⟨hwin, hbig⟩ := hb
  by_contra hcon
  push Not at hcon
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0R : (0 : ℝ) < b := by linarith
  have hlogpos : 0 < log (b : ℝ) := Real.log_pos hbR
  have hlogX : log b ≤ ε * (κ * log b) / c := by
    rw [le_div_iff₀ hc0]
    nlinarith [mul_le_mul_of_nonneg_right hεκ hlogpos.le]
  obtain ⟨p, hp, hXp, hpX, hpb⟩ := hwin b hb0 hlogX
  have hP₀ : P₀ ≤ p := by
    have h : (P₀ : ℝ) < p := lt_of_le_of_lt (le_trans (le_max_left _ _) hbig) hXp
    exact_mod_cast h.le
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hclose : |(a : ℝ) / b - G| ≤ exp (-(ρ * p)) := by
    rw [abs_sub_comm]
    refine hcon.trans ?_
    rw [Real.rpow_def_of_pos hb0R]
    apply Real.exp_le_exp.mpr
    have h : ρ * p ≤ ρ * ((1 + ε) * (κ * log b)) := mul_le_mul_of_nonneg_left hpX hρ.le
    nlinarith
  have hQ := hsmall p hP₀ hp _ hclose
  have hne := hnz p hP₀ hp a b hb0 hpb
  have h1 := one_le_pow_mul_abs_aeval (Q p) (hdeg p) a hb0 hne
  have hpow : (b : ℝ) ^ (d * p) = exp ((d : ℝ) * p * log b) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hb0R]
    congr 1
    push_cast
    ring
  have hdlog : (d : ℝ) * log b < η * p := by
    have h' : (d : ℝ) / η * log b < p :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hκd hlogpos.le) hXp
    calc (d : ℝ) * log b = η * ((d : ℝ) / η * log b) := by field_simp
      _ < η * p := mul_lt_mul_of_pos_left h' hη
  have hlt : (d : ℝ) * p * log b - η * (p : ℝ) ^ 2 < 0 := by
    nlinarith [mul_lt_mul_of_pos_right hdlog hppos]
  have hsmall' : (b : ℝ) ^ (d * p) * |aeval ((a : ℝ) / b) (Q p)| < 1 := by
    calc (b : ℝ) ^ (d * p) * |aeval ((a : ℝ) / b) (Q p)|
        ≤ exp ((d : ℝ) * p * log b) * exp (-(η * (p : ℝ) ^ 2)) := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_left hQ (exp_pos _).le
      _ = exp ((d : ℝ) * p * log b - η * (p : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr hlt
  linarith

end CatalanMeasure
