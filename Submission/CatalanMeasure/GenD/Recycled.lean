module

public import Submission.CatalanMeasure.RecycledPNTWindow

@[expose] public section

/-!
# Recycled-polynomial criterion with a free lower window end (module 5)

`irrationality_measure_of_recycled_polynomials_window` is the existing criterion with
`V = (κ - w) L` in place of `V = (κ - 1) L`; the hypothesis `2 < κ` becomes `2 w < κ`.
The coefficient hypothesis `hcoeff` is unchanged (recycled primes `q ≤ 2p`).
-/

open Real Filter Chebyshev Polynomial Finset
open scoped Topology BigOperators

namespace CatalanMeasure.GenD

/-- Window-parametrised sibling of `irrationality_measure_of_recycled_polynomials_window`:
the lower window end is `V = (κ - w) L` (`w = 1` is the original). -/
theorem irrationality_measure_of_recycled_polynomials_window
    (G : ℝ) (d : ℕ) {η ρ κ δ w : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hw0 : 0 < w) (hκ : 2 * w < κ) (hδ : 0 < δ)
    (hwindow : 1 < 2 * (w - δ * (2 * κ - w)))
    (hlinear : η < 2 * (d : ℝ))
    (hpay : (d : ℝ) + 4 * d * δ * κ < η * κ)
    (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ p, (Q p).natDegree ≤ d * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2 * p →
      ∀ i ≤ d * p, (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x - G| ≤ exp (-(ρ * p)) → |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(ρ * κ)) < |G - a / b| := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : 0 < κ - w := by linarith
  have hθ := OAI.Zeta5.W12.ImportedPNTCoreBridge.theta_ratio_tendsto_one
  have hlo : ∀ᶠ x : ℝ in atTop, (1 - δ) * x ≤ θ x := by
    filter_upwards [(tendsto_order.mp hθ).1 (1 - δ) (by linarith),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    exact ((le_div_iff₀ hx0).mp hx.le)
  have hhi : ∀ᶠ x : ℝ in atTop, θ x ≤ (1 + δ) * x := by
    filter_upwards [(tendsto_order.mp hθ).2 (1 + δ) (by linarith),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    exact ((div_le_iff₀ hx0).mp hx.le)
  obtain ⟨X₀, htheta⟩ := eventually_atTop.mp (hlo.and hhi)
  have hlogb : Tendsto (fun b : ℕ => (κ - w) * log b) atTop atTop :=
    Tendsto.const_mul_atTop hκ1 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hbig := hlogb.eventually (eventually_ge_atTop (max X₀ (max (P₀ : ℝ) 1)))
  filter_upwards [hbig, eventually_ge_atTop 2] with b hb hb2 a
  by_contra hcon
  push Not at hcon
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0R : (0 : ℝ) < b := by linarith
  have hL : 0 < log (b : ℝ) := Real.log_pos hbR
  let L : ℝ := log b
  let U : ℝ := κ * L
  let V : ℝ := (κ - w) * L
  have hV0 : 0 ≤ V := by dsimp [V, L]; positivity
  have hVU : V ≤ U := by dsimp [V, U]; nlinarith only [mul_pos hw0 hL]
  have hXV : X₀ ≤ V := le_trans (le_max_left _ _) hb
  have hPV : (P₀ : ℝ) ≤ V := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hb)
  have hV1 : (1 : ℝ) ≤ V := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hb)
  have hthetaV := htheta V hXV
  have hthetaU := htheta U (le_trans hXV hVU)
  have hgap : log b < 2 * (θ U - θ V) := by
    have hw := mul_pos (sub_pos.mpr hwindow) hL
    dsimp [U, V] at hthetaU hthetaV
    change L < 2 * (θ U - θ V)
    nlinarith only [hthetaU.1, hthetaV.2, hw]
  obtain ⟨p, hp, hpV, hpU, hpb, hafter⟩ :=
    exists_largest_prime_window_not_square_dvd hb0 hV0 hVU hgap
  have hP₀ : P₀ ≤ p := by exact_mod_cast (le_trans hPV hpV.le)
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpθ := htheta p (le_trans hXV hpV.le)
  have hpU0 : (0 : ℝ) ≤ p := hp0R.le
  let S := windowPrimes (p : ℝ) U
  let B : ℕ := ∏ q ∈ S, q ^ 2
  have hSprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact ((mem_windowPrimes_iff_of_nonneg hpU0 hpU).mp hq).1
  have hSdiv : ∀ q ∈ S, q ^ 2 ∣ b := by
    intro q hq
    obtain ⟨hqprime, hpq, hqU⟩ := (mem_windowPrimes_iff_of_nonneg hpU0 hpU).mp hq
    exact hafter q hqprime hpq hqU
  have hScoeff : ∀ q ∈ S, ∀ i ≤ d * p, (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i := by
    intro q hq
    obtain ⟨hqprime, hpq, hqU⟩ := (mem_windowPrimes_iff_of_nonneg hpU0 hpU).mp hq
    have hpqN : p < q := by exact_mod_cast hpq
    have hq2p : q ≤ 2 * p := by
      have hscale : U < 2 * V := by
        dsimp [U, V]
        nlinarith only [mul_pos (sub_pos.mpr hκ) hL]
      have : (q : ℝ) ≤ 2 * p := by linarith
      exact_mod_cast this
    exact hcoeff p hP₀ hp q hqprime hpqN hq2p
  have hBdiv : B ∣ b := prime_square_prod_dvd S b hSprime hSdiv
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBdiv hb0
  have hB0R : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hlogB : log (B : ℝ) = 2 * (θ U - θ p) :=
    log_prime_square_window_product hpU0 hpU
  have hclose : |(a : ℝ) / b - G| ≤ exp (-(ρ * p)) := by
    rw [abs_sub_comm]
    refine hcon.trans ?_
    rw [Real.rpow_def_of_pos hb0R]
    apply Real.exp_le_exp.mpr
    have hρp := mul_le_mul_of_nonneg_left hpU hρ.le
    dsimp [U, L] at hρp
    nlinarith only [hρp]
  have hsmallQ := hsmall p hP₀ hp _ hclose
  have hne := hnz p hP₀ hp a b hb0 hpb
  have h1 := one_le_prime_square_prod_recycled_pow_mul_abs_aeval
    (Q p) (hdeg p) a hb0 S hSprime hSdiv hScoeff hne
  have hpow : ((b : ℝ) / B) ^ (d * p) =
      exp ((d : ℝ) * p * (L - 2 * (θ U - θ p))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos hb0R hB0R),
      Real.log_div hb0R.ne' hB0R.ne', hlogB]
    congr 1
    push_cast
    ring
  have he : 1 ≤ exp ((d : ℝ) * p * (L - 2 * (θ U - θ p)) - η * (p : ℝ)^2) := by
    calc
      (1 : ℝ) ≤ ((b : ℝ) / B) ^ (d * p) * |aeval ((a : ℝ) / b) (Q p)| := h1
      _ ≤ exp ((d : ℝ) * p * (L - 2 * (θ U - θ p))) *
          exp (-(η * (p : ℝ)^2)) := by
        rw [hpow]
        exact mul_le_mul_of_nonneg_left hsmallQ (exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; rfl
  have hexp := Real.one_le_exp_iff.mp he
  have hpkey : η * p ≤ (d : ℝ) * (L - 2 * (θ U - θ p)) := by
    by_contra hh
    have hh' : (d : ℝ) * (L - 2 * (θ U - θ p)) - η * p < 0 := by linarith
    have := mul_neg_of_pos_of_neg hp0R hh'
    nlinarith only [hexp, this]
  have hT : U - p - 2 * δ * U ≤ θ U - θ p := by
    have hδp := mul_le_mul_of_nonneg_left hpU hδ.le
    nlinarith only [hthetaU.1, hpθ.2, hδp]
  have hdT := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * d)
  have htop := mul_le_mul_of_nonneg_left hpU (by linarith : (0 : ℝ) ≤ 2 * d - η)
  have hpaid := mul_pos (sub_pos.mpr hpay) hL
  dsimp [U, L] at hdT htop hpkey
  nlinarith only [hdT, htop, hpkey, hpaid]


end CatalanMeasure.GenD
