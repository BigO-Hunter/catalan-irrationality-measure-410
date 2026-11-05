module

public import Submission.CatalanMeasure.GenD.Signed.LemmaT
public import Submission.CatalanMeasure.GenD.Signed.TiltedTangent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Lemma K: the deficit identity and class containment (A4)

**(i) Deficit identity.**  The one-population Chebyshev energy engine
(`pair_log_add_field_le_trial`, `pair_log_add_cross_le_tilted`) drops the nonnegative square
`Σ_k (m_k - a_k)² / k` (resp. the tilted square `Σ_k ((a_k - m_k) + k β_k / 2)² / k`) in its last
step.  Here the squares are kept:

* `completed_square_hasSum`, `tilted_completed_square_hasSum`: the exact sequence identities,
* `pair_log_add_field_le_trial_sq`, `pair_log_add_cross_le_tilted_sq`: the particle statements,
  `energy + squares ≤ bound`.

**(ii) Class containment.**  A near-optimal configuration (energy within `Δ` of the bound) has every
bracket and the square sum at most `Δ` (`near_optimal_components`).

* `fraction_le_of_field_bracket` (Chebyshev inequality): a field bracket `M - ⟨X⟩ ≤ Δ` bounds the
  fraction of nodes in a set `R` on which `X ≤ s < M` by `Δ / (M - s)`.
* `linear_statistic_bound` (Cauchy–Schwarz): if `Σ d_k² / v_k ≤ Δ` and `Σ F_k² v_k = H`, then
  `|Σ F_k d_k| ≤ √(H Δ)`.
* `mass_lower_bound`: `m(x₊) ≥ g + 1 + δ N`.
* `slope_of_class`: the exact hypothesis `hslope` of `pow_le_norm_blaschke_of_slope`
  (Lemma T′), for a family of statistics with explicit constants, using Chebyshev for small `t` and
  Cauchy–Schwarz for `t ≥ t₀`; `pow_le_norm_blaschke_of_class` chains it with Lemma T′.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset Filter
open scoped BigOperators

noncomputable section

/-! ### Part (i): sequence-level deficit identities -/

/-- The untilted completed square, with the square kept (the identity behind `pin_first_tangent`). -/
theorem completed_square_hasSum (a m : ℕ → ℝ) (ha : Summable (fun k => |a k|)) {S : ℝ}
    (hS : HasSum (fun k : ℕ => m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S) :
    HasSum (fun k : ℕ => (a (k + 1) - m (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (barrierTrialNormSq a - 2 * (∑' k : ℕ, a (k + 1) * m (k + 1) / ((k + 1 : ℕ) : ℝ)) + S) := by
  have hn : ∀ k : ℕ, (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := fun k => by positivity
  have huS := energy_trial_norm_summable a ha
  have ham : Summable (fun k : ℕ => a (k + 1) * m (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    refine Summable.of_norm_bounded ((huS.add hS.summable).div_const 2) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hn k)]
    have h1 : |a (k + 1) * m (k + 1)| ≤ (a (k + 1) ^ 2 + m (k + 1) ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a (k + 1) - m (k + 1)),
        sq_nonneg (a (k + 1) + m (k + 1))]
    calc |a (k + 1) * m (k + 1)| / ((k + 1 : ℕ) : ℝ)
        ≤ ((a (k + 1) ^ 2 + m (k + 1) ^ 2) / 2) / ((k + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right h1 (hn k).le
      _ = (a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) + m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) / 2 := by
          ring
  have H := (huS.hasSum.sub (ham.hasSum.mul_left 2)).add hS
  unfold barrierTrialNormSq
  convert H using 1
  funext k
  have hk := hn k
  field_simp
  ring

/-- The tilted completed square, with the square kept (the identity behind
`tilted_energy_tangent`): the gap `RHS - LHS` is exactly `Σ ((a - m) + k β / 2)² / k`. -/
theorem tilted_completed_square_hasSum (a m β : ℕ → ℝ) (ha : Summable (fun k => |a k|)) {S : ℝ}
    (hS : HasSum (fun k : ℕ => m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S)
    (hβ : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * β (k + 1) ^ 2)) :
    HasSum (fun k : ℕ => ((a (k + 1) - m (k + 1)) + ((k + 1 : ℕ) : ℝ) * β (k + 1) / 2) ^ 2 /
        ((k + 1 : ℕ) : ℝ))
      ((barrierTrialNormSq a - 2 * (∑' k : ℕ, a (k + 1) * m (k + 1) / ((k + 1 : ℕ) : ℝ)) +
        (∑' k : ℕ, β (k + 1) * a (k + 1)) +
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * β (k + 1) ^ 2 / 4) -
        (-S + ∑' k : ℕ, β (k + 1) * m (k + 1))) := by
  have hn : ∀ k : ℕ, (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := fun k => by positivity
  have huS := energy_trial_norm_summable a ha
  have hbm : Summable (fun k : ℕ => β (k + 1) * m (k + 1)) :=
    Summable.of_norm_bounded ((hβ.add hS.summable).div_const 2)
      (fun k => by rw [Real.norm_eq_abs]; exact abs_mul_le_amgm _ _ _ (hn k))
  have hba : Summable (fun k : ℕ => β (k + 1) * a (k + 1)) :=
    Summable.of_norm_bounded ((hβ.add huS).div_const 2)
      (fun k => by rw [Real.norm_eq_abs]; exact abs_mul_le_amgm _ _ _ (hn k))
  have ham : Summable (fun k : ℕ => a (k + 1) * m (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    refine Summable.of_norm_bounded ((huS.add hS.summable).div_const 2) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hn k)]
    have h1 : |a (k + 1) * m (k + 1)| ≤ (a (k + 1) ^ 2 + m (k + 1) ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a (k + 1) - m (k + 1)),
        sq_nonneg (a (k + 1) + m (k + 1))]
    calc |a (k + 1) * m (k + 1)| / ((k + 1 : ℕ) : ℝ)
        ≤ ((a (k + 1) ^ 2 + m (k + 1) ^ 2) / 2) / ((k + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right h1 (hn k).le
      _ = (a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) + m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) / 2 := by
          ring
  have H1 := hS.neg.add hbm.hasSum
  have H2 := ((huS.hasSum.sub (ham.hasSum.mul_left 2)).add hba.hasSum).add
    (hβ.div_const 4).hasSum
  have H3 := H2.sub H1
  unfold barrierTrialNormSq
  convert H3 using 1
  funext k
  have hk := hn k
  set n : ℝ := ((k + 1 : ℕ) : ℝ) with hnn
  field_simp
  ring

/-! ### Part (i): particle-level statements with the squares kept -/

/-- J1 (Lemma 3.4′) with the completed square kept. -/
theorem pair_log_add_field_le_trial_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (Q : ℝ → ℝ) :
    (∑ i : Fin s, ∑ j ∈ Ioi i, Real.log |u j - u i|) / ν ^ 2 + (∑ i, Q (u i)) / ν +
        ∑' k : ℕ, (a (k + 1) - pinCosineMoment ν e u (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ) ≤
      -(1 / 2 : ℝ) * ((s : ℝ) / ν) ^ 2 * Real.log 2 + barrierTrialNormSq a +
        (∑ i, (Q (u i) - 2 * barrierTrialT a (u i))) / ν + trialPairError ν e a := by
  have hrx := population_cosine_regularization hν he hs hu hui
  have hS : HasSum (fun k : ℕ => pinCosineMoment ν e u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin s, ∑ j : Fin s,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (u i) (u j)) / ν ^ 2 +
        ((s : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e u k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hu
  have hd := (completed_square_hasSum a (pinCosineMoment ν e u) ha hS).tsum_eq
  have hav := (pin_hasSum_trialTau_average a ha ν he hu).tsum_eq
  have ht := pin_average_le_of_le_add hν hs
    (fun i => -2 * realEnergyTrialTau a e (u i))
    (fun i => -2 * barrierTrialT a (u i))
    (c := 2 * e * (∑' k, |a k|))
    (mul_nonneg (mul_nonneg (by norm_num) he.1.le) (tsum_nonneg fun _ => abs_nonneg _))
    (fun i => by
      have hh := (abs_le.mp (realEnergyTrialTau_sub_le a ha he (hu i))).1
      linarith only [hh])
  have hs1 : -2 * ((∑ i, realEnergyTrialTau a e (u i)) / ν) =
      (∑ i, -2 * realEnergyTrialTau a e (u i)) / ν := by
    rw [← mul_sum]; ring
  have hsplit : (∑ i, (Q (u i) - 2 * barrierTrialT a (u i))) / ν =
      (∑ i, Q (u i)) / ν + (∑ i, -2 * barrierTrialT a (u i)) / ν := by
    rw [← add_div, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun i _ => by ring
  unfold trialPairError
  rw [hsplit]
  rw [hav] at hd
  ring_nf at hrx hd ht hs1 ⊢
  linarith only [hrx, hd, ht, hs1]

/-- J2 (tilted, particle form) with the tilted completed square kept. -/
theorem pair_log_add_cross_le_tilted_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s n : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1) :
    (∑ i : Fin s, ∑ j ∈ Ioi i, Real.log |u j - u i|) / ν ^ 2 +
        (∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν +
        ∑' k : ℕ, ((a (k + 1) - pinCosineMoment ν e u (k + 1)) +
          ((k + 1 : ℕ) : ℝ) * crossBeta (realEnergyTau e) w y (k + 1) / 2) ^ 2 /
            ((k + 1 : ℕ) : ℝ) ≤
      -(1 / 2 : ℝ) * ((s : ℝ) / ν) ^ 2 * Real.log 2 + barrierTrialNormSq a +
        (∑ i, -2 * barrierTrialT a (u i)) / ν +
        (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l)) +
        crossTiltNorm (realEnergyTau e) w y + trialPairError ν e a := by
  have hτ := realEnergyTau_bounds he
  have hτ' : realEnergyTau e ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2⟩
  have hrx := population_cosine_regularization hν he hs hu hui
  have hS : HasSum (fun k : ℕ => pinCosineMoment ν e u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin s, ∑ j : Fin s,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (u i) (u j)) / ν ^ 2 +
        ((s : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e u k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hu
  have hΛs := crossBeta_summable hτ' w y hy
  have hβs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      crossBeta (realEnergyTau e) w y (k + 1) ^ 2) := by
    refine (hΛs.mul_left 4).congr (fun k => ?_)
    have := crossBeta_sq (realEnergyTau e) w y (k + 1) (Nat.succ_pos k)
    linarith only [this]
  have ht := (tilted_completed_square_hasSum a (pinCosineMoment ν e u)
    (crossBeta (realEnergyTau e) w y) ha hS hβs).tsum_eq
  rw [(crossBeta_pairing_hasSum hν he u hu w y hy).tsum_eq,
    (pin_hasSum_trialTau_average a ha ν he hu).tsum_eq] at ht
  have hba : HasSum (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1))
      (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l)) := by
    have hl : ∀ l, HasSum (fun k : ℕ => a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
        ((k + 1 : ℕ) : ℝ)) (barrierTrialS a (-(realEnergyTau e) * y l)) := by
      intro l
      refine (barrierTrialS_summable a ha ?_).hasSum
      rw [abs_mul, abs_neg, abs_of_pos hτ.1]
      calc _ ≤ 1 * |y l| := mul_le_mul_of_nonneg_right hτ.2.le (abs_nonneg _)
        _ ≤ 1 := by linarith [hy l]
    have hsum := hasSum_sum (s := Finset.univ)
      (fun l _ => ((hl l).mul_left (w l)).mul_left (-2 : ℝ))
    have hconv : ∀ k : ℕ, crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1) =
        ∑ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) := by
      intro k
      have h1 : ∀ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) = (-2 * (-1) ^ (k + 1) * realEnergyTau e ^ (k + 1) *
            a (k + 1) / ((k + 1 : ℕ) : ℝ)) * (w l * y l ^ (k + 1)) := by
        intro l; rw [mul_pow, neg_pow]; ring
      simp only [h1]
      rw [← mul_sum]
      unfold crossBeta
      ring
    have e1 : (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1)) =
        fun k : ℕ => ∑ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) := funext hconv
    rw [e1]
    convert hsum using 1
    rw [mul_sum]
  rw [hba.tsum_eq] at ht
  have hq : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * crossBeta (realEnergyTau e) w y (k + 1) ^ 2 / 4) =
      crossTiltNorm (realEnergyTau e) w y := by
    unfold crossTiltNorm
    exact tsum_congr fun k => crossBeta_sq (realEnergyTau e) w y (k + 1) (Nat.succ_pos k)
  rw [hq] at ht
  have hav := pin_average_le_of_le_add hν hs
    (fun i => -2 * realEnergyTrialTau a e (u i))
    (fun i => -2 * barrierTrialT a (u i))
    (c := 2 * e * (∑' k, |a k|))
    (mul_nonneg (mul_nonneg (by norm_num) he.1.le) (tsum_nonneg fun _ => abs_nonneg _))
    (fun i => by
      have hh := (abs_le.mp (realEnergyTrialTau_sub_le a ha he (hu i))).1
      linarith only [hh])
  have hs1 : -2 * ((∑ i, realEnergyTrialTau a e (u i)) / ν) =
      (∑ i, -2 * realEnergyTrialTau a e (u i)) / ν := by
    rw [← mul_sum]; ring
  unfold trialPairError
  ring_nf at hrx ht hav hs1 ⊢
  linarith only [hrx, ht, hav, hs1]

/-! ### Part (ii): near-optimality bounds every component -/

/-- If `energy + brackets + square ≤ bound` and the energy is within `Δ` of the bound, each
nonnegative component is at most `Δ`. -/
theorem near_optimal_components {U E b₁ b₂ sq Δ : ℝ} (h : E + b₁ + b₂ + sq ≤ U)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hsq : 0 ≤ sq) (hE : U - Δ ≤ E) :
    b₁ ≤ Δ ∧ b₂ ≤ Δ ∧ sq ≤ Δ := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **Lemma K(i), Chebyshev inequality.**  If `X ≤ M` everywhere, `X ≤ s < M` on `R` and the field
bracket `M - ⟨X⟩` is at most `Δ`, then the fraction of nodes in `R` is at most `Δ / (M - s)`. -/
theorem fraction_le_of_field_bracket {n : ℕ} (hn : 0 < n) (X : Fin n → ℝ) (R : Finset (Fin n))
    {M s Δ : ℝ} (hX : ∀ i, X i ≤ M) (hR : ∀ i ∈ R, X i ≤ s) (hs : s < M)
    (hΔ : M - (∑ i, X i) / n ≤ Δ) :
    (R.card : ℝ) / n ≤ Δ / (M - s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMs : 0 < M - s := sub_pos.mpr hs
  have h1 : ∑ i, (if i ∈ R then M - s else 0) ≤ ∑ i, (M - X i) := by
    refine sum_le_sum fun i _ => ?_
    split_ifs with h
    · linarith [hR i h]
    · linarith [hX i]
  have h2 : ∑ i, (if i ∈ R then M - s else 0) = R.card * (M - s) := by
    rw [Finset.sum_ite_mem]
    simp
    ring
  have h3 : ∑ i, (M - X i) = n * M - ∑ i, X i := by
    simp [Finset.sum_sub_distrib]
  rw [h2, h3] at h1
  have h4 : (R.card : ℝ) * (M - s) ≤ n * Δ := by
    have : M - (∑ i, X i) / n ≤ Δ := hΔ
    have h5 : (n : ℝ) * (M - (∑ i, X i) / n) = n * M - ∑ i, X i := by
      field_simp
    nlinarith
  rw [div_le_div_iff₀ hnR hMs]
  linarith

/-- AM–GM in the form used for Cauchy–Schwarz on series. -/
theorem two_abs_mul_le (q F d : ℝ) (hq : 0 < q) : 2 * |F * d| ≤ q * d ^ 2 + F ^ 2 / q := by
  have h : q * d ^ 2 + F ^ 2 / q - 2 * |F * d| = (q * |d| - |F|) ^ 2 / q := by
    rw [abs_mul]
    field_simp
    have := sq_abs d
    have := sq_abs F
    nlinarith
  have : 0 ≤ (q * |d| - |F|) ^ 2 / q := by positivity
  linarith

/-- **Lemma K(ii), Cauchy–Schwarz for series.**  If `Σ d_k² / v_k = D` and `Σ F_k² v_k = H`
(positive weights `v`), then `Σ F_k d_k` converges and its square is at most `H D`. -/
theorem tsum_mul_sq_le {d F v : ℕ → ℝ} (hv : ∀ k, 0 < v k) {D H : ℝ}
    (hD : HasSum (fun k => d k ^ 2 / v k) D) (hH : HasSum (fun k => F k ^ 2 * v k) H) :
    Summable (fun k => F k * d k) ∧ (∑' k, F k * d k) ^ 2 ≤ H * D := by
  have hD0 : 0 ≤ D := hD.nonneg (fun k => by have := hv k; positivity)
  have hH0 : 0 ≤ H := hH.nonneg (fun k => by have := hv k; positivity)
  -- pointwise bound with parameter `l > 0`
  have key : ∀ l : ℝ, 0 < l → ∀ k, 2 * |F k * d k| ≤
      l * (d k ^ 2 / v k) + (1 / l) * (F k ^ 2 * v k) := by
    intro l hl k
    have hvk := hv k
    have h := two_abs_mul_le (l / v k) (F k) (d k) (by positivity)
    have e1 : l / v k * d k ^ 2 = l * (d k ^ 2 / v k) := by ring
    have e2 : F k ^ 2 / (l / v k) = (1 / l) * (F k ^ 2 * v k) := by field_simp
    linarith
  have hbd : ∀ l : ℝ, 0 < l →
      HasSum (fun k => (l * (d k ^ 2 / v k) + (1 / l) * (F k ^ 2 * v k)) / 2)
        ((l * D + (1 / l) * H) / 2) := fun l _ =>
    ((hD.mul_left l).add (hH.mul_left (1 / l))).div_const 2
  have hsum : Summable (fun k => F k * d k) := by
    refine Summable.of_norm_bounded (hbd 1 one_pos).summable (fun k => ?_)
    rw [Real.norm_eq_abs]
    have := key 1 one_pos k
    simp only [one_mul, div_one] at this ⊢
    linarith
  refine ⟨hsum, ?_⟩
  set S := ∑' k, F k * d k with hSdef
  have hup : ∀ l : ℝ, 0 < l → |S| ≤ (l * D + (1 / l) * H) / 2 := by
    intro l hl
    have hk := key l hl
    have hle1 : S ≤ (l * D + (1 / l) * H) / 2 := by
      refine hasSum_le (fun k => ?_) hsum.hasSum (hbd l hl)
      have := hk k
      have := le_abs_self (F k * d k)
      linarith
    have hle2 : -S ≤ (l * D + (1 / l) * H) / 2 := by
      have hneg : HasSum (fun k => -(F k * d k)) (-S) := hsum.hasSum.neg
      refine hasSum_le (fun k => ?_) hneg (hbd l hl)
      have := hk k
      have := neg_abs_le (F k * d k)
      linarith
    exact abs_le.mpr ⟨by linarith, hle1⟩
  have hquad : ∀ x : ℝ, 0 ≤ D * (x * x) + (-2 * |S|) * x + H := by
    intro x
    rcases lt_or_ge 0 x with hx | hx
    · have h := hup x hx
      have h2 : 2 * |S| ≤ x * D + (1 / x) * H := by linarith
      have h3 : 2 * |S| * x ≤ x * x * D + H := by
        have := mul_le_mul_of_nonneg_right h2 hx.le
        have e : (x * D + 1 / x * H) * x = x * x * D + H := by field_simp
        linarith
      nlinarith
    · have : 0 ≤ D * (x * x) := mul_nonneg hD0 (mul_self_nonneg x)
      nlinarith [abs_nonneg S]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  have : |S| ^ 2 = S ^ 2 := sq_abs S
  nlinarith

/-- **Lemma K(ii), linear-statistic bound.**  Under `Σ d_k² / v_k ≤ Δ` and `Σ F_k² v_k = H`,
`|Σ F_k d_k| ≤ √(H Δ)`. -/
theorem linear_statistic_bound {d F v : ℕ → ℝ} (hv : ∀ k, 0 < v k) {D H Δ : ℝ}
    (hD : HasSum (fun k => d k ^ 2 / v k) D) (hDΔ : D ≤ Δ)
    (hH : HasSum (fun k => F k ^ 2 * v k) H) :
    |∑' k, F k * d k| ≤ Real.sqrt (H * Δ) := by
  have hH0 : 0 ≤ H := hH.nonneg (fun k => by have := hv k; positivity)
  have h := (tsum_mul_sq_le hv hD hH).2
  exact Real.abs_le_sqrt (h.trans (mul_le_mul_of_nonneg_left hDΔ hH0))

/-- A statistic `Φ` that equals `c + Σ F_k d_k` up to `ε` is within `√(H Δ) + ε` of `c`. -/
theorem statistic_dev_le {d F v : ℕ → ℝ} (hv : ∀ k, 0 < v k) {D H Δ : ℝ}
    (hD : HasSum (fun k => d k ^ 2 / v k) D) (hDΔ : D ≤ Δ)
    (hH : HasSum (fun k => F k ^ 2 * v k) H) {Φ c ε : ℝ}
    (hΦ : |Φ - (c + ∑' k, F k * d k)| ≤ ε) :
    |Φ - c| ≤ Real.sqrt (H * Δ) + ε := by
  have h1 := linear_statistic_bound hv hD hDΔ hH
  calc |Φ - c| = |(Φ - (c + ∑' k, F k * d k)) + ∑' k, F k * d k| := by ring_nf
    _ ≤ |Φ - (c + ∑' k, F k * d k)| + |∑' k, F k * d k| := abs_add_le _ _
    _ ≤ ε + Real.sqrt (H * Δ) := add_le_add hΦ h1
    _ = _ := by ring

/-! ### The mass `m(x₊)` -/

/-- The linear statistic `m(x₊) = Σ_{x_a > 0} x_a / (1 + x_a)` of the positive nodes. -/
def posMass {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => 0 < x a), x a / (1 + x a)

/-- **Lemma K, `m(x₊) ≥ g + 1 + δ N`.**  If `m(x₊)/n` equals `c + Σ F_k d_k` up to `ε` (the
Chebyshev expansion of the smoothed `x/(1+x)`), `Σ d_k²/v_k ≤ Δ`, and the centre value `c` has
margin `n (c - √(H Δ) - ε) ≥ g + 1 + δ N`, then `m(x₊) ≥ g + 1 + δ N`. -/
theorem mass_lower_bound {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) {d F v : ℕ → ℝ}
    (hv : ∀ k, 0 < v k) {D H Δ c ε : ℝ}
    (hD : HasSum (fun k => d k ^ 2 / v k) D) (hDΔ : D ≤ Δ)
    (hH : HasSum (fun k => F k ^ 2 * v k) H)
    (hΦ : |posMass x / n - (c + ∑' k, F k * d k)| ≤ ε) {g δ N : ℝ}
    (hmargin : g + 1 + δ * N ≤ n * (c - Real.sqrt (H * Δ) - ε)) :
    g + 1 + δ * N ≤ posMass x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := statistic_dev_le hv hD hDΔ hH hΦ
  have h2 := (abs_le.mp h).1
  have h3 : c - Real.sqrt (H * Δ) - ε ≤ posMass x / n := by linarith
  have h4 : (n : ℝ) * (c - Real.sqrt (H * Δ) - ε) ≤ n * (posMass x / n) :=
    mul_le_mul_of_nonneg_left h3 hnR.le
  have h5 : (n : ℝ) * (posMass x / n) = posMass x := by field_simp
  linarith

/-! ### The slope condition feeding Lemma T′ -/

/-- The kernel `k_t(x) = t² / (t² + x²) - x² t² / (1 + x² t²)` of Lemma T′. -/
def slopeKernel (t x : ℝ) : ℝ := t ^ 2 / (t ^ 2 + x ^ 2) - x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2)

theorem slopeKernel_nonneg_le_one {t : ℝ} (ht : 0 < t) (x : ℝ) : slopeKernel t x ≤ 1 := by
  unfold slopeKernel
  have h1 : t ^ 2 / (t ^ 2 + x ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [sq_nonneg x]
  have h2 : 0 ≤ x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) := by positivity
  linarith

theorem slopeKernel_le_of_far {t a₀ : ℝ} (ha₀ : 0 < a₀) {x : ℝ} (hx : a₀ ≤ |x|) :
    slopeKernel t x ≤ t ^ 2 / a₀ ^ 2 := by
  unfold slopeKernel
  have hx2 : a₀ ^ 2 ≤ x ^ 2 := by
    have := mul_self_le_mul_self ha₀.le hx
    nlinarith [sq_abs x]
  have h2 : 0 ≤ x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) := by positivity
  have h1 : t ^ 2 / (t ^ 2 + x ^ 2) ≤ t ^ 2 / a₀ ^ 2 := by
    apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
    nlinarith [sq_nonneg t]
  linarith

/-- **Lemma K(i) → small `t`.**  If at most `φ n` nodes have `|x a| < a₀` and `0 < t ≤ t₀`, then
`Σ_a k_t(x a) ≤ n (φ + t₀² / a₀²)`. -/
theorem sum_slopeKernel_le_of_few_small {n : ℕ} (x : Fin n → ℝ) {a₀ t t₀ φ : ℝ} (ha₀ : 0 < a₀)
    (ht : 0 < t) (htt : t ≤ t₀)
    (hfew : ((Finset.univ.filter (fun a => |x a| < a₀)).card : ℝ) ≤ φ * n) :
    ∑ a, slopeKernel t (x a) ≤ n * (φ + t₀ ^ 2 / a₀ ^ 2) := by
  set R := Finset.univ.filter (fun a => |x a| < a₀) with hR
  have hpt : ∀ a, slopeKernel t (x a) ≤ (if a ∈ R then 1 else 0) + t₀ ^ 2 / a₀ ^ 2 := by
    intro a
    have hq : t ^ 2 / a₀ ^ 2 ≤ t₀ ^ 2 / a₀ ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have hq0 : 0 ≤ t₀ ^ 2 / a₀ ^ 2 := by positivity
    by_cases h : a ∈ R
    · simp only [h, ite_true]
      linarith [slopeKernel_nonneg_le_one ht (x a)]
    · simp only [h, ite_false]
      have hfar : a₀ ≤ |x a| := by
        by_contra hc
        exact h (by simp [hR]; linarith)
      linarith [slopeKernel_le_of_far (t := t) ha₀ hfar]
  calc ∑ a, slopeKernel t (x a) ≤ ∑ a, ((if a ∈ R then (1 : ℝ) else 0) + t₀ ^ 2 / a₀ ^ 2) :=
        sum_le_sum fun a _ => hpt a
    _ = R.card + n * (t₀ ^ 2 / a₀ ^ 2) := by
        rw [sum_add_distrib, Finset.sum_ite_mem]; simp
    _ ≤ n * (φ + t₀ ^ 2 / a₀ ^ 2) := by nlinarith

/-- A family of upper bounds `Σ_a k_t(x a) < e` is exactly the slope hypothesis. -/
theorem slope_pos_of_bound {n : ℕ} (x : Fin n → ℝ) (e : ℕ)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ∑ a, slopeKernel t (x a) < e) :
    ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2)) := by
  intro t ht
  have := hb t ht
  unfold slopeKernel at this
  linarith

/-- **Lemma K ⟹ the hypothesis of Lemma T′.**  For a family of linear statistics
`Σ_a k_t(x a)/n = c_t + Σ F^t_k d_k` (up to `ε_t`) controlled by one square bound
`Σ d_k²/v_k ≤ Δ`, together with the few-nodes-near-zero bound from the Chebyshev inequality,
the slope hypothesis `0 < e - Σ_a k_t(x a)` of `pow_le_norm_blaschke_of_slope` holds for all
`t ∈ (0, 1]`.

* for `t ≤ t₀` the bound is `n (φ + t₀²/a₀²) < e` (few nodes within `a₀` of `0`);
* for `t₀ ≤ t ≤ 1` the bound is `n (c_t + √(H_t Δ) + ε_t) < e` (Cauchy–Schwarz). -/
theorem slope_of_class {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (e : ℕ) {d v : ℕ → ℝ}
    (hv : ∀ k, 0 < v k) {D Δ : ℝ} (hD : HasSum (fun k => d k ^ 2 / v k) D) (hDΔ : D ≤ Δ)
    (F : ℝ → ℕ → ℝ) (H c ε : ℝ → ℝ)
    (hH : ∀ t, HasSum (fun k => F t k ^ 2 * v k) (H t))
    {a₀ t₀ φ : ℝ} (ha₀ : 0 < a₀) (ht₀ : 0 < t₀)
    (hfew : ((Finset.univ.filter (fun a => |x a| < a₀)).card : ℝ) ≤ φ * n)
    (hsmall : (n : ℝ) * (φ + t₀ ^ 2 / a₀ ^ 2) < e)
    (hstat : ∀ t ∈ Ioc (0 : ℝ) 1, t₀ ≤ t →
      |(∑ a, slopeKernel t (x a)) / n - (c t + ∑' k, F t k * d k)| ≤ ε t)
    (hbig : ∀ t ∈ Ioc (0 : ℝ) 1, t₀ ≤ t →
      (n : ℝ) * (c t + Real.sqrt (H t * Δ) + ε t) < e) :
    ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine slope_pos_of_bound x e fun t ht => ?_
  rcases le_total t t₀ with h | h
  · exact lt_of_le_of_lt (sum_slopeKernel_le_of_few_small x ha₀ ht.1 h hfew) hsmall
  · have hdev := statistic_dev_le hv hD hDΔ (hH t) (hstat t ht h)
    have h2 := (abs_le.mp hdev).2
    have h3 : (∑ a, slopeKernel t (x a)) / n ≤ c t + Real.sqrt (H t * Δ) + ε t := by linarith
    have h4 : ∑ a, slopeKernel t (x a) ≤ n * (c t + Real.sqrt (H t * Δ) + ε t) := by
      rw [div_le_iff₀ hnR] at h3; linarith
    exact lt_of_le_of_lt h4 (hbig t ht h)

/-- The composite: the class condition gives Lemma T′'s conclusion `|y|^e ≤ ‖B(i y)‖`. -/
theorem pow_le_norm_blaschke_of_class {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) {e : ℕ} (he : 1 ≤ e)
    {d v : ℕ → ℝ} (hv : ∀ k, 0 < v k) {D Δ : ℝ} (hD : HasSum (fun k => d k ^ 2 / v k) D)
    (hDΔ : D ≤ Δ) (F : ℝ → ℕ → ℝ) (H c ε : ℝ → ℝ)
    (hH : ∀ t, HasSum (fun k => F t k ^ 2 * v k) (H t))
    {a₀ t₀ φ : ℝ} (ha₀ : 0 < a₀) (ht₀ : 0 < t₀)
    (hfew : ((Finset.univ.filter (fun a => |x a| < a₀)).card : ℝ) ≤ φ * n)
    (hsmall : (n : ℝ) * (φ + t₀ ^ 2 / a₀ ^ 2) < e)
    (hstat : ∀ t ∈ Ioc (0 : ℝ) 1, t₀ ≤ t →
      |(∑ a, slopeKernel t (x a)) / n - (c t + ∑' k, F t k * d k)| ≤ ε t)
    (hbig : ∀ t ∈ Ioc (0 : ℝ) 1, t₀ ≤ t →
      (n : ℝ) * (c t + Real.sqrt (H t * Δ) + ε t) < e) :
    ∀ y ∈ Icc (-1 : ℝ) 1, |y| ^ e ≤ 1 * ‖blaschke x ((y : ℂ) * Complex.I)‖ :=
  pow_le_norm_blaschke_of_slope x he
    (slope_of_class hn x e hv hD hDΔ F H c ε hH ha₀ ht₀ hfew hsmall hstat hbig)

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.completed_square_hasSum
#print axioms CatalanMeasure.Signed.tilted_completed_square_hasSum
#print axioms CatalanMeasure.Signed.pair_log_add_field_le_trial_sq
#print axioms CatalanMeasure.Signed.pair_log_add_cross_le_tilted_sq
#print axioms CatalanMeasure.Signed.near_optimal_components
#print axioms CatalanMeasure.Signed.fraction_le_of_field_bracket
#print axioms CatalanMeasure.Signed.tsum_mul_sq_le
#print axioms CatalanMeasure.Signed.linear_statistic_bound
#print axioms CatalanMeasure.Signed.mass_lower_bound
#print axioms CatalanMeasure.Signed.sum_slopeKernel_le_of_few_small
#print axioms CatalanMeasure.Signed.slope_of_class
#print axioms CatalanMeasure.Signed.pow_le_norm_blaschke_of_class
