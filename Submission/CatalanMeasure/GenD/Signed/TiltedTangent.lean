module

public import Submission.CatalanMeasure.GenD.Signed.CrossDilation
public import Submission.CatalanMeasure.Parametric.CoupledCosineRegularization
public import Submission.CatalanMeasure.PopulationDual
public import Submission.CatalanMeasure.PinDampedDual

/-!
# Lemma 3.4′ and the tilted completed square (J1, J2)

One-population Chebyshev energy engine, specialised to the particle population of the signed
second-sheet bound.

* `pair_log_add_field_le_trial` (J1, Lemma 3.4′): for distinct `u_1, …, u_s ∈ (-1, 1)`, `ν ≥ s`,
  `e ∈ (0, 1/8)`, a summable trial sequence `a` and an arbitrary field `Q`,
  `ν⁻² Σ_{l<l'} log|u_l' - u_l| + ν⁻¹ Σ Q(u_l) ≤ -(1/2)(s/ν)² log 2 + ‖a‖² +
   ν⁻¹ Σ (Q(u_l) - 2 T_a(u_l)) + err`.
  It is the composition `population_cosine_regularization` + `pin_first_tangent`'s square
  completion + `realEnergyTrialTau_sub_le`; no engine lemma is reproved.
* `tilted_energy_tangent` (J2, sequence form): the tilted completed square
  `-Σ m_k²/k + Σ β_k m_k ≤ ‖a‖² - 2 Σ a_k m_k/k + Σ β_k a_k + Σ k β_k²/4`.
* `pair_log_add_cross_le_tilted` (J2, particle form): the same with the tilt equal to the cross
  field of a signed configuration `(w, y)` dilated by `τ²` (`τ = 1 - e`).  The quadratic remainder is
  `Λ_τ(w, y) = Σ_k (τ^k Σ_i w_i y_i^k)² / k`, the Λ term of the configuration dilated by `τ`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

/-- The error of Lemma 3.4′: `(log 2 - 2 log (1 - τ²))/(2ν) + 2e + 2e Σ|a_k|`. -/
def trialPairError (ν e : ℝ) (a : ℕ → ℝ) : ℝ :=
  (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * ν) + 2 * e +
    2 * e * ∑' k : ℕ, |a k|

/-- J1, Lemma 3.4′. -/
theorem pair_log_add_field_le_trial {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (Q : ℝ → ℝ) :
    (∑ i : Fin s, ∑ j ∈ Ioi i, Real.log |u j - u i|) / ν ^ 2 + (∑ i, Q (u i)) / ν ≤
      -(1 / 2 : ℝ) * ((s : ℝ) / ν) ^ 2 * Real.log 2 + barrierTrialNormSq a +
        (∑ i, (Q (u i) - 2 * barrierTrialT a (u i))) / ν + trialPairError ν e a := by
  have hrx := population_cosine_regularization hν he hs hu hui
  have hd := pin_first_tangent hν he hs hu a ha
  rw [(pin_hasSum_trialTau_average a ha ν he hu).tsum_eq] at hd
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
  ring_nf at hrx hd ht hs1 ⊢
  linarith only [hrx, hd, ht, hs1]

/-- Elementary AM-GM bound used for summability. -/
theorem abs_mul_le_amgm (n x y : ℝ) (hn : 0 < n) :
    |x * y| ≤ (n * x ^ 2 + y ^ 2 / n) / 2 := by
  have h1 : n * x ^ 2 + y ^ 2 / n - 2 * (x * y) = (n * x - y) ^ 2 / n := by
    field_simp; ring
  have h2 : n * x ^ 2 + y ^ 2 / n + 2 * (x * y) = (n * x + y) ^ 2 / n := by
    field_simp; ring
  have h3 : 0 ≤ (n * x - y) ^ 2 / n := by positivity
  have h4 : 0 ≤ (n * x + y) ^ 2 / n := by positivity
  rw [abs_le]; constructor <;> linarith

/-- J2, sequence form: the tilted completed square. -/
theorem tilted_energy_tangent (a m β : ℕ → ℝ) (ha : Summable (fun k => |a k|)) {S : ℝ}
    (hS : HasSum (fun k : ℕ => m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S)
    (hβ : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * β (k + 1) ^ 2)) :
    -S + ∑' k : ℕ, β (k + 1) * m (k + 1) ≤
      barrierTrialNormSq a - 2 * (∑' k : ℕ, a (k + 1) * m (k + 1) / ((k + 1 : ℕ) : ℝ)) +
        (∑' k : ℕ, β (k + 1) * a (k + 1)) +
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * β (k + 1) ^ 2 / 4 := by
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
  refine hasSum_le (fun k => ?_) H1 H2
  have hk := hn k
  set n : ℝ := ((k + 1 : ℕ) : ℝ) with hnn
  have key : a (k + 1) ^ 2 / n - 2 * (a (k + 1) * m (k + 1) / n) + β (k + 1) * a (k + 1) +
      n * β (k + 1) ^ 2 / 4 - (-(m (k + 1) ^ 2 / n) + β (k + 1) * m (k + 1)) =
      ((a (k + 1) - m (k + 1)) + n * β (k + 1) / 2) ^ 2 / n := by
    field_simp; ring
  have : 0 ≤ ((a (k + 1) - m (k + 1)) + n * β (k + 1) / 2) ^ 2 / n := by positivity
  linarith

/-- The cross tilt `β_k = -2 (-1)^k τ^k (Σ_l w_l y_l^k) / k` of a signed configuration. -/
def crossBeta {n : ℕ} (τ : ℝ) (w y : Fin n → ℝ) (k : ℕ) : ℝ :=
  -2 * (-1) ^ k * τ ^ k * (∑ l, w l * y l ^ k) / (k : ℝ)

/-- The Λ term of the configuration `(w, y)` dilated by `τ`: `Σ_k (τ^k Σ_l w_l y_l^k)² / k`. -/
def crossTiltNorm {n : ℕ} (τ : ℝ) (w y : Fin n → ℝ) : ℝ :=
  ∑' k : ℕ, (τ ^ (k + 1) * ∑ l, w l * y l ^ (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)

theorem crossBeta_sq {n : ℕ} (τ : ℝ) (w y : Fin n → ℝ) (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * crossBeta τ w y k ^ 2 / 4 =
      (τ ^ k * ∑ l, w l * y l ^ k) ^ 2 / (k : ℝ) := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  unfold crossBeta
  field_simp
  rw [h1]; ring

theorem crossBeta_summable {n : ℕ} {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (w y : Fin n → ℝ)
    (hy : ∀ l, |y l| < 1) :
    Summable (fun k : ℕ => (τ ^ (k + 1) * ∑ l, w l * y l ^ (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have hg : Summable (fun k : ℕ => (∑ l, |w l|) ^ 2 * (τ ^ 2) ^ (k + 1)) :=
    ((summable_geometric_of_lt_one (by positivity) (by nlinarith [hτ.1, hτ.2])).comp_injective
      (add_left_injective 1)).mul_left _
  refine Summable.of_norm_bounded hg (fun k => ?_)
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hρ : |∑ l, w l * y l ^ (k + 1)| ≤ ∑ l, |w l| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (hy l).le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (τ ^ (k + 1) * ∑ l, w l * y l ^ (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)
      ≤ (τ ^ (k + 1) * ∑ l, w l * y l ^ (k + 1)) ^ 2 := div_le_self (sq_nonneg _) hk
    _ = (τ ^ (k + 1)) ^ 2 * |∑ l, w l * y l ^ (k + 1)| ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ (τ ^ (k + 1)) ^ 2 * (∑ l, |w l|) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hρ 2) (sq_nonneg _)
    _ = (∑ l, |w l|) ^ 2 * (τ ^ 2) ^ (k + 1) := by ring

/-- The pairing of the tilt with the damped particle moments is the dilated cross field. -/
theorem crossBeta_pairing_hasSum {ν e : ℝ} (hν : 0 < ν) {s n : ℕ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (u : Fin s → ℝ) (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1) :
    HasSum (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * pinCosineMoment ν e u (k + 1))
      ((∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν) := by
  have hτ := realEnergyTau_bounds he
  have hterm : ∀ i l, HasSum (fun k : ℕ => -2 * (-(realEnergyTau e ^ 2 * y l)) ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (u i) / ((k + 1 : ℕ) : ℝ))
      (crossLog (realEnergyTau e ^ 2 * y l) (u i)) := by
    intro i l
    have hyl := abs_lt.mp (hy l)
    apply crossLog_hasSum _ ⟨(hu i).1.le, (hu i).2.le⟩
    have h2 : realEnergyTau e ^ 2 < 1 := by nlinarith [hτ.1, hτ.2]
    have h3 : 0 < realEnergyTau e ^ 2 := by nlinarith [hτ.1, hτ.2]
    constructor <;> nlinarith [hyl.1, hyl.2]
  have hsum := (hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ)
    (fun l _ => (hterm i l).mul_left (w l)))).div_const ν
  convert hsum using 1
  funext k
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ∀ l, (-(realEnergyTau e ^ 2 * y l)) ^ (k + 1) =
      (-1) ^ (k + 1) * realEnergyTau e ^ (k + 1) * realEnergyTau e ^ (k + 1) * y l ^ (k + 1) := by
    intro l
    rw [show -(realEnergyTau e ^ 2 * y l) = (-1) * realEnergyTau e * realEnergyTau e * y l by ring]
    simp only [mul_pow]
  unfold crossBeta pinCosineMoment
  simp only [hpow]
  rw [sum_comm]
  rw [div_mul_div_comm]
  have hR : (∑ l, ∑ i, w l * (-2 * ((-1) ^ (k + 1) * realEnergyTau e ^ (k + 1) *
        realEnergyTau e ^ (k + 1) * y l ^ (k + 1)) *
        Polynomial.eval (u i) (Polynomial.Chebyshev.T ℝ ↑(k + 1)) / ((k + 1 : ℕ) : ℝ))) =
      (-2 * (-1) ^ (k + 1) * realEnergyTau e ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) *
        ((∑ l, w l * y l ^ (k + 1)) *
          ∑ i, realEnergyTau e ^ (k + 1) * Polynomial.eval (u i)
            (Polynomial.Chebyshev.T ℝ ↑(k + 1))) := by
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hR]
  field_simp

/-- J2, particle form. -/
theorem pair_log_add_cross_le_tilted {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s n : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1) :
    (∑ i : Fin s, ∑ j ∈ Ioi i, Real.log |u j - u i|) / ν ^ 2 +
        (∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν ≤
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
  have ht := tilted_energy_tangent a (pinCosineMoment ν e u) (crossBeta (realEnergyTau e) w y)
    ha hS hβs
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

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.pair_log_add_field_le_trial
#print axioms CatalanMeasure.Signed.tilted_energy_tangent
#print axioms CatalanMeasure.Signed.pair_log_add_cross_le_tilted
