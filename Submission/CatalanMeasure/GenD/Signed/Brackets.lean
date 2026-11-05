module

public import Submission.CatalanMeasure.GenD.Analytic.Second
public import Submission.CatalanMeasure.GenD.Signed.LemmaK
public import Submission.CatalanMeasure.GenD.Analytic.GroupedProduct

/-!
# The grouped second-population energy with its squares and field brackets kept (PROOF-A 17.9(a))

`Analytic.second_energy` bounds the grouped value by `U = -target + log 2 / 2 + cost * α + δ`.
Its proof drops, in this order,

* the completed squares of the cosine energy duals: for the free population `Σ_k (p_k - A_k(z))²/k`
  and `½ Σ_k (v_k - (B_k - 2 C_k))²/k` (`pin_first_tangent`, `pin_second_tangent`), and for the
  coupled actual/near cosine energy the squares `Σ_k (p_k - A_k(x))²/k`, `Σ_k B_k(y)²/k` with the
  first-mode cross term (`coupled_energy_tangent_of_hasSum`);
* the nonnegative field brackets `cap - X(node)` (the per-node field hypotheses of
  `grouped_field_caps_bound`).

Here all of them are kept.  `second_energy_sq` has output exactly of the form
`E + b₁ + b₂ + b₃ + b₄ + sq ≤ U` consumed by `near_optimal_components` (`LemmaK.lean`), with
`bracketSlack_nonneg` and `groupedSquares_nonneg`.  The damping `e` is an explicit parameter
(any `e` with `e * c < δ / 2` works, `c` the constant of `grouped_error_tendsto`), so that the
moments `A_k = Σ_i τ^k T_k(x_i) / ν` in the squares are the damped ones of OpenAI's Prop. 6.1.

`Second.lean` and everything in the 532 closure are untouched: this module only imports them.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Set Finset Filter
open scoped BigOperators Topology

noncomputable section

/-! ### The square tail -/

/-- `Σ_{k ≥ 1} (a_k - m_k)² / k`. -/
def sqTail (a m : ℕ → ℝ) : ℝ := ∑' k : ℕ, (a (k + 1) - m (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ)

theorem sqTail_nonneg (a m : ℕ → ℝ) : 0 ≤ sqTail a m :=
  tsum_nonneg fun _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem sqTail_eq (u m : ℕ → ℝ) (hu : Summable (fun k => |u k|)) {S : ℝ}
    (hS : HasSum (fun k : ℕ => m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S) :
    sqTail u m = barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * m (k + 1) / ((k + 1 : ℕ) : ℝ)) + S :=
  (completed_square_hasSum u m hu hS).tsum_eq

theorem first_le_sqTail (u m : ℕ → ℝ) (hu : Summable (fun k => |u k|)) {S : ℝ}
    (hS : HasSum (fun k : ℕ => m (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) S) :
    (u 1 - m 1) ^ 2 ≤ sqTail u m := by
  have h := completed_square_hasSum u m hu hS
  have hle := h.summable.le_tsum 0 (fun k _ =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg (k + 1)))
  rw [h.tsum_eq] at hle
  norm_num only [Nat.zero_add, Nat.cast_one, div_one] at hle
  unfold sqTail
  rw [h.tsum_eq]
  exact hle

/-! ### The tangent steps with the square kept -/

theorem pin_first_tangent_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ}
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    ((∑ i : Fin p, ∑ j : Fin p,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
      ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2 + sqTail u (pinCosineMoment ν e x) ≤
    barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * pinCosineMoment ν e x (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
  have hS : HasSum
      (fun k : ℕ => pinCosineMoment ν e x (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin p, ∑ j : Fin p,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
        ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e x k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hx
  have h := sqTail_eq u _ hu hS
  linarith only [h]

theorem pin_second_tangent_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (∑ i : Fin p, ∑ j : Fin p,
      Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
        (2 * ν ^ 2) +
    (∑ i : Fin p, ∑ j : Fin p,
      realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
        ν ^ 2 -
    (∑ i : Fin p, ∑ j : Fin p,
      Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
        (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / ν ^ 2 +
      ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      sqTail u (fun k => pinPowerMoment ν e x k - 2 * pinColumnMoment ν e s k) / 2 ≤
    barrierTrialNormSq u / 2 -
      (∑' k : ℕ, u (k + 1) * pinPowerMoment ν e x (k + 1) / ((k + 1 : ℕ) : ℝ)) +
      2 * (∑' k : ℕ, u (k + 1) * pinColumnMoment ν e s (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
  let a : ℕ → ℝ := fun k => pinPowerMoment ν e x k - 2 * pinColumnMoment ν e s k
  have hB := energy_trial_product_summable u (pinPowerMoment ν e x) hu
    (by norm_num : (0 : ℝ) ≤ 1) (pin_powerMoment_abs_le_one hν he hpν hx)
  have hC := energy_trial_product_summable u (pinColumnMoment ν e s) hu
    (by norm_num : (0 : ℝ) ≤ 1) (pin_columnMoment_abs_le_one hν he hpν hs)
  have hsplit :
      (∑' k : ℕ, u (k + 1) * a (k + 1) / ((k + 1 : ℕ) : ℝ)) =
      (∑' k : ℕ, u (k + 1) * pinPowerMoment ν e x (k + 1) / ((k + 1 : ℕ) : ℝ)) -
      2 * (∑' k : ℕ, u (k + 1) * pinColumnMoment ν e s (k + 1) /
        ((k + 1 : ℕ) : ℝ)) := by
    apply HasSum.tsum_eq
    convert hB.hasSum.sub (hC.hasSum.mul_left 2) using 1
    funext k
    dsimp [a]
    ring
  have hhalf := pin_hasSum_second_square hν e x s he hx hs
  have hfull := hhalf.mul_left 2
  have hS : HasSum (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (2 * (-((∑ i : Fin p, ∑ j : Fin p,
          Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
            (2 * ν ^ 2) +
        (∑ i : Fin p, ∑ j : Fin p,
          realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
            ν ^ 2 -
        (∑ i : Fin p, ∑ j : Fin p,
          Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
            (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / ν ^ 2 +
        ((p : ℝ) / ν) ^ 2 * Real.log 2))) := by
    apply (hasSum_nat_add_iff (f := fun k : ℕ => a k ^ 2 / (k : ℝ)) 1).2
    simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, add_zero]
    convert hfull using 1
    funext k
    dsimp [a]
    ring
  have h := sqTail_eq u a hu hS
  rw [hsplit] at h
  linarith only [h]

/-! ### The pin (free) population -/

theorem pinDampedInteraction_le_trials_sq {ν k e : ℝ} (hν : 0 < ν)
    (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    pinDampedInteraction ν k e x s + k * sqTail pp (pinCosineMoment ν e x) +
      sqTail v (fun j => pinPowerMoment ν e x j - 2 * pinColumnMoment ν e s j) / 2 ≤
      -(k / 2 + 1) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 -
      2 * k * (∑' j : ℕ, pp (j + 1) * pinCosineMoment ν e x (j + 1) /
        ((j + 1 : ℕ) : ℝ)) -
      (∑' j : ℕ, v (j + 1) * pinPowerMoment ν e x (j + 1) / ((j + 1 : ℕ) : ℝ)) +
      2 * (∑' j : ℕ, v (j + 1) * pinColumnMoment ν e s (j + 1) /
        ((j + 1 : ℕ) : ℝ)) := by
  have hfirst := mul_le_mul_of_nonneg_left (pin_first_tangent_sq hν he hx pp hp) hk
  have hsecond := pin_second_tangent_sq hν he hpν hx hs v hv
  unfold pinDampedInteraction
  simp only [div_eq_mul_inv, mul_inv_rev] at hfirst hsecond ⊢
  nlinarith only [hfirst, hsecond]

theorem pinDampedInteraction_le_canonicalTrials_sq {ν k e : ℝ} (hν : 0 < ν)
    (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    pinDampedInteraction ν k e x s + k * sqTail pp (pinCosineMoment ν e x) +
      sqTail v (fun j => pinPowerMoment ν e x j - 2 * pinColumnMoment ν e s j) / 2 ≤
      -(k / 2 + 1) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (∑ i : Fin p, (-2 * k * barrierTrialT pp (x i) - barrierTrialS v (x i))) / ν +
      (∑ j : Fin p, 2 * barrierTrialT v (s j)) / ν +
      2 * k * e * (∑' j : ℕ, |pp j|) + 4 * e * (∑' j : ℕ, |v j|) := by
  have hpsum : 0 ≤ ∑' j : ℕ, |pp j| := tsum_nonneg (fun _ => abs_nonneg _)
  have hvsum : 0 ≤ ∑' j : ℕ, |v j| := tsum_nonneg (fun _ => abs_nonneg _)
  have he0 : 0 ≤ e := he.1.le
  have hxavg := pin_average_le_of_le_add hν hpν
    (fun i => -2 * k * realEnergyTrialTau pp e (x i) - realEnergyTrialRho v e (x i))
    (fun i => -2 * k * barrierTrialT pp (x i) - barrierTrialS v (x i))
    (c := 2 * k * e * (∑' j : ℕ, |pp j|) + 2 * e * (∑' j : ℕ, |v j|)) (by positivity)
    (fun i => by
      have ht := (abs_le.mp (realEnergyTrialTau_sub_le pp hp he (hx i))).1
      have hr := (abs_le.mp (realEnergyTrialRho_sub_le v hv he (hx i))).1
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * k by positivity)
      nlinarith only [hm, hr])
  have hsavg := pin_average_le_of_le_add hν hpν
    (fun j => 2 * realEnergyTrialSigma v e (s j))
    (fun j => 2 * barrierTrialT v (s j))
    (c := 2 * e * (∑' j : ℕ, |v j|)) (by positivity) (fun j => by
      have ht := (abs_le.mp (realEnergyTrialSigma_sub_le v hv he (hs j))).2
      linarith)
  have hd := pinDampedInteraction_le_trials_sq hν hk he hpν hx hs pp v hp hv
  rw [(pin_hasSum_trialTau_average pp hp ν he hx).tsum_eq,
    (pin_hasSum_trialRho_average v hv ν he hx).tsum_eq,
    (pin_hasSum_trialSigma_average v hv ν he hs).tsum_eq] at hd
  have hsplit : (∑ i : Fin p, (-2 * k * realEnergyTrialTau pp e (x i) -
      realEnergyTrialRho v e (x i))) / ν =
      -2 * k * ((∑ i : Fin p, realEnergyTrialTau pp e (x i)) / ν) -
        (∑ i : Fin p, realEnergyTrialRho v e (x i)) / ν := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hsplit2 : (∑ j : Fin p, 2 * realEnergyTrialSigma v e (s j)) / ν =
      2 * ((∑ j : Fin p, realEnergyTrialSigma v e (s j)) / ν) := by
    rw [← Finset.mul_sum]
    ring
  linarith

theorem free_population_canonical_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hp : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (pp v : ℕ → ℝ) (hpp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    pinOffDiagonalInteraction ν 1 x s + sqTail pp (pinCosineMoment ν e x) +
      sqTail v (fun j => pinPowerMoment ν e x j - 2 * pinColumnMoment ν e s j) / 2 ≤
      -(3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (∑ i, (-2 * barrierTrialT pp (x i) - barrierTrialS v (x i))) / ν +
      (∑ j, 2 * barrierTrialT v (s j)) / ν -
      (∑ i, Real.log (1 - x i)) / (2 * ν ^ 2) - (∑ j, Real.log (1 - s j)) / ν ^ 2 +
      2 * e * (∑' j, |pp j|) + 4 * e * (∑' j, |v j|) + freePopulationRegularizationError ν e := by
  have hreg := free_population_regularization hν he hp hx hs hxi hsi
  have hdual := pinDampedInteraction_le_canonicalTrials_sq hν (by norm_num : (0 : ℝ) ≤ 1)
    he hp hx hs pp v hpp hv
  norm_num only [one_mul, mul_one] at hdual
  linarith only [hreg, hdual]

/-! ### The coupled actual/near cosine energy -/

/-- The squares kept by the coupled cosine energy of an actual population `x` against a near
population `y`, with trial `u`: `Σ (u_k - A_k(x))²/k + Σ B_k(y)²/k + (A_1(x) - u_1) B_1(y)`. -/
def cosineSquares (ν e : ℝ) (u : ℕ → ℝ) {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) : ℝ :=
  sqTail u (pinCosineMoment ν e x) + sqTail (fun _ => 0) (pinCosineMoment ν e y) +
    (pinCosineMoment ν e x 1 - u 1) * pinCosineMoment ν e y 1

theorem pin_coupled_first_tangent_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p q : ℕ}
    {x : Fin p → ℝ} {y : Fin q → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    ((∑ i : Fin p, ∑ j : Fin p,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
      ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2 +
    ((∑ i : Fin q, ∑ j : Fin q,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (y i) (y j)) / ν ^ 2 +
      ((q : ℝ) / ν) ^ 2 * Real.log 2) / 2 -
      pinCosineMoment ν e x 1 * pinCosineMoment ν e y 1 +
      cosineSquares ν e u x y ≤
    barrierTrialNormSq u -
      2 * (∑' k : ℕ, u (k + 1) * pinCosineMoment ν e x (k + 1) /
        ((k + 1 : ℕ) : ℝ)) - u 1 * pinCosineMoment ν e y 1 := by
  have hA : HasSum
      (fun k : ℕ => pinCosineMoment ν e x (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin p, ∑ j : Fin p,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
        ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e x k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hx
  have hB : HasSum
      (fun k : ℕ => pinCosineMoment ν e y (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin q, ∑ j : Fin q,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (y i) (y j)) / ν ^ 2 +
        ((q : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e y k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hy
  have h1 := sqTail_eq u _ hu hA
  have h2 : sqTail (fun _ => 0) (pinCosineMoment ν e y) =
      -((∑ i : Fin q, ∑ j : Fin q,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (y i) (y j)) / ν ^ 2 +
        ((q : ℝ) / ν) ^ 2 * Real.log 2) / 2 := by
    unfold sqTail
    simp only [zero_sub, neg_sq]
    exact hB.tsum_eq
  unfold cosineSquares
  rw [h2]
  nlinarith only [h1]

theorem grouped_cosine_cross_canonical_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p q : ℕ}
    (hp : (p : ℝ) ≤ ν) (hq : (q : ℝ) ≤ ν)
    (x : Fin p → ℝ) (y : Fin q → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (hxi : Function.Injective x) (hyi : Function.Injective y)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (∑ i : Fin p, ∑ j ∈ Ioi i, Real.log |x j - x i|) / ν ^ 2 +
    (∑ i : Fin q, ∑ j ∈ Ioi i, Real.log |y j - y i|) / ν ^ 2 +
    Real.log (crossCauchyProduct x y) / ν ^ 2 + cosineSquares ν e u x y ≤
      -(1 / 2 : ℝ) * (((p : ℝ) / ν) ^ 2 + ((q : ℝ) / ν) ^ 2) * Real.log 2 +
        barrierTrialNormSq u + (∑ i, -2 * barrierTrialT u (x i)) / ν -
          u 1 * ((∑ i, y i) / ν) + coupledCosineError ν e u := by
  have hxabs : ∀ i, |x i| < 1 := fun i => abs_lt.mpr (hx i)
  have hyabs : ∀ i, |y i| < 1 := fun i => abs_lt.mpr (hy i)
  have hX := normalized_node_sum_abs_le_one hν hp x (fun i => (hxabs i).le)
  have hY := normalized_node_sum_abs_le_one hν hq y (fun i => (hyabs i).le)
  have hrx := population_cosine_regularization hν he hp hx hxi
  have hry := population_cosine_regularization hν he hq hy hyi
  have hc := div_le_div_of_nonneg_right
    (crossCauchyProduct_log_le_first_moment x y hxabs hyabs) (sq_nonneg ν)
  have hfrac : -(∑ i, x i) * (∑ i, y i) / ν ^ 2 =
      -((∑ i, x i) / ν) * ((∑ i, y i) / ν) := by ring
  rw [hfrac] at hc
  have hcross := first_moment_product_damping_error he hX hY
  have hlinear := first_moment_linear_damping_error (u := u 1) he.1.le hY
  have hd := pin_coupled_first_tangent_sq hν he hx hy u hu
  generalize hQ : cosineSquares ν e u x y = Q at hd ⊢
  rw [pinCosineMoment_first, pinCosineMoment_first,
    (pin_hasSum_trialTau_average u hu ν he hx).tsum_eq] at hd
  have ht := pin_average_le_of_le_add hν hp
    (fun i => -2 * realEnergyTrialTau u e (x i))
    (fun i => -2 * barrierTrialT u (x i))
    (c := 2 * e * (∑' k, |u k|))
    (mul_nonneg (mul_nonneg (by norm_num) he.1.le) (tsum_nonneg fun _ => abs_nonneg _))
    (fun i => by
      have hh := (abs_le.mp (realEnergyTrialTau_sub_le u hu he (hx i))).1
      linarith only [hh])
  have hs : -2 * ((∑ i, realEnergyTrialTau u e (x i)) / ν) =
      (∑ i, -2 * realEnergyTrialTau u e (x i)) / ν := by
    rw [← mul_sum]
    ring
  unfold coupledCosineError
  ring_nf at hrx hry hc hcross hlinear hd ht hs ⊢
  linarith only [hrx, hry, hc, hcross, hlinear, hd, ht, hs]

/-! ### The complete grouped interaction -/

/-- The squares kept by the free population `(z, s)` with cosine trial `pp` and second trial `v`. -/
def freeSquares (ν e : ℝ) (pp v : ℕ → ℝ) {r : ℕ} (z s : Fin r → ℝ) : ℝ :=
  sqTail pp (pinCosineMoment ν e z) +
    sqTail v (fun j => pinPowerMoment ν e z j - 2 * pinColumnMoment ν e s j) / 2

/-- All squares kept by the grouped interaction with trials `(u, v, w)`. -/
def groupedSquares (ν e : ℝ) (u v w : ℕ → ℝ) {a b r : ℕ}
    (x : Fin a → ℝ) (y : Fin b → ℝ) (z s : Fin r → ℝ) : ℝ :=
  cosineSquares ν e u x y + freeSquares ν e v w z s

theorem grouped_population_canonical_sq {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {a b r : ℕ}
    (ha : (a : ℝ) ≤ ν) (hb : (b : ℝ) ≤ ν) (hr : (r : ℝ) ≤ ν)
    (x : Fin a → ℝ) (y : Fin b → ℝ) (z s : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hyi : Function.Injective y)
    (hzi : Function.Injective z) (hsi : Function.Injective s)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) (hw : Summable (fun k => |w k|)) :
    groupedPopulationInteraction ν x y z s + groupedSquares ν e u v w x y z s ≤
      -(1 / 2 : ℝ) * (((a : ℝ) / ν) ^ 2 + ((b : ℝ) / ν) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq u + barrierTrialNormSq v + barrierTrialNormSq w / 2 +
      (∑ i, -2 * barrierTrialT u (x i)) / ν +
      (∑ i, -u 1 * y i) / ν +
      (∑ i, (-2 * barrierTrialT v (z i) - barrierTrialS w (z i))) / ν +
      (∑ i, 2 * barrierTrialT w (s i)) / ν -
      (∑ i, Real.log (1 - z i)) / (2 * ν ^ 2) -
      (∑ i, Real.log (1 - s i)) / ν ^ 2 + groupedPopulationError ν e u v w := by
  have hc := grouped_cosine_cross_canonical_sq hν he ha hb x y hx hy hxi hyi u hu
  have hf := free_population_canonical_sq hν he hr hz hs hzi hsi v w hv hw
  have hySum : -u 1 * ((∑ i, y i) / ν) = (∑ i, -u 1 * y i) / ν := by
    rw [← mul_sum]
    ring
  unfold groupedPopulationInteraction groupedPopulationError groupedSquares freeSquares
  linarith only [hc, hf, hySum]

/-! ### Field brackets -/

/-- The bracket `(Σ_i (cap - X_i)) / ν`: the normalised gap between the supremum bound `cap` and
the node sum of the field `X`. -/
def bracketSlack (ν cap : ℝ) {m : ℕ} (X : Fin m → ℝ) : ℝ := (∑ i, (cap - X i)) / ν

theorem bracketSlack_nonneg {ν cap : ℝ} (hν : 0 < ν) {m : ℕ} {X : Fin m → ℝ}
    (h : ∀ i, X i ≤ cap) : 0 ≤ bracketSlack ν cap X :=
  div_nonneg (sum_nonneg fun i _ => sub_nonneg.mpr (h i)) hν.le

/-- All slack of the grouped bound: the four field brackets and the squares. -/
def groupedSlack (ν e : ℝ) (u v w : ℕ → ℝ) (R M L C : ℝ → ℝ) (RF MF LF CF : ℝ) {r a b : ℕ}
    (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ) : ℝ :=
  bracketSlack ν RF (fun i => R (z i) - 2 * barrierTrialT u (z i) -
        2 * barrierTrialT v (z i) - barrierTrialS w (z i) - Real.log (1 - z i) / (2 * ν)) +
      bracketSlack ν MF (fun i => M (x i) - 2 * barrierTrialT u (x i)) +
      bracketSlack ν LF (fun i => L (y i) - u 1 * y i) +
      bracketSlack ν CF (fun i => C (s i) + 2 * barrierTrialT w (s i) -
        Real.log (1 - s i) / ν) +
      groupedSquares ν e u v w (Fin.append z x) y z s

theorem grouped_field_caps_bound_sq {ν e constant : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {r a b : ℕ}
    (ha : ((r + a : ℕ) : ℝ) ≤ ν) (hb : (b : ℝ) ≤ ν)
    (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ)
    (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective z) (hxi : Function.Injective (Fin.append z x))
    (hyi : Function.Injective y) (hsi : Function.Injective s)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) (hw : Summable (fun k => |w k|))
    (R M L C : ℝ → ℝ) (RF MF LF CF : ℝ) :
    groupedValueWithFields ν constant R M L C z x y s +
      groupedSlack ν e u v w R M L C RF MF LF CF z x y s ≤
      constant - (1 / 2 : ℝ) * ((((r + a : ℕ) : ℝ) / ν) ^ 2 + ((b : ℝ) / ν) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq u + barrierTrialNormSq v + barrierTrialNormSq w / 2 +
      ((r : ℝ) / ν) * (RF + CF) + ((a : ℝ) / ν) * MF + ((b : ℝ) / ν) * LF +
      groupedPopulationError ν e u v w := by
  have hr : (r : ℝ) ≤ ν := by
    have ht : (r : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right r a
    exact ht.trans ha
  have hzx : ∀ i, Fin.append z x i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hz j
    · simpa using hx j
  have hi := grouped_population_canonical_sq hν he ha hb hr (Fin.append z x) y z s
    hzx hy hz hs hxi hyi hzi hsi u v w hu hv hw
  have hsplit : (∑ i : Fin (r + a), -2 * barrierTrialT u (Fin.append z x i)) =
      (∑ i : Fin r, -2 * barrierTrialT u (z i)) +
        (∑ i : Fin a, -2 * barrierTrialT u (x i)) := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hsplit] at hi
  unfold groupedSlack bracketSlack
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_div, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul] at hi ⊢
  unfold groupedValueWithFields
  generalize groupedSquares ν e u v w (Fin.append z x) y z s = Q at hi ⊢
  ring_nf at hi ⊢
  linarith only [hi]

/-! ### Nonnegativity -/

theorem pin_hasSum_cos_sq_shift {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ}
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => pinCosineMoment ν e x (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin p, ∑ j : Fin p,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
        ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
  apply (hasSum_nat_add_iff
    (f := fun k : ℕ => pinCosineMoment ν e x k ^ 2 / (k : ℝ)) 1).2
  simpa using pin_hasSum_first_square hν he hx

theorem cosineSquares_nonneg {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p q : ℕ}
    {x : Fin p → ℝ} {y : Fin q → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (3 / 4 : ℝ) * sqTail u (pinCosineMoment ν e x) ≤ cosineSquares ν e u x y ∧
      0 ≤ cosineSquares ν e u x y := by
  have h1 := first_le_sqTail u _ hu (pin_hasSum_cos_sq_shift hν he hx)
  have h2 := first_le_sqTail (fun _ => 0) _ (by simp) (pin_hasSum_cos_sq_shift hν he hy)
  unfold cosineSquares
  have hn := sqTail_nonneg u (pinCosineMoment ν e x)
  constructor <;> nlinarith [sq_nonneg (pinCosineMoment ν e x 1 - u 1 +
    2 * pinCosineMoment ν e y 1)]

theorem groupedSquares_nonneg {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {a b r : ℕ} {x : Fin a → ℝ} {y : Fin b → ℝ} (z s : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    0 ≤ groupedSquares ν e u v w x y z s := by
  have h1 := (cosineSquares_nonneg hν he hx hy u hu).2
  have h2 := sqTail_nonneg v (pinCosineMoment ν e z)
  have h3 := sqTail_nonneg w (fun j => pinPowerMoment ν e z j - 2 * pinColumnMoment ν e s j)
  unfold groupedSquares freeSquares
  linarith only [h1, h2, h3]

theorem groupedSlack_nonneg {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {r a b : ℕ} (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ)
    (hx : ∀ i, Fin.append z x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (R M L C : ℝ → ℝ) (RF MF LF CF : ℝ)
    (hR : ∀ i, R (z i) - 2 * barrierTrialT u (z i) -
        2 * barrierTrialT v (z i) - barrierTrialS w (z i) - Real.log (1 - z i) / (2 * ν) ≤ RF)
    (hM : ∀ i, M (x i) - 2 * barrierTrialT u (x i) ≤ MF)
    (hL : ∀ i, L (y i) - u 1 * y i ≤ LF)
    (hC : ∀ i, C (s i) + 2 * barrierTrialT w (s i) - Real.log (1 - s i) / ν ≤ CF) :
    0 ≤ groupedSlack ν e u v w R M L C RF MF LF CF z x y s := by
  unfold groupedSlack
  have := groupedSquares_nonneg hν he z s hx hy u v w hu
  have := bracketSlack_nonneg hν hR
  have := bracketSlack_nonneg hν hM
  have := bracketSlack_nonneg hν hL
  have := bracketSlack_nonneg hν hC
  linarith

/-! ### `second_energy` with the brackets and squares kept -/

set_option maxHeartbeats 1600000 in
/-- **`second_energy` keeping the dropped squares and field brackets.**  The output is
`E + (b₁ + b₂ + b₃ + b₄ + sq) ≤ U`, the hypothesis of `near_optimal_components`, where
`groupedSlack ≥ 0` is the sum of the four field brackets (free rows, marked rows, near rows,
columns; each `cap - X(node)` normalised by `ν`) and the completed squares `groupedSquares`
(damped cosine moments `A_k` of the actual nodes `Fin.append z x` against the trial `D.p`, the
near moments, the free population's `A_k(z)` and `B_k - 2 C_k` against `D.p`, `D.v`).
The damping `e` is a parameter: any `e ∈ (0, 1/8)` with `e c < δ / 2` works, `c` as below. -/
theorem second_energy_sq {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20) < δ / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationPhysicalColumnField P N (a + b))
        z x y s +
      groupedSlack (P.n N : ℝ) e D.p D.p D.v (populationPhysicalFreeField P N)
        (groupedMarkedField P N) (groupedNearField P N)
        (populationPhysicalColumnField P N (a + b))
        (D.MX + δ / 4) (residual + δ / 4) (nearCap + δ / 4)
        (D.MY + δ / 4 + (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * Real.log 2) z x y s ≤
        -target + Real.log 2 / 2 + cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ := by
  have hε : 0 < δ / 4 := by linarith only [hδ]
  have herr : ∀ᶠ N : ℕ in atTop,
      groupedPopulationError ((P.n0 : ℝ) * N) e D.p D.p D.v ≤ δ / 2 :=
    ((tendsto_order.mp (grouped_error_tendsto hP e D.p D.v)).2 (δ / 2) hec).mono
      (fun _ h => h.le)
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  have hα : 0 ≤ ((a + b : ℕ) : ℝ) / (P.n N : ℝ) := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ (b : ℝ) / (P.n N : ℝ) := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / (P.n N : ℝ) = 1 - ((a + b : ℕ) : ℝ) / (P.n N : ℝ) := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    linarith only [hf]
  have hmarked : (a : ℝ) / (P.n N : ℝ) =
      ((a + b : ℕ) : ℝ) / (P.n N : ℝ) - (b : ℝ) / (P.n N : ℝ) := by
    rw [Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound_sq (constant := groupedConstant P N r a b) hν he
    (by exact_mod_cast (show r + a ≤ P.n N by omega))
    (by exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (groupedMarkedField P N)
    (groupedNearField P N) (populationPhysicalColumnField P N (a + b))
    (D.MX + δ / 4) (residual + δ / 4)
    (nearCap + δ / 4) (D.MY + δ / 4 + (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * Real.log 2)
  have hconst := grouped_constant_le hP hN hcount
  have hbudget := D.budget hα hβ
  have hnorm := D.norm_le
  have hfields := congrArg (fun t : ℝ => (1 - ((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * t) D.field_sum
  have hεα := mul_nonneg hε.le hα
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  ring_nf at hb hconst hbudget hfields hnorm herror hεα ⊢
  nlinarith only [hb, hconst, hbudget, hfields, hnorm, herror, hεα, hsmall]



/-! ### Lemma K containment: the spike count of a near-optimal configuration -/

/-- The free-row node function of the bracket (`R - 4T_p - S_v - log(1-x)/(2n)`). -/
def freeRowX (P : Parameters) (N : ℕ) (p v : ℕ → ℝ) (x : ℝ) : ℝ :=
  populationPhysicalFreeField P N x - 2 * barrierTrialT p x - 2 * barrierTrialT p x -
    barrierTrialS v x - Real.log (1 - x) / (2 * (P.n N : ℝ))

/-- Counting: if every term of a bracket is `≥ 0` and the terms on `S` are `≥ d`, then
`|S| d ≤ ν · bracket`. -/
theorem card_mul_le_bracket {ν cap d : ℝ} (hν : 0 < ν) {m : ℕ} (X : Fin m → ℝ)
    (S : Finset (Fin m)) (hX : ∀ i, X i ≤ cap) (hS : ∀ i ∈ S, X i ≤ cap - d) :
    (S.card : ℝ) * d ≤ ν * bracketSlack ν cap X := by
  unfold bracketSlack
  rw [mul_div_cancel₀ _ hν.ne']
  calc (S.card : ℝ) * d = ∑ i ∈ S, d := by simp
    _ ≤ ∑ i ∈ S, (cap - X i) := Finset.sum_le_sum fun i hi => by linarith [hS i hi]
    _ ≤ ∑ i, (cap - X i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => sub_nonneg.mpr (hX i)

set_option maxHeartbeats 1600000 in
/-- **Lemma K containment, spike count (PROOF-A 17.8-17.9, 17.34; NOTES 13.5/13.7).**  Let `D` be
the old (532) trial and `d` the drop of the free-row node function beyond `1 - θ` below the cap
`MX + δ/4` (`hsup`, a per-trial sup certificate).  Eventually in `N`, for every grouped
configuration whose product exceeds the target-`t0` bound (the near-optimal class), the free
spikes `S = {i : 1 - θ < z_i}` satisfy `|S| d ≤ n (U - V0)`, with `U = -target + log 2/2 + cost α + δ`
the old route's value and `V0 = -t0 + log 2/2 + c2 N (a+b)/n²` the violated level. -/
theorem free_spike_count {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G) {δ e : ℝ} (hδ : 0 < δ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20) < δ / 2)
    {θ d t0 c2 : ℝ}
    (hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1 - θ) 1, freeRowX P N D.p D.v x ≤ D.MX + δ / 4 - d) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-t0 + Real.log 2 / 2) + c2 * N * (a + b)) <
        groupedProduct P N z x y s →
      ((Finset.univ.filter (fun i => 1 - θ < z i)).card : ℝ) * d ≤
        (P.n N : ℝ) * ((-target + Real.log 2 / 2 + cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ) -
          ((-t0 + Real.log 2 / 2) + c2 * N * (a + b) / (P.n N : ℝ) ^ 2)) := by
  have hε : 0 < δ / 4 := by linarith
  filter_upwards [second_energy_sq hP D hδ he hec, D.row hε, D.column hε, hsup,
    log_reciprocal_eventually hP hε, eventually_gt_atTop (0 : ℕ)]
    with N hE hrow hcol hsupN hl2 hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi hv
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hE1 := hE r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  have hpos : 0 < groupedProduct P N z x y s := lt_trans (Real.exp_pos _) hv
  have hlog := log_groupedProduct hP hN z x y s hz hx hy' hs hz0 (fun i => (hy i).1.ne')
    hzi hxi hyi hsi
  set V := groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
    (populationPhysicalFreeField P N) (groupedMarkedField P N) (groupedNearField P N)
    (populationPhysicalColumnField P N (a + b)) z x y s with hV
  have hV0 : ((P.n0 : ℝ) * N) ^ 2 * (-t0 + Real.log 2 / 2) + c2 * N * (a + b) <
      (P.n N : ℝ) ^ 2 * V := by
    rw [← hlog]
    exact (Real.lt_log_iff_exp_lt hpos).mpr hv
  have hV1 : (-t0 + Real.log 2 / 2) + c2 * N * (a + b) / (P.n N : ℝ) ^ 2 < V := by
    have hn2 : 0 < (P.n N : ℝ) ^ 2 := by positivity
    rw [← n_cast] at hV0
    have e1 : ((-t0 + Real.log 2 / 2) + c2 * N * (a + b) / (P.n N : ℝ) ^ 2) * (P.n N : ℝ) ^ 2 =
        (P.n N : ℝ) ^ 2 * (-t0 + Real.log 2 / 2) + c2 * N * (a + b) := by
      field_simp
    have h2 : ((-t0 + Real.log 2 / 2) + c2 * N * (a + b) / (P.n N : ℝ) ^ 2) * (P.n N : ℝ) ^ 2 <
        V * (P.n N : ℝ) ^ 2 := by rw [e1]; linarith
    exact lt_of_mul_lt_mul_right h2 hn2.le
  have hzx : ∀ i, Fin.append z x i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hz j
    · simpa using hx j
  have hXz : ∀ i, freeRowX P N D.p D.v (z i) ≤ D.MX + δ / 4 := by
    intro i
    have hzi' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
      rcases lt_or_gt_of_ne (hz0 i) with h | h
      · exact Or.inl ⟨(hz i).1.le, h⟩
      · exact Or.inr ⟨h, (hz i).2⟩
    have := hrow (z i) hzi'
    unfold freeRowX
    linarith
  have hM : ∀ i, groupedMarkedField P N (x i) - 2 * barrierTrialT D.p (x i) ≤ residual + δ / 4 :=
    fun i => (D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)).trans (by linarith)
  have hL : ∀ i, groupedNearField P N (y i) - D.p 1 * y i ≤ nearCap + δ / 4 :=
    fun i => (D.near hN (hy i)).trans (by linarith)
  have hC : ∀ i, populationPhysicalColumnField P N (a + b) (s i) + 2 * barrierTrialT D.v (s i) -
      Real.log (1 - s i) / (P.n N : ℝ) ≤
        D.MY + δ / 4 + (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * Real.log 2 := by
    intro i
    have h1 := hcol (s i) (hs i)
    have hl : Real.log (1 + s i) ≤ Real.log 2 :=
      Real.log_le_log (by linarith [(hs i).1]) (by linarith [(hs i).2])
    have hα : 0 ≤ (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) := by positivity
    have hm := mul_le_mul_of_nonneg_left hl hα
    have e1 : populationPhysicalColumnField P N (a + b) (s i) =
        populationEndpointColumnField P N 0 (s i) +
          (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * Real.log (1 + s i) := by
      unfold populationPhysicalColumnField populationEndpointColumnField
      push_cast
      ring
    rw [e1]
    linarith
  have hb2 := bracketSlack_nonneg hν hM
  have hb3 := bracketSlack_nonneg hν hL
  have hb4 := bracketSlack_nonneg hν hC
  have hsq := groupedSquares_nonneg hν he z s hzx hy' D.p D.p D.v D.p_summable
  have hfree : bracketSlack (P.n N : ℝ) (D.MX + δ / 4)
      (fun i => populationPhysicalFreeField P N (z i) - 2 * barrierTrialT D.p (z i) -
        2 * barrierTrialT D.p (z i) - barrierTrialS D.v (z i) -
        Real.log (1 - z i) / (2 * (P.n N : ℝ))) ≤
      (-target + Real.log 2 / 2 + cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ) - V := by
    unfold groupedSlack at hE1
    linarith
  have hcnt := card_mul_le_bracket hν
    (fun i => populationPhysicalFreeField P N (z i) - 2 * barrierTrialT D.p (z i) -
        2 * barrierTrialT D.p (z i) - barrierTrialS D.v (z i) -
        Real.log (1 - z i) / (2 * (P.n N : ℝ)))
    (Finset.univ.filter (fun i => 1 - θ < z i)) hXz
    (fun i hi => hsupN (z i) ⟨(Finset.mem_filter.mp hi).2, (hz i).2⟩)
  calc _ ≤ _ := hcnt
    _ ≤ (P.n N : ℝ) * ((-target + Real.log 2 / 2 +
          cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ) - V) :=
        mul_le_mul_of_nonneg_left hfree hν.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hν.le

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.second_energy_sq
#print axioms CatalanMeasure.Signed.groupedSlack_nonneg
#print axioms CatalanMeasure.Signed.cosineSquares_nonneg
#print axioms CatalanMeasure.Signed.grouped_field_caps_bound_sq
#print axioms CatalanMeasure.Signed.free_spike_count
