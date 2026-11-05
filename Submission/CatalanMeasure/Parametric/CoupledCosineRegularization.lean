module

public import Submission.CatalanMeasure.Parametric.CoupledFirstEnergy
public import Submission.CatalanMeasure.PopulationDual

/-!
# Undamped grouped cosine energy and its first-moment interaction
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset
open scoped BigOperators

noncomputable section

theorem normalized_node_sum_abs_le_one {ν : ℝ} (hν : 0 < ν) {p : ℕ}
    (hp : (p : ℝ) ≤ ν) (x : Fin p → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |(∑ i, x i) / ν| ≤ 1 := by
  rw [abs_div, abs_of_pos hν, div_le_one hν]
  calc
    |∑ i, x i| ≤ ∑ i, |x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin p, (1 : ℝ) := sum_le_sum fun i _ => hx i
    _ = (p : ℝ) := by simp
    _ ≤ ν := hp

theorem pinCosineMoment_first (ν e : ℝ) {p : ℕ} (x : Fin p → ℝ) :
    pinCosineMoment ν e x 1 = realEnergyTau e * ((∑ i, x i) / ν) := by
  simp [pinCosineMoment, Polynomial.Chebyshev.T_one, ← mul_sum, mul_div_assoc]

theorem first_moment_product_damping_error {e X Y : ℝ}
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hX : |X| ≤ 1) (hY : |Y| ≤ 1) :
    -X * Y ≤ -(realEnergyTau e * X) * (realEnergyTau e * Y) + 2 * e := by
  have hXY : |X * Y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hX hY (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hl : -1 ≤ X * Y := (abs_le.mp hXY).1
  have hq : 0 ≤ 1 - (1 - e) ^ 2 := by nlinarith only [he.1, he.2]
  have hh := mul_nonneg hq (by linarith only [hl] : 0 ≤ X * Y + 1)
  dsimp only [realEnergyTau]
  nlinarith only [hh, sq_nonneg e]

theorem first_moment_linear_damping_error {e u Y : ℝ}
    (he : 0 ≤ e) (hY : |Y| ≤ 1) :
    -u * (realEnergyTau e * Y) ≤ -u * Y + e * |u| := by
  have hbase : u * Y ≤ |u| := by
    calc
      _ ≤ |u * Y| := le_abs_self _
      _ = |u| * |Y| := abs_mul _ _
      _ ≤ |u| * 1 := mul_le_mul_of_nonneg_left hY (abs_nonneg _)
      _ = |u| := mul_one _
  have hh := mul_le_mul_of_nonneg_left hbase he
  dsimp only [realEnergyTau]
  nlinarith only [hh]

def coupledCosineError (ν e : ℝ) (u : ℕ → ℝ) : ℝ :=
  (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / ν +
    6 * e + 2 * e * (∑' k, |u k|) + e * |u 1|

theorem grouped_cosine_cross_canonical {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p q : ℕ}
    (hp : (p : ℝ) ≤ ν) (hq : (q : ℝ) ≤ ν)
    (x : Fin p → ℝ) (y : Fin q → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (hxi : Function.Injective x) (hyi : Function.Injective y)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    (∑ i : Fin p, ∑ j ∈ Ioi i, Real.log |x j - x i|) / ν ^ 2 +
    (∑ i : Fin q, ∑ j ∈ Ioi i, Real.log |y j - y i|) / ν ^ 2 +
    Real.log (crossCauchyProduct x y) / ν ^ 2 ≤
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
  have hd := pin_coupled_first_tangent hν he hp hx hy u hu
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

end

end CatalanMeasure.Parametric
