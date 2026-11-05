module

public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergySupDual

@[expose] public section

/-!
# The damped energy dual for a configuration of `p` points normalized by `ν`

OpenAI's `RealEnergyDampedDual` proves the square-completion ("dual certificate") bound for a
configuration of exactly `n N` row nodes and `n N` column nodes, normalized by `n N`.  The
perturbation lemma needs the same bound for configurations of `p ≤ n N` nodes that are still
normalized by `n N`.  This file is OpenAI's argument with `Fin (n N)` replaced by `Fin p` and
the normalizer `n N` replaced by a real `ν ≥ p`; the only changes are the constants
`(p / ν)^2 log 2` coming from the diagonal of the square completion.
-/

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial Set
open scoped BigOperators

def pinCosineMoment (ν e : ℝ) {p : ℕ} (x : Fin p → ℝ) (k : ℕ) : ℝ :=
  (∑ i, realEnergyTau e ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (x i)) / ν

def pinPowerMoment (ν e : ℝ) {p : ℕ} (x : Fin p → ℝ) (k : ℕ) : ℝ :=
  (∑ i, realEnergyRho e (x i) ^ k * x i ^ k) / ν

def pinColumnMoment (ν e : ℝ) {p : ℕ} (s : Fin p → ℝ) (k : ℕ) : ℝ :=
  (∑ j, realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / ν

theorem pin_cosineMoment_square_div_eq (ν e : ℝ) {p : ℕ}
    (x : Fin p → ℝ) (k : ℕ) :
    pinCosineMoment ν e x k ^ 2 / (k : ℝ) =
      (1 / (2 * ν ^ 2)) *
        (∑ i : Fin p, ∑ j : Fin p,
          2 * (realEnergyTau e ^ 2) ^ k *
            (Chebyshev.T ℝ (k : ℤ)).eval (x i) *
            (Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ)) := by
  unfold pinCosineMoment
  rw [← Finset.mul_sum, energy_sum_sum_mul_div]
  simp only [pow_two, mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem pin_hasSum_first_square {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {p : ℕ} {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => pinCosineMoment ν e x k ^ 2 / (k : ℝ))
      (-((∑ i : Fin p, ∑ j : Fin p,
            realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
          ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
  have ht := realEnergyTau_bounds he
  have hr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    have hm := mul_lt_mul_of_pos_left ht.2 ht.1
    nlinarith [ht.2]
  have hn : ν ≠ 0 := hν.ne'
  have hseries :
      HasSum (fun k : ℕ => ∑ i : Fin p, ∑ j : Fin p,
          2 * (realEnergyTau e ^ 2) ^ k *
            (Chebyshev.T ℝ (k : ℤ)).eval (x i) *
            (Chebyshev.T ℝ (k : ℤ)).eval (x j) / (k : ℝ))
        (∑ i : Fin p, ∑ j : Fin p,
          (-realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j) -
            Real.log 2)) := by
    apply hasSum_sum
    intro i hi
    apply hasSum_sum
    intro j hj
    exact energy_hasSum_cosine_kernel hr
      ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hx j).1.le, (hx j).2.le⟩
  convert hseries.mul_left (1 / (2 * ν ^ 2)) using 1
  · funext k
    exact pin_cosineMoment_square_div_eq ν e x k
  · simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn]
    ring

theorem pin_abs_average_le_one {ν : ℝ} (hν : 0 < ν) {p : ℕ} (hp : (p : ℝ) ≤ ν)
    (a : Fin p → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |(∑ i, a i) / ν| ≤ 1 := by
  rw [abs_div, abs_of_pos hν]
  apply (div_le_iff₀ hν).mpr
  calc
    |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin p, (1 : ℝ) := Finset.sum_le_sum (fun i _ => ha i)
    _ = (p : ℝ) := by simp
    _ ≤ 1 * ν := by linarith

theorem pin_cosineMoment_abs_le_one {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hp : (p : ℝ) ≤ ν)
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    |pinCosineMoment ν e x k| ≤ 1 := by
  apply pin_abs_average_le_one hν hp
  intro i
  have ht := realEnergyTau_bounds he
  rw [abs_mul, abs_pow, abs_of_pos ht.1]
  exact (mul_le_mul (pow_le_one₀ ht.1.le ht.2.le)
    (energy_chebyshev_abs_le_one k ⟨(hx i).1.le, (hx i).2.le⟩)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem pin_powerMoment_abs_le_one {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hp : (p : ℝ) ≤ ν)
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (k : ℕ) :
    |pinPowerMoment ν e x k| ≤ 1 := by
  apply pin_abs_average_le_one hν hp
  intro i
  have hr := realEnergyRho_mem he (hx i)
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos hr.1]
  exact (mul_le_mul (pow_le_one₀ hr.1.le hr.2.le)
    (pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩))
    (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq (one_mul _)

theorem pin_columnMoment_abs_le_one {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hp : (p : ℝ) ≤ ν)
    {s : Fin p → ℝ} (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |pinColumnMoment ν e s k| ≤ 1 := by
  apply pin_abs_average_le_one hν hp
  intro j
  have hr := realEnergySigma_mem he (hs j)
  rw [abs_mul, abs_pow, abs_of_pos hr.1]
  exact (mul_le_mul (pow_le_one₀ hr.1.le hr.2.le)
    (energy_chebyshev_abs_le_one k ⟨by linarith [(hs j).1], (hs j).2.le⟩)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem pin_secondMoment_abs_le_three {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hp : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |pinPowerMoment ν e x k - 2 * pinColumnMoment ν e s k| ≤ 3 := by
  have hb := pin_powerMoment_abs_le_one hν he hp hx k
  have hc := pin_columnMoment_abs_le_one hν he hp hs k
  calc
    _ ≤ |pinPowerMoment ν e x k| + |2 * pinColumnMoment ν e s k| := abs_sub _ _
    _ = |pinPowerMoment ν e x k| + 2 * |pinColumnMoment ν e s k| := by
      rw [abs_mul]; norm_num
    _ ≤ 3 := by linarith

theorem pin_hasSum_power_square (ν e : ℝ) {p : ℕ} (x : Fin p → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => pinPowerMoment ν e x k ^ 2 / (k : ℝ))
      (-(∑ i : Fin p, ∑ j : Fin p,
        Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
          ν ^ 2) := by
  have hp (i j : Fin p) := energy_hasSum_mul_power_div
    (realEnergy_damped_node_mem he (hx i)) (realEnergy_damped_node_mem he (hx j))
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin p, ∑ j : Fin p,
        ((realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j)) ^ k / (k : ℝ))
      (∑ i : Fin p, ∑ j : Fin p,
        -Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin p, ∑ j : Fin p,
        ((realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j)) ^ k / (k : ℝ)) =
      (∑ i : Fin p, realEnergyRho e (x i) ^ k * x i ^ k) ^ 2 / (k : ℝ) := by
    simp only [mul_pow]
    simpa only [one_mul, pow_two] using energy_sum_sum_mul_div
      (fun i : Fin p => realEnergyRho e (x i) ^ k * x i ^ k)
      (fun i : Fin p => realEnergyRho e (x i) ^ k * x i ^ k) 1 (k : ℝ)
  convert hs.mul_left (1 / ν ^ 2) using 1
  · ext k
    rw [hc]
    unfold pinPowerMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_neg_distrib]
    ring

theorem pin_hasSum_column_square {ν : ℝ} (hν : 0 < ν)
    (e : ℝ) {p : ℕ} (s : Fin p → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * pinColumnMoment ν e s k ^ 2 / (k : ℝ))
      (-(∑ i : Fin p, ∑ j : Fin p,
        realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
          ν ^ 2 - ((p : ℝ) / ν) ^ 2 * Real.log 2) := by
  have hn0 : ν ≠ 0 := hν.ne'
  have hs' (i : Fin p) : s i ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(hs i).1], (hs i).2.le⟩
  have hr (i j : Fin p) :
      realEnergySigma e (s i) * realEnergySigma e (s j) ∈ Ico (0 : ℝ) 1 :=
    ⟨(mul_pos (realEnergySigma_mem he (hs i)).1 (realEnergySigma_mem he (hs j)).1).le,
      (realEnergySigma_mul_bounds he (hs i) (hs j)).2⟩
  have hp (i j : Fin p) := energy_hasSum_cosine_kernel (hr i j) (hs' i) (hs' j)
  have hh : HasSum
      (fun k : ℕ => ∑ i : Fin p, ∑ j : Fin p,
        2 * (realEnergySigma e (s i) * realEnergySigma e (s j)) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s i) * (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ))
      (∑ i : Fin p, ∑ j : Fin p,
        (-realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j) -
          Real.log 2)) := hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin p, ∑ j : Fin p,
        2 * (realEnergySigma e (s i) * realEnergySigma e (s j)) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s i) * (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ)) =
      2 * (∑ i : Fin p, realEnergySigma e (s i) ^ k *
        (Chebyshev.T ℝ (k : ℤ)).eval (s i)) ^ 2 / (k : ℝ) := by
    calc
      _ = ∑ i : Fin p, ∑ j : Fin p,
          2 * (realEnergySigma e (s i) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s i)) *
            (realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        ring
      _ = _ := by rw [energy_sum_sum_mul_div]; ring
  convert hh.mul_left (1 / ν ^ 2) using 1
  · ext k
    rw [hc]
    unfold pinColumnMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
    field_simp [hn0]

theorem pin_hasSum_mixed_moments (ν e : ℝ) {p : ℕ} (x s : Fin p → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * pinPowerMoment ν e x k *
      pinColumnMoment ν e s k / (k : ℝ))
      (-(∑ i : Fin p, ∑ j : Fin p,
        Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
          (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / ν ^ 2) := by
  have hs' (j : Fin p) : s j ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(hs j).1], (hs j).2.le⟩
  have hz (i j : Fin p) :
      realEnergyRho e (x i) * realEnergySigma e (s j) * x i ∈ Ioo (-1 : ℝ) 1 := by
    have hr := realEnergyRho_mem he (hx i)
    have ht := realEnergySigma_mem he (hs j)
    exact energy_mul_mem_Ioo
      (energy_mul_mem_Ioo ⟨by linarith [hr.1], hr.2⟩ ⟨by linarith [ht.1], ht.2⟩) (hx i)
  have hp (i j : Fin p) := energy_hasSum_cross_kernel (hz i j) (hs' j)
  have hh : HasSum
      (fun k : ℕ => ∑ i : Fin p, ∑ j : Fin p,
        2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ))
      (∑ i : Fin p, ∑ j : Fin p,
        -Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
          (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => hp i j))
  have hc (k : ℕ) :
      (∑ i : Fin p, ∑ j : Fin p,
        2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j) / (k : ℝ)) =
      2 * (∑ i : Fin p, realEnergyRho e (x i) ^ k * x i ^ k) *
        (∑ j : Fin p, realEnergySigma e (s j) ^ k *
          (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
    calc
      _ = ∑ i : Fin p, ∑ j : Fin p,
          2 * (realEnergyRho e (x i) ^ k * x i ^ k) *
            (realEnergySigma e (s j) ^ k * (Chebyshev.T ℝ (k : ℤ)).eval (s j)) / (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [mul_pow]
        ring
      _ = _ := energy_sum_sum_mul_div _ _ _ _
  convert hh.mul_left (1 / ν ^ 2) using 1
  · ext k
    rw [hc]
    unfold pinPowerMoment pinColumnMoment
    simp only [div_eq_mul_inv]
    ring
  · simp only [Finset.sum_neg_distrib]
    ring

theorem pin_hasSum_second_square {ν : ℝ} (hν : 0 < ν)
    (e : ℝ) {p : ℕ} (x s : Fin p → ℝ)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ =>
      (pinPowerMoment ν e x k - 2 * pinColumnMoment ν e s k) ^ 2 / (2 * (k : ℝ)))
      (-((∑ i : Fin p, ∑ j : Fin p,
          Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
            (2 * ν ^ 2) +
        (∑ i : Fin p, ∑ j : Fin p,
          realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
            ν ^ 2 -
        (∑ i : Fin p, ∑ j : Fin p,
          Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
            (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / ν ^ 2 +
        ((p : ℝ) / ν) ^ 2 * Real.log 2)) := by
  have hp := (pin_hasSum_power_square ν e x he hx).mul_left (1 / 2 : ℝ)
  have hc := pin_hasSum_column_square hν e s he hs
  have hm := pin_hasSum_mixed_moments ν e x s he hx hs
  convert (hp.add hc).sub hm using 1
  · ext k
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem pin_hasSum_trialTau_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (ν : ℝ) {e : ℝ} {p : ℕ}
    {x : Fin p → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * pinCosineMoment ν e x (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ i : Fin p, realEnergyTrialTau u e (x i)) / ν) := by
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin p,
        u (k + 1) * realEnergyTau e ^ (k + 1) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x i) / ((k + 1 : ℕ) : ℝ))
      (∑ i : Fin p, realEnergyTrialTau u e (x i)) := by
    apply hasSum_sum
    intro i hi
    exact (realEnergyTrialTau_summable u hu he (hx i)).hasSum
  convert hs.div_const ν using 1
  funext k
  simp only [pinCosineMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pin_hasSum_trialRho_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (ν : ℝ) {e : ℝ} {p : ℕ}
    {x : Fin p → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * pinPowerMoment ν e x (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ i : Fin p, realEnergyTrialRho u e (x i)) / ν) := by
  have hs : HasSum
      (fun k : ℕ => ∑ i : Fin p,
        u (k + 1) * realEnergyRho e (x i) ^ (k + 1) * x i ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))
      (∑ i : Fin p, realEnergyTrialRho u e (x i)) := by
    apply hasSum_sum
    intro i hi
    exact (realEnergyTrialRho_summable u hu he (hx i)).hasSum
  convert hs.div_const ν using 1
  funext k
  simp only [pinPowerMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pin_hasSum_trialSigma_average (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) (ν : ℝ) {e : ℝ} {p : ℕ}
    {s : Fin p → ℝ} (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun k : ℕ => u (k + 1) * pinColumnMoment ν e s (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      ((∑ j : Fin p, realEnergyTrialSigma u e (s j)) / ν) := by
  have hh : HasSum
      (fun k : ℕ => ∑ j : Fin p,
        u (k + 1) * realEnergySigma e (s j) ^ (k + 1) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (s j) / ((k + 1 : ℕ) : ℝ))
      (∑ j : Fin p, realEnergyTrialSigma u e (s j)) := by
    apply hasSum_sum
    intro j hj
    exact (realEnergyTrialSigma_summable u hu he (hs j)).hasSum
  convert hh.div_const ν using 1
  funext k
  simp only [pinColumnMoment, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem pin_first_tangent {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    ((∑ i : Fin p, ∑ j : Fin p,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
      ((p : ℝ) / ν) ^ 2 * Real.log 2) / 2 ≤
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
  have ht := energy_tangent_of_hasSum u (pinCosineMoment ν e x) hu
    (by norm_num : (0 : ℝ) ≤ 1) (pin_cosineMoment_abs_le_one hν he hpν hx) hS
  linarith

theorem pin_second_tangent {ν e : ℝ} (hν : 0 < ν)
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
      ((p : ℝ) / ν) ^ 2 * Real.log 2 ≤
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
  have ht := energy_tangent_of_hasSum u a hu (by norm_num : (0 : ℝ) ≤ 3)
    (pin_secondMoment_abs_le_three hν he hpν hx hs) hS
  rw [hsplit] at ht
  linarith

def pinDampedInteraction (ν k e : ℝ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  (k / 2) *
    (∑ i : Fin p, ∑ j : Fin p,
      realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)) / ν ^ 2 +
  (∑ i : Fin p, ∑ j : Fin p,
    Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))) /
      (2 * ν ^ 2) +
  (∑ i : Fin p, ∑ j : Fin p,
    realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)) /
      ν ^ 2 -
  (∑ i : Fin p, ∑ j : Fin p,
    Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
      (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)) / ν ^ 2

theorem pinDampedInteraction_le_trials {ν k e : ℝ} (hν : 0 < ν)
    (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    pinDampedInteraction ν k e x s ≤ -(k / 2 + 1) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 -
      2 * k * (∑' j : ℕ, pp (j + 1) * pinCosineMoment ν e x (j + 1) /
        ((j + 1 : ℕ) : ℝ)) -
      (∑' j : ℕ, v (j + 1) * pinPowerMoment ν e x (j + 1) / ((j + 1 : ℕ) : ℝ)) +
      2 * (∑' j : ℕ, v (j + 1) * pinColumnMoment ν e s (j + 1) /
        ((j + 1 : ℕ) : ℝ)) := by
  have hfirst := mul_le_mul_of_nonneg_left (pin_first_tangent hν he hpν hx pp hp) hk
  have hsecond := pin_second_tangent hν he hpν hx hs v hv
  unfold pinDampedInteraction
  simp only [div_eq_mul_inv, mul_inv_rev] at hfirst hsecond ⊢
  nlinarith only [hfirst, hsecond]

theorem pin_average_le_of_le_add {ν : ℝ} (hν : 0 < ν) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    (f g : Fin p → ℝ) {c : ℝ} (hc : 0 ≤ c) (hfg : ∀ i, f i ≤ g i + c) :
    (∑ i, f i) / ν ≤ (∑ i, g i) / ν + c := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hfg i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  have hpc : (p : ℝ) * c ≤ ν * c := mul_le_mul_of_nonneg_right hpν hc
  calc
    _ ≤ ((∑ i, g i) + ν * c) / ν :=
      div_le_div_of_nonneg_right (by linarith) hν.le
    _ = _ := by field_simp [hν.ne']

theorem pinDampedInteraction_le_canonicalTrials {ν k e : ℝ} (hν : 0 < ν)
    (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    pinDampedInteraction ν k e x s ≤ -(k / 2 + 1) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
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
  have hd := pinDampedInteraction_le_trials hν hk he hpν hx hs pp v hp hv
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

end

end InternalCatalan

end

end OAI
