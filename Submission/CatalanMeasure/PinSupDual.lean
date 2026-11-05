module

public import Submission.CatalanMeasure.PinDampedDual

@[expose] public section

/-!
# The uniform energy dual for configurations of `p ≤ n N` nodes

OpenAI's `RealEnergySupDual` bounds the normalized log-energy `realEnergyFiniteValue N k x s`
of every configuration `x s : Fin (n N) → ℝ` by the certified dual constant
`realEnergyDualConstant k p v Bx Bs` up to `o(1)`.  Here the configuration has only `p ≤ n N`
row/column pairs, still normalized by `n N`.  The bound becomes

`pinFiniteValue N k x s ≤ realEnergyDualConstant k p v Bx Bs + d + c · (n N - p) / n N`,

where `c` collects the one-point bounds `|Bx| + |Bs|`, the `log 2` diagonal constant and the
case-field correction.  So every missing pair costs only `O(n N)` in the log of the integrand,
which is what the perturbation lemma needs.
-/

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial Set
open scoped BigOperators

/-- OpenAI's normalized log-energy, for a configuration of `p` pairs normalized by `n N`. -/
def pinFiniteValue (N : ℕ) (k : ℝ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
      Real.log 2 +
    (∑ i : Fin p, (realEnergyField k (x i) +
      (k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) / (n N : ℝ) +
    (∑ j : Fin p, realEnergyColumnField (s j)) / (n N : ℝ) +
    k * (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (n N : ℝ) ^ 2 +
    (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) / (n N : ℝ) ^ 2 +
    2 * (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) / (n N : ℝ) ^ 2 -
    (∑ i : Fin p, ∑ j : Fin p, Real.log (1 - 2 * x i * s j + x i ^ 2)) /
      (n N : ℝ) ^ 2

def pinOffDiagonalInteraction (ν k : ℝ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  k * (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2 +
  (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) / ν ^ 2 +
  2 * (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) / ν ^ 2 -
  (∑ i : Fin p, ∑ j : Fin p, Real.log (1 - 2 * x i * s j + x i ^ 2)) / ν ^ 2

theorem pinOffDiagonalInteraction_le_damped {ν k e : ℝ} (hν : 0 < ν)
    (hk : 0 ≤ k) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ}
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    pinOffDiagonalInteraction ν k x s ≤
      pinDampedInteraction ν k e x s -
      k / (2 * ν ^ 2) *
        (∑ i : Fin p, realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) -
      (∑ i : Fin p, Real.log (1 - (realEnergyRho e (x i) * x i) ^ 2)) /
        (2 * ν ^ 2) -
      (∑ j : Fin p, realEnergyCosineKernel (realEnergySigma e (s j) ^ 2) (s j) (s j)) /
        ν ^ 2 +
      (4 * k + 12) * e * (p.choose 2 : ℝ) / ν ^ 2 + 6 * e * (p : ℝ) ^ 2 / ν ^ 2 := by
  let F : Fin p → Fin p → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x j)
  let G : Fin p → Fin p → ℝ := fun i j =>
    Real.log (1 - (realEnergyRho e (x i) * x i) * (realEnergyRho e (x j) * x j))
  let H : Fin p → Fin p → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergySigma e (s i) * realEnergySigma e (s j)) (s i) (s j)
  let Q : Fin p → Fin p → ℝ := fun i j =>
    Real.log (1 - 2 * (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) * s j +
      (realEnergyRho e (x i) * realEnergySigma e (s j) * x i) ^ 2)
  have hF := energy_sum_pairs_le_of_le_add p
    (fun i j => Real.log |x j - x i|) F (4 * e) (fun i j hij => by
      dsimp [F]
      rw [abs_sub_comm (x j) (x i)]
      exact realEnergy_cosine_tau_le he ⟨(hx i).1.le, (hx i).2.le⟩
        ⟨(hx j).1.le, (hx j).2.le⟩ (fun h => (ne_of_lt hij) (hxi h)))
  have hG := energy_sum_pairs_le_of_le_add p
    (fun i j => Real.log (1 - x i * x j)) G (4 * e) (fun i j _ => by
      have hc := realEnergy_power_kernel_le he (hx i) (hx j)
      dsimp [G]
      convert hc using 1; congr 2; ring)
  have hH := energy_sum_pairs_le_of_le_add p
    (fun i j => Real.log |s j - s i|) H (4 * e) (fun i j hij => by
      dsimp [H]
      rw [abs_sub_comm (s j) (s i)]
      exact realEnergy_cosine_sigma_le he (hs i) (hs j)
        (fun h => (ne_of_lt hij) (hsi h)))
  have hQ :
      -(∑ i : Fin p, ∑ j : Fin p, Real.log (1 - 2 * x i * s j + x i ^ 2)) ≤
      -(∑ i : Fin p, ∑ j : Fin p, Q i j) + 6 * e * (p : ℝ) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => realEnergy_cross_kernel_le he (hx i) (hs j)))
    simpa only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Q, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have ht := realEnergyTau_bounds he
  have htr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hFsym (i j : Fin p) : F i j = F j i :=
    realEnergyCosineKernel_symm htr ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hx j).1.le, (hx j).2.le⟩
  have hGsym (i j : Fin p) : G i j = G j i := by dsimp [G]; rw [mul_comm]
  have hHsym (i j : Fin p) : H i j = H j i := by
    have hi := realEnergySigma_mem he (hs i)
    have hj := realEnergySigma_mem he (hs j)
    have hr : realEnergySigma e (s i) * realEnergySigma e (s j) ∈ Ico (0 : ℝ) 1 :=
      ⟨mul_nonneg hi.1.le hj.1.le, (realEnergySigma_mul_bounds he (hs i) (hs j)).2⟩
    dsimp [H]
    rw [realEnergyCosineKernel_symm hr
      ⟨by linarith [(hs i).1], (hs i).2.le⟩ ⟨by linarith [(hs j).1], (hs j).2.le⟩]
    rw [mul_comm]
  have hpF : (∑ i, ∑ j ∈ Finset.Ioi i, F i j) =
      ((∑ i, ∑ j, F i j) - ∑ i, F i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric p F hFsym]
  have hpG : (∑ i, ∑ j ∈ Finset.Ioi i, G i j) =
      ((∑ i, ∑ j, G i j) - ∑ i, G i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric p G hGsym]
  have hpH : (∑ i, ∑ j ∈ Finset.Ioi i, H i j) =
      ((∑ i, ∑ j, H i j) - ∑ i, H i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric p H hHsym]
  have hh := add_le_add
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hF hk) hG)
      (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2))) hQ
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg ν)
  calc
    pinOffDiagonalInteraction ν k x s =
        (k * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
          (∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
          2 * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) +
          -(∑ i, ∑ j, Real.log (1 - 2 * x i * s j + x i ^ 2))) / ν ^ 2 := by
      unfold pinOffDiagonalInteraction
      ring
    _ ≤ _ := hd
    _ = _ := by
      rw [hpF, hpG, hpH]
      dsimp [F, G, H, Q, pinDampedInteraction]
      simp only [pow_two]
      field_simp [hν.ne']; ring

/-! ### Diagonal terms -/

theorem pin_tau_diagonal_sum {ν e k : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) (hk : 0 ≤ k) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    -(k / (2 * ν ^ 2)) *
        (∑ i : Fin p, realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) ≤
      k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * ν) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    realEnergy_cosine_tau_diagonal_lower he ⟨(hx i).1.le, (hx i).2.le⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ k / (2 * ν ^ 2) by positivity)
  have ht := realEnergyTau_bounds he
  have ht2 : 0 < 1 - realEnergyTau e ^ 2 := by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hlog : Real.log (1 - realEnergyTau e ^ 2) ≤ 0 :=
    Real.log_nonpos ht2.le (by nlinarith [sq_nonneg (realEnergyTau e)])
  have hc0 : 0 ≤ Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  have hkc := mul_nonneg hk hc0
  have hpk : (p : ℝ) * (k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2))) ≤
      ν * (k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2))) :=
    mul_le_mul_of_nonneg_right hpν hkc
  have hc : k / (2 * ν ^ 2) *
      ((p : ℝ) * (-Real.log 2 + 2 * Real.log (1 - realEnergyTau e ^ 2))) =
      -((p : ℝ) * (k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)))) /
        (2 * ν ^ 2) := by
    field_simp [hν.ne']
    ring
  rw [hc, neg_div] at hm
  have hfin : ((p : ℝ) * (k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)))) /
      (2 * ν ^ 2) ≤ k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * ν) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hpk (show 0 ≤ 2 * ν by positivity)]
  have hneg : -(k / (2 * ν ^ 2)) *
      (∑ i : Fin p, realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i)) =
      -(k / (2 * ν ^ 2) *
        (∑ i : Fin p, realEnergyCosineKernel (realEnergyTau e ^ 2) (x i) (x i))) := by ring
  rw [hneg]
  linarith

theorem pin_power_diagonal_sum {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {x : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    -(∑ i : Fin p, Real.log (1 - realEnergyRho e (x i) ^ 2 * x i ^ 2)) /
        (2 * ν ^ 2) ≤
      -(∑ i : Fin p, Real.log (1 - x i)) / (2 * ν ^ 2) +
        (Real.log 2 - Real.log e) / (2 * ν) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    realEnergy_log_power_diagonal_ge he (hx i))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := div_le_div_of_nonneg_right (neg_le_neg hb)
    (show 0 ≤ 2 * ν ^ 2 by positivity)
  have hc0 : 0 ≤ Real.log 2 - Real.log e := by
    have := Real.log_le_log he.1 (show e ≤ 2 by linarith [he.2])
    linarith
  have hpk : (p : ℝ) * (Real.log 2 - Real.log e) ≤ ν * (Real.log 2 - Real.log e) :=
    mul_le_mul_of_nonneg_right hpν hc0
  apply hm.trans
  have heq : -(∑ i : Fin p, Real.log (1 - x i) + (p : ℝ) * Real.log e -
      (p : ℝ) * Real.log 2) / (2 * ν ^ 2) =
      -(∑ i : Fin p, Real.log (1 - x i)) / (2 * ν ^ 2) +
        (p : ℝ) * (Real.log 2 - Real.log e) / (2 * ν ^ 2) := by
    field_simp [hν.ne']; ring
  rw [heq]
  have hfin : (p : ℝ) * (Real.log 2 - Real.log e) / (2 * ν ^ 2) ≤
      (Real.log 2 - Real.log e) / (2 * ν) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hpk (show 0 ≤ 2 * ν by positivity)]
  linarith

theorem pin_sigma_diagonal_sum {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    {s : Fin p → ℝ} (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    -(∑ j : Fin p, realEnergyCosineKernel (realEnergySigma e (s j) ^ 2) (s j) (s j)) /
        ν ^ 2 ≤
      -(∑ j : Fin p, Real.log (1 - s j)) / ν ^ 2 +
        (Real.log 2 - 2 * Real.log e) / ν := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    realEnergy_cosine_sigma_diagonal_lower he (hs j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  have hm := div_le_div_of_nonneg_right (neg_le_neg hb) (sq_nonneg ν)
  have hc0 : 0 ≤ Real.log 2 - 2 * Real.log e := by
    have h1 := Real.log_nonpos he.1.le (by linarith [he.2])
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  have hpk : (p : ℝ) * (Real.log 2 - 2 * Real.log e) ≤ ν * (Real.log 2 - 2 * Real.log e) :=
    mul_le_mul_of_nonneg_right hpν hc0
  apply hm.trans
  have heq : -((p : ℝ) * -Real.log 2 + (p : ℝ) * (2 * Real.log e) +
      ∑ j : Fin p, Real.log (1 - s j)) / ν ^ 2 =
      -(∑ j : Fin p, Real.log (1 - s j)) / ν ^ 2 +
        (p : ℝ) * (Real.log 2 - 2 * Real.log e) / ν ^ 2 := by
    field_simp [hν.ne']; ring
  rw [heq]
  have hfin : (p : ℝ) * (Real.log 2 - 2 * Real.log e) / ν ^ 2 ≤
      (Real.log 2 - 2 * Real.log e) / ν := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hpk (show 0 ≤ ν by positivity)]
  linarith

/-! ### The finite value, regularized -/

theorem pin_finite_correction_le {N : ℕ} (hN : 0 < N) {k : ℝ} (hk : k = 1 ∨ k = 2)
    {p : ℕ} (hpn : p ≤ n N) (x : Fin p → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    (∑ i : Fin p, ((k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2))) / (n N : ℝ) ≤
      2 * Real.log 2 / (n N : ℝ) := by
  have hn : 0 < (n N : ℝ) := Nat.cast_pos.mpr (show 0 < n N by unfold n; omega)
  have hpν : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hpn
  have hk0 : 0 ≤ k + 2 := by rcases hk with rfl | rfl <;> norm_num
  have hk4 : k + 2 ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  have hc0 : 0 ≤ (k + 2) / (2 * (n N : ℝ)) := div_nonneg hk0 (by positivity)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hterm (i : Fin p) :
      (k + 2) / (2 * (n N : ℝ)) * Real.log (1 + x i ^ 2) ≤
        (k + 2) / (2 * (n N : ℝ)) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (energy_log_one_add_sq_bounds (hx i)).2 hc0
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hb : (p : ℝ) * ((k + 2) / (2 * (n N : ℝ)) * Real.log 2) ≤ 2 * Real.log 2 := by
    have h1 : (p : ℝ) * ((k + 2) / (2 * (n N : ℝ))) ≤ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    calc (p : ℝ) * ((k + 2) / (2 * (n N : ℝ)) * Real.log 2) =
        ((p : ℝ) * ((k + 2) / (2 * (n N : ℝ)))) * Real.log 2 := by ring
      _ ≤ 2 * Real.log 2 := mul_le_mul_of_nonneg_right h1 hlog2
  exact div_le_div_of_nonneg_right (hsum.trans hb) hn.le

def pinRegularizationError (ν k e : ℝ) : ℝ :=
  2 * Real.log 2 / ν +
    k * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * ν) +
    (Real.log 2 - Real.log e) / (2 * ν) +
    (Real.log 2 - 2 * Real.log e) / ν +
    (2 * k + 12) * e

theorem pinFiniteValue_le_regularized {N : ℕ} (hN : 0 < N)
    {k e : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {p : ℕ} (hpn : p ≤ n N)
    {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    pinFiniteValue N k x s ≤
      ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
        Real.log 2 +
      (∑ i : Fin p, (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ j : Fin p, (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      pinDampedInteraction (n N : ℝ) k e x s + pinRegularizationError (n N : ℝ) k e := by
  have hnpos : (0 : ℝ) < n N := Nat.cast_pos.mpr (show 0 < n N by unfold n; omega)
  have hn : (n N : ℝ) ≠ 0 := hnpos.ne'
  have hpν : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hpn
  have hk0 : 0 ≤ k := by
    rcases hk with rfl | rfl <;> norm_num
  have hcorrection := pin_finite_correction_le hN hk hpn x hx
  have hinteraction := pinOffDiagonalInteraction_le_damped hnpos hk0 he hx hs hxi hsi
  have htau := pin_tau_diagonal_sum hnpos he hk0 hpν hx
  have hpower := pin_power_diagonal_sum hnpos he hpν hx
  have hsigma := pin_sigma_diagonal_sum hnpos he hpν hs
  have hchoose : ((p.choose 2 : ℕ) : ℝ) ≤ (n N : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hpν, hnpos, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hsq : (p : ℝ) ^ 2 ≤ (n N : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg p) hpν 2
  have he0 : 0 ≤ e := he.1.le
  have hpair : (4 * k + 12) * e * ((p.choose 2 : ℕ) : ℝ) / (n N : ℝ) ^ 2 +
      6 * e * (p : ℝ) ^ 2 / (n N : ℝ) ^ 2 ≤ (2 * k + 12) * e := by
    have h1 := mul_le_mul_of_nonneg_left hchoose (show 0 ≤ (4 * k + 12) * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * e by positivity)
    rw [← add_div, div_le_iff₀ (by positivity)]
    nlinarith only [h1, h2]
  simp only [mul_pow] at hinteraction
  simp only [neg_mul] at htau
  simp only [neg_div] at hpower hsigma
  have hsplit : pinFiniteValue N k x s =
      ((Cdegree N : ℝ) / (n N : ℝ) + (k - 2) / 2 - (k + 1) / (2 * (n N : ℝ))) *
        Real.log 2 +
      (∑ i : Fin p, realEnergyField k (x i)) / (n N : ℝ) +
      (∑ j : Fin p, realEnergyColumnField (s j)) / (n N : ℝ) +
      (∑ i : Fin p, ((k + 2) / (2 * (n N : ℝ)) *
        Real.log (1 + x i ^ 2))) / (n N : ℝ) +
      pinOffDiagonalInteraction (n N : ℝ) k x s := by
    unfold pinFiniteValue pinOffDiagonalInteraction
    rw [Finset.sum_add_distrib]
    ring
  have hrow :
      (∑ i : Fin p, (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) =
      (∑ i : Fin p, realEnergyField k (x i)) / (n N : ℝ) -
        (∑ i : Fin p, Real.log (1 - x i)) / (2 * (n N : ℝ) ^ 2) := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp [hn]
  have hcolumn :
      (∑ j : Fin p, (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) =
      (∑ j : Fin p, realEnergyColumnField (s j)) / (n N : ℝ) -
        (∑ j : Fin p, Real.log (1 - s j)) / (n N : ℝ) ^ 2 := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    field_simp [hn]
  rw [hsplit, hrow, hcolumn]
  unfold pinRegularizationError
  linarith only [hcorrection, hinteraction, htau, hpower, hsigma, hpair]

/-! ### Trial fields -/

theorem pin_caseField_correction {N : ℕ} (hN : 0 < N) {p : ℕ} (_hpn : p ≤ n N)
    (x : Fin p → ℝ)
    (hcase : ((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
      ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ lam * ((∑ i : Fin p, realEnergyCaseField (x i)) / (n N : ℝ)) +
      lam * (1 + ((n N : ℝ) - p) / 6) / (n N : ℝ) := by
  have hn : 1 ≤ n N := by unfold n; omega
  have hg : 2 * g N ≤ n N - 1 := by unfold n g; omega
  have hnpos : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by omega)
  have hc : ((n N - 1 - 2 * g N : ℕ) : ℝ) = (5 / 6 : ℝ) * (n N : ℝ) - 1 := by
    rw [Nat.cast_sub hg, Nat.cast_sub hn, Nat.cast_one]
    simp only [n, g, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hsum : (∑ i : Fin p, realEnergyCaseField (x i)) =
      (∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2)) - (5 / 6 : ℝ) * p := by
    simp_rw [realEnergyCaseField_eq]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  have hlow : -(1 + ((n N : ℝ) - p) / 6) < ∑ i : Fin p, realEnergyCaseField (x i) := by
    rw [hsum]; rw [hc] at hcase; linarith
  have hd : -(1 + ((n N : ℝ) - p) / 6) / (n N : ℝ) <
      (∑ i : Fin p, realEnergyCaseField (x i)) / (n N : ℝ) :=
    div_lt_div_of_pos_right hlow hnpos
  have hm := mul_le_mul_of_nonneg_left hd.le hlam
  have heq : lam * (-(1 + ((n N : ℝ) - p) / 6) / (n N : ℝ)) =
      -(lam * (1 + ((n N : ℝ) - p) / 6) / (n N : ℝ)) := by ring
  rw [heq] at hm
  linarith

theorem pinFiniteValue_le_trialFields {N : ℕ} (hN : 0 < N)
    {k e lam : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) {p : ℕ} (hpn : p ≤ n N) {x s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
      ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2)))
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    pinFiniteValue N k x s ≤
      (-(11 / 16 : ℝ) - (k + 1) / (2 * (n N : ℝ))) * Real.log 2 +
      (k / 2 + 1) * (1 - ((p : ℝ) / (n N : ℝ)) ^ 2) * Real.log 2 +
      k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (∑ i : Fin p, (realEnergyRowTrialField k lam pp v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ j : Fin p, (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      pinRegularizationError (n N : ℝ) k e +
      2 * k * e * (∑' j : ℕ, |pp j|) + 4 * e * (∑' j : ℕ, |v j|) +
      lam * (1 + ((n N : ℝ) - p) / 6) / (n N : ℝ) := by
  have hnpos : (0 : ℝ) < n N := Nat.cast_pos.mpr (show 0 < n N by unfold n; omega)
  have hpν : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hpn
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hfinite := pinFiniteValue_le_regularized hN hk he hpn hx hs hxi hsi
  have hdual := pinDampedInteraction_le_canonicalTrials hnpos hk0 he hpν hx hs pp v hp hv
  have hcaseAdd : 0 ≤ lam * ((∑ i : Fin p, realEnergyCaseField (x i)) / (n N : ℝ)) +
      lam * (1 + ((n N : ℝ) - p) / 6) / (n N : ℝ) := by
    rcases hcase with hlam0 | hfail
    · simp [hlam0]
    · exact pin_caseField_correction hN hpn x hfail lam hlam
  have hrow :
      (∑ i : Fin p, (realEnergyRowTrialField k lam pp v (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) =
      (∑ i : Fin p, (realEnergyField k (x i) -
        Real.log (1 - x i) / (2 * (n N : ℝ)))) / (n N : ℝ) +
      (∑ i : Fin p, (-2 * k * barrierTrialT pp (x i) - barrierTrialS v (x i))) / (n N : ℝ) +
      lam * ((∑ i : Fin p, realEnergyCaseField (x i)) / (n N : ℝ)) := by
    unfold realEnergyRowTrialField
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hcolumn :
      (∑ j : Fin p, (realEnergyColumnTrialField v (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) =
      (∑ j : Fin p, (realEnergyColumnField (s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      (∑ j : Fin p, 2 * barrierTrialT v (s j)) / (n N : ℝ) := by
    unfold realEnergyColumnTrialField
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hconstant := congrArg (fun z : ℝ => z * Real.log 2) (energy_constant_after_squares hN k)
  norm_num only at hconstant
  rw [hrow, hcolumn]
  simp only [div_eq_mul_inv, mul_inv_rev] at hfinite hdual hcaseAdd hconstant ⊢
  nlinarith only [hfinite, hdual, hcaseAdd, hconstant]

/-! ### The uniform dual bound -/

def pinDualFiniteCoefficient (k e lam : ℝ) (pp v : ℕ → ℝ) (Bx Bs : ℝ) : ℝ :=
  2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
    (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e) + lam +
    6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx| +
    12 * |2 * (∑' j : ℕ, |v j|) - Bs|

/-- The cost, per unit of `(n N - p) / n N`, of the missing pairs. -/
def pinMissingCoefficient (k lam Bx Bs : ℝ) : ℝ :=
  (k + 2) * Real.log 2 + |Bx| + |Bs| + lam / 6

theorem pin_average_bound {ν : ℝ} (hν : 0 < ν) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    (f : Fin p → ℝ) {B R : ℝ} (hf : ∀ i, f i ≤ B + R / ν) :
    (∑ i, f i) / ν ≤ B + (ν - p) / ν * |B| + |R| / ν := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hf i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hr0 : 0 ≤ (ν - p) / ν := div_nonneg (by linarith) hν.le
  have hratio : (p : ℝ) / ν = 1 - (ν - p) / ν := by field_simp; ring
  have hpr : (p : ℝ) / ν ≤ 1 := (div_le_one hν).mpr hpν
  have hpr0 : 0 ≤ (p : ℝ) / ν := div_nonneg hp0 hν.le
  have h1 : (∑ i, f i) / ν ≤ (p : ℝ) / ν * B + (p : ℝ) / ν * (R / ν) := by
    rw [div_le_iff₀ hν]
    calc (∑ i, f i) ≤ (p : ℝ) * (B + R / ν) := hsum
      _ = ((p : ℝ) / ν * B + (p : ℝ) / ν * (R / ν)) * ν := by field_simp
  have h2 : (p : ℝ) / ν * B ≤ B + (ν - p) / ν * |B| := by
    rw [hratio]
    have := mul_le_mul_of_nonneg_left (neg_le_abs B) hr0
    nlinarith
  have h3 : (p : ℝ) / ν * (R / ν) ≤ |R| / ν := by
    have hR : R / ν ≤ |R| / ν := div_le_div_of_nonneg_right (le_abs_self R) hν.le
    have hR0 : 0 ≤ |R| / ν := div_nonneg (abs_nonneg R) hν.le
    calc (p : ℝ) / ν * (R / ν) ≤ (p : ℝ) / ν * (|R| / ν) :=
          mul_le_mul_of_nonneg_left hR hpr0
      _ ≤ 1 * (|R| / ν) := mul_le_mul_of_nonneg_right hpr hR0
      _ = |R| / ν := one_mul _
  linarith

theorem pinFiniteValue_le_uniformDual {N : ℕ} (hN : 0 < N)
    {k e lam Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) {p : ℕ} (hpn : p ≤ n N) {x s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
      ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2)))
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam pp v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs) :
    pinFiniteValue N k x s ≤ realEnergyDualConstant k pp v Bx Bs +
      e * realEnergyDualDampingCoefficient k pp v +
      pinDualFiniteCoefficient k e lam pp v Bx Bs / (n N : ℝ) +
      ((n N : ℝ) - p) / (n N : ℝ) * pinMissingCoefficient k lam Bx Bs := by
  have hnpos : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by unfold n; omega)
  have hpν : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hpn
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  set ν : ℝ := (n N : ℝ) with hνdef
  set r : ℝ := (ν - p) / ν with hrdef
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hnpos.le
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one hnpos]; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hpr : (p : ℝ) / ν = 1 - r := by rw [hrdef]; field_simp; ring
  have hrow := pin_average_bound hnpos hpν
    (fun i => realEnergyRowTrialField k lam pp v (x i) - Real.log (1 - x i) / (2 * ν))
    (B := Bx) (R := 6 * (lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx))
    (fun i => by
      have h := realEnergyRowTrialField_weaken_le hN hk0 hlam
        (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩) pp v hp hv
        (hBx (x i) ⟨(hx i).1.le, (hx i).2⟩ (hx0 i))
      simpa only [hνdef, mul_div_assoc] using h)
  have hcol := pin_average_bound hnpos hpν
    (fun j => realEnergyColumnTrialField v (s j) - Real.log (1 - s j) / ν)
    (B := Bs) (R := 12 * (2 * (∑' j : ℕ, |v j|) - Bs))
    (fun j => by
      have h := realEnergyColumnTrialField_weaken_le hN (hs j) v hv (hBs (s j) (hs j))
      simpa only [hνdef, mul_div_assoc] using h)
  have hfinite := pinFiniteValue_le_trialFields hN hk he hlam hpn hx hs hxi hsi hcase pp v hp hv
  rw [← hνdef] at hfinite
  have hconst : (-(11 / 16 : ℝ) - (k + 1) / (2 * ν)) * Real.log 2 ≤
      -(11 / 16 : ℝ) * Real.log 2 := by
    have hh : 0 ≤ ((k + 1) / (2 * ν)) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    nlinarith only [hh]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : (k / 2 + 1) * (1 - ((p : ℝ) / ν) ^ 2) * Real.log 2 ≤
      r * ((k + 2) * Real.log 2) := by
    rw [hpr]
    have h1 : 1 - (1 - r) ^ 2 ≤ 2 * r := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (k / 2 + 1) * Real.log 2 by positivity)
    nlinarith only [h2]
  have hcase' : lam * (1 + (ν - p) / 6) / ν = lam / ν + r * (lam / 6) := by
    rw [hrdef]; field_simp
  have hreg : pinRegularizationError ν k e =
      (2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
        (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e)) / ν +
      (2 * k + 12) * e := by
    unfold pinRegularizationError; field_simp
  rw [hcase', hreg] at hfinite
  unfold realEnergyDualConstant realEnergyDualDampingCoefficient pinDualFiniteCoefficient
    pinMissingCoefficient
  have hfin2 : (6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx|) / ν +
      (12 * |2 * (∑' j : ℕ, |v j|) - Bs|) / ν =
      (6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx| +
        12 * |2 * (∑' j : ℕ, |v j|) - Bs|) / ν := by ring
  have hR1 : |6 * (lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx)| =
      6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx| := by
    rw [abs_mul]; norm_num
  have hR2 : |12 * (2 * (∑' j : ℕ, |v j|) - Bs)| = 12 * |2 * (∑' j : ℕ, |v j|) - Bs| := by
    rw [abs_mul]; norm_num
  rw [hR1] at hrow
  rw [hR2] at hcol
  have htot : (2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
        (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e) + lam +
        6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx| +
        12 * |2 * (∑' j : ℕ, |v j|) - Bs|) / ν =
      (2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
        (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e)) / ν + lam / ν +
      (6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx|) / ν +
      (12 * |2 * (∑' j : ℕ, |v j|) - Bs|) / ν := by ring
  rw [htot]
  have hdist : r * ((k + 2) * Real.log 2 + |Bx| + |Bs| + lam / 6) =
      r * ((k + 2) * Real.log 2) + r * |Bx| + r * |Bs| + r * (lam / 6) := by ring
  rw [hdist]
  nlinarith only [hfinite, hrow, hcol, hconst, hsq]

theorem pin_uniform_dual_eventually
    {k lam Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (hlam : 0 ≤ lam)
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam pp v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z ≤ Bs)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, p ≤ n N →
      ∀ x s : Fin p → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
        ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2))) →
      pinFiniteValue N k x s ≤ realEnergyDualConstant k pp v Bx Bs + d +
        ((n N : ℝ) - p) / (n N : ℝ) * pinMissingCoefficient k lam Bx Bs := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  let D : ℝ := realEnergyDualDampingCoefficient k pp v
  have hD : 0 ≤ D := realEnergyDualDampingCoefficient_nonneg hk0 pp v
  let e : ℝ := min (1 / 16) (d / (2 * (D + 1)))
  have he0 : 0 < e := by
    apply lt_min (by norm_num)
    exact div_pos hd (by positivity)
  have he8 : e < (1 / 8 : ℝ) := by
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have he : e ∈ Ioo (0 : ℝ) (1 / 8) := ⟨he0, he8⟩
  have heD : e * D < d / 2 := by
    have heSmall : e ≤ d / (2 * (D + 1)) := min_le_right _ _
    have hprod := (le_div_iff₀ (show 0 < 2 * (D + 1) by positivity)).mp heSmall
    nlinarith only [hprod, he0]
  let C : ℝ := pinDualFiniteCoefficient k e lam pp v Bx Bs
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * |C| / d)
  refine ⟨M + 1, ?_⟩
  intro N hNlarge p hpn x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hMN : M ≤ n N := by unfold n; omega
  have hbig : 2 * |C| / d < (n N : ℝ) :=
    hM.trans_le (Nat.cast_le.mpr hMN)
  have hCabs : |C| / (n N : ℝ) < d / 2 := by
    apply (div_lt_iff₀ hn).mpr
    have hprod := (div_lt_iff₀ hd).mp hbig
    nlinarith only [hprod]
  have hC : C / (n N : ℝ) < d / 2 :=
    (div_le_div_of_nonneg_right (le_abs_self C) hn.le).trans_lt hCabs
  have hfinite := pinFiniteValue_le_uniformDual hN hk he hlam hpn hx hs hx0 hxi hsi
    hcase pp v hp hv hBx hBs
  change pinFiniteValue N k x s ≤ realEnergyDualConstant k pp v Bx Bs +
    e * D + C / (n N : ℝ) + ((n N : ℝ) - p) / (n N : ℝ) * pinMissingCoefficient k lam Bx Bs
    at hfinite
  linarith only [hfinite, heD, hC]

end InternalCatalan

end

end OAI
