module

public import Submission.CatalanMeasure.GenD.DenomExp
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.SmallOddPrimePartition

@[expose] public section

/-!
# Growth of the denominator, part 1: the 2-adic and small-prime terms (module 4)

For every admissible design:
* `twoAdic_growth`: `twoAdicExp · log 2 ≤ (A2(n0,H1,b0) log 2 + ε) N²` eventually;
* `smallPrime_growth`: the total small-prime contribution `2 √H · 6 n log H` is `≤ ε N²` eventually.
-/

namespace CatalanMeasure.GenD

open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter
open scoped Topology

noncomputable section

theorem twoAdic_arg_nonneg (P : Parameters) (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    0 ≤ TwoAdic.A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ) +
      (P.n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2) := by
  have hnb : P.n N + P.b N ≤ P.H N := by
    simp only [Parameters.H, Parameters.C, Parameters.L]; omega
  have hnbR : (P.n N : ℝ) + P.b N ≤ P.H N := by exact_mod_cast hnb
  have hn0 : (0 : ℝ) ≤ P.n N := Nat.cast_nonneg _
  have hHpos : 0 < P.H N := by
    have h1 : 0 < P.n N := Nat.mul_pos hP.1 hN
    omega
  have hH1 : (1 : ℝ) ≤ P.H N := by exact_mod_cast hHpos
  have hA : 0 ≤ TwoAdic.A2 (P.n N) (P.H N) (P.b N) := by
    unfold TwoAdic.A2
    nlinarith [Nat.cast_nonneg (α := ℝ) (P.b N)]
  have hF := one_le_discrepancyNormFactor 0
  have hl : 0 ≤ Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2) := by
    apply Real.logb_nonneg (by norm_num)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH1 2]
  have := mul_nonneg hn0 hl
  linarith

theorem twoAdic_growth (P : Parameters) (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (twoAdicExp P N : ℝ) * Real.log 2 ≤
      (TwoAdic.A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) * Real.log 2 + ε) * (N : ℝ) ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : (0 : ℝ) < P.n0 := by exact_mod_cast hP.1
  set ε1 : ℝ := ε / (2 * (P.n0 : ℝ) ^ 2 * Real.log 2) with hε1
  have hε1pos : 0 < ε1 := by rw [hε1]; positivity
  have hE : ∀ᶠ N : ℕ in atTop,
      (3 / 2 + Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2)) / (P.n N : ℝ) < ε1 :=
    (tendsto_order.mp (TwoAdic.tendsto_two_adic_log_error P hP.1 0)).2 ε1 hε1pos
  have hbig : ∀ᶠ N : ℕ in atTop, 1 ≤ ε / (2 * Real.log 2) * (N : ℝ) ^ 2 := by
    have hc : 0 < ε / (2 * Real.log 2) := by positivity
    have ht : Tendsto (fun N : ℕ => ε / (2 * Real.log 2) * (N : ℝ) ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop hc ((tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    exact ht.eventually (eventually_ge_atTop 1)
  filter_upwards [hE, hbig, eventually_gt_atTop (0 : ℕ)] with N hEN hbN hN
  have hnN : (0 : ℝ) < P.n N := by exact_mod_cast Nat.mul_pos hP.1 hN
  have hr := twoAdic_arg_nonneg P hP hN
  have hceil := Nat.ceil_lt_add_one hr
  have hA : TwoAdic.A2 (P.n N) (P.H N) (P.b N) =
      TwoAdic.A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) * (N : ℝ) ^ 2 := by
    rw [TwoAdic.cast_n, TwoAdic.cast_H, TwoAdic.cast_b]  -- n N ↦ n0 * N etc.
    exact TwoAdic.A2_scale _ _ _ _
  have hlog : (3 / 2 + Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2)) <
      ε1 * (P.n N : ℝ) := (div_lt_iff₀ hnN).mp hEN
  have hnn : (P.n N : ℝ) = (P.n0 : ℝ) * N := TwoAdic.cast_n P N
  have hmain : (twoAdicExp P N : ℝ) ≤
      TwoAdic.A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) * (N : ℝ) ^ 2 +
        ε1 * (P.n0 : ℝ) ^ 2 * (N : ℝ) ^ 2 + 1 := by
    have h1 : (twoAdicExp P N : ℝ) <
        TwoAdic.A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ) +
          (P.n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2) + 1 := hceil
    have h2 : (3 / 2) * (P.n N : ℝ) +
          (P.n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2) =
        ((P.n0 : ℝ) * N) * (3 / 2 + Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2)) := by
      rw [hnn]; ring
    have h3 := mul_lt_mul_of_pos_left hlog hnN
    rw [hnn] at h3
    nlinarith only [h1, h2, h3, hA]
  have hε1' : ε1 * (P.n0 : ℝ) ^ 2 * Real.log 2 = ε / 2 := by
    rw [hε1]; field_simp
  have hb : (1 : ℝ) * Real.log 2 ≤ ε / 2 * (N : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hbN hl2.le
    have e : ε / (2 * Real.log 2) * (N : ℝ) ^ 2 * Real.log 2 = ε / 2 * (N : ℝ) ^ 2 := by
      field_simp
    nlinarith only [this, e]
  have := mul_le_mul_of_nonneg_right hmain hl2.le
  nlinarith only [this, hε1', hb]

/-- The small-prime contribution is `o(N²)`. -/
theorem smallPrime_growth (P : Parameters) (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.sqrt (P.H N) * (6 * (P.n N : ℝ) * Real.log (P.H N)) ≤
      ε * (N : ℝ) ^ 2 := by
  have hH1 : (0 : ℝ) < P.H 1 := by
    have : 0 < P.H 1 := by
      simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n]
      have := hP.1
      omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < P.n0 := by exact_mod_cast hP.1
  have hi : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := ((hi.const_mul (Real.log (P.H 1 : ℝ))).add log_nat_div_sqrt_tendsto_zero).const_mul
    (12 * (P.n0 : ℝ) * Real.sqrt (P.H 1 : ℝ))
  simp only [mul_zero, add_zero] at h
  have hev := (tendsto_order.mp h).2 ε hε
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hHN : (P.H N : ℝ) = (P.H 1 : ℝ) * N := TwoAdic.cast_H P N
  have hnN : (P.n N : ℝ) = (P.n0 : ℝ) * N := TwoAdic.cast_n P N
  have hlogH : Real.log (P.H N : ℝ) = Real.log (P.H 1 : ℝ) + Real.log (N : ℝ) := by
    rw [hHN, Real.log_mul hH1.ne' hNr.ne']
  have hsqrtH : Real.sqrt (P.H N : ℝ) = Real.sqrt (P.H 1 : ℝ) * Real.sqrt (N : ℝ) := by
    rw [hHN, Real.sqrt_mul hH1.le]
  have hNN : (N : ℝ) = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := (Real.mul_self_sqrt hNr.le).symm
  have heq : 2 * Real.sqrt (P.H N) * (6 * (P.n N : ℝ) * Real.log (P.H N)) =
      (12 * (P.n0 : ℝ) * Real.sqrt (P.H 1 : ℝ) *
        (Real.log (P.H 1 : ℝ) * (Real.sqrt (N : ℝ))⁻¹ + Real.log (N : ℝ) / Real.sqrt (N : ℝ))) *
          (N : ℝ) ^ 2 := by
    rw [hsqrtH, hnN, hlogH]
    field_simp
    rw [Real.sq_sqrt hNr.le]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (le_of_lt hN) (sq_nonneg _)

end

end CatalanMeasure.GenD
