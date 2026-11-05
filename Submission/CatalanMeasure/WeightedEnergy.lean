module

public import Submission.CatalanMeasure.PinSupDual
public import Submission.CatalanMeasure.AveragedEnergyAlgebra

@[expose] public section

open OAI.InternalCatalan Set Finset Real
open scoped BigOperators

namespace OAI.InternalCatalan

noncomputable def pinWeightedValue (N : ℕ) (k a : ℝ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  pinFiniteValue N k x s + a * (∑ j, Real.log (1 + s j)) / (n N : ℝ)

theorem weighted_column_weaken_le {N : ℕ} (hN : 0 < N) {s B a : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a)
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|))
    (hB : realEnergyColumnTrialField v s + a * Real.log (1 + s) ≤ B) :
    realEnergyColumnTrialField v s + a * Real.log (1 + s) -
      Real.log (1 - s) / (n N : ℝ) ≤
      B + 12 * (2 * (∑' j : ℕ, |v j|) + a * Real.log 2 - B) / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := Nat.cast_pos.mpr (by unfold n; omega)
  have hn12 : (12 : ℝ) ≤ n N := by exact_mod_cast (show 12 ≤ n N by unfold n; omega)
  have hd0 : (0 : ℝ) ≤ 12 / (n N : ℝ) := by positivity
  have hd1 : (12 : ℝ) / (n N : ℝ) ≤ 1 := (div_le_iff₀ hn).mpr (by simpa using hn12)
  have hr := realEnergyColumnTrialField_residual_le hs v hv
  have hl : Real.log (1 + s) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [hs.1]) (by linarith [hs.2])
  have hm := mul_le_mul_of_nonneg_left hl ha
  have hres : realEnergyColumnTrialField v s + a * Real.log (1 + s) -
      Real.log (1 - s) / 12 ≤ 2 * (∑' j : ℕ, |v j|) + a * Real.log 2 := by
    linarith
  convert energy_endpoint_convex_bound hd0 hd1 hB hres using 1 <;> ring

theorem pin_average_bound_mass {ν : ℝ} (hν : 0 < ν) {p : ℕ} (hpν : (p : ℝ) ≤ ν)
    (f : Fin p → ℝ) {B R : ℝ} (hf : ∀ i, f i ≤ B + R / ν) :
    (∑ i, f i) / ν ≤ (p : ℝ) / ν * B + |R| / ν := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hf i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hratio : (p : ℝ) / ν ≤ 1 := (div_le_one hν).mpr hpν
  have hratio0 : (0 : ℝ) ≤ (p : ℝ) / ν := div_nonneg hp0 hν.le
  have hr : (p : ℝ) / ν * (R / ν) ≤ |R| / ν := by
    calc
      (p : ℝ) / ν * (R / ν) ≤ (p : ℝ) / ν * (|R| / ν) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self R) hν.le) hratio0
      _ ≤ 1 * (|R| / ν) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = |R| / ν := one_mul _
  have hs : (∑ i, f i) / ν ≤ (p : ℝ) / ν * B + (p : ℝ) / ν * (R / ν) := by
    rw [div_le_iff₀ hν]
    calc (∑ i, f i) ≤ (p : ℝ) * (B + R / ν) := hsum
      _ = ((p : ℝ) / ν * B + (p : ℝ) / ν * (R / ν)) * ν := by field_simp <;> ring
  linarith

noncomputable def pinWeightedFiniteCoefficient (k e lam a : ℝ) (pp v : ℕ → ℝ) (Bx Bs : ℝ) : ℝ :=
  2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
    (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e) + lam +
    6 * |lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx| +
    12 * |2 * (∑' j : ℕ, |v j|) + a * Real.log 2 - Bs|

theorem pinWeightedValue_le_finiteDual {N : ℕ} (hN : 0 < N)
    {k e lam a Bx Bs : ℝ} (hk : k = 1 ∨ k = 2) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hlam : 0 ≤ lam) (ha : 0 ≤ a) {p : ℕ} (hpn : p ≤ n N) {x s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hcase : lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
      ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2)))
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam pp v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z + a * Real.log (1 + z) ≤ Bs) :
    pinWeightedValue N k a x s ≤
      -(11 / 16 : ℝ) * Real.log 2 + k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (p : ℝ) / (n N : ℝ) * (Bx + Bs) +
      (k / 2 + 1) * (1 - ((p : ℝ) / (n N : ℝ)) ^ 2) * Real.log 2 +
      lam * ((n N : ℝ) - p) / (6 * (n N : ℝ)) +
      e * realEnergyDualDampingCoefficient k pp v +
      pinWeightedFiniteCoefficient k e lam a pp v Bx Bs / (n N : ℝ) := by
  have hn : (0 : ℝ) < n N := Nat.cast_pos.mpr (by unfold n; omega)
  have hpν : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hpn
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hrow := pin_average_bound_mass hn hpν
    (fun i => realEnergyRowTrialField k lam pp v (x i) - Real.log (1 - x i) / (2 * (n N : ℝ)))
    (B := Bx) (R := 6 * (lam / 6 + 2 * k * (∑' j : ℕ, |pp j|) + (∑' j : ℕ, |v j|) - Bx))
    (fun i => by
      simpa only [mul_div_assoc] using realEnergyRowTrialField_weaken_le hN hk0 hlam
        (abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩) pp v hp hv
        (hBx (x i) ⟨(hx i).1.le, (hx i).2⟩ (hx0 i)))
  have hcol := pin_average_bound_mass hn hpν
    (fun j => realEnergyColumnTrialField v (s j) + a * Real.log (1 + s j) -
      Real.log (1 - s j) / (n N : ℝ))
    (B := Bs) (R := 12 * (2 * (∑' j : ℕ, |v j|) + a * Real.log 2 - Bs))
    (fun j => by simpa only [mul_div_assoc] using
      weighted_column_weaken_le hN (hs j) ha v hv (hBs (s j) (hs j)))
  have hfinite := pinFiniteValue_le_trialFields hN hk he hlam hpn hx hs hxi hsi hcase pp v hp hv
  have hconstant : (-(11 / 16 : ℝ) - (k + 1) / (2 * (n N : ℝ))) * Real.log 2 ≤
      -(11 / 16 : ℝ) * Real.log 2 := by
    have hnonneg : 0 ≤ (k + 1) / (2 * (n N : ℝ)) * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    nlinarith only [hnonneg]
  have hcol_eq : (∑ j : Fin p, (realEnergyColumnTrialField v (s j) -
      Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) +
      a * (∑ j, Real.log (1 + s j)) / (n N : ℝ) =
      (∑ j, (realEnergyColumnTrialField v (s j) + a * Real.log (1 + s j) -
        Real.log (1 - s j) / (n N : ℝ))) / (n N : ℝ) := by
    simp only [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hreg : pinRegularizationError (n N : ℝ) k e =
      (2 * Real.log 2 + k / 2 * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) +
        (Real.log 2 - Real.log e) / 2 + (Real.log 2 - 2 * Real.log e)) / (n N : ℝ) +
      (2 * k + 12) * e := by unfold pinRegularizationError; field_simp <;> ring
  have hcase_eq : lam * (1 + ((n N : ℝ) - p) / 6) / (n N : ℝ) =
      lam / (n N : ℝ) + lam * ((n N : ℝ) - p) / (6 * (n N : ℝ)) := by field_simp <;> ring
  rw [hreg, hcase_eq] at hfinite
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num),
    abs_of_nonneg (show (0 : ℝ) ≤ 12 by norm_num)] at hrow hcol
  unfold pinWeightedValue pinWeightedFiniteCoefficient realEnergyDualDampingCoefficient
  rw [show (p : ℝ) / (n N : ℝ) * (Bx + Bs) =
      (p : ℝ) / (n N : ℝ) * Bx + (p : ℝ) / (n N : ℝ) * Bs by ring]
  simp only [div_eq_mul_inv, mul_inv_rev] at hfinite hrow hcol hconstant hcol_eq ⊢
  norm_num only [invOf_eq_inv] at hfinite hrow hcol hconstant hcol_eq ⊢
  nlinarith only [hfinite, hrow, hcol, hconstant, hcol_eq]

/-- A fixed weighted endpoint, retaining its mass rather than linearizing it. -/
theorem pin_weighted_dual_eventually
    {k lam a Bx Bs Kn : ℝ} (hk : k = 1 ∨ k = 2) (hlam : 0 ≤ lam) (ha : 0 ≤ a)
    (pp v : ℕ → ℝ) (hp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|))
    (hBx : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField k lam pp v z ≤ Bx)
    (hBs : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v z + a * Real.log (1 + z) ≤ Bs)
    (hKn : k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 ≤ Kn)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, p ≤ n N →
      ∀ x s : Fin p → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (lam = 0 ∨ (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
        ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2))) →
      pinWeightedValue N k a x s ≤
        -(11 / 16 : ℝ) * Real.log 2 + Kn + (p : ℝ) / (n N : ℝ) * (Bx + Bs) +
        (k / 2 + 1) * (1 - ((p : ℝ) / (n N : ℝ)) ^ 2) * Real.log 2 +
        lam * ((n N : ℝ) - p) / (6 * (n N : ℝ)) + d := by
  have hk0 : 0 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  let D : ℝ := realEnergyDualDampingCoefficient k pp v
  have hD : 0 ≤ D := realEnergyDualDampingCoefficient_nonneg hk0 pp v
  let e : ℝ := min (1 / 16) (d / (2 * (D + 1)))
  have he0 : 0 < e := lt_min (by norm_num) (div_pos hd (by positivity))
  have he8 : e < (1 / 8 : ℝ) := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have heD : e * D < d / 2 := by
    have heSmall : e ≤ d / (2 * (D + 1)) := min_le_right _ _
    have hprod := (le_div_iff₀ (show 0 < 2 * (D + 1) by positivity)).mp heSmall
    nlinarith only [hprod, he0]
  let C : ℝ := pinWeightedFiniteCoefficient k e lam a pp v Bx Bs
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * |C| / d)
  refine ⟨M + 1, ?_⟩
  intro N hNlarge p hpn x s hx hs hx0 hxi hsi hcase
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := Nat.cast_pos.mpr (by unfold n; omega)
  have hMN : M ≤ n N := by unfold n; omega
  have hbig : 2 * |C| / d < (n N : ℝ) := hM.trans_le (Nat.cast_le.mpr hMN)
  have hCabs : |C| / (n N : ℝ) < d / 2 := by
    apply (div_lt_iff₀ hn).mpr
    have hprod := (div_lt_iff₀ hd).mp hbig
    nlinarith only [hprod]
  have hC : C / (n N : ℝ) < d / 2 :=
    (div_le_div_of_nonneg_right (le_abs_self C) hn.le).trans_lt hCabs
  have hf := pinWeightedValue_le_finiteDual hN hk ⟨he0, he8⟩ hlam ha hpn
    hx hs hx0 hxi hsi hcase pp v hp hv hBx hBs
  change pinWeightedValue N k a x s ≤
      -(11 / 16 : ℝ) * Real.log 2 + k * barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (p : ℝ) / (n N : ℝ) * (Bx + Bs) +
      (k / 2 + 1) * (1 - ((p : ℝ) / (n N : ℝ)) ^ 2) * Real.log 2 +
      lam * ((n N : ℝ) - p) / (6 * (n N : ℝ)) + e * D + C / (n N : ℝ) at hf
  linarith only [hf, hKn, heD, hC]

/-- Combining the two fixed endpoint inequalities introduces no trial-family errors. -/
theorem weighted_endpoint_mixture {N p : ℕ} {k t E₀ E₁ : ℝ} {x s : Fin p → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h₀ : pinWeightedValue N k 0 x s ≤ E₀)
    (h₁ : pinWeightedValue N k 1 x s ≤ E₁) :
    pinWeightedValue N k t x s ≤ (1 - t) * E₀ + t * E₁ := by
  have h0 := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht1)
  have h1 := mul_le_mul_of_nonneg_left h₁ ht0
  have h := add_le_add h0 h1
  convert h using 1 <;> unfold pinWeightedValue <;> ring

end OAI.InternalCatalan
