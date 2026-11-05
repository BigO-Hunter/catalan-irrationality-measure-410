module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Data.Nat.Factorization.Basic
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.FinitePlaceAssembly

@[expose] public section

/-!
# A common denominator for the values of `Δ_N` at integers  (Proposition 3)

OpenAI's local estimates bound `v_ℓ(Δ_N(z))` from below for rational `z`, and at an integer
`z` (where `z.den = 1`) these bounds do not depend on `z`:

* `ℓ = 2`: `v₂ ≥ -(505/4608) n² - 2n - n log₂(8 F(z) H²)` and `F(z) ≤ F(0)` for integers;
* `ℓ` odd, `ℓ ≤ 2√H`: `v_ℓ ≥ -6 n ⌊log_ℓ H⌋`;
* `ℓ` odd, `ℓ > 2√H`: `v_ℓ ≥ -N · oddPrimeLoss(ℓ / N)`, which is `0` once `ℓ ≥ H`.

So `denomBound N = ∏_{ℓ ≤ H} ℓ ^ (denomExp N ℓ)` clears the denominator of `Δ_N(i)` for
every natural number `i` (`exists_int_denomBound_mul`), and summing OpenAI's estimates gives
`log (denomBound N) ≤ (8609/4608 + (505/4608) log 2 + ε) n²` for large `N`
(`log_denomBound_eventually_le`).  This is the constant `A` of the write-up.
-/

open Filter Real
open scoped Topology BigOperators

namespace OAI.InternalCatalan

/-- The primes up to `H N`. -/
def measurePrimes (N : ℕ) : Finset ℕ := (Finset.Ioc 0 (H N)).filter Nat.Prime

/-- The real 2-adic loss bound at integer points. -/
noncomputable def twoAdicBound (N : ℕ) : ℝ :=
  (505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ) +
    (n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (H N : ℝ) ^ 2)

/-- The exponent of `ℓ` in the common denominator. -/
noncomputable def denomExp (N ℓ : ℕ) : ℕ :=
  if ℓ = 2 then ⌈twoAdicBound N⌉₊
  else if (ℓ : ℝ) ≤ 2 * Real.sqrt (H N) then 6 * n N * Nat.log ℓ (H N)
  else ⌈(N : ℝ) * oddPrimeLoss ((ℓ : ℝ) / N)⌉₊

/-- The common denominator `D_N`. -/
noncomputable def denomBound (N : ℕ) : ℕ := ∏ ℓ ∈ measurePrimes N, ℓ ^ denomExp N ℓ

theorem denomBound_ne_zero (N : ℕ) : denomBound N ≠ 0 := by
  unfold denomBound
  rw [Finset.prod_ne_zero_iff]
  intro ℓ hℓ
  exact pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero

theorem discrepancyNormFactor_natCast_le (i : ℕ) :
    discrepancyNormFactor (i : ℚ) ≤ discrepancyNormFactor 0 := by
  unfold discrepancyNormFactor
  have hi : ‖(4 * ((i : ℚ) : ℚ_[2]) : ℚ_[2])‖ ≤ 1 := by
    have h4 : (4 * ((i : ℚ) : ℚ_[2]) : ℚ_[2]) = (((4 * i : ℕ) : ℤ) : ℚ_[2]) := by
      push_cast
      try ring
    rw [h4]
    exact Padic.norm_int_le_one _
  have hsub : ‖4 * ((i : ℚ) : ℚ_[2]) - smoothingMoment 0 0‖ ≤ max 1 ‖smoothingMoment 0 0‖ := by
    calc ‖4 * ((i : ℚ) : ℚ_[2]) - smoothingMoment 0 0‖
        ≤ max ‖4 * ((i : ℚ) : ℚ_[2])‖ ‖smoothingMoment 0 0‖ := by
          rw [sub_eq_add_neg, ← norm_neg (smoothingMoment 0 0)]
          exact Padic.nonarchimedean _ _
      _ ≤ max 1 ‖smoothingMoment 0 0‖ := max_le_max hi le_rfl
  have h0 : ‖4 * (((0 : ℚ)) : ℚ_[2]) - smoothingMoment 0 0‖ = ‖smoothingMoment 0 0‖ := by
    simp
  rw [h0]
  apply max_le (le_max_left _ _)
  apply max_le
  · exact hsub.trans (max_le_max le_rfl (le_max_left _ _))
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- A valuation lower bound `-e ≤ v_ℓ(x)` bounds the `ℓ`-part of the denominator of `x`. -/
theorem padicValNat_den_le_of_padicValRat {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {x : ℚ} {e : ℕ}
    (h : -(e : ℤ) ≤ padicValRat ℓ x) : padicValNat ℓ x.den ≤ e := by
  by_cases hd : ℓ ∣ x.den
  · have hnum : ¬ (ℓ : ℤ) ∣ x.num := by
      intro hn
      have h1 : ℓ ∣ x.num.natAbs := Int.ofNat_dvd_left.mp hn
      have h2 : ℓ ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd h1 hd
      rw [Nat.Coprime.gcd_eq_one x.reduced] at h2
      exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp h2)
    unfold padicValRat at h
    rw [padicValInt.eq_zero_of_not_dvd hnum] at h
    omega
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

theorem natCast_den_one (i : ℕ) : (i : ℚ).den = 1 := by simp

theorem natCast_den_zmod_ne_zero (i : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (((i : ℚ).den : ℕ) : ZMod ℓ) ≠ 0 := by
  rw [natCast_den_one, Nat.cast_one]
  exact one_ne_zero

theorem twoAdicBound_nonneg {N : ℕ} (hN : 0 < N) : 0 ≤ twoAdicBound N := by
  unfold twoAdicBound
  have hF := one_le_discrepancyNormFactor 0
  have hH : (1 : ℝ) ≤ (H N : ℝ) := by exact_mod_cast (show 1 ≤ H N by unfold H; omega)
  have harg : (1 : ℝ) ≤ 8 * discrepancyNormFactor 0 * (H N : ℝ) ^ 2 := by nlinarith
  have hlog := Real.logb_nonneg (b := 2) (by norm_num) harg
  positivity

/-- The local estimates at an integer point, in the form `-(denomExp N ℓ) ≤ v_ℓ(Δ_N(i))`. -/
theorem padicValRat_determinantRat_natCast_lower {N : ℕ} (hN : 0 < N) (i : ℕ)
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hd : determinantRat (i : ℚ) N ≠ 0) :
    -(denomExp N ℓ : ℤ) ≤ padicValRat ℓ (determinantRat (i : ℚ) N) := by
  unfold denomExp
  split_ifs with h2 hsmall
  · subst h2
    have hv := determinantRat_two_adic_valuation_lower (i : ℚ) hN hd
    have hF := discrepancyNormFactor_natCast_le i
    have hFi := one_le_discrepancyNormFactor (i : ℚ)
    have hH : (0 : ℝ) < (H N : ℝ) := by exact_mod_cast (show 0 < H N by unfold H; omega)
    have hH2 : (0 : ℝ) < (H N : ℝ) ^ 2 := pow_pos hH 2
    have hlog : Real.logb 2 (8 * discrepancyNormFactor (i : ℚ) * (H N : ℝ) ^ 2) ≤
        Real.logb 2 (8 * discrepancyNormFactor 0 * (H N : ℝ) ^ 2) := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · exact mul_pos (mul_pos (by norm_num) (by linarith)) hH2
      · exact mul_le_mul_of_nonneg_right (by linarith) hH2.le
    have hceil := Nat.le_ceil (twoAdicBound N)
    have hn : (0 : ℝ) ≤ n N := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hn
    have hTB : twoAdicBound N = (505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ) +
        (n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (H N : ℝ) ^ 2) := rfl
    have hreal : -(⌈twoAdicBound N⌉₊ : ℝ) ≤ (padicValRat 2 (determinantRat (i : ℚ) N) : ℝ) := by
      linarith
    exact_mod_cast hreal
  · have hv := determinantRat_odd_prime_log_lower h2 (i : ℚ) N
    rw [natCast_den_one, padicValNat.one] at hv
    push_cast at hv ⊢
    linarith
  · have hcut : 2 * Real.sqrt (H N) < (ℓ : ℝ) := not_le.mp hsmall
    have hv := determinantRat_odd_prime_large_loss_lower h2 hN hcut (i : ℚ)
      (natCast_den_zmod_ne_zero i ℓ)
    have hceil := Nat.le_ceil ((N : ℝ) * oddPrimeLoss ((ℓ : ℝ) / N))
    have hreal : -(⌈(N : ℝ) * oddPrimeLoss ((ℓ : ℝ) / N)⌉₊ : ℝ) ≤
        (padicValRat ℓ (determinantRat (i : ℚ) N) : ℝ) := by
      have heq : -(N : ℝ) * oddPrimeLoss ((ℓ : ℝ) / N) =
          -((N : ℝ) * oddPrimeLoss ((ℓ : ℝ) / N)) := by ring
      linarith
    exact_mod_cast hreal

theorem den_dvd_denomBound {N : ℕ} (hN : 0 < N) (i : ℕ)
    (hd : determinantRat (i : ℚ) N ≠ 0) :
    (determinantRat (i : ℚ) N).den ∣ denomBound N := by
  have hM := denomBound_ne_zero N
  rw [← Nat.factorization_le_iff_dvd (Rat.den_pos _).ne' hM, Finsupp.le_def]
  intro ℓ
  by_cases hp : ℓ.Prime
  · haveI : Fact ℓ.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp]
    by_cases hS : ℓ ∈ measurePrimes N
    · have h1 := padicValNat_den_le_of_padicValRat
        (padicValRat_determinantRat_natCast_lower hN i (ℓ := ℓ) hd)
      have h2 : denomExp N ℓ ≤ (denomBound N).factorization ℓ := by
        apply (hp.pow_dvd_iff_le_factorization hM).mp
        unfold denomBound
        exact Finset.dvd_prod_of_mem (fun ℓ => ℓ ^ denomExp N ℓ) hS
      exact h1.trans h2
    · have hH : H N < ℓ := by
        by_contra hle
        push Not at hle
        exact hS (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, hle⟩, hp⟩)
      have h2 : ℓ ≠ 2 := by
        unfold H at hH
        omega
      have hv := determinantRat_above_degrees_local_integral h2 hN hH.le (i : ℚ)
        (natCast_den_zmod_ne_zero i ℓ)
      have h0 := padicValNat_den_le_of_padicValRat (e := 0) (by simpa using hv)
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- `D_N · Δ_N(i)` is an integer for every natural number `i`. -/
theorem exists_int_denomBound_mul {N : ℕ} (hN : 0 < N) (i : ℕ) :
    ∃ m : ℤ, (denomBound N : ℚ) * determinantRat (i : ℚ) N = m := by
  by_cases hd : determinantRat (i : ℚ) N = 0
  · exact ⟨0, by rw [hd, mul_zero, Int.cast_zero]⟩
  · obtain ⟨c, hc⟩ := den_dvd_denomBound hN i hd
    refine ⟨(c : ℤ) * (determinantRat (i : ℚ) N).num, ?_⟩
    rw [hc]
    push_cast
    have h := Rat.mul_den_eq_num (determinantRat (i : ℚ) N)
    linear_combination (c : ℚ) * h

/-! ### Size of the common denominator -/

theorem log_denomBound_eq (N : ℕ) :
    Real.log (denomBound N) =
      ∑ ℓ ∈ measurePrimes N, (denomExp N ℓ : ℝ) * Real.log ℓ := by
  unfold denomBound
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [Nat.cast_pow, Real.log_pow]
  · intro ℓ hℓ
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/-- Termwise bound: each prime contributes to exactly one of the three error terms. -/
theorem denomExp_mul_log_le {N ℓ : ℕ} (hN : 0 < N) (hℓ : ℓ ∈ measurePrimes N) :
    (denomExp N ℓ : ℝ) * Real.log ℓ ≤
      (if ℓ = 2 then (twoAdicBound N + 1) * Real.log 2 else 0) +
      (if ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ 2 * Real.sqrt (H N) then 6 * (n N : ℝ) * Real.log (H N) else 0) +
      (if ℓ ≠ 2 ∧ 2 * Real.sqrt (H N) < (ℓ : ℝ) then
        (N : ℝ) * (oddPrimeLoss ((ℓ : ℝ) / N) * Real.log ℓ) + Real.log ℓ else 0) := by
  obtain ⟨hmem, hp⟩ := Finset.mem_filter.mp hℓ
  have hlogℓ : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hH : 0 < H N := by unfold H; omega
  unfold denomExp
  by_cases h2 : ℓ = 2
  · subst h2
    have hs : ¬ ((2 : ℕ) ≠ 2) := fun h => h rfl
    simp only [if_true, hs, false_and, if_false, add_zero]
    have hc := Nat.ceil_lt_add_one (twoAdicBound_nonneg hN)
    exact mul_le_mul_of_nonneg_right hc.le (Real.log_nonneg (by norm_num))
  · by_cases hsmall : (ℓ : ℝ) ≤ 2 * Real.sqrt (H N)
    · have hnot : ¬ (2 * Real.sqrt (H N) < (ℓ : ℝ)) := not_lt.mpr hsmall
      simp only [h2, if_false, hsmall, ne_eq, not_false_eq_true, and_self, if_true, hnot,
        and_false, zero_add, add_zero]
      have h := nat_log_mul_log_prime_le hp hH
      have hn : (0 : ℝ) ≤ n N := by positivity
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * n N)]
    · have hlarge : 2 * Real.sqrt (H N) < (ℓ : ℝ) := not_le.mp hsmall
      simp only [h2, if_false, hsmall, ne_eq, not_false_eq_true, and_false, hlarge, and_self,
        if_true, zero_add]
      have hloss := oddPrimeLoss_nonneg ((ℓ : ℝ) / N)
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hc := Nat.ceil_lt_add_one (mul_nonneg hN0 hloss)
      nlinarith [mul_le_mul_of_nonneg_right hc.le hlogℓ]

/-- The OpenAI index set of large odd primes. -/
theorem measurePrimes_large_subset (N : ℕ) :
    (measurePrimes N).filter (fun ℓ : ℕ => ℓ ≠ 2 ∧ 2 * Real.sqrt (H N) < (ℓ : ℝ)) ⊆
      (Finset.Ioc 0 (H N)).filter (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)) := by
  intro ℓ hℓ
  simp only [measurePrimes, Finset.mem_filter] at hℓ ⊢
  exact ⟨hℓ.1.1, hℓ.1.2, hℓ.2.2⟩

theorem sum_log_measurePrimes_le_theta (N : ℕ) :
    ∑ ℓ ∈ measurePrimes N, Real.log (ℓ : ℝ) ≤ Chebyshev.theta (H N : ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ℓ hℓ
    simp only [measurePrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hℓ ⊢
    exact ⟨⟨Nat.zero_le _, hℓ.1.2⟩, hℓ.2⟩
  · intro ℓ hℓ _
    simp only [Finset.mem_filter] at hℓ
    exact Real.log_nonneg (by exact_mod_cast hℓ.2.one_lt.le)

/-- `log D_N` is at most the sum of the three error terms. -/
theorem log_denomBound_le {N : ℕ} (hN : 0 < N) :
    Real.log (denomBound N) ≤
      (twoAdicBound N + 1) * Real.log 2 + smallOddPrimeError 1 N +
        ((N : ℝ) * ∑ p ∈ (Finset.Ioc 0 (H N)).filter
            (fun p : ℕ => p.Prime ∧ 2 * Real.sqrt (H N) < (p : ℝ)),
            oddPrimeLoss ((p : ℝ) / N) * Real.log (p : ℝ) +
          Chebyshev.theta (H N : ℝ)) := by
  have hH : 0 < H N := by unfold H; omega
  have hn : (0 : ℝ) ≤ n N := by positivity
  have hlogH : 0 ≤ Real.log (H N : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  rw [log_denomBound_eq]
  refine (Finset.sum_le_sum (fun ℓ hℓ => denomExp_mul_log_le hN hℓ)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the prime `2`
    rw [Finset.sum_ite_eq']
    have h0 : 0 ≤ (twoAdicBound N + 1) * Real.log 2 :=
      mul_nonneg (by linarith [twoAdicBound_nonneg hN]) (Real.log_nonneg (by norm_num))
    split_ifs <;> linarith
  · -- small odd primes
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : (measurePrimes N).filter
        (fun ℓ : ℕ => ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ 2 * Real.sqrt (H N)) ⊆ smallOddPrimes N := by
      intro ℓ hℓ
      simp only [measurePrimes, Finset.mem_filter] at hℓ
      exact (mem_smallOddPrimes_iff N ℓ).mpr ⟨hℓ.1.2, hℓ.2.1, hℓ.2.2⟩
    have hcard : (((measurePrimes N).filter
        (fun ℓ : ℕ => ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ 2 * Real.sqrt (H N))).card : ℝ) ≤ 2 * Real.sqrt (H N) :=
      (by exact_mod_cast Finset.card_le_card hsub : _ ≤ ((smallOddPrimes N).card : ℝ)).trans
        (smallOddPrimes_card_le N)
    have herr : smallOddPrimeError 1 N = 2 * Real.sqrt (H N) * (n N : ℝ) * (6 * Real.log (H N)) := by
      simp [smallOddPrimeError]
    rw [herr]
    have h6 : 0 ≤ 6 * (n N : ℝ) * Real.log (H N) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcard h6]
  · -- large odd primes
    rw [← Finset.sum_filter, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hNR : (0 : ℝ) ≤ N := by positivity
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ hNR) ?_
    · apply Finset.sum_le_sum_of_subset_of_nonneg (measurePrimes_large_subset N)
      intro p hp _
      simp only [Finset.mem_filter] at hp
      exact mul_nonneg (oddPrimeLoss_nonneg _)
        (Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le))
    · refine le_trans ?_ (sum_log_measurePrimes_le_theta N)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ℓ hℓ _
      simp only [measurePrimes, Finset.mem_filter] at hℓ
      exact Real.log_nonneg (by exact_mod_cast hℓ.2.one_lt.le)

/-- **Proposition 3.**  `log D_N ≤ (8609/4608 + (505/4608) log 2 + ε) n²` for all large `N`. -/
theorem log_denomBound_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (denomBound N) ≤
      (8609 / 4608 + 505 / 4608 * Real.log 2 + ε) * (n N : ℝ) ^ 2 := by
  have h2 := (tendsto_order.mp (tendsto_twoAdic_log_error 0)).2 (ε / 8) (by positivity)
  have hs := (tendsto_order.mp (smallOddPrimeError_div_sq_tendsto_zero 1)).2 (ε / 4)
    (by positivity)
  have hl := oddPrimeLoss_large_prime_normalized_eventually_upper (ε := ε / 4) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_gt (131 / ε)
  filter_upwards [h2, hs, hl, eventually_ge_atTop K, eventually_gt_atTop 0]
    with N h2N hsN hlN hKN hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : (n N : ℝ) = 48 * N := by simp [n]
  have hHN : (H N : ℝ) = 65 * N := by simp [H]
  have hn : (0 : ℝ) < n N := by rw [hnN]; positivity
  have hn2 : (0 : ℝ) < (n N : ℝ) ^ 2 := by positivity
  have hεN : 131 < ε * N := by
    have hKR : (K : ℝ) ≤ N := by exact_mod_cast hKN
    have h1 := (div_lt_iff₀ hε).mp hK
    nlinarith [mul_le_mul_of_nonneg_right hKR hε.le]
  -- 2-adic term
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have h2N' : 2 + Real.logb 2 (8 * discrepancyNormFactor 0 * (H N : ℝ) ^ 2) < ε / 8 * n N :=
    (div_lt_iff₀ hn).mp h2N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hone : 1 ≤ ε / 8 * (n N : ℝ) ^ 2 := by
    rw [hnN]
    nlinarith [mul_lt_mul_of_pos_right hεN hNR]
  have hT2 : (twoAdicBound N + 1) * Real.log 2 ≤
      (505 / 4608 * Real.log 2 + ε / 4) * (n N : ℝ) ^ 2 := by
    have hb : twoAdicBound N + 1 ≤ (505 / 4608 + ε / 4) * (n N : ℝ) ^ 2 := by
      unfold twoAdicBound
      nlinarith [mul_lt_mul_of_pos_left h2N' hn]
    have hb0 : 0 ≤ twoAdicBound N + 1 := by linarith [twoAdicBound_nonneg hN]
    have hεn : 0 ≤ ε / 4 * (n N : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hb hlog2.le,
      mul_le_mul_of_nonneg_left hlog2'.le hεn]
  -- small odd primes
  have hS : smallOddPrimeError 1 N ≤ ε / 4 * (n N : ℝ) ^ 2 :=
    ((div_lt_iff₀ hn2).mp hsN).le
  -- large odd primes
  have hL := ((div_lt_iff₀ hn2).mp hlN).le
  -- Chebyshev term
  have hθ : Chebyshev.theta (H N : ℝ) ≤ ε / 4 * (n N : ℝ) ^ 2 := by
    have h := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ H N by positivity)
    have hlog4 : Real.log 4 < 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      linarith
    rw [hHN] at h
    rw [hHN, hnN]
    nlinarith [mul_lt_mul_of_pos_right hεN hNR, mul_lt_mul_of_pos_right hlog4 hNR]
  have hmain := log_denomBound_le hN
  linarith

end OAI.InternalCatalan
