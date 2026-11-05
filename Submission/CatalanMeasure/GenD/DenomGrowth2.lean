module

public import Submission.CatalanMeasure.GenD.DenomGrowth
public import Submission.CatalanMeasure.GenD.PrimeGrowth

@[expose] public section

/-!
# Growth of the denominator, part 2: the odd-prime sum and the total (module 4)

`denom_growth`: for the denominator `expDenom P (denExp P lb)`,
`log D_N ≤ (G + ε) N²` eventually, with
`G = A2(n0,H1,b0) log 2 + (κ0 + ∫_1^{H1} f) - totalArea l`,
where `f` is the real odd-loss profile (`oddLossNat = N f(p/N)` for `p ≤ H`), `κ0` its value on
`[0,1]`, and `l` the list of gain windows for `lb.kap`.
-/

namespace CatalanMeasure.GenD

open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter
open scoped Topology BigOperators

noncomputable section

/-- The odd branch: primes `p ≠ 2` with `H < p²`, `p ≤ H`. -/
def oddBranch (P : Parameters) (N : ℕ) : Finset ℕ :=
  (denomPrimes P N).filter (fun p => p ≠ 2 ∧ ¬ p ^ 2 ≤ P.H N)

/-- Termwise bound. -/
theorem denExp_term_le (P : Parameters) (lb : NullityLB P) {N p : ℕ} (hp : p ∈ denomPrimes P N)
    (hgain : p ≠ 2 → ¬ p ^ 2 ≤ P.H N → lb.kap N p ≤ OddProfile.oddLossNat P N p ∧
      (0 < lb.kap N p → 2 * P.n N ≤ OddProfile.oddLossNat P N p)) :
    (denExp P lb N p : ℝ) * Real.log p ≤
      (if p = 2 then (twoAdicExp P N : ℝ) * Real.log 2 else 0) +
      (if p ≠ 2 ∧ p ^ 2 ≤ P.H N then 6 * (P.n N : ℝ) * Real.log (P.H N) else 0) +
      (if p ≠ 2 ∧ ¬ p ^ 2 ≤ P.H N then
        ((OddProfile.oddLossNat P N p : ℝ) - (lb.kap N p : ℝ)) * Real.log p else 0) := by
  obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hp
  have hpH : 0 < P.H N := lt_of_lt_of_le (Finset.mem_Ioc.mp hmem).1 (Finset.mem_Ioc.mp hmem).2
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  unfold denExp
  by_cases h2 : p = 2
  · subst h2
    simp only [if_true, ne_eq, not_true_eq_false, false_and, if_false, add_zero]
    exact le_refl _
  · by_cases hs : p ^ 2 ≤ P.H N
    · simp only [h2, hs, if_true, if_false, ne_eq, not_false_eq_true, true_and, not_true_eq_false,
        and_false, zero_add, add_zero]
      have h := nat_log_mul_log_prime_le hprime hpH
      have hn : (0 : ℝ) ≤ P.n N := by positivity
      unfold smallExp
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * P.n N)]
    · simp only [h2, hs, if_false, ne_eq, not_false_eq_true, true_and, and_true, if_true,
        zero_add]
      have hg := hgain h2 hs
      have hk := hg.1
      have hmin : oddExp P lb N p ≤ OddProfile.oddLossNat P N p - lb.kap N p := by
        unfold oddExp
        by_cases hk0 : lb.kap N p = 0
        · rw [hk0]; simp
        · have := hg.2 (Nat.pos_of_ne_zero hk0)
          have := min_le_right (OddProfile.oddLossNat P N p) (2 * P.n N - lb.kap N p)
          omega
      have hcast : (oddExp P lb N p : ℝ) ≤ (OddProfile.oddLossNat P N p : ℝ) - (lb.kap N p : ℝ) := by
        have := (Nat.cast_le (α := ℝ)).mpr hmin
        rwa [Nat.cast_sub hk] at this
      exact mul_le_mul_of_nonneg_right hcast hlogp

theorem denom_growth (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    (f : PL.Prof) (l : List PrimeGrowth.Seg) (κ0 : ℝ) (sl : ℕ)
    (hloss : ∀ N p : ℕ, 0 < N → p ≤ P.H N →
      (OddProfile.oddLossNat P N p : ℝ) = N * f.eval ((p : ℝ) / N))
    (hf0 : ∀ x : ℝ, x ≤ 1 → f.eval x = κ0)
    (hH1 : 1 < P.H 1)
    (hgain : ∀ N p : ℕ, 0 < N → p.Prime → P.H N < p ^ 2 → p ≤ P.H N →
      lb.kap N p ≤ OddProfile.oddLossNat P N p ∧
        (0 < lb.kap N p → 2 * P.n N ≤ OddProfile.oddLossNat P N p))
    (hgood : ∀ s ∈ l, PrimeGrowth.Seg.Good (fun N p => lb.kap N p + sl) s)
    (hord : l.Pairwise (fun s t => s.b ≤ t.a))
    (hwin : ∀ s ∈ l, ∀ N p : ℕ, 0 < N → p.Prime → s.a * N < p → (p : ℝ) ≤ s.b * N →
      p ≠ 2 ∧ P.H N < p ^ 2 ∧ p ≤ P.H N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (expDenom P (denExp P lb) N : ℝ) ≤
      (TwoAdic.A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) * Real.log 2 +
        (κ0 + ∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) - PrimeGrowth.totalArea l + ε) *
        (N : ℝ) ^ 2 := by
  have hcont : Continuous f.eval := f.continuous
  have hM := OddProfile.prime_sum_tendsto_from_zero hcont κ0 hf0 hH1
  have e1 := twoAdic_growth P hP (show 0 < ε / 5 by positivity)
  have e2 := smallPrime_growth P hP (show 0 < ε / 5 by positivity)
  have e3 := (tendsto_order.mp hM).2 (κ0 + (∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) + ε / 5)
    (by linarith)
  have e4 := PrimeGrowth.segs_growth (fun N p => lb.kap N p + sl) (fun N => oddBranch P N) l hgood hord
    (fun N s hs p hp h1 h2 => by
      have hN : 0 < N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          simp at h2
          exact absurd h2 hp.ne_zero
        · exact h
      obtain ⟨hp2, hsq, hpH⟩ := hwin s hs N p hN hp h1 h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, hpH⟩, hp⟩,
        hp2, not_le.mpr hsq⟩)
    (c := PrimeGrowth.totalArea l - ε / 5) (by linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hH1R : (0 : ℝ) < P.H 1 := by exact_mod_cast (lt_trans Nat.zero_lt_one hH1)
  filter_upwards [e1, e2, e3, e4, eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop ⌈5 * (sl : ℝ) * (Real.log 4 * (P.H 1 : ℝ)) / ε⌉₊]
    with N h1 h2 h3 h4 hN hN5
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [log_expDenom]
  -- termwise bound
  have hsum : ∑ p ∈ denomPrimes P N, (denExp P lb N p : ℝ) * Real.log p ≤
      ∑ p ∈ denomPrimes P N,
        ((if p = 2 then (twoAdicExp P N : ℝ) * Real.log 2 else 0) +
        (if p ≠ 2 ∧ p ^ 2 ≤ P.H N then 6 * (P.n N : ℝ) * Real.log (P.H N) else 0) +
        (if p ≠ 2 ∧ ¬ p ^ 2 ≤ P.H N then
          ((OddProfile.oddLossNat P N p : ℝ) - (lb.kap N p : ℝ)) * Real.log p else 0)) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hp
    exact denExp_term_le P lb hp (fun _ hs => hgain N p hN hprime (not_le.mp hs)
      (Finset.mem_Ioc.mp hmem).2)
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the three sums
  have hA : ∑ p ∈ denomPrimes P N, (if p = 2 then (twoAdicExp P N : ℝ) * Real.log 2 else 0) ≤
      (twoAdicExp P N : ℝ) * Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_refl _
    · positivity
  have hlogH : 0 ≤ 6 * (P.n N : ℝ) * Real.log (P.H N) := by
    have hH1' : (1 : ℝ) ≤ P.H N := by
      have : 0 < P.H N := by
        have h1' : 0 < P.n N := Nat.mul_pos hP.1 hN
        simp only [Parameters.H, Parameters.C, Parameters.L]; omega
      exact_mod_cast this
    have := Real.log_nonneg hH1'
    positivity
  have hB : ∑ p ∈ denomPrimes P N,
      (if p ≠ 2 ∧ p ^ 2 ≤ P.H N then 6 * (P.n N : ℝ) * Real.log (P.H N) else 0) ≤
      2 * Real.sqrt (P.H N) * (6 * (P.n N : ℝ) * Real.log (P.H N)) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : (denomPrimes P N).filter (fun p => p ≠ 2 ∧ p ^ 2 ≤ P.H N) ⊆
        Finset.Ioc 0 ⌊Real.sqrt (P.H N)⌋₊ := by
      intro p hp
      obtain ⟨hmem, hp2, hsq⟩ := Finset.mem_filter.mp hp
      have hpp := (Finset.mem_filter.mp hmem).2
      refine Finset.mem_Ioc.mpr ⟨hpp.pos, Nat.le_floor ?_⟩
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast hsq
    have hcard : (((denomPrimes P N).filter (fun p => p ≠ 2 ∧ p ^ 2 ≤ P.H N)).card : ℝ) ≤
        2 * Real.sqrt (P.H N) := by
      have h1' := Finset.card_le_card hsub
      simp only [Nat.card_Ioc, Nat.sub_zero] at h1'
      have h2' : ((⌊Real.sqrt (P.H N)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (P.H N) :=
        Nat.floor_le (Real.sqrt_nonneg _)
      have h3' : (((denomPrimes P N).filter (fun p => p ≠ 2 ∧ p ^ 2 ≤ P.H N)).card : ℝ) ≤
          ((⌊Real.sqrt (P.H N)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1'
      nlinarith [Real.sqrt_nonneg (P.H N : ℝ)]
    exact mul_le_mul_of_nonneg_right hcard hlogH
  have hC : ∑ p ∈ denomPrimes P N,
      (if p ≠ 2 ∧ ¬ p ^ 2 ≤ P.H N then
        ((OddProfile.oddLossNat P N p : ℝ) - (lb.kap N p : ℝ)) * Real.log p else 0) ≤
      N * (N * (κ0 + (∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) + ε / 5)) -
        (PrimeGrowth.totalArea l - ε / 5) * (N : ℝ) ^ 2 + ε / 5 * (N : ℝ) ^ 2 := by
    rw [← Finset.sum_filter]
    change ∑ p ∈ oddBranch P N, ((OddProfile.oddLossNat P N p : ℝ) - (lb.kap N p : ℝ)) *
      Real.log p ≤ _
    simp only [sub_mul, Finset.sum_sub_distrib]
    have hL : ∑ p ∈ oddBranch P N, (OddProfile.oddLossNat P N p : ℝ) * Real.log p ≤
        ∑ p ∈ denomPrimes P N, (OddProfile.oddLossNat P N p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    have hL2 : ∑ p ∈ denomPrimes P N, (OddProfile.oddLossNat P N p : ℝ) * Real.log p =
        N * ∑ p ∈ (Finset.Ioc 0 (P.H 1 * N)).filter Nat.Prime,
          f.eval ((p : ℝ) / N) * Real.log (p : ℝ) := by
      rw [Finset.mul_sum, ← H_scale P N]
      apply Finset.sum_congr rfl
      intro p hp
      have hpH := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      rw [hloss N p hN hpH]
      ring
    have h3' : ∑ p ∈ (Finset.Ioc 0 (P.H 1 * N)).filter Nat.Prime,
        f.eval ((p : ℝ) / N) * Real.log (p : ℝ) ≤
        (κ0 + (∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) + ε / 5) * N := by
      have := (div_lt_iff₀ hNr).mp h3
      exact this.le
    -- the slack: Σ_T (kap + sl) log p = Σ_T kap log p + sl Σ_T log p, Σ_T log p ≤ θ(H N)
    have hθ : ∑ p ∈ oddBranch P N, Real.log (p : ℝ) ≤ Real.log 4 * (P.H N : ℝ) := by
      refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _))
      rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hp
        obtain ⟨hmem2, hpr⟩ := Finset.mem_filter.mp hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.zero_le _, (Finset.mem_Ioc.mp hmem2).2⟩, hpr⟩
      · intro p hp _
        have hpr := (Finset.mem_filter.mp hp).2
        exact Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hslack : (sl : ℝ) * (Real.log 4 * (P.H N : ℝ)) ≤ ε / 5 * (N : ℝ) ^ 2 := by
      have hc : 5 * (sl : ℝ) * (Real.log 4 * (P.H 1 : ℝ)) / ε ≤ N :=
        (Nat.le_ceil _).trans (by exact_mod_cast hN5)
      have hc' : (sl : ℝ) * (Real.log 4 * (P.H 1 : ℝ)) ≤ ε / 5 * N := by
        have := (div_le_iff₀ hε).mp hc
        linarith
      rw [TwoAdic.cast_H]
      have := mul_le_mul_of_nonneg_right hc' hNr.le
      nlinarith only [this]
    have h4' : (PrimeGrowth.totalArea l - ε / 5) * (N : ℝ) ^ 2 ≤
        ∑ p ∈ oddBranch P N, (lb.kap N p : ℝ) * Real.log p + ε / 5 * (N : ℝ) ^ 2 := by
      have hsplit : ∑ p ∈ oddBranch P N, ((lb.kap N p + sl : ℕ) : ℝ) * Real.log p =
          ∑ p ∈ oddBranch P N, (lb.kap N p : ℝ) * Real.log p +
            (sl : ℝ) * ∑ p ∈ oddBranch P N, Real.log (p : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        push_cast; ring
      have := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg (α := ℝ) sl)
      rw [hsplit] at h4
      nlinarith only [h4, this, hslack]
    have hmono := mul_le_mul_of_nonneg_left h3' hNr.le
    nlinarith only [hL, hL2, hmono, h4']
  nlinarith only [hA, hB, hC, h1, h2]

end

end CatalanMeasure.GenD
