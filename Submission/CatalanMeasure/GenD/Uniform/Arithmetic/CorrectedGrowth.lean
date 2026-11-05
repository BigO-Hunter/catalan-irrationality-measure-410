module
public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.PriceGrowth
public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.Negligible
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic
open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Filter
open scoped Topology BigOperators
noncomputable section
theorem denom_growth_corrected (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    (f : PL.Prof) (l : List PrimeGrowth.Seg) (κ0 : ℝ) (sl : ℕ)
    (hloss : ∀ N p : ℕ, 0 < N → p ≤ P.H N →
      (safeOddLoss P N p : ℝ) ≤ N * f.eval ((p : ℝ) / N))
    (hf0 : ∀ x : ℝ, x ≤ 1 → f.eval x = κ0)
    (hH1 : 1 < P.H 1)
    (charge : ℕ→ℕ→ℕ) (E : ℕ→Finset ℕ) (M : ℕ) (c : ℝ)
    (hc : 0≤c) (hE : ∀N,(E N).card≤M)
    (hsupport : ∀N p,p∉E N→charge N p=0)
    (hcharge : ∀N p,(charge N p:ℝ)≤c*N)
    (hgood : ∀ s ∈ l, WindowGrowth.GoodEventually (fun N p => saving P lb N p + sl + charge N p) s)
    (hord : l.Pairwise (fun s t => s.b ≤ t.a))
    (hwin : ∀ᶠ N:ℕ in atTop, ∀ s∈l, ∀p:ℕ,p.Prime→ s.a * N < p → (p : ℝ) ≤ s.b * N →
      p ≠ 2 ∧ P.H N < p ^ 2 ∧ p ≤ P.H N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (expDenom P (denExp P lb) N : ℝ) ≤
      (TwoAdic.A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) * Real.log 2 +
        (κ0 + ∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) - PrimeGrowth.totalArea l + ε) *
        (N : ℝ) ^ 2 := by
  have hcont : Continuous f.eval := f.continuous
  have hM := OddProfile.prime_sum_tendsto_from_zero hcont κ0 hf0 hH1
  have e1 := twoAdic_growth P hP (show 0 < ε / 6 by positivity)
  have e2 := smallPrime_growth P hP (show 0 < ε / 6 by positivity)
  have e3 := (tendsto_order.mp hM).2 (κ0 + (∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) + ε / 6)
    (by linarith)
  have e4 := WindowGrowth.segs_growth_eventually (fun N p => saving P lb N p + sl + charge N p) (fun N => oddBranch P N) l hgood hord
    (by
      filter_upwards [hwin,eventually_gt_atTop (0:ℕ)] with N hwinN hN
      intro s hs p hp h1 h2
      obtain ⟨hp2, hsq, hpH⟩ := hwinN s hs p hp h1 h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, hpH⟩, hp⟩,
        hp2, not_le.mpr hsq⟩)
    (c := PrimeGrowth.totalArea l - ε / 6) (by linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hH1R : (0 : ℝ) < P.H 1 := by exact_mod_cast (lt_trans Nat.zero_lt_one hH1)
  have e5 := linear_log_negligible ((M:ℝ)*c) (P.H 1:ℝ) hH1R
    (show 0<ε/6 by positivity)
  filter_upwards [e5,e1, e2, e3, e4, eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop ⌈6 * (sl : ℝ) * (Real.log 4 * (P.H 1 : ℝ)) / ε⌉₊]
    with N h5 h1 h2 h3 h4 hN hN5
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [log_expDenom]
  -- termwise bound
  have hsum : ∑ p ∈ denomPrimes P N, (denExp P lb N p : ℝ) * Real.log p ≤
      ∑ p ∈ denomPrimes P N,
        ((if p = 2 then (twoAdicExp P N : ℝ) * Real.log 2 else 0) +
        (if p ≠ 2 ∧ p ^ 2 ≤ P.H N then 6 * (P.n N : ℝ) * Real.log (P.H N) else 0) +
        (if p ≠ 2 ∧ ¬ p ^ 2 ≤ P.H N then
          ((safeOddLoss P N p : ℝ) - (saving P lb N p : ℝ)) * Real.log p else 0)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact denExp_term_le P lb hp

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
        ((safeOddLoss P N p : ℝ) - (saving P lb N p : ℝ)) * Real.log p else 0) ≤
      N * (N * (κ0 + (∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) + ε / 6)) -
        (PrimeGrowth.totalArea l - ε / 6) * (N : ℝ) ^ 2 +
          ε / 6 * (N : ℝ) ^ 2 + ε / 6 * (N : ℝ) ^ 2 := by
    rw [← Finset.sum_filter]
    change ∑ p ∈ oddBranch P N, ((safeOddLoss P N p : ℝ) - (saving P lb N p : ℝ)) *
      Real.log p ≤ _
    simp only [sub_mul, Finset.sum_sub_distrib]
    have hL : ∑ p ∈ oddBranch P N, (safeOddLoss P N p : ℝ) * Real.log p ≤
        ∑ p ∈ denomPrimes P N, (safeOddLoss P N p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    have hL2 : ∑ p ∈ denomPrimes P N, (safeOddLoss P N p : ℝ) * Real.log p ≤
        N * ∑ p ∈ (Finset.Ioc 0 (P.H 1 * N)).filter Nat.Prime,
          f.eval ((p : ℝ) / N) * Real.log (p : ℝ) := by
      rw [Finset.mul_sum, ← H_scale P N]
      apply Finset.sum_le_sum
      intro p hp
      have hpH := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have hh := mul_le_mul_of_nonneg_right (hloss N p hN hpH)
        (Real.log_natCast_nonneg p)
      convert hh using 1 <;> ring
    have h3' : ∑ p ∈ (Finset.Ioc 0 (P.H 1 * N)).filter Nat.Prime,
        f.eval ((p : ℝ) / N) * Real.log (p : ℝ) ≤
        (κ0 + (∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x) + ε / 6) * N := by
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
    have hslack : (sl : ℝ) * (Real.log 4 * (P.H N : ℝ)) ≤ ε / 6 * (N : ℝ) ^ 2 := by
      have hc : 6 * (sl : ℝ) * (Real.log 4 * (P.H 1 : ℝ)) / ε ≤ N :=
        (Nat.le_ceil _).trans (by exact_mod_cast hN5)
      have hc' : (sl : ℝ) * (Real.log 4 * (P.H 1 : ℝ)) ≤ ε / 6 * N := by
        have := (div_le_iff₀ hε).mp hc
        linarith
      rw [TwoAdic.cast_H]
      have := mul_le_mul_of_nonneg_right hc' hNr.le
      nlinarith only [this]
    have hchargeSum : ∑p∈oddBranch P N,(charge N p:ℝ)*Real.log p≤ε/6*(N:ℝ)^2 := by
      let T := (oddBranch P N).filter (fun p => charge N p≠0)
      have hT : T⊆E N := by
        intro p hp
        have hz := (Finset.mem_filter.mp hp).2
        by_contra he
        exact hz (hsupport N p he)
      have hcard : T.card≤M := (Finset.card_le_card hT).trans (hE N)
      have hH : 1≤(P.H 1:ℝ)*(N:ℝ) := by
        have hh := H_scale P N
        have hp : 0<P.H N := by rw [hh]; exact Nat.mul_pos (by omega) hN
        rw [←Nat.cast_mul,←hh]
        exact_mod_cast hp
      have hb := bounded_support_cost T M c (P.H 1) N hc hNr.le hH hcard
        (fun p => charge N p) (fun p _ => hcharge N p) (by
          intro p hp
          have hm := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
          have hh := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2
          rw [←TwoAdic.cast_H]
          exact_mod_cast hh)
      have heq : ∑p∈oddBranch P N,(charge N p:ℝ)*Real.log p=
          ∑p∈T,(charge N p:ℝ)*Real.log p := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro p hp hn
        have hz : charge N p=0 := by
          by_contra hz
          exact hn (Finset.mem_filter.mpr ⟨hp,hz⟩)
        simp [hz]
      rw [heq]
      exact hb.trans (by convert h5 using 1 <;> ring)
    have h4' : (PrimeGrowth.totalArea l - ε / 6) * (N : ℝ) ^ 2 ≤
        ∑ p ∈ oddBranch P N, (saving P lb N p : ℝ) * Real.log p +
          ε / 6 * (N : ℝ) ^ 2 + ε / 6 * (N : ℝ) ^ 2 := by
      have hsplit : ∑ p ∈ oddBranch P N, ((saving P lb N p + sl + charge N p : ℕ) : ℝ) * Real.log p =
          ∑ p ∈ oddBranch P N, (saving P lb N p : ℝ) * Real.log p +
            (sl : ℝ) * ∑ p ∈ oddBranch P N, Real.log (p : ℝ) +
            ∑p∈oddBranch P N,(charge N p:ℝ)*Real.log p := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        push_cast; ring
      have := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg (α := ℝ) sl)
      rw [hsplit] at h4
      nlinarith only [h4, this, hslack, hchargeSum]
    have hmono := mul_le_mul_of_nonneg_left h3' hNr.le
    nlinarith only [hL, hL2, hmono, h4']
  nlinarith only [hA, hB, hC, h1, h2]

end

end CatalanMeasure.GenD.Uniform.Arithmetic
