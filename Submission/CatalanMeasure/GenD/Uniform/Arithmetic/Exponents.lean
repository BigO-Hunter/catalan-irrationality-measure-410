module

public import Submission.CatalanMeasure.GenD.Interface
public import Submission.CatalanMeasure.GenD.Denominator
public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.SafeOdd
public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.TwoAdic
public import Submission.CatalanMeasure.Denominators

@[expose] public section

/-!
# Actual prime exponents and recycling-safe normalizers

At two use the clamped selector budget, at small odd primes use the proved
logarithmic bound, and at large odd primes take the minimum of the safe pool
and the actual nullity price. The canonical normalizer disables gains on the
recycling band explicitly; no global upper-side condition is assumed.
-/

namespace CatalanMeasure.GenD.Uniform.Arithmetic

open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan

noncomputable section

/-- The 2-adic exponent (ceiling of the `TwoAdic` bound, with the discrepancy factor at `0`). -/
def twoAdicExp (P : Parameters) (N : ℕ) : ℕ :=
  ⌈TwoAdic.A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ) +
    (P.n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2)⌉₊

/-- Exponent for small odd primes. -/
def smallExp (P : Parameters) (N p : ℕ) : ℕ := 6 * P.n N * Nat.log p (P.H N)

/-- Exponent for odd primes above `√H`: the better of odd profile and nullity bound. -/
def oddExp (P : Parameters) (lb : NullityLB P) (N p : ℕ) : ℕ :=
  min (safeOddLoss P N p) (2 * P.n N - lb.kap N p)

/-- The denominator exponent. -/
def denExp (P : Parameters) (lb : NullityLB P) (N p : ℕ) : ℕ :=
  if p = 2 then twoAdicExp P N else if p ^ 2 ≤ P.H N then smallExp P N p else oddExp P lb N p

theorem two_adic_case (P : Parameters) (hP : Admissible P) {N : ℕ} (hN : 0 < N) (i : ℕ)
    (hd : Parametric.determinantRat P (i : ℚ) N ≠ 0) :
    -(twoAdicExp P N : ℤ) ≤ padicValRat 2 (Parametric.determinantRat P (i : ℚ) N) := by
  have hHpos : 0 < P.H N := by
    have : P.n N ≤ P.H N := by
      simp only [Parameters.H, Parameters.C, Parameters.L]
      omega
    have h1 : 0 < P.n N := Nat.mul_pos hP.1 hN
    omega
  have hv := TwoAdic.determinantRat_two_adic_valuation_lower P hP (i : ℚ) hN hHpos hd
  have hF := discrepancyNormFactor_natCast_le i
  have hFi := one_le_discrepancyNormFactor (i : ℚ)
  have hH : (0 : ℝ) < P.H N := by exact_mod_cast hHpos
  have hH2 := pow_pos hH 2
  have hl : Real.logb 2 (8 * discrepancyNormFactor (i : ℚ) * (P.H N : ℝ) ^ 2) ≤
      Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2) := by
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact mul_pos (mul_pos (by norm_num) (by linarith only [hFi])) hH2
    · exact mul_le_mul_of_nonneg_right (by linarith only [hF]) hH2.le
  have hc := Nat.le_ceil (TwoAdic.A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ) +
    (P.n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor 0 * (P.H N : ℝ) ^ 2))
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ (P.n N : ℝ))
  have hr : -((twoAdicExp P N : ℕ) : ℝ) ≤
      (padicValRat 2 (Parametric.determinantRat P (i : ℚ) N) : ℝ) := by
    unfold twoAdicExp
    nlinarith only [hv, hc, hm]
  exact_mod_cast hr

theorem small_case (P : Parameters) {N p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (i : ℕ) :
    -(smallExp P N p : ℤ) ≤ padicValRat p (Parametric.determinantRat P (i : ℚ) N) := by
  have hv := paramDeterminantRat_odd_prime_log_lower P hp2 (i : ℚ) N
  simp only [Rat.den_natCast, padicValNat.one, Nat.cast_zero, sub_zero] at hv
  unfold smallExp
  push_cast
  nlinarith only [hv]

theorem odd_case (P : Parameters) (hP : Admissible P) (lb : NullityLB P) {N p : ℕ}
    [hpp : Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2) (hHsq : P.H N < p ^ 2) (hpH : p ≤ P.H N)
    (i : ℕ) :
    -(oddExp P lb N p : ℤ) ≤ padicValRat p (Parametric.determinantRat P (i : ℚ) N) := by
  have hz := natCast_den_zmod_ne_zero i p
  have h1 := safeOdd_valuation P hP hN hp2 hHsq (i : ℚ) hz
  have h2 := det_valuation_of_nullity P hp2 hHsq (lb.ok N p hN hpp.out hp2 hHsq) (i : ℚ) hz
  unfold oddExp
  rcases le_total (safeOddLoss P N p) (2 * P.n N - lb.kap N p) with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h2

/-- **Valuation lower bound with the combined exponent.** -/
theorem denExp_valuation (P : Parameters) (hP : Admissible P) (lb : NullityLB P) {N p : ℕ}
    (hN : 0 < N) (hp : p.Prime) (hpH : p ≤ P.H N)
    (i : ℕ)
    (hd : Parametric.determinantRat P (i : ℚ) N ≠ 0) :
    -(denExp P lb N p : ℤ) ≤ padicValRat p (Parametric.determinantRat P (i : ℚ) N) := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold denExp
  by_cases h2 : p = 2
  · subst h2
    simpa using two_adic_case P hP hN i hd
  · by_cases hs : p ^ 2 ≤ P.H N
    · simp only [h2, hs, if_true, if_false]
      exact small_case P h2 i
    · simp only [h2, hs, if_false]
      exact odd_case P hP lb hN h2 (not_le.mp hs) hpH i

/-- **The normalizer of a design.** -/
def normalizerOf (P : Parameters) (hP : Admissible P) (lb : NullityLB P) (N0 : ℕ)
    (hN0 : P.H 1 < N0)
    (rec_ok : ∀ N q : ℕ, N0 ≤ N → q.Prime → N < q → q ≤ 2 * N →
      2 * P.n N ≤ safeOddLoss P N q ∧ lb.kap N q = 0) :
    Normalizer P :=
  Normalizer.ofExponents P hP N0 hN0 (denExp P lb)
    (fun N hN i p hp hpH hd =>
      denExp_valuation P hP lb (lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hN0) hN) hp hpH
        i hd)
    (fun N q hN hq hNq hqN => by
      have hg : P.H N < q ^ 2 := by
        have hs := H_scale P N
        have h0 := hN0
        rw [hs]
        have h1 : P.H 1 * N < N * N := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        nlinarith [Nat.mul_le_mul hNq.le hNq.le]
      have hq2 : q ≠ 2 := by
        have hH2 : 2 ≤ P.H 1 := by
          have := hP
          simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
            Parameters.q, Parameters.g, Parameters.h, Admissible] at this ⊢
          omega
        omega
      have hq2' : ¬ q ^ 2 ≤ P.H N := not_le.mpr hg
      obtain ⟨h1, h2⟩ := rec_ok N q hN hq hNq hqN
      unfold denExp oddExp
      simp only [hq2, hq2', if_false, h2, Nat.sub_zero]
      exact le_min h1 le_rfl)


/-- A normalizer must retain the full recycling exponent. Disable rank claims
on that band explicitly; all other source bounds are preserved. -/
def recyclingSafeLB (P : Parameters) (lb : NullityLB P) : NullityLB P where
  kap N p := if N<p ∧ p≤2*N then 0 else lb.kap N p
  ok := by
    intro N p hN hp hp2 hsq
    by_cases hr : N<p ∧ p≤2*N
    · simp only [hr, and_self, if_true]
      exact Nat.zero_le _
    · simp only [hr, if_false]
      exact lb.ok N p hN hp hp2 hsq

def canonicalNormalizer (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    (N0 : ℕ) (hN0 : P.H 1<N0) : Normalizer P :=
  normalizerOf P hP (recyclingSafeLB P lb) N0 hN0 (by
    intro N q hN hq hNq hqN
    have hH : 1≤P.H 1 := by
      have hn := hP.1
      simp only [Parameters.H,Parameters.C,Parameters.L,Parameters.n,Nat.mul_one]
      omega
    have hn : 1<N := by omega
    constructor
    · exact (recycling_pool P hP hn hq hNq hqN).ge
    · simp [recyclingSafeLB,hNq,hqN])

end

end CatalanMeasure.GenD.Uniform.Arithmetic

