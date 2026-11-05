module

public import Submission.CatalanMeasure.GenD.Normalizer
public import Submission.CatalanMeasure.GenD.PrimeGrowth
public import Submission.CatalanMeasure.Parametric.OddLogBounds
public import Submission.CatalanMeasure.Denominators

@[expose] public section

/-!
# Normalizers from prime exponents (module 4, glue)

Given exponents `e N p` bounding `v_p(Δ_N(i)) ≥ -e N p` for the primes `p ≤ H`, with
`e N q ≥ 2 n` for the recycling primes `N < q ≤ 2N`, the denominator
`D N = ∏_{p ≤ H} p ^ (e N p)` is a `Normalizer`; primes above `H` need no denominator because
the determinant is `p`-integral there (`paramDeterminantRat_above_degrees_local_integral`).
-/

namespace CatalanMeasure.GenD

open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan

noncomputable section

/-- The primes carrying a denominator. -/
def denomPrimes (P : Parameters) (N : ℕ) : Finset ℕ := (Finset.Ioc 0 (P.H N)).filter Nat.Prime

/-- The denominator attached to an exponent function. -/
def expDenom (P : Parameters) (e : ℕ → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∏ p ∈ denomPrimes P N, p ^ e N p

theorem expDenom_ne_zero (P : Parameters) (e : ℕ → ℕ → ℕ) (N : ℕ) : expDenom P e N ≠ 0 := by
  unfold expDenom
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero

theorem log_expDenom (P : Parameters) (e : ℕ → ℕ → ℕ) (N : ℕ) :
    Real.log (expDenom P e N : ℝ) = ∑ p ∈ denomPrimes P N, (e N p : ℝ) * Real.log p :=
  PrimeGrowth.log_prod_pow (denomPrimes P N) (fun p hp => (Finset.mem_filter.mp hp).2) (e N)

/-- The denominator clears the determinant at every natural `i`. -/
theorem den_dvd_expDenom (P : Parameters) (e : ℕ → ℕ → ℕ) {N : ℕ} (hH2 : 2 < P.H N)
    (hval : ∀ i : ℕ, ∀ p : ℕ, p.Prime → p ≤ P.H N →
      Parametric.determinantRat P (i : ℚ) N ≠ 0 →
        -(e N p : ℤ) ≤ padicValRat p (Parametric.determinantRat P (i : ℚ) N))
    (i : ℕ) (hd : Parametric.determinantRat P (i : ℚ) N ≠ 0) :
    (Parametric.determinantRat P (i : ℚ) N).den ∣ expDenom P e N := by
  have hM := expDenom_ne_zero P e N
  rw [← Nat.factorization_le_iff_dvd (Rat.den_pos _).ne' hM, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp]
    by_cases hS : p ∈ denomPrimes P N
    · have h1 := padicValNat_den_le_of_padicValRat
        (hval i p hp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hS).1).2 hd)
      have h2 : e N p ≤ (expDenom P e N).factorization p := by
        apply (hp.pow_dvd_iff_le_factorization hM).mp
        unfold expDenom
        exact Finset.dvd_prod_of_mem (fun p => p ^ e N p) hS
      exact h1.trans h2
    · have hH : P.H N < p := by
        by_contra hle
        push Not at hle
        exact hS (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, hle⟩, hp⟩)
      have hp2 : p ≠ 2 := by omega
      have hv := paramDeterminantRat_above_degrees_local_integral P (N := N) (p := p) hp2 hH
        (i : ℚ) (natCast_den_zmod_ne_zero i p)
      have h0 := padicValNat_den_le_of_padicValRat (e := 0) (by simpa using hv)
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem exists_int_expDenom_mul (P : Parameters) (e : ℕ → ℕ → ℕ) {N : ℕ} (hH2 : 2 < P.H N)
    (hval : ∀ i : ℕ, ∀ p : ℕ, p.Prime → p ≤ P.H N →
      Parametric.determinantRat P (i : ℚ) N ≠ 0 →
        -(e N p : ℤ) ≤ padicValRat p (Parametric.determinantRat P (i : ℚ) N))
    (i : ℕ) :
    ∃ m : ℤ, (expDenom P e N : ℚ) * Parametric.determinantRat P (i : ℚ) N = m := by
  by_cases hd : Parametric.determinantRat P (i : ℚ) N = 0
  · exact ⟨0, by rw [hd, mul_zero, Int.cast_zero]⟩
  obtain ⟨c, hc⟩ := den_dvd_expDenom P e hH2 hval i hd
  refine ⟨(c : ℤ) * (Parametric.determinantRat P (i : ℚ) N).num, ?_⟩
  rw [hc]
  push_cast
  have hh := Rat.mul_den_eq_num (Parametric.determinantRat P (i : ℚ) N)
  linear_combination (c : ℚ) * hh

/-- **Normalizer from exponents.** -/
def Normalizer.ofExponents (P : Parameters) (hP : Admissible P) (N0 : ℕ) (hN0 : P.H 1 < N0)
    (e : ℕ → ℕ → ℕ)
    (hval : ∀ N, N0 ≤ N → ∀ i : ℕ, ∀ p : ℕ, p.Prime → p ≤ P.H N →
      Parametric.determinantRat P (i : ℚ) N ≠ 0 →
        -(e N p : ℤ) ≤ padicValRat p (Parametric.determinantRat P (i : ℚ) N))
    (hrec : ∀ N q : ℕ, N0 ≤ N → q.Prime → N < q → q ≤ 2 * N → 2 * P.n N ≤ e N q) :
    Normalizer P where
  adm := hP
  N0 := N0
  hN0 := hN0
  D := expDenom P e
  D_ne := expDenom_ne_zero P e
  int_val := fun N hN i => by
    have hH2 : 2 < P.H N := by
      have hs := H_scale P N
      have h4 : 4 ≤ P.H 1 := by
        have := hP
        simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
          Parameters.q, Parameters.g, Parameters.h, Admissible] at this ⊢
        omega
      rw [hs]; nlinarith
    exact exists_int_expDenom_mul P e hH2 (hval N hN) i
  recycle := fun N q hN hq hNq hqN => by
    have hmem : q ∈ denomPrimes P N := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq.pos, ?_⟩, hq⟩
      have hs := H_scale P N
      have h4 : 4 ≤ P.H 1 := by
        have := hP
        simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
          Parameters.q, Parameters.g, Parameters.h, Admissible] at this ⊢
        omega
      rw [hs]; nlinarith
    exact (pow_dvd_pow q (hrec N q hN hq hNq hqN)).trans
      (Finset.dvd_prod_of_mem (fun p => p ^ e N p) hmem)

end

end CatalanMeasure.GenD
