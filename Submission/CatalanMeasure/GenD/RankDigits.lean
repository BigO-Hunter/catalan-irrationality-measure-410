module
public import Submission.CatalanMeasure.GenD.RankCommon
@[expose] public section

/-!
# Digit-vanishing arithmetic for Theorems U6g and S (GenD)

Pure statements about two coefficient sequences `q` (of `Qh`) and `d` (of `Dh`) and an auxiliary
sequence `y` (of the Frobenius quotient `Y`) over `ZMod p`.  No polynomial and no design appears:
all hypotheses are linear in the natural-number parameters.

`DigitSeq p a L TQ TD TY e q d y` packages the six facts proved once from the row polynomials:
supports, identity K6 (`2 Qh[i] = 2 Dh[i] - Dh[i-2p]` for `i < L`) and the Frobenius relation
`(1-X)^e Qh = (1-X^p) Y`.
-/

namespace CatalanMeasure.GenD
noncomputable section

structure DigitSeq (p a L TQ TD TY e : ℕ) [Fact p.Prime] (q d y : ℕ → ZMod p) : Prop where
  q_lo : ∀ i, i ≤ a → q i = 0
  q_hi : ∀ i, TQ < i → q i = 0
  d_lo : ∀ i, i ≤ a → d i = 0
  d_hi : ∀ i, TD < i → d i = 0
  y_lo : ∀ i, i ≤ a → y i = 0
  y_hi : ∀ i, TY < i → y i = 0
  k6 : ∀ i, i < L → 2 * q i = 2 * d i - (if 2 * p ≤ i then d (i - 2 * p) else 0)
  frob : ∀ i, e ≤ i → ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
      q (i - t) = y i - (if p ≤ i then y (i - p) else 0)

section
variable {p a L TQ TD TY e : ℕ} [Fact p.Prime] {q d y : ℕ → ZMod p}

/-- **Theorem S, digit part.**  Constraints: `Dh_j(mu) = 0` for `j = 1,2,3` on `[m0,m1)` and
`Qh_4(mu) = 0` on the first `e` residues.  Conclusion: every digit of `Qh` and `Dh` vanishes. -/
theorem digits_vanish_S (D : DigitSeq p a L TQ TD TY e q d y) (h2 : (2 : ZMod p) ≠ 0)
    {m0 m1 : ℕ} (hm1p : m1 ≤ p) (hm1a : m1 ≤ a + 1) (hL : 3 * p + m1 ≤ L)
    (hTQ : TQ < 5 * p + m0) (hTY : TY < 5 * p + m0) (hTD : TD < 4 * p + m0)
    (he : m0 + e ≤ m1)
    (hD1 : ∀ mu, m0 ≤ mu → mu < m1 → d (p + mu) = 0)
    (hD2 : ∀ mu, m0 ≤ mu → mu < m1 → d (2 * p + mu) = 0)
    (hD3 : ∀ mu, m0 ≤ mu → mu < m1 → d (3 * p + mu) = 0)
    (hQ4 : ∀ mu, m0 ≤ mu → mu < m0 + e → q (4 * p + mu) = 0) :
    ∀ mu, m0 ≤ mu → mu < m1 → ∀ u, q (u * p + mu) = 0 ∧ d (u * p + mu) = 0 := by
  have hA : ∀ mu, mu < m1 → d mu = 0 := fun mu h => D.d_lo mu (by omega)
  have hq1 : ∀ mu, m0 ≤ mu → mu < m1 → q (p + mu) = 0 := by
    intro mu h0 h1
    have k := D.k6 (p + mu) (by omega)
    rw [if_neg (by omega), hD1 mu h0 h1] at k
    have : 2 * q (p + mu) = 0 := by rw [k]; ring
    exact (mul_eq_zero.mp this).resolve_left h2
  have hq2 : ∀ mu, m0 ≤ mu → mu < m1 → q (2 * p + mu) = 0 := by
    intro mu h0 h1
    have k := D.k6 (2 * p + mu) (by omega)
    rw [if_pos (by omega), show 2 * p + mu - 2 * p = mu by omega, hA mu h1,
      hD2 mu h0 h1] at k
    have : 2 * q (2 * p + mu) = 0 := by rw [k]; ring
    exact (mul_eq_zero.mp this).resolve_left h2
  have hq3 : ∀ mu, m0 ≤ mu → mu < m1 → q (3 * p + mu) = 0 := by
    intro mu h0 h1
    have k := D.k6 (3 * p + mu) (by omega)
    rw [if_pos (by omega), show 3 * p + mu - 2 * p = p + mu by omega, hD1 mu h0 h1,
      hD3 mu h0 h1] at k
    have : 2 * q (3 * p + mu) = 0 := by rw [k]; ring
    exact (mul_eq_zero.mp this).resolve_left h2
  -- the triangular recurrence for the fourth digit
  have hrec : ∀ mu, m0 + e ≤ mu → mu < m1 →
      ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
        q (4 * p + mu - t) = 0 := by
    intro mu h0 h1
    have f0 := D.frob mu (by omega)
    have f1 := D.frob (p + mu) (by omega)
    have f2 := D.frob (2 * p + mu) (by omega)
    have f3 := D.frob (3 * p + mu) (by omega)
    have f4 := D.frob (4 * p + mu) (by omega)
    have f5 := D.frob (5 * p + mu) (by omega)
    rw [if_neg (by omega)] at f0
    rw [if_pos (by omega), show p + mu - p = mu by omega] at f1
    rw [if_pos (by omega), show 2 * p + mu - p = p + mu by omega] at f2
    rw [if_pos (by omega), show 3 * p + mu - p = 2 * p + mu by omega] at f3
    rw [if_pos (by omega), show 4 * p + mu - p = 3 * p + mu by omega] at f4
    rw [if_pos (by omega), show 5 * p + mu - p = 4 * p + mu by omega] at f5
    have y5 : y (5 * p + mu) = 0 := D.y_hi _ (by omega)
    have hsum : ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
        q (4 * p + mu - t) = ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t *
          (e.choose t : ZMod p) * q (mu - t) +
        ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
          q (p + mu - t) +
        ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
          q (2 * p + mu - t) +
        ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
          q (3 * p + mu - t) +
        ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
          q (4 * p + mu - t) +
        ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
          q (5 * p + mu - t) := by
      have hz : ∀ t ∈ Finset.range (e + 1),
          (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (mu - t) = 0 ∧
          (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (p + mu - t) = 0 ∧
          (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (2 * p + mu - t) = 0 ∧
          (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (3 * p + mu - t) = 0 ∧
          (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (5 * p + mu - t) = 0 := by
        intro t ht
        have htl := Finset.mem_range.mp ht
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [D.q_lo _ (by omega), mul_zero]
        · rw [show p + mu - t = p + (mu - t) by omega, hq1 (mu - t) (by omega) (by omega),
            mul_zero]
        · rw [show 2 * p + mu - t = 2 * p + (mu - t) by omega,
            hq2 (mu - t) (by omega) (by omega), mul_zero]
        · rw [show 3 * p + mu - t = 3 * p + (mu - t) by omega,
            hq3 (mu - t) (by omega) (by omega), mul_zero]
        · rw [D.q_hi _ (by omega), mul_zero]
      rw [Finset.sum_eq_zero (fun t ht => (hz t ht).1),
        Finset.sum_eq_zero (fun t ht => (hz t ht).2.1),
        Finset.sum_eq_zero (fun t ht => (hz t ht).2.2.1),
        Finset.sum_eq_zero (fun t ht => (hz t ht).2.2.2.1),
        Finset.sum_eq_zero (fun t ht => (hz t ht).2.2.2.2)]
      ring
    rw [hsum, f0, f1, f2, f3, f4, f5, y5]
    ring
  have h4 := alt_binom_vanish (fun mu => if mu < m1 then q (4 * p + mu) else 0) e m0 m1
    (by
      intro mu h0 h1
      refine Eq.trans ?_ (hrec mu h0 h1)
      refine Finset.sum_congr rfl fun t ht => ?_
      have htl := Finset.mem_range.mp ht
      simp only [show mu - t < m1 by omega, if_true]
      rw [show 4 * p + mu - t = 4 * p + (mu - t) by omega])
    (by
      intro mu h0 h1
      simp only [show mu < m1 by omega, if_true]
      exact hQ4 mu h0 h1)
  intro mu h0 h1 u
  have hq4 : q (4 * p + mu) = 0 := by
    have := h4 mu h0 h1
    simpa [h1] using this
  constructor
  · by_cases hu : 5 ≤ u
    · exact D.q_hi _ (by have := Nat.mul_le_mul_right p hu; omega)
    · interval_cases u
      · exact D.q_lo _ (by omega)
      · simpa using hq1 mu h0 h1
      · exact hq2 mu h0 h1
      · exact hq3 mu h0 h1
      · exact hq4
  · by_cases hu : 4 ≤ u
    · exact D.d_hi _ (by have := Nat.mul_le_mul_right p hu; omega)
    · interval_cases u
      · exact D.d_lo _ (by omega)
      · simpa using hD1 mu h0 h1
      · exact hD2 mu h0 h1
      · exact hD3 mu h0 h1

/-- **Theorem U6g, digit part.**  Constraints: `Qh_u(mu) = 0` for `u = 2..5` on `[m0,m1)` and
`Qh_6(mu) = 0` on the first `e` residues. -/
theorem digits_vanish_U6 (D : DigitSeq p a L TQ TD TY e q d y) (h2 : (2 : ZMod p) ≠ 0)
    {m0 m1 : ℕ} (hm1p : m1 ≤ p) (hm1a : p + m1 ≤ a + 1) (hL : 5 * p + m1 ≤ L)
    (hTQ : TQ < 7 * p + m0) (hTY : TY < 6 * p + m0 + e) (hTD : TD < 6 * p + m0)
    (he : m0 + e ≤ m1)
    (hQ2 : ∀ mu, m0 ≤ mu → mu < m1 → q (2 * p + mu) = 0)
    (hQ3 : ∀ mu, m0 ≤ mu → mu < m1 → q (3 * p + mu) = 0)
    (hQ4 : ∀ mu, m0 ≤ mu → mu < m1 → q (4 * p + mu) = 0)
    (hQ5 : ∀ mu, m0 ≤ mu → mu < m1 → q (5 * p + mu) = 0)
    (hQ6 : ∀ mu, m0 ≤ mu → mu < m0 + e → q (6 * p + mu) = 0) :
    ∀ mu, m0 ≤ mu → mu < m1 → ∀ u, q (u * p + mu) = 0 ∧ d (u * p + mu) = 0 := by
  have hrec : ∀ mu, m0 + e ≤ mu → mu < m1 →
      ∑ t ∈ Finset.range (e + 1), (-1 : ZMod p) ^ t * (e.choose t : ZMod p) *
        q (6 * p + mu - t) = 0 := by
    intro mu h0 h1
    have f2 := D.frob (2 * p + mu) (by omega)
    have f3 := D.frob (3 * p + mu) (by omega)
    have f4 := D.frob (4 * p + mu) (by omega)
    have f5 := D.frob (5 * p + mu) (by omega)
    have f6 := D.frob (6 * p + mu) (by omega)
    rw [if_pos (by omega), show 2 * p + mu - p = p + mu by omega] at f2
    rw [if_pos (by omega), show 3 * p + mu - p = 2 * p + mu by omega] at f3
    rw [if_pos (by omega), show 4 * p + mu - p = 3 * p + mu by omega] at f4
    rw [if_pos (by omega), show 5 * p + mu - p = 4 * p + mu by omega] at f5
    rw [if_pos (by omega), show 6 * p + mu - p = 5 * p + mu by omega] at f6
    have y1 : y (p + mu) = 0 := D.y_lo _ (by omega)
    have y6 : y (6 * p + mu) = 0 := D.y_hi _ (by omega)
    have hz : ∀ t ∈ Finset.range (e + 1),
        (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (2 * p + mu - t) = 0 ∧
        (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (3 * p + mu - t) = 0 ∧
        (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (4 * p + mu - t) = 0 ∧
        (-1 : ZMod p) ^ t * (e.choose t : ZMod p) * q (5 * p + mu - t) = 0 := by
      intro t ht
      have htl := Finset.mem_range.mp ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show 2 * p + mu - t = 2 * p + (mu - t) by omega,
          hQ2 (mu - t) (by omega) (by omega), mul_zero]
      · rw [show 3 * p + mu - t = 3 * p + (mu - t) by omega,
          hQ3 (mu - t) (by omega) (by omega), mul_zero]
      · rw [show 4 * p + mu - t = 4 * p + (mu - t) by omega,
          hQ4 (mu - t) (by omega) (by omega), mul_zero]
      · rw [show 5 * p + mu - t = 5 * p + (mu - t) by omega,
          hQ5 (mu - t) (by omega) (by omega), mul_zero]
    rw [Finset.sum_eq_zero (fun t ht => (hz t ht).1)] at f2
    rw [Finset.sum_eq_zero (fun t ht => (hz t ht).2.1)] at f3
    rw [Finset.sum_eq_zero (fun t ht => (hz t ht).2.2.1)] at f4
    rw [Finset.sum_eq_zero (fun t ht => (hz t ht).2.2.2)] at f5
    rw [f6]
    linear_combination y6 + f5 + f4 + f3 + f2 - y1
  have h6 := alt_binom_vanish (fun mu => if mu < m1 then q (6 * p + mu) else 0) e m0 m1
    (by
      intro mu h0 h1
      refine Eq.trans ?_ (hrec mu h0 h1)
      refine Finset.sum_congr rfl fun t ht => ?_
      have htl := Finset.mem_range.mp ht
      simp only [show mu - t < m1 by omega, if_true]
      rw [show 6 * p + mu - t = 6 * p + (mu - t) by omega])
    (by
      intro mu h0 h1
      simp only [show mu < m1 by omega, if_true]
      exact hQ6 mu h0 h1)
  intro mu h0 h1 u
  have hq6 : q (6 * p + mu) = 0 := by
    have := h6 mu h0 h1
    simpa [h1] using this
  have hd2 : d (2 * p + mu) = 0 := by
    have k := D.k6 (2 * p + mu) (by omega)
    rw [if_pos (by omega), show 2 * p + mu - 2 * p = mu by omega, D.d_lo mu (by omega),
      hQ2 mu h0 h1] at k
    have : 2 * d (2 * p + mu) = 0 := by linear_combination -k
    exact (mul_eq_zero.mp this).resolve_left h2
  have hd3 : d (3 * p + mu) = 0 := by
    have k := D.k6 (3 * p + mu) (by omega)
    rw [if_pos (by omega), show 3 * p + mu - 2 * p = p + mu by omega, D.d_lo (p + mu) (by omega),
      hQ3 mu h0 h1] at k
    have : 2 * d (3 * p + mu) = 0 := by linear_combination -k
    exact (mul_eq_zero.mp this).resolve_left h2
  have hd4 : d (4 * p + mu) = 0 := by
    have k := D.k6 (4 * p + mu) (by omega)
    rw [if_pos (by omega), show 4 * p + mu - 2 * p = 2 * p + mu by omega, hd2,
      hQ4 mu h0 h1] at k
    have : 2 * d (4 * p + mu) = 0 := by linear_combination -k
    exact (mul_eq_zero.mp this).resolve_left h2
  have hd5 : d (5 * p + mu) = 0 := by
    have k := D.k6 (5 * p + mu) (by omega)
    rw [if_pos (by omega), show 5 * p + mu - 2 * p = 3 * p + mu by omega, hd3,
      hQ5 mu h0 h1] at k
    have : 2 * d (5 * p + mu) = 0 := by linear_combination -k
    exact (mul_eq_zero.mp this).resolve_left h2
  constructor
  · by_cases hu : 7 ≤ u
    · exact D.q_hi _ (by have := Nat.mul_le_mul_right p hu; omega)
    · interval_cases u
      · exact D.q_lo _ (by omega)
      · exact D.q_lo _ (by omega)
      · exact hQ2 mu h0 h1
      · exact hQ3 mu h0 h1
      · exact hQ4 mu h0 h1
      · exact hQ5 mu h0 h1
      · exact hq6
  · by_cases hu : 6 ≤ u
    · exact D.d_hi _ (by have := Nat.mul_le_mul_right p hu; omega)
    · interval_cases u
      · exact D.d_lo _ (by omega)
      · exact D.d_lo _ (by omega)
      · exact hd2
      · exact hd3
      · exact hd4
      · exact hd5

end
end
end CatalanMeasure.GenD
