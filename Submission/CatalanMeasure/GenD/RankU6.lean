module
public import Submission.CatalanMeasure.GenD.RankS
@[expose] public section

/-!
# Theorem U6g for a general design (GenD)

For `P : Parameters`, `N > 0`, an odd prime `p` with `H < p^2`, (H1) `q + h ≤ (p+1)/2`,
(H2) `n ≤ 4p + 2g + 1`, `L ≤ 6p` and (H3) `b + q ≤ p + mu0`, put `e = (p+1)/2 - q - h`,
`mu0 = max(q, H + q - 6p)`, `mu1 = L - 5p`.  Then the left nullity of the filtered matrix is at
least `mu1 - mu0 - e`, that is `min((p-1)/2 - g, n+b+q+h - (11p+1)/2)` (truncated at zero).
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

/-- Lower residue bound `max(q, H+q-6p)`. -/
def uM0 (P : Parameters) (N p : ℕ) : ℕ := max (P.q N) (P.H N + P.q N - 6 * p)

/-- Upper residue bound `L - 5p`. -/
def uM1 (P : Parameters) (N p : ℕ) : ℕ := P.L N - 5 * p

/-- The `4w + e` functionals of Theorem U6g (all on `Qh`). -/
def uFam (P : Parameters) (N p m0 w e : ℕ) [Fact p.Prime] :
    Fin (4 * w + e) → (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p := fun a =>
  if a.val < w then coeffQ P N p (2 * p + m0 + a.val)
  else if a.val < 2 * w then coeffQ P N p (3 * p + m0 + (a.val - w))
  else if a.val < 3 * w then coeffQ P N p (4 * p + m0 + (a.val - 2 * w))
  else if a.val < 4 * w then coeffQ P N p (5 * p + m0 + (a.val - 3 * w))
  else coeffQ P N p (6 * p + m0 + (a.val - 4 * w))

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- **Theorem U6g, block form.** -/
theorem u6_block_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1)
    {m0 m1 : ℕ} (hm0q : P.q N ≤ m0) (hm0H : P.H N + P.q N ≤ 6 * p + m0)
    (hH3 : P.b N + P.q N ≤ p + m0) (hm1p : m1 ≤ p) (hm1L : 5 * p + m1 ≤ P.L N)
    (he : m0 + sE P N p ≤ m1) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (m1 - m0 - sE P N p) ≤ P.n N := by
  have hgn := two_g_lt_n hP hN
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  set w := m1 - m0 with hw
  set e := sE P N p with he'
  have hsE : e = (p + 1) / 2 - P.q N - P.h N := rfl
  have hr := rank_of_digit_block (J0 := 1) (nJ := 5) (m0 := m0) (m1 := m1) hP hN hp2 hH
    hm0q hm1p
    (fun J mu hJ _ h0 h1 => by
      have := Nat.mul_le_mul_right p (show 1 ≤ J by omega)
      omega)
    (fun J mu _ hJ h0 h1 => by
      have := Nat.mul_le_mul_right p (show J ≤ 5 by omega)
      omega)
    (m := 4 * w + e) (uFam P N p m0 w e) (by
      intro c hc mu h0 h1 u
      have hseq := digitSeq_design (P := P) hp2 hgn hH1 hH2 c
      have hfam : ∀ a : Fin (4 * w + e), uFam P N p m0 w e a c = 0 := hc
      refine digits_vanish_U6 hseq (two_ne_zero_zmod hp2) (m0 := m0) (m1 := m1) hm1p
        (by omega) (by omega) (by omega) (by omega) (by omega) he ?_ ?_ ?_ ?_ ?_ mu h0 h1 u
      · intro mu' h0' h1'
        have := hfam ⟨mu' - m0, by omega⟩
        simp only [uFam, if_pos (show mu' - m0 < w by omega), coeffQ_apply] at this
        rwa [show 2 * p + m0 + (mu' - m0) = 2 * p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (w + (mu' - m0) < w) by omega),
          if_pos (show w + (mu' - m0) < 2 * w by omega), coeffQ_apply] at this
        rwa [show 3 * p + m0 + (w + (mu' - m0) - w) = 3 * p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨2 * w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (2 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (2 * w + (mu' - m0) < 2 * w) by omega),
          if_pos (show 2 * w + (mu' - m0) < 3 * w by omega), coeffQ_apply] at this
        rwa [show 4 * p + m0 + (2 * w + (mu' - m0) - 2 * w) = 4 * p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨3 * w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (3 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (3 * w + (mu' - m0) < 2 * w) by omega),
          if_neg (show ¬ (3 * w + (mu' - m0) < 3 * w) by omega),
          if_pos (show 3 * w + (mu' - m0) < 4 * w by omega), coeffQ_apply] at this
        rwa [show 5 * p + m0 + (3 * w + (mu' - m0) - 3 * w) = 5 * p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨4 * w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (4 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (4 * w + (mu' - m0) < 2 * w) by omega),
          if_neg (show ¬ (4 * w + (mu' - m0) < 3 * w) by omega),
          if_neg (show ¬ (4 * w + (mu' - m0) < 4 * w) by omega), coeffQ_apply] at this
        rwa [show 6 * p + m0 + (4 * w + (mu' - m0) - 4 * w) = 6 * p + mu' by omega] at this)
  omega

/-- **Theorem U6g (general design).** -/
theorem u6_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1)
    (hL6 : P.L N ≤ 6 * p) (hH3 : P.b N + P.q N ≤ p + uM0 P N p) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (uM1 P N p - uM0 P N p - sE P N p) ≤ P.n N := by
  by_cases hnt : uM0 P N p + sE P N p < uM1 P N p
  · have h0 : uM0 P N p = max (P.q N) (P.H N + P.q N - 6 * p) := rfl
    have h1 : uM1 P N p = P.L N - 5 * p := rfl
    exact u6_block_rank hP hN hp2 hH hH1 hH2 (m0 := uM0 P N p) (m1 := uM1 P N p)
      (by omega) (by omega) hH3 (by omega) (by omega) hnt.le
  · have := Matrix.rank_le_width (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val))
    omega

/-- Closed form: `min((p-1)/2 - g, n+b+q+h - (11p+1)/2)`. -/
theorem u6_rank_closed (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1)
    (hL6 : P.L N ≤ 6 * p) (hH3 : P.b N + P.q N ≤ p + uM0 P N p) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        min ((p - 1) / 2 - P.g N) (P.n N + P.b N + P.q N + P.h N - (11 * p + 1) / 2) ≤
          P.n N := by
  have h := u6_rank hP hN hp2 hH hH1 hH2 hL6 hH3
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  have h0 : uM0 P N p = max (P.q N) (P.H N + P.q N - 6 * p) := rfl
  have h1 : uM1 P N p = P.L N - 5 * p := rfl
  have h2 : sE P N p = (p + 1) / 2 - P.q N - P.h N := rfl
  omega

end
end
end CatalanMeasure.GenD
