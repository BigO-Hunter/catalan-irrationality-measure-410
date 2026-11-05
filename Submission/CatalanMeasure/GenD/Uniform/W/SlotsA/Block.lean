module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsA.Seq
public import Submission.CatalanMeasure.GenD.RankU6
@[expose] public section
set_option Elab.async false

/-!
# Theorem A (truncated U6g): the rank bound

For a design `P` and an odd prime `p` with `H < p^2`, `L ≤ 6p`, `b + q ≤ p + mu0`, put
`e = (p+1)/2 - q - h` (truncated at 0), `mu0 = max(q, H+q-6p)`, `mu1 = L-5p`, `ns = 4p+2g+1`,
`δ = n - ns`.  Then the left nullity of the filtered matrix is at least `mu1 - mu0 - e - δ`.
No (H1), no (H2): the rows `r ≥ ns` are killed by `δ` coordinate functionals, and for `q + h > (p+1)/2`
the Frobenius relation holds with `e = 0` (`Seq.digitSeq_neg`).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsA
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD
noncomputable section

/-- The truncation length `ns = min(n, 4p+2g+1)` (rows `r ≥ ns` are dropped). -/
def aNs (P : Parameters) (N p : ℕ) : ℕ := min (P.n N) (4 * p + 2 * P.g N + 1)

/-- The `4w + e + δ` functionals of Theorem A: those of U6g plus `δ` coordinates. -/
def aFam (P : Parameters) (N p m0 w e δ ns : ℕ) [Fact p.Prime] :
    Fin (4 * w + e + δ) → (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p := fun a =>
  if h : a.val < 4 * w + e then uFam P N p m0 w e ⟨a.val, h⟩
  else if h2 : ns + (a.val - (4 * w + e)) < P.n N then
    LinearMap.proj (R := ZMod p) (φ := fun _ : Fin (P.n N) => ZMod p)
      ⟨ns + (a.val - (4 * w + e)), h2⟩
  else 0

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

theorem aFam_low (m0 w e δ ns : ℕ) (a : Fin (4 * w + e + δ)) (h : a.val < 4 * w + e) :
    aFam P N p m0 w e δ ns a = uFam P N p m0 w e ⟨a.val, h⟩ := by
  unfold aFam; rw [dif_pos h]

theorem aFam_high (m0 w e δ ns : ℕ) (a : Fin (4 * w + e + δ)) (h : ¬ a.val < 4 * w + e)
    (h2 : ns + (a.val - (4 * w + e)) < P.n N) (c : Fin (P.n N) → ZMod p) :
    aFam P N p m0 w e δ ns a c = c ⟨ns + (a.val - (4 * w + e)), h2⟩ := by
  unfold aFam; rw [dif_neg h, dif_pos h2]; rfl

/-- **Theorem A, block form.** -/
theorem a_block_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {m0 m1 : ℕ} (hm0q : P.q N ≤ m0) (hm0H : P.H N + P.q N ≤ 6 * p + m0)
    (hH3 : P.b N + P.q N ≤ p + m0) (hm1p : m1 ≤ p) (hm1L : 5 * p + m1 ≤ P.L N)
    (he : m0 + sE P N p ≤ m1) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (m1 - m0 - sE P N p - (P.n N - aNs P N p)) ≤ P.n N := by
  have hgn := two_g_lt_n hP hN
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  have hnsd : aNs P N p = min (P.n N) (4 * p + 2 * P.g N + 1) := rfl
  set ns := aNs P N p with hns
  set w := m1 - m0 with hw
  set e := sE P N p with he'
  set δ := P.n N - ns with hδ
  have hsE : e = (p + 1) / 2 - P.q N - P.h N := rfl
  have hnsn : ns ≤ P.n N := by omega
  have hnsp : ns ≤ 4 * p + 2 * P.g N + 1 := by omega
  have hs : 2 * P.g N + 1 ≤ ns := by omega
  obtain ⟨A, hA⟩ : ∃ A, A + ns = P.C N + P.g N := ⟨P.C N + P.g N - ns, by omega⟩
  have hr := rank_of_digit_block (J0 := 1) (nJ := 5) (m0 := m0) (m1 := m1) hP hN hp2 hH
    hm0q hm1p
    (fun J mu hJ _ h0 h1 => by
      have := Nat.mul_le_mul_right p (show 1 ≤ J by omega)
      omega)
    (fun J mu _ hJ h0 h1 => by
      have := Nat.mul_le_mul_right p (show J ≤ 5 by omega)
      omega)
    (m := 4 * w + e + δ) (aFam P N p m0 w e δ ns) (by
      intro c hc mu h0 h1 u
      have htr : ∀ r : Fin (P.n N), ns ≤ r.val → c r = 0 := by
        intro r hr
        have hlt : 4 * w + e + (r.val - ns) < 4 * w + e + δ := by
          have := r.isLt; omega
        have h := hc ⟨4 * w + e + (r.val - ns), hlt⟩
        rw [aFam_high m0 w e δ ns _ (by simp) (by simp; have := r.isLt; omega)] at h
        simpa [show ns + (r.val - ns) = r.val by omega] using h
      have hfam : ∀ a : Fin (4 * w + e), uFam P N p m0 w e a c = 0 := by
        intro a
        have h := hc ⟨a.val, by omega⟩
        rw [aFam_low m0 w e δ ns _ (by simp)] at h
        exact h
      have hQ2 : ∀ mu', m0 ≤ mu' → mu' < m1 → (qhP P N p c).coeff (2 * p + mu') = 0 := by
        intro mu' h0' h1'
        have := hfam ⟨mu' - m0, by omega⟩
        simp only [uFam, if_pos (show mu' - m0 < w by omega), coeffQ_apply] at this
        rwa [show 2 * p + m0 + (mu' - m0) = 2 * p + mu' by omega] at this
      have hQ3 : ∀ mu', m0 ≤ mu' → mu' < m1 → (qhP P N p c).coeff (3 * p + mu') = 0 := by
        intro mu' h0' h1'
        have := hfam ⟨w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (w + (mu' - m0) < w) by omega),
          if_pos (show w + (mu' - m0) < 2 * w by omega), coeffQ_apply] at this
        rwa [show 3 * p + m0 + (w + (mu' - m0) - w) = 3 * p + mu' by omega] at this
      have hQ4 : ∀ mu', m0 ≤ mu' → mu' < m1 → (qhP P N p c).coeff (4 * p + mu') = 0 := by
        intro mu' h0' h1'
        have := hfam ⟨2 * w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (2 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (2 * w + (mu' - m0) < 2 * w) by omega),
          if_pos (show 2 * w + (mu' - m0) < 3 * w by omega), coeffQ_apply] at this
        rwa [show 4 * p + m0 + (2 * w + (mu' - m0) - 2 * w) = 4 * p + mu' by omega] at this
      have hQ5 : ∀ mu', m0 ≤ mu' → mu' < m1 → (qhP P N p c).coeff (5 * p + mu') = 0 := by
        intro mu' h0' h1'
        have := hfam ⟨3 * w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (3 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (3 * w + (mu' - m0) < 2 * w) by omega),
          if_neg (show ¬ (3 * w + (mu' - m0) < 3 * w) by omega),
          if_pos (show 3 * w + (mu' - m0) < 4 * w by omega), coeffQ_apply] at this
        rwa [show 5 * p + m0 + (3 * w + (mu' - m0) - 3 * w) = 5 * p + mu' by omega] at this
      have hQ6 : ∀ mu', m0 ≤ mu' → mu' < m0 + e → (qhP P N p c).coeff (6 * p + mu') = 0 := by
        intro mu' h0' h1'
        have := hfam ⟨4 * w + (mu' - m0), by omega⟩
        simp only [uFam, if_neg (show ¬ (4 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (4 * w + (mu' - m0) < 2 * w) by omega),
          if_neg (show ¬ (4 * w + (mu' - m0) < 3 * w) by omega),
          if_neg (show ¬ (4 * w + (mu' - m0) < 4 * w) by omega), coeffQ_apply] at this
        rwa [show 6 * p + m0 + (4 * w + (mu' - m0) - 4 * w) = 6 * p + mu' by omega] at this
      by_cases hH1 : P.q N + P.h N ≤ (p + 1) / 2
      · have hseq := digitSeq_pos (P := P) hp2 hgn hH1 hnsn hs hnsp hA c htr
        exact digits_vanish_U6 hseq (two_ne_zero_zmod hp2) (m0 := m0) (m1 := m1) hm1p
          (by omega) (by omega) (by omega) (by omega) (by omega) he hQ2 hQ3 hQ4 hQ5 hQ6 mu h0 h1 u
      · have hseq := digitSeq_neg (P := P) hp2 hgn (by omega) hnsn hs hnsp hA c htr
        have he0 : e = 0 := by omega
        exact digits_vanish_U6 hseq (two_ne_zero_zmod hp2) (m0 := m0) (m1 := m1) hm1p
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hQ2 hQ3 hQ4 hQ5
          (fun mu' _ h1' => absurd h1' (by omega)) mu h0 h1 u)
  omega

/-- **Theorem A (general design).** -/
theorem a_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hL6 : P.L N ≤ 6 * p) (hH3 : P.b N + P.q N ≤ p + uM0 P N p) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (uM1 P N p - uM0 P N p - sE P N p - (P.n N - aNs P N p)) ≤ P.n N := by
  by_cases hnt : uM0 P N p + sE P N p < uM1 P N p
  · have h0 : uM0 P N p = max (P.q N) (P.H N + P.q N - 6 * p) := rfl
    have h1 : uM1 P N p = P.L N - 5 * p := rfl
    exact a_block_rank hP hN hp2 hH (m0 := uM0 P N p) (m1 := uM1 P N p)
      (by omega) (by omega) hH3 (by omega) (by omega) hnt.le
  · have := Matrix.rank_le_width (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val))
    omega

end
end
end CatalanMeasure.GenD.Uniform.W.SlotsA
