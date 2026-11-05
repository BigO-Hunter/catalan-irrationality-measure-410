module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseWindow
@[expose] public section
set_option Elab.async false

/-!
# Response of a monomial slot (shared step for the thin-window families)

A slot polynomial `X^e * G(X^p)` has its coefficient at index `i` equal to a single coefficient
of `G` when `p ∣ i - e`, and `0` otherwise (`intrinsicCoeff_monomial_expand`).  Hence the raw
residue response (formula (R)) of a pair `(X^e G(X^p), X^e T(X^p))` is one source covector
`digitPhi` (`intrinsicResponse_monomial`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open Polynomial CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem intrinsicCoeff_monomial_expand (e : ℕ) (G : (ZMod p)[X]) (i : ℤ) :
    intrinsicCoeff (X ^ e * G.comp (X ^ p)) i =
      if (p : ℤ) ∣ i - e then intrinsicCoeff G ((i - e) / p) else 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hc : G.comp (X ^ p) = Polynomial.expand (ZMod p) p G := by
    rw [Polynomial.expand_eq_comp_X_pow]
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [intrinsicCoeff_nat, hc, Polynomial.coeff_X_pow_mul', Polynomial.coeff_expand hp0]
    by_cases hen : e ≤ n
    · have hd : ((n : ℤ) - e) = ((n - e : ℕ) : ℤ) := by omega
      rw [if_pos hen, hd]
      by_cases hdv : p ∣ n - e
      · rw [if_pos hdv, if_pos (Int.natCast_dvd_natCast.mpr hdv)]
        rw [show ((n - e : ℕ) : ℤ) / (p : ℤ) = ((n - e) / p : ℕ) by push_cast; rfl]
        rw [intrinsicCoeff_nat]
      · rw [if_neg hdv, if_neg (fun h => hdv (Int.natCast_dvd_natCast.mp h))]
    · rw [if_neg hen]
      by_cases hdv : (p : ℤ) ∣ (n : ℤ) - e
      · rw [if_pos hdv]
        have : ((n : ℤ) - e) / p < 0 := Int.ediv_neg_of_neg_of_pos (by omega) (by exact_mod_cast hp0)
        simp [intrinsicCoeff, not_le.mpr this]
      · rw [if_neg hdv]
  · have hneg : i < 0 := by omega
    have h0 : intrinsicCoeff (X ^ e * G.comp (X ^ p)) i = 0 := by simp [intrinsicCoeff, hi]
    rw [h0]
    by_cases hdv : (p : ℤ) ∣ i - e
    · rw [if_pos hdv]
      have : (i - e) / p < 0 := Int.ediv_neg_of_neg_of_pos (by omega) (by exact_mod_cast hp0)
      simp [intrinsicCoeff, not_le.mpr this]
    · rw [if_neg hdv]

/-- **Monomial slot.** -/
theorem intrinsicResponse_monomial (H J ell e : ℕ) (G T : (ZMod p)[X]) :
    intrinsicResponse H J ell (X ^ e * G.comp (X ^ p)) (X ^ e * T.comp (X ^ p)) =
      if (p : ℤ) ∣ (H : ℤ) - 1 - ell - e then
        digitPhi H (((H : ℤ) - 1 - ell - e) / p) (sourceM (p := p) J) (sourceZ (p := p) J) G T (3 / 2)
      else 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold intrinsicResponse
  simp_rw [intrinsicCoeff_monomial_expand]
  by_cases hd : (p : ℤ) ∣ (H : ℤ) - 1 - ell - e
  · rw [if_pos hd]
    obtain ⟨a, ha⟩ := hd
    have hdiv : ((H : ℤ) - 1 - ell - e) / p = a := by rw [ha]; exact Int.mul_ediv_cancel_left _ hp0
    rw [hdiv]
    unfold digitPhi
    have h1 : ∀ v : ℕ, ((H : ℤ) - 1 - ell - ((v : ℤ) - 1) * p - e) = (a + 1 - v) * p := by
      intro v; linarith
    have h2 : ∀ v : ℕ, ((H : ℤ) - 1 - ell - (v : ℤ) * p - e) = (a - v) * p := by
      intro v; linarith
    have e1 : ∀ v : ℕ, (p : ℤ) ∣ ((H : ℤ) - 1 - ell - ((v : ℤ) - 1) * p - e) := by
      intro v; rw [h1]; exact dvd_mul_left _ _
    have e2 : ∀ v : ℕ, (p : ℤ) ∣ ((H : ℤ) - 1 - ell - (v : ℤ) * p - e) := by
      intro v; rw [h2]; exact dvd_mul_left _ _
    simp_rw [if_pos (e1 _), if_pos (e2 _), h1, h2, Int.mul_ediv_cancel _ hp0]
  · rw [if_neg hd]
    have e1 : ∀ v : ℕ, ¬ (p : ℤ) ∣ ((H : ℤ) - 1 - ell - ((v : ℤ) - 1) * p - e) := by
      intro v hv; apply hd
      have : (H : ℤ) - 1 - ell - e = ((H : ℤ) - 1 - ell - ((v : ℤ) - 1) * p - e) + ((v : ℤ) - 1) * p := by ring
      rw [this]; exact dvd_add hv (dvd_mul_left _ _)
    have e2 : ∀ v : ℕ, ¬ (p : ℤ) ∣ ((H : ℤ) - 1 - ell - (v : ℤ) * p - e) := by
      intro v hv; apply hd
      have : (H : ℤ) - 1 - ell - e = ((H : ℤ) - 1 - ell - (v : ℤ) * p - e) + (v : ℤ) * p := by ring
      rw [this]; exact dvd_add hv (dvd_mul_left _ _)
    simp [if_neg (e1 _), if_neg (e2 _)]

#print axioms intrinsicResponse_monomial
end
end CatalanMeasure.GenD.Uniform.W.Thin
