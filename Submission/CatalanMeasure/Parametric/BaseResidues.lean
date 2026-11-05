module
public import Submission.CatalanMeasure.Parametric.Contractions
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem three_halves_den {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (((3 / 2 : ℚ).den : ℕ) : ZMod p) ≠ 0 := by
  have hp : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) hp) hdiv
  simpa only [show (3 / 2 : ℚ).den = 2 by norm_num, Nat.cast_ofNat] using htwo

theorem rawEntryRat_zero (P : Parameters) (N r j : ℕ) :
    rawEntryRat P 0 N r j =
      (∑ i ∈ Finset.range (P.H N), ((rowP P N r).coeff i : ℚ) * momentRat i j) -
      (3 / 2 : ℚ) * ∑ i ∈ Finset.range (P.H N), ((rowD P N r).coeff i : ℚ) * zetaRat i j := by
  simp [rawEntryRat]

theorem baseRawEntry_den {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H 1 ≤ p) (r j : ℕ) (hj : j < p) :
    ((rawEntryRat P 0 1 r j).den : ZMod p) ≠ 0 := by
  have hM : ∀ i ∈ Finset.range (P.H 1),
      (((((rowP P 1 r).coeff i : ℚ) * momentRat i j)).den : ZMod p) ≠ 0 := by
    intro i hi
    apply (rational_residue_mul (by simp) ?_).1
    exact momentRat_odd_prime_small_den_ne_zero hp2
      (by have := Finset.mem_range.mp hi; omega) hj
  have hZ : ∀ i ∈ Finset.range (P.H 1),
      (((((rowD P 1 r).coeff i : ℚ) * zetaRat i j)).den : ZMod p) ≠ 0 := by
    intro i hi
    apply (rational_residue_mul (by simp) ?_).1
    exact zetaRat_small_den_ne_zero (by have := Finset.mem_range.mp hi; omega) hj
  rw [rawEntryRat_zero]
  exact (rational_residue_sub (rational_residue_sum _ _ hM).1
    (rational_residue_mul (three_halves_den hp2) (rational_residue_sum _ _ hZ).1).1).1

theorem baseRawContraction_eq_residue {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H 1 ≤ p) (r j : ℕ) (hj : j < p) :
    baseRawContraction P p r j = palindromicRatResidue p (rawEntryRat P 0 1 r j) := by
  have hM := palindromicRatResidue_int_sum (p := p) (Finset.range (P.H 1))
    (fun i => (rowP P 1 r).coeff i) (fun i => momentRat i j) (by
      intro i hi
      exact momentRat_odd_prime_small_den_ne_zero hp2 (by have := Finset.mem_range.mp hi; omega) hj)
  have hZ := palindromicRatResidue_int_sum (p := p) (Finset.range (P.H 1))
    (fun i => (rowD P 1 r).coeff i) (fun i => zetaRat i j) (by
      intro i hi
      exact zetaRat_small_den_ne_zero (by have := Finset.mem_range.mp hi; omega) hj)
  symm
  rw [rawEntryRat_zero, palindromicRatResidue_sub hM.1
      (rational_residue_mul (three_halves_den hp2) hZ.1).1,
    palindromicRatResidue_mul (three_halves_den hp2) hZ.1, hM.2, hZ.2]
  have hthree : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := by
    norm_num [palindromicRatResidue]
  rw [hthree]
  rfl

theorem filterCoeff_den (P : Parameters) {p : ℕ} [Fact p.Prime] (N v : ℕ) :
    ((filterCoeffRat P N v).den : ZMod p) ≠ 0 := by
  have hcast : (((-1 : ℤ) ^ v * ((P.q N).choose v : ℤ) : ℤ) : ℚ) =
      filterCoeffRat P N v := by simp [filterCoeffRat]
  rw [← hcast, Rat.den_intCast, Nat.cast_one]
  exact one_ne_zero

theorem filterCoeff_residue (P : Parameters) (p N v : ℕ) [Fact p.Prime] :
    palindromicRatResidue p (filterCoeffRat P N v) =
      (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) := by
  simpa [filterCoeffRat] using palindromicRatResidue_intCast p
    ((-1 : ℤ) ^ v * ((P.q N).choose v : ℤ))

theorem baseFilteredContraction_eq_residue {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H 1 ≤ p) (r : ℕ) (k : Fin P.n0) :
    baseFilteredContraction P p r k = palindromicRatResidue p (filteredEntryRat P 0 1 r k.val) := by
  have hL : P.n0 + P.b0 + P.q0 ≤ p := by
    simpa only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
      Parameters.q, Parameters.g, Parameters.h, Nat.mul_one] using
      (show P.L 1 ≤ p from le_trans (by unfold Parameters.H Parameters.C; omega) hH)
  have hraw : ∀ v ∈ Finset.range (P.q 1 + 1),
      ((rawEntryRat P 0 1 r (P.b 1 + k.val + v)).den : ZMod p) ≠ 0 := by
    intro v hv
    apply baseRawEntry_den hp2 hH
    have hk := k.isLt
    have hv' := Finset.mem_range.mp hv
    simp only [Parameters.q, Parameters.b, Nat.mul_one] at hv' ⊢
    omega
  symm
  unfold filteredEntryRat
  rw [palindromicRatResidue_sum _ _ (fun v hv =>
    (rational_residue_mul (filterCoeff_den P 1 v) (hraw v hv)).1)]
  simp only [baseFilteredContraction, baseFilterWeight, Parameters.q, Parameters.b, Nat.mul_one]
  apply Finset.sum_congr rfl
  intro v hv
  have hr0 := hraw v (by simpa only [Parameters.q, Nat.mul_one] using hv)
  simp only [Parameters.b, Nat.mul_one] at hr0
  rw [palindromicRatResidue_mul (filterCoeff_den P 1 v) hr0, filterCoeff_residue]
  simp only [Parameters.q, Nat.mul_one]
  rw [baseRawContraction_eq_residue hp2 hH r (P.b0 + k.val + v) (by
    have hk := k.isLt; have hv' := Finset.mem_range.mp hv; omega)]

end
end CatalanMeasure.Parametric
