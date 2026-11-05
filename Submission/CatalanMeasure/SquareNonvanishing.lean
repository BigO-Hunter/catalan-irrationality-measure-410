module
public import Submission.CatalanMeasure.Nonvanishing
public import Submission.CatalanMeasure.DeltaPoly
@[expose] public section
open Finset Polynomial Matrix
open scoped BigOperators
namespace OAI.InternalCatalan
/-! The scaled matrix has the same residue as at zero whenever p*z has p-unit denominator. -/
theorem filteredCatalanCoeff_den {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (N r k : ℕ) :
    ((filteredCatalanCoeffRat N r k).den : ZMod p) ≠ 0 := by
  unfold filteredCatalanCoeffRat
  apply (rational_residue_sum (p := p) _ _ ?_).1
  intro v _
  exact (rational_residue_mul (filterCoeffRat_prime_den_ne_zero (p := p) N v)
    (rawCatalanCoeffRat_odd_prime_den_ne_zero hp2 N r (b N + k + v))).1

theorem scaledCatalanCoeff_reduction {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) (N r k : ℕ) :
    (((p : ℚ)^2 * z * filteredCatalanCoeffRat N r k).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ)^2 * z * filteredCatalanCoeffRat N r k) = 0 := by
  have hz := rational_residue_mul (a := (p : ℚ)) (b := (p : ℚ) * z) (by simp) hzp
  have hf := rational_residue_mul hz.1 (filteredCatalanCoeff_den hp2 N r k)
  have he : (p : ℚ) * ((p : ℚ) * z) * filteredCatalanCoeffRat N r k =
      (p : ℚ)^2 * z * filteredCatalanCoeffRat N r k := by ring
  rw [← he]
  refine ⟨hf.1, ?_⟩
  unfold palindromicRatResidue
  rw [hf.2, hz.2]
  simp

theorem palindromic_scaled_residue_transfer {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0)
    (r k : Fin p × Fin 48) :
    ((palindromicScaledRatMatrix z p r k).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (palindromicScaledRatMatrix z p r k) =
        palindromicRatResidue p (palindromicScaledRatMatrix 0 p r k) := by
  have hp2 : p ≠ 2 := by omega
  have hbase := palindromicScaledRatMatrix_entry_den_ne_zero hp (0 : ℚ) (by norm_num) r k
  have hterm := scaledCatalanCoeff_reduction hp2 z hzp p
    (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)
  have he : palindromicScaledRatMatrix z p r k =
      palindromicScaledRatMatrix 0 p r k +
      (p : ℚ)^2 * z * filteredCatalanCoeffRat p
        (p * r.2.val + r.1.val) (k.1.val + p * k.2.val) := by
    unfold palindromicScaledRatMatrix
    rw [filteredEntryRat_affine]
    ring
  rw [he]
  have ha := rational_residue_add hbase hterm.1
  refine ⟨ha.1, ?_⟩
  change ((palindromicScaledRatMatrix 0 p r k +
    (p : ℚ)^2 * z * filteredCatalanCoeffRat p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)).num : ZMod p) /
      ((palindromicScaledRatMatrix 0 p r k +
    (p : ℚ)^2 * z * filteredCatalanCoeffRat p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)).den : ZMod p) = _
  rw [ha.2]
  change palindromicRatResidue p (palindromicScaledRatMatrix 0 p r k) +
    palindromicRatResidue p ((p : ℚ)^2 * z * filteredCatalanCoeffRat p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)) = _
  rw [hterm.2, add_zero]

theorem determinantRat_prime_ne_zero_of_pmul_den {z : ℚ} {p : ℕ} [Fact p.Prime]
    (hp : fixedDeterminantPrimeCutoff < p) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) :
    determinantRat z p ≠ 0 := by
  have hp260 : 260 < p := lt_of_le_of_lt fixedDeterminantPrimeCutoff_ge_260 hp
  have hs := palindromic_scaled_residue_transfer hp260 z hzp
  apply determinantRat_ne_zero_of_scaledResidueMatrix z (fun r k => (hs r k).1)
  have hm : palindromicScaledResidueMatrix z p = palindromicScaledResidueMatrix 0 p := by
    ext r k
    exact (hs r k).2
  rw [hm, palindromicScaledResidueMatrix_eq_extracted hp260 (0 : ℚ) (by norm_num)]
  have hdet := fixedDeterminants_mod_prime_ne_zero_of_lt fixedMatrix_zero_det_ne_zero
    fixedMatrix_one_det_ne_zero fixedMatrix_neg_one_det_ne_zero hp
  exact det_palindromicExtractedResidueMatrix_ne_zero_of_fixed hp260 hdet.1 hdet.2.1 hdet.2.2

theorem rat_div_den_unit {p : ℕ} [Fact p.Prime] (a : ℤ) {b : ℕ} (hpb : ¬ p ∣ b) :
    ((((a : ℚ) / b).den : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hden : ((a : ℚ) / b).den ∣ b := by
    have h := Rat.den_dvd a (b : ℤ)
    rw [Rat.divInt_eq_div] at h
    push_cast at h
    exact_mod_cast h
  exact hpb (dvd_trans ((ZMod.natCast_eq_zero_iff _ p).mp hzero) hden)

theorem prime_mul_div_den_unit {p : ℕ} [hpPrime : Fact p.Prime] (a : ℤ)
    {b : ℕ} (hb : 0 < b) (hpb : ¬ p^2 ∣ b) :
    (((p : ℚ) * ((a : ℚ)/b)).den : ZMod p) ≠ 0 := by
  by_cases hd : p ∣ b
  · let c : ℕ := b / p
    have hbc : b = p * c := (Nat.mul_div_cancel' hd).symm
    have hc0 : c ≠ 0 := by intro he; rw [he, mul_zero] at hbc; omega
    have hpc : ¬ p ∣ c := by
      rintro ⟨d, hd⟩
      apply hpb
      refine ⟨d, ?_⟩
      rw [hbc, hd, pow_two]
      ring
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hbcq : (b : ℚ) = (p : ℚ) * c := by exact_mod_cast hbc
    have he : (p : ℚ) * ((a : ℚ)/b) = (a : ℚ)/c := by
      rw [hbcq]
      field_simp
    rw [he]
    exact rat_div_den_unit a hpc
  · exact (rational_residue_mul (a := (p : ℚ)) (by simp)
      (rat_div_den_unit a hd)).1

theorem determinantRat_div_ne_zero_of_not_square_dvd {p : ℕ} [Fact p.Prime]
    (hp : fixedDeterminantPrimeCutoff < p) (a : ℤ) {b : ℕ} (hb : 0 < b)
    (hpb : ¬ p^2 ∣ b) : determinantRat ((a : ℚ)/b) p ≠ 0 := by
  exact determinantRat_prime_ne_zero_of_pmul_den hp (prime_mul_div_den_unit a hb hpb)

end OAI.InternalCatalan
