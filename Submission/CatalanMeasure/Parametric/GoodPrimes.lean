module
public import Submission.CatalanMeasure.Parametric.PrimeNonvanishing
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix
open OAI.InternalCatalan
noncomputable section

def baseMatrixRat (P : Parameters) (sigma : ℤ) : Matrix (Fin P.n0) (Fin P.n0) ℚ :=
  fun r k => filteredEntryRat P 0 1 r.val k.val +
    (sigma : ℚ) * filteredEntryRat P 0 1 (r.val+1) k.val

theorem baseFilteredEntry_den {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H 1 ≤ p) (r : ℕ) (k : Fin P.n0) :
    ((filteredEntryRat P 0 1 r k.val).den : ZMod p) ≠ 0 := by
  have hL : P.L 1 ≤ p := le_trans (by unfold Parameters.H Parameters.C; omega) hH
  unfold filteredEntryRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  apply (rational_residue_mul (filterCoeff_den P 1 v) ?_).1
  apply baseRawEntry_den hp2 hH
  have hk := k.isLt
  have hv' := Finset.mem_range.mp hv
  simp only [Parameters.L, Parameters.n, Parameters.b, Parameters.q, Nat.mul_one] at hL hv' ⊢
  omega

theorem baseMatrix_det_residue {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hH : P.H 1 ≤ p) (sigma : ℤ) :
    palindromicRatResidue p (baseMatrixRat P sigma).det =
      (baseB0Residue P p + (sigma : ZMod p) • baseB1Residue P p).det := by
  have h0 := baseFilteredEntry_den hp2 hH
  have hentry (r k : Fin P.n0) : ((baseMatrixRat P sigma r k).den : ZMod p) ≠ 0 :=
    (rational_residue_add (h0 r.val k)
      (rational_residue_mul (a := (sigma : ℚ)) (by simp) (h0 (r.val+1) k)).1).1
  have hdet := (palindromicRatResidue_det (baseMatrixRat P sigma) hentry).2
  rw [hdet]
  congr 1
  ext r k
  simp only [baseMatrixRat, baseB0Residue, baseB1Residue, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [palindromicRatResidue_add (h0 r.val k)
      (rational_residue_mul (a := (sigma : ℚ)) (by simp) (h0 (r.val+1) k)).1,
    palindromicRatResidue_mul (a := (sigma : ℚ)) (by simp) (h0 (r.val+1) k),
    palindromicRatResidue_intCast,
    ← baseFilteredContraction_eq_residue hp2 hH r.val k,
    ← baseFilteredContraction_eq_residue hp2 hH (r.val+1) k]

def finitePrimeCutoff (P : Parameters) : ℕ :=
  max (P.H 1 + 2) (max
    ((baseMatrixRat P 0).det.num.natAbs + (baseMatrixRat P 0).det.den)
    (max ((baseMatrixRat P 1).det.num.natAbs + (baseMatrixRat P 1).det.den)
      ((baseMatrixRat P (-1)).det.num.natAbs + (baseMatrixRat P (-1)).det.den)))

theorem base_residue_determinants_nonzero {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp : finitePrimeCutoff P < p)
    (h0 : (baseMatrixRat P 0).det ≠ 0)
    (hplus : (baseMatrixRat P 1).det ≠ 0)
    (hminus : (baseMatrixRat P (-1)).det ≠ 0) :
    (baseB0Residue P p).det ≠ 0 ∧
      (baseB0Residue P p + baseB1Residue P p).det ≠ 0 ∧
      (baseB0Residue P p - baseB1Residue P p).det ≠ 0 := by
  have hbound := hp
  unfold finitePrimeCutoff at hbound
  have hp2 : p ≠ 2 := by omega
  have hH : P.H 1 ≤ p := by omega
  have hz := palindromicRatResidue_ne_zero_of_bounds (p := p) (baseMatrixRat P 0).det h0 (by omega) (by omega)
  have hpos := palindromicRatResidue_ne_zero_of_bounds (p := p) (baseMatrixRat P 1).det hplus (by omega) (by omega)
  have hneg := palindromicRatResidue_ne_zero_of_bounds (p := p) (baseMatrixRat P (-1)).det hminus (by omega) (by omega)
  rw [baseMatrix_det_residue hp2 hH] at hz hpos hneg
  simpa only [Int.cast_zero, zero_smul, add_zero, Int.cast_one, one_smul,
    Int.cast_neg, neg_smul, sub_eq_add_neg] using And.intro hz (And.intro hpos hneg)

/-- Three finite rational certificates suffice for every prime beyond one fixed cutoff. -/
theorem determinantRat_prime_ne_zero (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp : finitePrimeCutoff P < p)
    (h0 : (baseMatrixRat P 0).det ≠ 0)
    (hplus : (baseMatrixRat P 1).det ≠ 0)
    (hminus : (baseMatrixRat P (-1)).det ≠ 0)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) : determinantRat P z p ≠ 0 := by
  have hbound := hp
  unfold finitePrimeCutoff at hbound
  have hp2 : p ≠ 2 := by omega
  have hH : P.H 1 < p := by omega
  have hs := base_residue_determinants_nonzero hp h0 hplus hminus
  exact determinantRat_ne_zero_of_base_residues P hP hp2 hH z hzp hs.1 hs.2.1 hs.2.2

end
end CatalanMeasure.Parametric
