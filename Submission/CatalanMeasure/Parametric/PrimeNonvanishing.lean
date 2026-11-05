module
public import Mathlib.Logic.Equiv.Fin.Basic
public import Submission.CatalanMeasure.Parametric.BlockAlgebra
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedDeterminantGoodPrimes
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix
open OAI.InternalCatalan
noncomputable section

def residueIndexEquiv (P : Parameters) (p : ℕ) : Fin p × Fin P.n0 ≃ Fin (P.n p) :=
  (Equiv.prodComm (Fin p) (Fin P.n0)).trans finProdFinEquiv

theorem residueIndexEquiv_val (P : Parameters) (p : ℕ) (r : Fin p × Fin P.n0) :
    (residueIndexEquiv P p r).val = r.1.val + p * r.2.val := rfl

def scaledRatMatrix (P : Parameters) (z : ℚ) (p : ℕ) :
    Matrix (Fin p × Fin P.n0) (Fin p × Fin P.n0) ℚ :=
  fun r k => (p : ℚ) ^ 2 * filteredEntryRat P z p
    (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)

theorem scaledRatMatrix_eq_submatrix (P : Parameters) (z : ℚ) (p : ℕ) :
    scaledRatMatrix P z p =
      (((p : ℚ) ^ 2) •
        Matrix.of (fun r k : Fin (P.n p) => filteredEntryRat P z p r.val k.val)).submatrix
          (residueIndexEquiv P p) (residueIndexEquiv P p) := by
  ext r k
  change (p : ℚ) ^ 2 * filteredEntryRat P z p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val) =
    (p : ℚ) ^ 2 * filteredEntryRat P z p
      (r.1.val + p * r.2.val) (k.1.val + p * k.2.val)
  rw [Nat.add_comm (p * r.2.val) r.1.val]

theorem det_scaledRatMatrix (P : Parameters) (z : ℚ) (p : ℕ) :
    (scaledRatMatrix P z p).det = (p : ℚ) ^ (2 * P.n p) * determinantRat P z p := by
  rw [scaledRatMatrix_eq_submatrix, Matrix.det_submatrix_equiv_self, Matrix.det_smul]
  simp only [Fintype.card_fin, ← pow_mul, determinantRat]
  rfl

theorem scaledRatMatrix_entry_den (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) (hpH : P.H 1 < p)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0)
    (r k : Fin p × Fin P.n0) :
    ((scaledRatMatrix P z p r k).den : ZMod p) ≠ 0 :=
  (filtered_block_reduction P hP hp2 hpH r.2 r.1 k.1 k.2 z hzp).1

theorem scaledRatMatrix_residue_eq_blocks (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) (hpH : P.H 1 < p)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) :
    (fun r k => palindromicRatResidue p (scaledRatMatrix P z p r k)) = ResidueBlockMatrix P p := by
  ext r k
  rw [show palindromicRatResidue p (scaledRatMatrix P z p r k) =
      extractedFilteredEntry P p r.2 r.1 k.1 k.2 from
        (filtered_block_reduction P hP hp2 hpH r.2 r.1 k.1 k.2 z hzp).2,
    extractedFilteredEntry_factor P hP hp2]
  rfl

/-- The uniform prime theorem, with the three finite base certificates exposed as hypotheses. -/
theorem determinantRat_ne_zero_of_base_residues (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) (hpH : P.H 1 < p)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0)
    (h0 : (baseB0Residue P p).det ≠ 0)
    (hplus : (baseB0Residue P p + baseB1Residue P p).det ≠ 0)
    (hminus : (baseB0Residue P p - baseB1Residue P p).det ≠ 0) :
    determinantRat P z p ≠ 0 := by
  have hscaled := rational_det_ne_zero_of_residue_det_ne_zero (scaledRatMatrix P z p)
    (scaledRatMatrix_entry_den P hP hp2 hpH z hzp) (by
      rw [scaledRatMatrix_residue_eq_blocks P hP hp2 hpH z hzp]
      exact CatalanMeasure.Parametric.det_palindromicResidueBlockMatrix_ne_zero_of_fixed P hp2 h0 hplus hminus)
  rw [det_scaledRatMatrix] at hscaled
  exact (mul_ne_zero_iff.mp hscaled).2

end
end CatalanMeasure.Parametric
