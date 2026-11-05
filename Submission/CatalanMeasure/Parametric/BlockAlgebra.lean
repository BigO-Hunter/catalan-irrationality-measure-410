module
public import Submission.CatalanMeasure.Parametric.FilterDigitReduction
@[expose] public section
namespace CatalanMeasure.Parametric
open Matrix
open OAI.InternalCatalan
open scoped BigOperators Kronecker
noncomputable section

def baseB0Residue (P : Parameters) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin P.n0) (Fin P.n0) (ZMod p) :=
  fun r k => baseFilteredContraction P p r.val k

def baseB1Residue (P : Parameters) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin P.n0) (Fin P.n0) (ZMod p) :=
  fun r k => baseFilteredContraction P p (r.val + 1) k

def ResidueBlockMatrix (P : Parameters) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin P.n0) (Fin p × Fin P.n0) (ZMod p) :=
  fun r k => palindromicTransitionMatrix p k.1 r.1 * baseB0Residue P p r.2 k.2 +
    palindromicReversedTransitionMatrix p k.1 r.1 * baseB1Residue P p r.2 k.2

theorem ResidueBlockMatrix_kronecker (P : Parameters) (p : ℕ) [Fact p.Prime] :
    ResidueBlockMatrix P p =
      (palindromicTransitionMatrix p)ᵀ ⊗ₖ baseB0Residue P p +
        (palindromicReversedTransitionMatrix p)ᵀ ⊗ₖ baseB1Residue P p := by
  ext r k
  rfl

def ResidueColumnChange (P : Parameters) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin P.n0) (Fin p × Fin P.n0) (ZMod p) :=
  ((palindromicTransitionMatrix p)ᵀ)⁻¹ ⊗ₖ
    (1 : Matrix (Fin P.n0) (Fin P.n0) (ZMod p))

def ReducedBlockMatrix (P : Parameters) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin P.n0) (Fin p × Fin P.n0) (ZMod p) :=
  (1 : Matrix (Fin p) (Fin p) (ZMod p)) ⊗ₖ baseB0Residue P p +
    (palindromicReversalMatrix p)ᵀ ⊗ₖ baseB1Residue P p

theorem ResidueBlockMatrix_factor (P : Parameters) (p : ℕ) [Fact p.Prime] :
    ResidueBlockMatrix P p = ReducedBlockMatrix P p *
      ((palindromicTransitionMatrix p)ᵀ ⊗ₖ
        (1 : Matrix (Fin P.n0) (Fin P.n0) (ZMod p))) := by
  rw [ResidueBlockMatrix_kronecker P, ReducedBlockMatrix,
    Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    ← palindromicReversedTransitionMatrix_transpose]

theorem ResidueBlockMatrix_mul_columnChange (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    ResidueBlockMatrix P p * ResidueColumnChange P p =
      ReducedBlockMatrix P p := by
  have hu : IsUnit ((palindromicTransitionMatrix p)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (det_palindromicTransitionMatrix_ne_zero hp2)
  rw [ResidueBlockMatrix_factor P, ResidueColumnChange,
    Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul, Matrix.one_kronecker_one, Matrix.mul_one]

theorem det_palindromicResidueColumnChange (P : Parameters) {p : ℕ} [Fact p.Prime] :
    (ResidueColumnChange P p).det =
      ((palindromicTransitionMatrix p).det⁻¹) ^ P.n0 := by
  rw [ResidueColumnChange, Matrix.det_kronecker,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Matrix.det_transpose,
    Matrix.det_one, one_pow, mul_one]
  simp only [Fintype.card_fin]

theorem det_palindromicResidueColumnChange_ne_zero (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (ResidueColumnChange P p).det ≠ 0 := by
  rw [det_palindromicResidueColumnChange]
  exact pow_ne_zero _ (inv_ne_zero (det_palindromicTransitionMatrix_ne_zero hp2))

theorem det_palindromicResidueBlockMatrix (P : Parameters) {p : ℕ} [Fact p.Prime] :
    (ResidueBlockMatrix P p).det =
      (palindromicTransitionMatrix p).det ^ P.n0 *
        (ReducedBlockMatrix P p).det := by
  rw [ResidueBlockMatrix_factor P, Matrix.det_mul, Matrix.det_kronecker,
    Matrix.det_transpose, Matrix.det_one, one_pow, mul_one]
  simpa using mul_comm (ReducedBlockMatrix P p).det
    ((palindromicTransitionMatrix p).det ^ P.n0)

theorem det_palindromicResidueBlockMatrix_ne_zero_iff (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (ResidueBlockMatrix P p).det ≠ 0 ↔
      (ReducedBlockMatrix P p).det ≠ 0 := by
  rw [det_palindromicResidueBlockMatrix]
  exact mul_ne_zero_iff.trans
    (and_iff_right (pow_ne_zero P.n0 (det_palindromicTransitionMatrix_ne_zero hp2)))



open Matrix
open scoped Kronecker

def ReducedBlockRightInverse (P : Parameters) (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin P.n0) (Fin p × Fin P.n0) (ZMod p) :=
  (palindromicReversalProjZero p)ᵀ ⊗ₖ (baseB0Residue P p)⁻¹ +
    (palindromicReversalProjPlus p)ᵀ ⊗ₖ (baseB0Residue P p + baseB1Residue P p)⁻¹ +
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ (baseB0Residue P p - baseB1Residue P p)⁻¹

theorem ReducedBlock_mul_projZero (P : Parameters) {p : ℕ} [Fact p.Prime]
    (h0 : (baseB0Residue P p).det ≠ 0) :
    ReducedBlockMatrix P p *
        ((palindromicReversalProjZero p)ᵀ ⊗ₖ (baseB0Residue P p)⁻¹) =
      (palindromicReversalProjZero p)ᵀ ⊗ₖ
        (1 : Matrix (Fin P.n0) (Fin P.n0) (ZMod p)) := by
  have hp0 : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjZero p)ᵀ = 0 := by
    rw [← Matrix.transpose_mul, palindromicReversalProjZero_mul_matrix, Matrix.transpose_zero]
  rw [ReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hp0, Matrix.zero_kronecker, add_zero,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h0)]

theorem ReducedBlock_mul_projPlus (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hplus : (baseB0Residue P p + baseB1Residue P p).det ≠ 0) :
    ReducedBlockMatrix P p *
        ((palindromicReversalProjPlus p)ᵀ ⊗ₖ
          (baseB0Residue P p + baseB1Residue P p)⁻¹) =
      (palindromicReversalProjPlus p)ᵀ ⊗ₖ
        (1 : Matrix (Fin P.n0) (Fin P.n0) (ZMod p)) := by
  have hpp : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjPlus p)ᵀ =
      (palindromicReversalProjPlus p)ᵀ := by
    rw [← Matrix.transpose_mul, palindromicReversalProjPlus_mul_matrix]
  rw [ReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hpp, ← Matrix.kronecker_add, ← Matrix.add_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hplus)]

theorem ReducedBlock_mul_projMinus (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hminus : (baseB0Residue P p - baseB1Residue P p).det ≠ 0) :
    ReducedBlockMatrix P p *
        ((palindromicReversalProjMinus p)ᵀ ⊗ₖ
          (baseB0Residue P p - baseB1Residue P p)⁻¹) =
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ
        (1 : Matrix (Fin P.n0) (Fin P.n0) (ZMod p)) := by
  have hpm : (palindromicReversalMatrix p)ᵀ * (palindromicReversalProjMinus p)ᵀ =
      -(palindromicReversalProjMinus p)ᵀ := by
    rw [← Matrix.transpose_mul, palindromicReversalProjMinus_mul_matrix, Matrix.transpose_neg]
  rw [ReducedBlockMatrix, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hpm]
  have hcombine (C : Matrix (Fin P.n0) (Fin P.n0) (ZMod p)) :
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ (baseB0Residue P p * C) +
        (-(palindromicReversalProjMinus p)ᵀ) ⊗ₖ (baseB1Residue P p * C) =
      (palindromicReversalProjMinus p)ᵀ ⊗ₖ ((baseB0Residue P p - baseB1Residue P p) * C) := by
    rw [Matrix.sub_mul]
    ext ⟨i, r⟩ ⟨j, k⟩
    simp only [Matrix.add_apply, Matrix.kronecker_apply, Matrix.neg_apply, Matrix.sub_apply]
    ring
  rw [hcombine, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hminus)]

theorem ReducedBlock_mul_rightInverse (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (baseB0Residue P p).det ≠ 0)
    (hplus : (baseB0Residue P p + baseB1Residue P p).det ≠ 0)
    (hminus : (baseB0Residue P p - baseB1Residue P p).det ≠ 0) :
    ReducedBlockMatrix P p * ReducedBlockRightInverse P p = 1 := by
  rw [ReducedBlockRightInverse, Matrix.mul_add, Matrix.mul_add,
    ReducedBlock_mul_projZero P h0, ReducedBlock_mul_projPlus P hplus,
    ReducedBlock_mul_projMinus P hminus,
    ← Matrix.add_kronecker, ← Matrix.add_kronecker,
    ← Matrix.transpose_add, ← Matrix.transpose_add,
    palindromicReversalProjections_sum hp2, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem det_palindromicReducedBlockMatrix_ne_zero_of_fixed (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (baseB0Residue P p).det ≠ 0)
    (hplus : (baseB0Residue P p + baseB1Residue P p).det ≠ 0)
    (hminus : (baseB0Residue P p - baseB1Residue P p).det ≠ 0) :
    (ReducedBlockMatrix P p).det ≠ 0 := by
  have hd := congrArg Matrix.det (ReducedBlock_mul_rightInverse P hp2 h0 hplus hminus)
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact left_ne_zero_of_mul_eq_one hd

theorem det_palindromicResidueBlockMatrix_ne_zero_of_fixed (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h0 : (baseB0Residue P p).det ≠ 0)
    (hplus : (baseB0Residue P p + baseB1Residue P p).det ≠ 0)
    (hminus : (baseB0Residue P p - baseB1Residue P p).det ≠ 0) :
    (ResidueBlockMatrix P p).det ≠ 0 :=
  (det_palindromicResidueBlockMatrix_ne_zero_iff P hp2).mpr
    (det_palindromicReducedBlockMatrix_ne_zero_of_fixed P hp2 h0 hplus hminus)

end
end CatalanMeasure.Parametric
