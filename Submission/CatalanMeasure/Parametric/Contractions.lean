module
public import Submission.CatalanMeasure.Parametric.CoefficientBounds
public import Submission.OAI.NumberTheory.Catalan.Estimates.PalindromicBlockInverse
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open OAI.InternalCatalan
open scoped BigOperators
noncomputable section
theorem ZModIntCast_apply (p : ℕ) (z : ℤ) :
    (Int.castRingHom (ZMod p)) z = (z : ZMod p) := rfl

theorem actual_P_extraction (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < P.n0) (i ell : Fin p) (u : ℕ) :
    (X * (rowP P p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val) =
      palindromicTransitionMatrix p ell i * ((rowP P 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowP P 1 (r0 + 1)).coeff u : ZMod p) := by
  have h := PResidueSum_coeff P p r0 u i ell
  rw [← rowP_frobenius P hP hp2 hr i] at h
  simpa only [PBase, coeff_map, ZModIntCast_apply] using h

theorem actual_D_extraction (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < P.n0) (i ell : Fin p) (u : ℕ) :
    ((rowD P p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) =
      palindromicTransitionMatrix p ell i * ((rowD P 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowD P 1 (r0 + 1)).coeff u : ZMod p) := by
  have h := DResidueSum_coeff P p r0 u i ell
  rw [← rowD_frobenius P hP hp2 hr i] at h
  simpa only [DBase, coeff_map, ZModIntCast_apply] using h

theorem actual_P_extraction_below (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < P.n0) (i ell : Fin p) :
    (X * (rowP P p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ell.val = 0 := by
  rw [rowP_frobenius P hP hp2 hr i]
  exact PResidueSum_coeff_below P p r0 i ell

theorem actual_extracted_rows (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < P.n0) (i ell : Fin p) (u : ℕ) :
    ((X * (rowP P p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
          (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val),
      ((rowD P p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p)) =
      (palindromicTransitionMatrix p ell i * ((rowP P 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowP P 1 (r0 + 1)).coeff u : ZMod p),
       palindromicTransitionMatrix p ell i * ((rowD P 1 r0).coeff u : ZMod p) +
        palindromicReversedTransitionMatrix p ell i *
          ((rowD P 1 (r0 + 1)).coeff u : ZMod p)) := by
  exact Prod.ext (actual_P_extraction P hP hp2 hr i ell u)
    (actual_D_extraction P hP hp2 hr i ell u)

def baseRawContraction (P : Parameters) (p : ℕ) [Fact p.Prime] (r k : ℕ) : ZMod p :=
  (∑ u ∈ Finset.range (P.H 1), ((rowP P 1 r).coeff u : ZMod p) *
    palindromicRatResidue p (momentRat u k)) -
  (3 / 2 : ZMod p) *
    ∑ u ∈ Finset.range (P.H 1), ((rowD P 1 r).coeff u : ZMod p) *
      palindromicRatResidue p (zetaRat u k)

def extractedRawContraction (P : Parameters) (p : ℕ) [Fact p.Prime] (r0 : ℕ)
    (i ell : Fin p) (k : ℕ) :
    ZMod p :=
  (∑ u ∈ Finset.range (P.H 1),
    (X * (rowP P p (p * r0 + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2)).coeff ((u + 1) * p + ell.val) *
      palindromicRatResidue p (momentRat u k)) -
  (3 / 2 : ZMod p) *
    ∑ u ∈ Finset.range (P.H 1),
      ((rowD P p (p * r0 + i.val)).coeff (u * p + ell.val) : ZMod p) *
        palindromicRatResidue p (zetaRat u k)

theorem extractedRawContraction_factor (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r0 : ℕ} (hr : r0 < P.n0) (i ell : Fin p) (k : ℕ) :
    extractedRawContraction P p r0 i ell k =
      palindromicTransitionMatrix p ell i * baseRawContraction P p r0 k +
        palindromicReversedTransitionMatrix p ell i *
          baseRawContraction P p (r0 + 1) k := by
  simp only [extractedRawContraction, baseRawContraction]
  simp_rw [actual_P_extraction P hP hp2 hr i ell,
    actual_D_extraction P hP hp2 hr i ell,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

def baseFilterWeight (P : Parameters) (p v : ℕ) : ZMod p :=
  (-1 : ZMod p) ^ v * (Nat.choose P.q0 v : ZMod p)

def baseFilteredContraction (P : Parameters) (p : ℕ) [Fact p.Prime] (r : ℕ)
    (k0 : Fin P.n0) : ZMod p :=
  ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P p v *
    baseRawContraction P p r (P.b0 + k0.val + v)

def extractedFilteredEntry (P : Parameters) (p : ℕ) [Fact p.Prime] (r0 : Fin P.n0)
    (i ell : Fin p) (k0 : Fin P.n0) : ZMod p :=
  ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P p v *
    extractedRawContraction P p r0.val i ell (P.b0 + k0.val + v)

theorem extractedFilteredEntry_factor (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) (r0 : Fin P.n0) (i ell : Fin p) (k0 : Fin P.n0) :
    extractedFilteredEntry P p r0 i ell k0 =
      palindromicTransitionMatrix p ell i *
          baseFilteredContraction P p r0.val k0 +
        palindromicReversedTransitionMatrix p ell i *
          baseFilteredContraction P p (r0.val + 1) k0 := by
  unfold extractedFilteredEntry baseFilteredContraction
  simp_rw [extractedRawContraction_factor P hP hp2 r0.isLt i ell,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    ring
  · apply Finset.sum_congr rfl
    intro v hv
    ring


end
end CatalanMeasure.Parametric
