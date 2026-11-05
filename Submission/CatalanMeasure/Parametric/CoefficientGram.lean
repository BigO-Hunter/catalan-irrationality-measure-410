module

public import Submission.CatalanMeasure.Parametric.KernelGram
public import Submission.CatalanMeasure.Parametric.CrossGramBound

/-!
# Exact volume of the rational numerator coefficient basis

The volume is the reciprocal square root of the full Cauchy denominator
product. Together with the two kernel-group volumes this produces regular
cross factors, in place of a cross-group Vandermonde.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Finset
open scoped BigOperators

noncomputable section

def sheetCoefficientFamily {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (r : Fin n) : firstSheetSpace x hx :=
  ⟨firstSheetRationalEmbedding x hx (Pi.single r 1), ⟨Pi.single r 1, rfl⟩⟩

def sheetKernelFamily {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| < 1)
    (i : Fin n) : firstSheetSpace x hx :=
  ⟨firstSheetKernelVector (x i) (hx i), firstSheetKernelVector_mem_space x hx i⟩

theorem sheetCoefficientFamily_inner {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (i r : Fin n) :
    inner ℂ (sheetKernelFamily x hx i) (sheetCoefficientFamily x hx r) =
      (x i : ℂ) ^ (r : ℕ) / firstSheetDenominator univ x (x i : ℂ) := by
  change inner ℂ (firstSheetKernelVector (x i) (hx i))
    (firstSheetRationalEmbedding x hx (Pi.single r 1)) = _
  rw [firstSheetRationalEmbedding_inner_kernel, firstSheetRational, firstSheetNumerator_single]

theorem norm_sheetCoefficientFamily_inner_det {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) :
    ‖(Matrix.of (fun i r => inner ℂ (sheetKernelFamily x hx i)
      (sheetCoefficientFamily x hx r))).det‖ =
      |∏ i : Fin n, ∏ j ∈ Ioi i, (x j - x i)| /
        (∏ i : Fin n, ∏ j : Fin n, (1 - x i * x j)) := by
  have hden : 0 < ∏ i : Fin n, ∏ j : Fin n, (1 - x i * x j) :=
    prod_pos fun i _ => prod_pos fun j _ => one_sub_node_mul_pos (hx i) (hx j)
  have hmatrix : Matrix.of (fun i r => inner ℂ (sheetKernelFamily x hx i)
      (sheetCoefficientFamily x hx r)) =
      (Matrix.of (fun i r => (∏ j : Fin n, (1 - x j * x i))⁻¹ *
        (Matrix.vandermonde x) i r)).map Complex.ofReal := by
    ext i r
    simp only [Matrix.of_apply, Matrix.map_apply]
    rw [sheetCoefficientFamily_inner]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.vandermonde_apply,
      firstSheetDenominator, Complex.ofReal_mul, Complex.ofReal_inv, map_prod,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
    push_cast
    ring
  have hp : (∏ i : Fin n, ∏ j : Fin n, (1 - x j * x i)) =
      ∏ i : Fin n, ∏ j : Fin n, (1 - x i * x j) := prod_comm
  rw [hmatrix, firstSheet_norm_ofReal_det, Matrix.det_mul_column,
    Matrix.det_vandermonde, abs_mul, prod_inv_distrib, abs_inv, hp,
    abs_of_pos hden]
  ring

theorem sqrt_norm_sheetCoefficientFamily_gram_det {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, |x i| < 1) (hxi : Function.Injective x) :
    Real.sqrt ‖(Matrix.gram ℂ (sheetCoefficientFamily x hx)).det‖ =
      1 / Real.sqrt (∏ i : Fin n, ∏ j : Fin n, (1 - x i * x j)) := by
  let D := ∏ i : Fin n, ∏ j : Fin n, (1 - x i * x j)
  let V := |∏ i : Fin n, ∏ j ∈ Ioi i, (x j - x i)|
  let z := Real.sqrt ‖(Matrix.gram ℂ (sheetCoefficientFamily x hx)).det‖
  have hD : 0 < D := prod_pos fun i _ => prod_pos fun j _ =>
    one_sub_node_mul_pos (hx i) (hx j)
  have hV : V ≠ 0 := by
    apply abs_ne_zero.mpr
    rw [← Matrix.det_vandermonde]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hxi
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  let b : OrthonormalBasis (Fin n) ℂ (firstSheetSpace x hx) :=
    (stdOrthonormalBasis ℂ (firstSheetSpace x hx)).reindex
      (finCongr (firstSheetSpace_finrank x hx hxi))
  have h := norm_innerMatrix_det_gram b (sheetKernelFamily x hx) (sheetCoefficientFamily x hx)
  rw [norm_sheetCoefficientFamily_inner_det] at h
  have hgram : Matrix.gram ℂ (sheetKernelFamily x hx) =
      Matrix.gram ℂ (fun i => firstSheetKernelVector (x i) (hx i)) := rfl
  rw [hgram, sqrt_norm_firstSheetKernelVector_gram_det] at h
  change V / D = V / Real.sqrt D * z at h
  have hh : 1 / D = z / Real.sqrt D := by
    apply (mul_left_cancel₀ hV)
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using h
  have hh' := (div_eq_div_iff hD.ne' hs.ne').mp hh
  have hDs : D = Real.sqrt D * Real.sqrt D := (Real.mul_self_sqrt hD.le).symm
  nth_rw 2 [hDs] at hh'
  have hz : z * Real.sqrt D = 1 := by
    apply (mul_left_cancel₀ hs.ne')
    nlinarith only [hh']
  exact (eq_div_iff hs.ne').mpr hz

end

end CatalanMeasure.Parametric
