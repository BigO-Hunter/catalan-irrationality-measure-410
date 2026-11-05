module

public import Submission.CatalanMeasure.MixedArbitraryAtoms
public import Submission.CatalanMeasure.GenD.Analytic.MarkedSheet
public import Submission.CatalanMeasure.GenD.Signed.BinomVandermonde

@[expose] public section

/-!
# Analytic layer: marked mixed majorant (design-generic)

Restatement of `Parametric.MarkedMixedMajorant` and `Parametric.MarkedAtomsDegeneracy`
(both design-generic but importing the P20 certificates through `MarkedSheetPhysical`), over the
generic `markedSheetProduct` of `GenD.Analytic.MarkedSheet`.  Same proofs.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Polynomial Finset Set
open scoped BigOperators

noncomputable section

def originalPolyAtoms (P : Parameters) (N : ℕ) {p m : ℕ} (y : Fin m → ℝ) :
    Fin (p + m) → Fin m → ℝ :=
  fun r j => (realPoly (rowP P N r)).eval (realCoordinateInv (y j))

theorem original_poly_atoms_rowDet_factor {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) :
    |CatalanMeasure.rowDetWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
        (realCoordinateInv ∘ x)| =
      (∏ i : Fin (P.n N), paramRowNodeWeight P N
        (Fin.append x y (Fin.cast hpm.symm i))) *
      |(markedLaurentMatrix (P.g N)
        (fun i => Fin.append x y (Fin.cast hpm.symm i))
        (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| := by
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  have hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    change Fin.append x y (Fin.cast hpm.symm i) ∈ Ioo (-1 : ℝ) 1
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j)
      (Fin.cast hpm.symm i)
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i
    change Fin.append x y (Fin.cast hpm.symm i) ≠ 0
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j)
      (Fin.cast hpm.symm i)
  have hm : (Matrix.of fun r c : Fin (p + m) =>
      Fin.addCases (fun i => paramPinRowFun P N r ((realCoordinateInv ∘ x) i))
        (fun j => originalPolyAtoms P N y r j) c).submatrix
        (finCongr hpm.symm) (finCongr hpm.symm) =
      (markedPhysicalMatrix P N z marked).transpose := by
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply,
      markedPhysicalMatrix, finCongr_apply]
    generalize hc : Fin.cast hpm.symm c = c'
    cases c' using Fin.addCases with
    | left i => simp [marked, z, hc, paramPinRowFun]
    | right j => simp [marked, z, hc, originalPolyAtoms]
  rw [CatalanMeasure.rowDetWithAtoms,
    ← Matrix.det_submatrix_equiv_self (finCongr hpm.symm), hm, Matrix.det_transpose]
  exact marked_physical_det_factor hP hN z marked hz hz0

/-- The selected filtered-column and Cauchy factors do not depend on the atom
row type, for an arbitrary bound `F` on the generalized Vandermonde factor
`|det [s_l ^ E_i]| ≤ F |V(s)|` (`F = (∏ (1+s))^m` or the binomial product of Lemma V). -/
theorem original_poly_atoms_mixedDouble_le_of_vand {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) {F : ℝ}
    (hvand : |(Matrix.of fun l i : Fin p => s l ^ E i).det| ≤
      F * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| ≤
      F *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s := by
  have hrow := original_poly_atoms_rowDet_factor hP hN hpm x y hx hx0 hy hy0
  have hw : (∏ i : Fin (P.n N), paramRowNodeWeight P N
      (Fin.append x y (Fin.cast hpm.symm i))) =
      (∏ i, paramRowNodeWeight P N (x i)) * ∏ j, paramRowNodeWeight P N (y j) := by
    rw [prod_fin_cast hpm (fun c => paramRowNodeWeight P N (Fin.append x y c)),
      Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hw] at hrow
  have ht : ∀ i, (realCoordinateInv ∘ x) i ∈ Ioo (-1 : ℝ) 1 :=
    fun i => realCoordinateInv_mem (hx i)
  have hD : 0 < ∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j) :=
    prod_pos fun i _ => prod_pos fun j _ => realCoordinateInv_kernel_pos _ (hs j)
  have hK : (Matrix.of fun i j : Fin p => paramPinKernel ((realCoordinateInv ∘ x) i) (s j)).det =
      ((∏ i : Fin p, ∏ j ∈ Ioi i, ((realCoordinateInv ∘ x) j - (realCoordinateInv ∘ x) i)) *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i))) /
        (∏ i : Fin p, ∏ j : Fin p, (1 - (realCoordinateInv ∘ x) i * s j)) :=
    realCauchy_det_eq_prod _ s ht hs
  have hG : (Matrix.of fun j i : Fin p => paramPinColFun P N E i (s j)).det =
      (∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N)) *
        (Matrix.of fun l i : Fin p => s l ^ E i).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext j i
    simp only [paramPinColFun, CatalanMeasure.Parametric.filteredColumn, Matrix.of_apply, eval_mul,
      eval_pow, eval_X, eval_sub, eval_one]
    ring
  have hsw : 0 ≤ ∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N) :=
    prod_nonneg fun j _ => mul_nonneg (pow_nonneg (hs j).1.le _)
      (pow_nonneg (sub_pos.mpr (hs j).2).le _)
  have hGb : |(Matrix.of fun j i : Fin p => paramPinColFun P N E i (s j)).det| ≤
      (∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N)) *
        (F * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|) := by
    rw [hG, abs_mul, abs_of_nonneg hsw]
    exact mul_le_mul_of_nonneg_left hvand hsw
  have hKabs : |(Matrix.of fun i j : Fin p => paramPinKernel ((realCoordinateInv ∘ x) i) (s j)).det| =
      |∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
          (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j)) := by
    rw [hK, abs_div, abs_mul]
    simp only [Function.comp_apply, abs_of_pos hD]
  unfold CatalanMeasure.mixedDoubleWithAtoms
  rw [abs_mul, abs_mul, hrow, hKabs]
  have hleft : 0 ≤ ((∏ i, paramRowNodeWeight P N (x i)) *
      (∏ j, paramRowNodeWeight P N (y j)) *
      |(markedLaurentMatrix (P.g N)
        (fun i => Fin.append x y (Fin.cast hpm.symm i))
        (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det|) *
      (|∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
          (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j))) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hx i))
      (prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j))) (abs_nonneg _))
      (div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD.le)
  have hb := mul_le_mul_of_nonneg_left hGb hleft
  convert hb using 1
  unfold paramPinPrincipal
  ring

/-- The selected filtered-column and Cauchy factors do not depend on the atom
row type. This is the original/P-only counterpart of MixedMajorant. -/
theorem original_poly_atoms_mixedDouble_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| ≤
      (∏ j : Fin p, (1 + s j)) ^ m *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s := by
  have hGV := CatalanMeasure.genVandermonde_abs_le_product s
    (fun j => ⟨(hs j).1.le, (hs j).2.le⟩) E hE hEn
  have hm : P.n N - p = m := by omega
  rw [hm] at hGV
  exact original_poly_atoms_mixedDouble_le_of_vand hP hN hpm E x y s hx hx0 hy hy0 hs hGV

/-- Binomial form (Lemma V, PROOF-RHO 2.1): the Vandermonde factor is the product of `β(k)` over
the columns `k` not selected by `E`, independent of `s`. -/
theorem original_poly_atoms_mixedDouble_le_binom {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| ≤
      (∏ k ∈ Finset.range (P.n N) \ Finset.univ.image E, (CatalanMeasure.binomBeta p m k : ℝ)) *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s := by
  have hGV := CatalanMeasure.genVandermonde_abs_le_binom s
    (fun j => ⟨(hs j).1.le, (hs j).2.le⟩) E hE hEn
  have hm : P.n N - p = m := by omega
  rw [hm] at hGV
  exact original_poly_atoms_mixedDouble_le_of_vand hP hN hpm E x y s hx hx0 hy hy0 hs hGV

theorem original_poly_atoms_mixedDouble_mul_weight_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) (β : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) {Q : ℝ}
    (hweight : ∀ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| ≤ Q) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| * (∏ j, |β j|) ≤
      markedSheetProduct P N hpm x y s * Q ^ m := by
  let C := ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|
  have hc (j : Fin m) : 0 < |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hC : 0 < C := prod_pos fun j _ => hc j
  have hp : 0 ≤ markedSheetProduct P N hpm x y s := by
    unfold markedSheetProduct
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg
        (pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _) (abs_nonneg _))
        (prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)))
        (paramPinPrincipal_nonneg P N x s hx hs)
    · exact hC.le
  have hbase := original_poly_atoms_mixedDouble_le hP hN hpm E hE hEn x y s hx hx0 hy hy0 hs
  have hprod : (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j|) ≤ Q ^ m := by
    calc
      _ ≤ ∏ _j : Fin m, Q := prod_le_prod₀
        (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (fun j _ => hweight j)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
  have heq : markedSheetProduct P N hpm x y s *
      (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j|) =
      ((∏ j : Fin p, (1 + s j)) ^ m *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s) * ∏ j, |β j| := by
    rw [prod_mul_distrib]
    unfold markedSheetProduct
    change (_ / C) * (C * _) = _
    rw [← mul_assoc, div_mul_cancel₀ _ hC.ne']
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase (prod_nonneg fun j _ => abs_nonneg _)
    _ = _ := heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hp

/-- The unselected columns `k_j` (injective, below `n`, disjoint from `E`) exhaust the complement. -/
theorem range_sdiff_image_eq_image_of_injective {n p m : ℕ} (hpm : p + m = n)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n)
    (k : Fin m → ℕ) (hk : Function.Injective k) (hkn : ∀ j, k j < n)
    (hkE : ∀ j i, k j ≠ E i) :
    Finset.range n \ Finset.univ.image E = Finset.univ.image k := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (hkn j), ?_⟩
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact hkE j i hi.symm
  · have hsub : Finset.univ.image E ⊆ Finset.range n := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (hEn i)
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injective _ hE,
      Finset.card_image_of_injective _ hk]
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_range]
    omega

/-- **Weight-side combination with Lemma V.**  If for every marked node the joint weight times
the binomial factor `β(k_j)` is at most `Q`, then the mixed integrand times the weights is at most
`markedSheetFree * Q^m`: the sheet product is taken without `(∏ (1+s_i))^m`. -/
theorem original_poly_atoms_mixedDouble_binom_mul_weight_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) (β : Fin m → ℝ) (k : Fin m → ℕ)
    (hk : Function.Injective k) (hkn : ∀ j, k j < P.n N) (hkE : ∀ j i, k j ≠ E i)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) {Q : ℝ}
    (hweight : ∀ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| *
      (CatalanMeasure.binomBeta p m (k j) : ℝ) ≤ Q) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| * (∏ j, |β j|) ≤
      markedSheetFree P N hpm x y s * Q ^ m := by
  let C := ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|
  have hc (j : Fin m) : 0 < |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hC : 0 < C := prod_pos fun j _ => hc j
  have hp : 0 ≤ markedSheetFree P N hpm x y s := by
    unfold markedSheetFree
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (abs_nonneg _)
        (prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)))
        (paramPinPrincipal_nonneg P N x s hx hs)
    · exact hC.le
  have hbase := original_poly_atoms_mixedDouble_le_binom hP hN hpm E hE hEn x y s hx hx0 hy hy0 hs
  rw [range_sdiff_image_eq_image_of_injective hpm E hE hEn k hk hkn hkE,
    Finset.prod_image (fun a _ b _ h => hk h)] at hbase
  have hprod : (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| *
      (CatalanMeasure.binomBeta p m (k j) : ℝ)) ≤ Q ^ m := by
    calc
      _ ≤ ∏ _j : Fin m, Q := prod_le_prod₀
        (fun j _ => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg _))
        (fun j _ => hweight j)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
  have heq : markedSheetFree P N hpm x y s *
      (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| *
        (CatalanMeasure.binomBeta p m (k j) : ℝ)) =
      ((∏ j, (CatalanMeasure.binomBeta p m (k j) : ℝ)) *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s) * ∏ j, |β j| := by
    rw [prod_mul_distrib, prod_mul_distrib]
    unfold markedSheetFree
    change (_ / C) * ((C * _) * _) = _
    field_simp
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase (prod_nonneg fun j _ => abs_nonneg _)
    _ = _ := heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hp

/-- Duplicate original P-only atoms give identical fixed columns. This does
not assert any collision zero between positive atoms and actual free nodes. -/
theorem original_poly_atoms_rowDet_eq_zero_of_not_injective (P : Parameters)
    (N : ℕ) {p m : ℕ} (y : Fin m → ℝ) (t : Fin p → ℝ)
    (hi : ¬Function.Injective y) :
    CatalanMeasure.rowDetWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y) t = 0 := by
  unfold Function.Injective at hi
  push Not at hi
  obtain ⟨j, j', hy, hne⟩ := hi
  unfold CatalanMeasure.rowDetWithAtoms
  apply Matrix.det_zero_of_column_eq
    (show Fin.natAdd p j ≠ Fin.natAdd p j' from fun he => hne (Fin.natAdd_injective _ _ he))
  intro r
  simp only [Matrix.of_apply, Fin.addCases_right, originalPolyAtoms, hy]

theorem original_poly_atoms_mixedDouble_eq_zero_of_not_injective (P : Parameters)
    (N : ℕ) {p m : ℕ} (y : Fin m → ℝ) (t s : Fin p → ℝ) (E : Fin p → ℕ)
    (hi : ¬Function.Injective y) :
    CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel t s = 0 := by
  unfold CatalanMeasure.mixedDoubleWithAtoms
  rw [original_poly_atoms_rowDet_eq_zero_of_not_injective P N y t hi]
  simp only [zero_mul]


end
end Analytic
end CatalanMeasure.GenD

#print axioms CatalanMeasure.GenD.Analytic.original_poly_atoms_mixedDouble_le_of_vand

#print axioms CatalanMeasure.GenD.Analytic.original_poly_atoms_mixedDouble_le_binom

#print axioms CatalanMeasure.GenD.Analytic.original_poly_atoms_mixedDouble_binom_mul_weight_le
