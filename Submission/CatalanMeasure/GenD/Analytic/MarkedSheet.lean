module

public import Submission.CatalanMeasure.Parametric.MarkedSheetHadamard
public import Submission.CatalanMeasure.Parametric.PopulationProductPositive
public import Submission.CatalanMeasure.Parametric.MixedLogs
public import Submission.CatalanMeasure.GenD.Analytic.First
public import Submission.CatalanMeasure.GenD.Analytic.GroupedProduct
public import Submission.CatalanMeasure.GenD.Analytic.FullInterval
public import Submission.CatalanMeasure.GenD.Analytic.CommonField

@[expose] public section

/-!
# Analytic layer: the first-population marked sheet product (design-generic)

Restatement, for an arbitrary admissible `P`, of `Parametric.MarkedSheetPhysical`
(`markedPhysicalMatrix`, `markedSheetProduct`, `marked_sheet_product_first_le`),
`Parametric.GroupedNodeWeights.marked_sheet_weight_cancellation` and of
`first_marked_product_with_trial`/`first_marked_sheet_with_trial`, whose originals import the
P20 certificates.  No certificate is imported: the first-population energy enters through
`first_energy` and `FirstTrialBounds P`.

Constants: `(n0 N)² (-target + log 2/2 + ε) + (n0 · c) N m`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Polynomial Filter
open scoped BigOperators Topology

noncomputable section

/-- The common factor has been removed only at marked nodes. -/
def firstMarkedProduct (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  populationOneProduct P N hpm x y s /
    ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- Node-first matrix of actual free rows and original polynomial marked rows. -/
def markedPhysicalMatrix (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ)
    (marked : Fin (P.n N) → Bool) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ :=
  Matrix.of fun i r => if marked i then
    (realPoly (rowP P N r)).eval (realCoordinateInv (x i))
    else realRowAmplitude P N r (realCoordinateInv (x i))

theorem marked_physical_matrix_factor {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    markedPhysicalMatrix P N x marked = Matrix.of (fun i r =>
      ((1 - realCoordinateInv (x i)) ^ P.h N *
        realCoordinateInv (x i) ^ (P.C N - 1)) *
          markedLaurentMatrix (P.g N) x marked i r) := by
  ext i r
  cases hmi : marked i
  · simp only [markedPhysicalMatrix, hmi, Bool.false_eq_true, ↓reduceIte,
      Matrix.of_apply, markedLaurentMatrix]
    rw [realRowAmplitude_sheet hP hN r.isLt (hx i) (hx0 i)]
    simp only [actualLaurentEntry, CatalanMeasure.Parametric.rowOffset, neg_sub]
  · simp only [markedPhysicalMatrix, hmi, ↓reduceIte, Matrix.of_apply,
      markedLaurentMatrix]
    rw [rowP_realCoordinateInv_signed hP hN r.isLt (hx0 i)]
    simp only [CatalanMeasure.Parametric.rowOffset, neg_sub]
    ring

theorem marked_physical_det_factor {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    |(markedPhysicalMatrix P N x marked).det| =
      (∏ i, paramRowNodeWeight P N (x i)) *
        |(markedLaurentMatrix (P.g N) x marked).det| := by
  rw [marked_physical_matrix_factor hP hN x marked hx hx0,
    Matrix.det_mul_column, abs_mul, abs_prod]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hx i))]
  unfold paramRowNodeWeight
  ring

/-- The normalized sheet part of an arbitrary selected-column mixed integrand.
The kernel/column determinant estimate is independent of the marked row type. -/
def markedSheetProduct (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  (∏ i, (1 + s i)) ^ m * |(markedLaurentMatrix (P.g N) z marked).det| *
    (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- The sheet product **without** the factor `(∏ (1 + s_i))^m` (PROOF-RHO §2.5, §5): the Vandermonde
part is paid column by column on the weight side (`genVandermonde_abs_le_binom`). -/
def markedSheetFree (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  |(markedLaurentMatrix (P.g N) z marked).det| *
    (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- `markedSheetProduct` is the removed factor times `markedSheetFree`. -/
theorem markedSheetProduct_eq_pow_mul_free (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    markedSheetProduct P N hpm x y s = (∏ i, (1 + s i)) ^ m * markedSheetFree P N hpm x y s := by
  unfold markedSheetProduct markedSheetFree
  simp only
  ring

theorem marked_sheet_product_first_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    markedSheetProduct P N hpm x y s ≤
      ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
        firstMarkedProduct P N hpm x y s := by
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
  have hsheet := marked_laurent_hadamard hP hN z marked hz hz0
  have hprod : 0 ≤ (∏ i, (1 + s i)) ^ m :=
    pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _
  have hfixed : 0 ≤ ∏ j, paramRowNodeWeight P N (y j) :=
    prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)
  have hprincipal := paramPinPrincipal_nonneg P N x s hx hs
  have hcommon : 0 ≤ ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| :=
    prod_nonneg fun j _ => abs_nonneg _
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsheet hprod) hfixed) hprincipal) hcommon
  convert hh using 1
  · rfl
  · unfold firstMarkedProduct populationOneProduct paramSheetOneWeight
    dsimp only [z]
    ring

theorem marked_sheet_weight_cancellation {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    |x| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) * paramRowNodeWeight P N x =
      |(rowCommonFactor P N).eval (realCoordinateInv x)| * markedSheetWeight P N x := by
  have hn := n_pos hP hN
  have hg := two_g_lt_n hP hN
  have hng : P.g N ≤ P.n N := by omega
  have hn1 : 1 ≤ P.n N := by omega
  have hng1 : 1 ≤ P.n N - P.g N := by omega
  have hC1 : 1 ≤ P.C N := by
    rw [C_eq_A_add_residual hP hN]
    omega
  have ht0 : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) (by positivity)
  have ht1 : realCoordinateInv x ≠ 1 := (sub_pos.mp (one_sub_realCoordinateInv_pos hx)).ne
  have hc0 := rowCommonFactor_eval_ne_zero_of P N ht0 ht1
  have hleft : 0 < |x| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) * paramRowNodeWeight P N x :=
    mul_pos (zpow_pos (abs_pos.mpr hx0) _) (paramRowNodeWeight_pos P N hx hx0)
  have hright : 0 < |(rowCommonFactor P N).eval (realCoordinateInv x)| * markedSheetWeight P N x :=
    mul_pos (abs_pos.mpr hc0) (markedSheetWeight_pos P N x)
  apply Real.log_injOn_pos hleft hright
  rw [Real.log_mul (zpow_ne_zero _ (abs_ne_zero.mpr hx0))
      (paramRowNodeWeight_pos P N hx hx0).ne',
    Real.log_mul (abs_ne_zero.mpr hc0) (markedSheetWeight_pos P N x).ne',
    Real.log_zpow, log_paramRowNodeWeight P N hx hx0,
    commonFactor_coordinate_log_full P N hx hx0, log_markedSheetWeight]
  have hC : (P.C N : ℝ) = (P.A N : ℝ) + (P.n N : ℝ) - (P.g N : ℝ) := by
    rw [C_eq_A_add_residual hP hN, Nat.cast_add, Nat.cast_sub hng]
    ring
  simp only [Int.cast_sub, Int.cast_natCast, Nat.cast_sub hn1,
    Nat.cast_sub hng1, Nat.cast_sub hng, Nat.cast_sub hC1, Nat.cast_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hC]
  ring

/-- Generic `first_marked_product_with_trial`. -/
theorem first_marked_product {P : Parameters} (hP : Admissible P) {target c : ℝ}
    (D : FirstTrialBounds P target c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) →
      firstMarkedProduct P N hpm x y s ≤
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          ((P.n0 : ℝ) * c) * N * m) := by
  filter_upwards [first_energy hP D hε, eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  have hz : ∀ i, Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i, Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hp := populationOneProduct_pos hP hN hpm x y s hz hz0 hs hxi hsi
  have hc : ∀ j, 0 < |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    intro j
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcp : 0 < ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| :=
    prod_pos fun j _ => hc j
  have hlog := log_populationOneProduct_weighted hP hN hpm
    x y s hz hz0 hs hxi hsi
  have hval := he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
  have hn0 : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : (P.n N : ℝ) ^ 2 *
      (-target + Real.log 2 / 2 + c * ((m : ℝ) / P.n N) + ε) =
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
        ((P.n0 : ℝ) * c) * N * m := by
    rw [hn]
    field_simp
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (P.n N : ℝ))
  rw [← hlog, hid] at hbound
  rw [firstMarkedProduct, ← Real.exp_log (div_pos hp hcp)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div hp.ne' hcp.ne', Real.log_prod (fun j _ => (hc j).ne')]
  exact hbound

/-- The sheet prefactor `(3/2)^n n^(n/2) + (1 + 10 e^12 n)^n` (generic `twentySheetPrefactor`). -/
def sheetPrefactor (P : Parameters) (N : ℕ) : ℝ :=
  (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) +
    (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N

/-- Generic `first_marked_sheet_with_trial`. -/
theorem first_marked_sheet {P : Parameters} (hP : Admissible P) {target c : ℝ}
    (F : FirstTrialBounds P target c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) →
      markedSheetProduct P N hpm x y s ≤
        ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            ((P.n0 : ℝ) * c) * N * m) := by
  filter_upwards [first_marked_product hP F hε,
      Filter.eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  exact (marked_sheet_product_first_le hP hN hpm x y s hx hx0 hy hy0 hs).trans
    (mul_le_mul_of_nonneg_left (he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase)
      (by positivity))

end
end Analytic
end CatalanMeasure.GenD
