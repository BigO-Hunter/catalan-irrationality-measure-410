module

public import Submission.CatalanMeasure.PinSupDual
public import Submission.CatalanMeasure.GenVandermondeSharp
public import Submission.CatalanMeasure.MixedAndreief
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealDeterminantCore
public import Submission.OAI.NumberTheory.Catalan.Analysis.RealEnergyLogMajorants
public import Submission.OAI.NumberTheory.Catalan.Analysis.RealFactoredIntegral

@[expose] public section

/-!
# The pointwise bound for the mixed integrand

For a configuration of `p` free row nodes `t = x̂` (in OpenAI's coordinate `t = 2x/(1+x²)`),
`p` free column nodes `s`, and `m = n N - p` fixed row nodes `τ' = ŷ` with `y ∈ (-1, 0)`, the
fully antisymmetrized mixed integrand of `MixedAndreief.lean` is

  `det [φ_r(t ⧺ τ')] · det [1/(1 - t_i s_j)] · det [ψ_{E_i}(s_j)]`.

Using OpenAI's two sheet bounds for the `n × n` row determinant, the coordinate formulas, and the
generalized Vandermonde bound for the column determinant, we prove

  `|integrand| ≤ K_κ · 2^(n m) · 2^(2 h m) · exp (n² (pinFiniteValue N κ x s + log 2 / 2))`

in case `κ` of OpenAI's case split (`κ = 1`: Hadamard bound, `κ = 2`: first-sheet bound).
The fixed nodes cost at most `2^(2h)` each: the powers of two they contribute are exactly
compensated by the difference between OpenAI's `n`-node normalization and the `p`-node one.
-/

open Finset Set

namespace OAI.InternalCatalan

open scoped BigOperators

/-! ### Transport between `Fin (p + m)` and `Fin (n N)` -/

theorem fin_append_comp {p m : ℕ} (f : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    Fin.append (f ∘ x) (f ∘ y) = f ∘ Fin.append x y := by
  funext c
  refine Fin.addCases (fun i => ?_) (fun j => ?_) c <;> simp

theorem prod_fin_cast {a b : ℕ} (h : a = b) (f : Fin a → ℝ) :
    ∏ c : Fin b, f (Fin.cast h.symm c) = ∏ c : Fin a, f c := by
  subst h
  simp

theorem sum_fin_cast {a b : ℕ} (h : a = b) (f : Fin a → ℝ) :
    ∑ c : Fin b, f (Fin.cast h.symm c) = ∑ c : Fin a, f c := by
  subst h
  simp

theorem prod_Ioi_fin_cast {a b : ℕ} (h : a = b) (H : Fin a → Fin a → ℝ) :
    ∏ c : Fin b, ∏ c' ∈ Ioi c, H (Fin.cast h.symm c) (Fin.cast h.symm c') =
      ∏ c : Fin a, ∏ c' ∈ Ioi c, H c c' := by
  subst h
  simp

theorem det_fin_cast {a b : ℕ} (h : a = b) (M : Matrix (Fin a) (Fin a) ℝ) :
    (Matrix.of fun r c : Fin b => M (Fin.cast h.symm r) (Fin.cast h.symm c)).det = M.det := by
  subst h
  rfl

theorem injective_fin_cast_comp {a b : ℕ} (h : a = b) {z : Fin a → ℝ}
    (hz : Function.Injective z) : Function.Injective (fun c : Fin b => z (Fin.cast h.symm c)) :=
  fun c c' hcc => (Fin.cast_injective h.symm) (hz hcc)

theorem prod_Ioi_eq_prod_ite {k : ℕ} (H : Fin k → Fin k → ℝ) :
    ∏ a : Fin k, ∏ b ∈ Ioi a, H a b = ∏ a : Fin k, ∏ b : Fin k, if a < b then H a b else 1 := by
  apply prod_congr rfl
  intro a _
  rw [← prod_filter]
  congr 1
  ext b
  simp

theorem prod_Ioi_append {p m : ℕ} (H : ℝ → ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ) :
    ∏ a : Fin (p + m), ∏ b ∈ Ioi a, H (Fin.append x y a) (Fin.append x y b) =
      (∏ i : Fin p, ∏ i' ∈ Ioi i, H (x i) (x i')) * (∏ i : Fin p, ∏ j : Fin m, H (x i) (y j)) *
        ∏ j : Fin m, ∏ j' ∈ Ioi j, H (y j) (y j') := by
  rw [prod_Ioi_eq_prod_ite (fun a b => H (Fin.append x y a) (Fin.append x y b)),
    prod_Ioi_eq_prod_ite (fun i i' => H (x i) (x i')),
    prod_Ioi_eq_prod_ite (fun j j' => H (y j) (y j'))]
  have h1 : ∀ (i i' : Fin p), (Fin.castAdd m i < Fin.castAdd m i') ↔ i < i' := by
    intro i i'
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h2 : ∀ (i : Fin p) (j : Fin m), Fin.castAdd m i < Fin.natAdd p j := by
    intro i j
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : ∀ (i : Fin p) (j : Fin m), ¬ (Fin.natAdd p j < Fin.castAdd m i) := by
    intro i j
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h4 : ∀ (j j' : Fin m), (Fin.natAdd p j < Fin.natAdd p j') ↔ j < j' := by
    intro j j'
    simp only [Fin.lt_def, Fin.val_natAdd]
    omega
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, h1, h2, h3, h4,
    ite_true, ite_false, prod_const_one, mul_one, prod_mul_distrib]
  ring

theorem two_mul_choose_two_add (p m : ℕ) :
    (p + m).choose 2 = p.choose 2 + p * m + m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : (p + (m + 1)).choose 2 = (p + m).choose 2 + (p + m) := by
      rw [show p + (m + 1) = (p + m) + 1 by omega, Nat.choose_succ_succ', Nat.choose_one_right]
      ring
    have e2 : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      ring
    rw [e1, ih, e2]
    ring

/-! ### The specialized mixed integrand -/

/-- Row functions: OpenAI's real row amplitudes. -/
noncomputable def pinRowFun (N : ℕ) {k : ℕ} (r : Fin k) (t : ℝ) : ℝ := realRowAmplitude N r.val t

/-- Column functions: the filtered columns with exponents `E i`. -/
noncomputable def pinColFun (N : ℕ) {p : ℕ} (E : Fin p → ℕ) (i : Fin p) (s : ℝ) : ℝ :=
  (filteredColumn N (E i)).eval s

/-- The Cauchy kernel. -/
noncomputable def pinKernel (t s : ℝ) : ℝ := 1 / (1 - t * s)

/-- The weight of a row node in the sheet factorization. -/
noncomputable def rowNodeWeight (N : ℕ) (x : ℝ) : ℝ :=
  |realCoordinateInv x| ^ (Cdegree N - 1) * (1 - realCoordinateInv x) ^ h N

/-- The `p`-node principal integrand (OpenAI's `realPrincipalIntegrand` with `p` nodes). -/
noncomputable def pinPrincipal (N : ℕ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  (∏ i, rowNodeWeight N (x i)) *
    |∏ i, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
    |∏ i, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 /
    (∏ i, ∏ j, (1 - realCoordinateInv (x i) * s j)) *
    ∏ j, (s j ^ b N * (1 - s j) ^ q N)

theorem rowNodeWeight_nonneg (N : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ rowNodeWeight N x :=
  mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (one_sub_realCoordinateInv_pos hx).le _)

theorem pinPrincipal_nonneg (N : ℕ) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 ≤ pinPrincipal N x s := by
  unfold pinPrincipal
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (mul_nonneg (prod_nonneg fun i _ => rowNodeWeight_nonneg N (hx i))
        (abs_nonneg _)) (pow_nonneg (abs_nonneg _) _)
    · exact prod_nonneg fun i _ => prod_nonneg fun j _ => (realCoordinateInv_kernel_pos _ (hs j)).le
  · exact prod_nonneg fun j _ =>
      mul_nonneg (pow_nonneg (hs j).1.le _) (pow_nonneg (sub_pos.mpr (hs j).2).le _)

/-- The row determinant through OpenAI's sheet determinant. -/
theorem abs_rowDet_eq_sheet {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (hz : ∀ c, Fin.append x y c ∈ Ioo (-1 : ℝ) 1)
    (hz0 : ∀ c, Fin.append x y c ≠ 0) :
    |CatalanMeasure.rowDet (pinRowFun N) (realCoordinateInv ∘ y) (realCoordinateInv ∘ x)| =
      |realSheetDeterminant N (fun c => Fin.append x y (Fin.cast hpm.symm c))| *
        (∏ i, rowNodeWeight N (x i)) * ∏ j, rowNodeWeight N (y j) := by
  set z : Fin (n N) → ℝ := fun c => Fin.append x y (Fin.cast hpm.symm c) with hzdef
  have hzm : ∀ c, z c ∈ Ioo (-1 : ℝ) 1 := fun c => hz _
  have hz0' : ∀ c, z c ≠ 0 := fun c => hz0 _
  have hrow : CatalanMeasure.rowDet (pinRowFun N) (realCoordinateInv ∘ y)
      (realCoordinateInv ∘ x) =
      Matrix.det (Matrix.of (fun r i : Fin (n N) =>
        realRowAmplitude N r.val (realCoordinateInv (z i)))) := by
    unfold CatalanMeasure.rowDet
    rw [fin_append_comp, ← det_fin_cast hpm]
    rfl
  rw [hrow, realRowAmplitude_det_eq_sheet hN z hzm hz0', abs_mul, abs_prod]
  have hw : ∀ c, |realCoordinateInv (z c) ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (z c)) ^ h N| = rowNodeWeight N (z c) := by
    intro c
    rw [abs_mul, abs_pow, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hzm c))]
    rfl
  simp_rw [hw]
  rw [mul_assoc]
  congr 1
  rw [hzdef, prod_fin_cast hpm (fun c => rowNodeWeight N (Fin.append x y c)),
    Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Factorization bound** for the mixed integrand. -/
theorem abs_mixedDouble_le_sheet {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c, Fin.append x y c ∈ Ioo (-1 : ℝ) 1) (hz0 : ∀ c, Fin.append x y c ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E) pinKernel
        (realCoordinateInv ∘ x) s| ≤
      (2 : ℝ) ^ (n N * m) *
        |realSheetDeterminant N (fun c => Fin.append x y (Fin.cast hpm.symm c))| *
        (∏ j, rowNodeWeight N (y j)) * pinPrincipal N x s := by
  have hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1 := fun i => by simpa using hz (Fin.castAdd m i)
  have ht : ∀ i, (realCoordinateInv ∘ x) i ∈ Ioo (-1 : ℝ) 1 :=
    fun i => realCoordinateInv_mem (hx i)
  unfold CatalanMeasure.mixedDouble
  rw [abs_mul, abs_mul, abs_rowDet_eq_sheet hN hpm x y hz hz0]
  -- the Cauchy determinant
  have hK : (Matrix.of fun i j : Fin p => pinKernel ((realCoordinateInv ∘ x) i) (s j)).det =
      ((∏ i : Fin p, ∏ j ∈ Ioi i, ((realCoordinateInv ∘ x) j - (realCoordinateInv ∘ x) i)) *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i))) /
          (∏ i : Fin p, ∏ j : Fin p, (1 - (realCoordinateInv ∘ x) i * s j)) :=
    realCauchy_det_eq_prod _ s ht hs
  have hD : 0 < ∏ i : Fin p, ∏ j : Fin p, (1 - (realCoordinateInv ∘ x) i * s j) :=
    prod_pos fun i _ => prod_pos fun j _ => realCoordinateInv_kernel_pos _ (hs j)
  -- the column determinant
  have hG : (Matrix.of fun j i : Fin p => pinColFun N E i (s j)).det =
      (∏ j, (s j ^ b N * (1 - s j) ^ q N)) *
        (Matrix.of fun l i : Fin p => s l ^ E i).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext j i
    simp only [pinColFun, filteredColumn, Matrix.of_apply, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
    ring
  have hsw : 0 ≤ ∏ j, (s j ^ b N * (1 - s j) ^ q N) := prod_nonneg fun j _ =>
    mul_nonneg (pow_nonneg (hs j).1.le _) (pow_nonneg (sub_pos.mpr (hs j).2).le _)
  have hGV0 := CatalanMeasure.genVandermonde_abs_le_two s (fun j => ⟨(hs j).1.le, (hs j).2.le⟩)
    E hE hEn
  have hm : n N - p = m := by omega
  rw [hm] at hGV0
  have hGV : |(Matrix.of fun l i : Fin p => s l ^ E i).det| ≤
      (2 : ℝ) ^ (n N * m) * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| :=
    hGV0.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right m (by omega))) (abs_nonneg _))
  have hGb : |(Matrix.of fun j i : Fin p => pinColFun N E i (s j)).det| ≤
      (∏ j, (s j ^ b N * (1 - s j) ^ q N)) *
        ((2 : ℝ) ^ (n N * m) * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|) := by
    rw [hG, abs_mul, abs_of_nonneg hsw]
    exact mul_le_mul_of_nonneg_left hGV hsw
  have hKabs : |(Matrix.of fun i j : Fin p => pinKernel ((realCoordinateInv ∘ x) i) (s j)).det| =
      |∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
          (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j)) := by
    rw [hK, abs_div, abs_mul, abs_of_pos hD]
    rfl
  rw [hKabs]
  have hS0 : 0 ≤ |realSheetDeterminant N (fun c => Fin.append x y (Fin.cast hpm.symm c))| *
      (∏ i, rowNodeWeight N (x i)) * ∏ j, rowNodeWeight N (y j) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (prod_nonneg fun i _ => rowNodeWeight_nonneg N (hx i)))
      (prod_nonneg fun j _ => rowNodeWeight_nonneg N (by simpa using hz (Fin.natAdd p j)))
  have hK0 : 0 ≤ |∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
          (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j)) :=
    div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD.le
  calc _ ≤ |realSheetDeterminant N (fun c => Fin.append x y (Fin.cast hpm.symm c))| *
        (∏ i, rowNodeWeight N (x i)) * (∏ j, rowNodeWeight N (y j)) *
        (|∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
            (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j))) *
        ((∏ j, (s j ^ b N * (1 - s j) ^ q N)) *
          ((2 : ℝ) ^ (n N * m) * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|)) :=
        mul_le_mul_of_nonneg_left hGb (mul_nonneg hS0 hK0)
    _ = _ := by
        unfold pinPrincipal
        ring

/-! ### Coordinates and logarithms of the `p`-node majorants -/

theorem rowNodeWeight_coordinate (N : ℕ) (x : ℝ) :
    rowNodeWeight N x = (2 : ℝ) ^ (Cdegree N - 1) * (|x| ^ (Cdegree N - 1) *
      (1 - x) ^ (2 * h N)) / (1 + x ^ 2) ^ (Cdegree N - 1 + h N) := by
  unfold rowNodeWeight
  rw [energy_row_weight_coordinate]
  ring

theorem pin_quadratic_cancel {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : 1 ≤ p) (x : ℝ) :
    (1 + x ^ 2) ^ p / ((1 + x ^ 2) ^ (p - 1) * (1 + x ^ 2) ^ (Cdegree N - 1 + h N)) =
      1 / (1 + x ^ 2) ^ (H N - 2) := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (realCoordinateInv_denominator_pos x)
  have he : (p - 1) + (Cdegree N - 1 + h N) = p + (H N - 2) := by
    unfold Cdegree h H
    omega
  rw [← pow_add, he, pow_add]
  field_simp

theorem pinPrincipal_coordinate {N : ℕ} (hN : 0 < N) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) :
    pinPrincipal N x s =
      (2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
        (∏ j : Fin p, (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin p, (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) /
        ((∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2))) := by
  have hcancel : (∏ i : Fin p, (1 + x i ^ 2) ^ p) /
      ((∏ i : Fin p, (1 + x i ^ 2) ^ (p - 1)) *
        (∏ i : Fin p, (1 + x i ^ 2) ^ (Cdegree N - 1 + h N))) =
      1 / (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2)) := by
    rw [← prod_mul_distrib, ← prod_div_distrib]
    rw [show (1 : ℝ) / (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2)) =
      ∏ i : Fin p, 1 / (1 + x i ^ 2) ^ (H N - 2) by
        rw [prod_div_distrib, prod_const_one]]
    apply prod_congr rfl
    intro i _
    exact pin_quadratic_cancel hN (Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne') (x i)
  unfold pinPrincipal
  simp_rw [rowNodeWeight_coordinate]
  rw [abs_vandermonde_realCoordinateInv x hx, prod_realCoordinateInv_kernel]
  simp only [prod_div_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  calc _ = ((2 : ℝ) ^ (Cdegree N - 1)) ^ p * (2 : ℝ) ^ p.choose 2 *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
          (∏ j : Fin p, (s j ^ b N * (1 - s j) ^ q N)) *
          ((∏ i : Fin p, |x i| ^ (Cdegree N - 1)) * ∏ i : Fin p, (1 - x i) ^ (2 * h N)) /
          (∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) *
        ((∏ i : Fin p, (1 + x i ^ 2) ^ p) /
          ((∏ i : Fin p, (1 + x i ^ 2) ^ (p - 1)) *
            (∏ i : Fin p, (1 + x i ^ 2) ^ (Cdegree N - 1 + h N)))) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, prod_mul_distrib]
        ring
    _ = _ := by
        rw [hcancel, pow_add, ← pow_mul, mul_comm (Cdegree N - 1) p]
        simp only [div_eq_mul_inv, mul_inv_rev, prod_mul_distrib]
        ring

/-- Case-one sheet weight of a node. -/
noncomputable def sheetOneWeight (N : ℕ) (x : ℝ) : ℝ :=
  (1 + x ^ 2) ^ (((n N : ℝ) - 1) / 2) * |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))

/-- The `p`-node case-one majorant. -/
noncomputable def pinMajorantOne (N : ℕ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  pinPrincipal N x s * ∏ i, sheetOneWeight N (x i)

/-- The `p`-node case-two majorant. -/
noncomputable def pinMajorantTwo (N : ℕ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  pinPrincipal N x s * |∏ i : Fin p, ∏ j ∈ Ioi i, ((x j)⁻¹ - (x i)⁻¹)| *
    (∏ i, |x i| ^ g N) / ∏ i, |x i| ^ (n N - p)

theorem pinMajorantOne_coordinate {N : ℕ} (hN : 0 < N) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    pinMajorantOne N x s =
      (2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
        (∏ j : Fin p, (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
          (1 + x i ^ 2) ^ (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2))) /
        (∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) := by
  have hw : ((∏ i : Fin p, (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
      (∏ i : Fin p, sheetOneWeight N (x i))) / (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2)) =
      ∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
        (1 + x i ^ 2) ^ (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2)) := by
    rw [← prod_mul_distrib, ← prod_div_distrib]
    apply prod_congr rfl
    intro i _
    unfold sheetOneWeight
    calc _ = (|x i| ^ (Cdegree N - 1) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) * (1 - x i) ^ (2 * h N) *
          ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + x i ^ 2) ^ (H N - 2)) := by ring
      _ = _ := by rw [energy_abs_node_weight_cancel hN (hx0 i), energy_one_quadratic_weight hN]
  unfold pinMajorantOne
  rw [pinPrincipal_coordinate hN x s hx]
  calc _ = ((2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
          (∏ j : Fin p, (s j ^ b N * (1 - s j) ^ q N)) /
          (∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2))) *
        (((∏ i : Fin p, (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
          (∏ i : Fin p, sheetOneWeight N (x i))) /
          (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
    _ = _ := by
        rw [hw]
        ring

theorem pinMajorantTwo_coordinate {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ≤ n N)
    (x s : Fin p → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    pinMajorantTwo N x s =
      (2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| ^ 2 *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
        (∏ j : Fin p, (s j ^ b N * (1 - s j) ^ q N)) *
        (∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N))) /
        ((∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) *
          (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2))) := by
  have hw : ((∏ i : Fin p, (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
      (∏ i : Fin p, |x i| ^ g N)) /
        ((∏ i : Fin p, |x i| ^ (p - 1)) * ∏ i : Fin p, |x i| ^ (n N - p)) =
      ∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
    apply prod_congr rfl
    intro i _
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
    have hexp : |x i| ^ (p - 1) * |x i| ^ (n N - p) = |x i| ^ (n N - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hexp]
    calc _ = ((|x i| ^ (Cdegree N - 1) * |x i| ^ g N) / |x i| ^ (n N - 1)) *
          (1 - x i) ^ (2 * h N) := by ring
      _ = _ := by rw [energy_abs_node_weight_two_cancel hN (hx0 i)]
  unfold pinMajorantTwo
  rw [pinPrincipal_coordinate hN x s hx, abs_vandermonde_inv x hx0]
  calc _ = ((2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (x j - x i)| ^ 2 *
          |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 *
          (∏ i : Fin p, ∏ j ∈ Ioi i, (1 - x i * x j)) *
          (∏ j : Fin p, (s j ^ b N * (1 - s j) ^ q N)) /
          ((∏ i : Fin p, ∏ j : Fin p, (1 - 2 * x i * s j + x i ^ 2)) *
            (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2)))) *
        (((∏ i : Fin p, (|x i| ^ (Cdegree N - 1) * (1 - x i) ^ (2 * h N))) *
          (∏ i : Fin p, |x i| ^ g N)) /
            ((∏ i : Fin p, |x i| ^ (p - 1)) * ∏ i : Fin p, |x i| ^ (n N - p))) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
    _ = _ := by
        rw [hw]
        ring

theorem pin_s_weight_product_pos (N : ℕ) {p : ℕ} (s : Fin p → ℝ)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    0 < ∏ i : Fin p, (s i ^ b N * (1 - s i) ^ q N) :=
  prod_pos fun i _ => mul_pos (pow_pos (hs i).1 _) (pow_pos (sub_pos.mpr (hs i).2) _)

theorem log_pin_s_weight_product (N : ℕ) {p : ℕ} (s : Fin p → ℝ)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    Real.log (∏ i : Fin p, (s i ^ b N * (1 - s i) ^ q N)) =
      ∑ i : Fin p, ((b N : ℝ) * Real.log (s i) + (q N : ℝ) * Real.log (1 - s i)) := by
  rw [Real.log_prod (fun i _ =>
    mul_ne_zero (pow_ne_zero _ (hs i).1.ne') (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'))]
  apply sum_congr rfl
  intro i _
  rw [Real.log_mul (pow_ne_zero _ (hs i).1.ne')
    (pow_ne_zero _ (sub_pos.mpr (hs i).2).ne'), Real.log_pow, Real.log_pow]

theorem pin_node_weight_pos (N : ℕ) (k : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    0 < |x| ^ A N * (1 - x) ^ (2 * h N) * (1 + x ^ 2) ^ k :=
  mul_pos (mul_pos (pow_pos (abs_pos.mpr hx0) _) (pow_pos (sub_pos.mpr hx.2) _))
    (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos x) _)

theorem log_pin_node_weight_product (N : ℕ) (k : ℝ) {p : ℕ} (x : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    Real.log (∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N) * (1 + x i ^ 2) ^ k)) =
      ∑ i : Fin p, ((A N : ℝ) * Real.log |x i| +
        ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i) + k * Real.log (1 + x i ^ 2)) := by
  rw [Real.log_prod (fun i _ => (pin_node_weight_pos N k (hx i) (hx0 i)).ne')]
  apply sum_congr rfl
  intro i _
  have ha : |x i| ^ A N ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr (hx0 i))
  have hb : (1 - x i) ^ (2 * h N) ≠ 0 := pow_ne_zero _ (sub_pos.mpr (hx i).2).ne'
  have hc : (1 + x i ^ 2) ^ k ≠ 0 :=
    (Real.rpow_pos_of_pos (realCoordinateInv_denominator_pos (x i)) k).ne'
  rw [Real.log_mul (mul_ne_zero ha hb) hc, Real.log_mul ha hb,
    Real.log_pow, Real.log_pow, Real.log_rpow (realCoordinateInv_denominator_pos (x i))]

theorem log_pin_quadratic_product (N : ℕ) {p : ℕ} (x : Fin p → ℝ) :
    Real.log (∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2)) =
      ∑ i : Fin p, ((H N - 2 : ℕ) : ℝ) * Real.log (1 + x i ^ 2) := by
  rw [Real.log_prod (fun i _ =>
    pow_ne_zero _ (realCoordinateInv_denominator_pos (x i)).ne')]
  simp only [Real.log_pow]

/-- **Log of the case-one majorant** in terms of the generalized finite value. -/
theorem log_pinMajorantOne {N : ℕ} (hN : 0 < N) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (pinMajorantOne N x s) =
      (n N : ℝ) ^ 2 * (pinFiniteValue N 1 x s + Real.log 2 / 2) +
        (((p * (Cdegree N - 1) + p.choose 2 : ℕ) : ℝ) -
          (n N : ℝ) * ((Cdegree N : ℝ) - 1)) * Real.log 2 := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := pin_s_weight_product_pos N s hs
  have hW : 0 < ∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
      (1 + x i ^ 2) ^ (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2)) :=
    prod_pos fun i _ => pin_node_weight_pos N _ (hx i) (hx0 i)
  rw [pinMajorantOne_coordinate hN x s hx hx0]
  rw [Real.log_div (by positivity) hK.ne',
    Real.log_mul (by positivity) hW.ne',
    Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) hX.ne']
  rw [Real.log_pow, Real.log_pow, log_abs_vandermonde x hxi,
    log_abs_vandermonde s hsi, log_energy_pair_product x hx,
    log_pin_s_weight_product N s hs,
    log_pin_node_weight_product N _ x hx hx0,
    log_energy_mixed_product x s hs]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  unfold pinFiniteValue realEnergyField realEnergyColumnField
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_mul, Nat.cast_add, Nat.cast_sub hC, Nat.cast_one]
  simp only [n, Cdegree, A, b, q, h, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- **Log of the case-two majorant** in terms of the generalized finite value. -/
theorem log_pinMajorantTwo {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ≤ n N) (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (pinMajorantTwo N x s) =
      (n N : ℝ) ^ 2 * (pinFiniteValue N 2 x s + Real.log 2 / 2) +
        (((p * (Cdegree N - 1) + p.choose 2 : ℕ) : ℝ) -
          (n N : ℝ) * ((Cdegree N : ℝ) - 1) - ((n N).choose 2 : ℝ)) * Real.log 2 := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := pin_s_weight_product_pos N s hs
  have hW : 0 < ∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
    have := prod_pos (s := (univ : Finset (Fin p))) fun i _ => pin_node_weight_pos N 0 (hx i) (hx0 i)
    simpa only [Real.rpow_zero, mul_one] using this
  have hD : 0 < ∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2) :=
    prod_pos fun i _ => pow_pos (realCoordinateInv_denominator_pos (x i)) _
  have hH : 2 ≤ H N := by unfold H; omega
  have hc : ((H N - 2 : ℕ) : ℝ) = (Cdegree N : ℝ) + (h N : ℝ) - 2 := by
    rw [Nat.cast_sub hH, H_eq_Cdegree_add_h, Nat.cast_add, Nat.cast_ofNat]
  have hlogW : Real.log (∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N))) =
      ∑ i : Fin p, ((A N : ℝ) * Real.log |x i| + ((2 * h N : ℕ) : ℝ) * Real.log (1 - x i)) := by
    have := log_pin_node_weight_product N 0 x hx hx0
    simpa only [Real.rpow_zero, mul_one, zero_mul, add_zero] using this
  rw [pinMajorantTwo_coordinate hN hp x s hx hx0]
  rw [Real.log_div (by positivity) (mul_pos hK hD).ne',
    Real.log_mul (by positivity) hW.ne',
    Real.log_mul (by positivity) hSW.ne',
    Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (pow_ne_zero _ hS.ne'),
    Real.log_mul (by positivity) (pow_ne_zero _ hX.ne'),
    Real.log_mul hK.ne' hD.ne']
  rw [Real.log_pow, Real.log_pow, Real.log_pow,
    log_abs_vandermonde x hxi, log_abs_vandermonde s hsi,
    log_energy_pair_product x hx, log_pin_s_weight_product N s hs,
    hlogW, log_energy_mixed_product x s hs, log_pin_quadratic_product N x]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  unfold pinFiniteValue realEnergyField realEnergyColumnField
  simp only [hc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_mul, Nat.cast_add, Nat.cast_sub hC, Nat.cast_one, Nat.cast_choose_two]
  simp only [n, Cdegree, A, b, q, h, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

/-! ### The fixed nodes -/

theorem exp_sub_mul_log_two (a b : ℕ) :
    Real.exp (((a : ℝ) - (b : ℝ)) * Real.log 2) = (2 : ℝ) ^ a / (2 : ℝ) ^ b := by
  rw [sub_mul, Real.exp_sub, ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
    Real.exp_log (by positivity)]

theorem fixed_node_bounds {N : ℕ} (hN : 0 < N) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 0) :
    |y| ^ A N ≤ 1 ∧ (1 - y) ^ (2 * h N) ≤ (2 : ℝ) ^ (2 * h N) ∧ 0 < 1 - y := by
  have hya : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, by linarith [hy.2]⟩
  refine ⟨pow_le_one₀ (abs_nonneg _) hya, ?_, by linarith [hy.2]⟩
  exact pow_le_pow_left₀ (by linarith [hy.2]) (by linarith [hy.1]) _

theorem rowNodeWeight_mul_sheetOneWeight_le {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 0) :
    rowNodeWeight N y * sheetOneWeight N y ≤ (2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N) := by
  obtain ⟨hA, h2h, h1y⟩ := fixed_node_bounds hN hy
  have hy0 : y ≠ 0 := hy.2.ne
  have hd : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  have hdpos : (0 : ℝ) < 1 + y ^ 2 := by linarith
  have hQ : (1 + y ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N) ≤ 1 := by
    rw [show (1 + y ^ 2) ^ (Cdegree N - 1 + h N) =
        (1 + y ^ 2) ^ ((Cdegree N - 1 + h N : ℕ) : ℝ) from (Real.rpow_natCast _ _).symm,
      div_le_one (Real.rpow_pos_of_pos hdpos _)]
    apply Real.rpow_le_rpow_of_exponent_le hd
    have hC : 1 ≤ Cdegree N := Cdegree_pos hN
    rw [Nat.cast_add, Nat.cast_sub hC]
    simp only [n, Cdegree, h, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hQ0 : 0 ≤ (1 + y ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N) :=
    div_nonneg (Real.rpow_nonneg hdpos.le _) (pow_nonneg hdpos.le _)
  have heq : rowNodeWeight N y * sheetOneWeight N y = (2 : ℝ) ^ (Cdegree N - 1) *
      ((|y| ^ (Cdegree N - 1) * |y| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) * (1 - y) ^ (2 * h N) *
        ((1 + y ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N))) := by
    rw [rowNodeWeight_coordinate]
    unfold sheetOneWeight
    ring
  rw [heq, energy_abs_node_weight_cancel hN hy0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc |y| ^ A N * (1 - y) ^ (2 * h N) *
        ((1 + y ^ 2) ^ (((n N : ℝ) - 1) / 2) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N))
      ≤ 1 * (2 : ℝ) ^ (2 * h N) * 1 :=
        mul_le_mul (mul_le_mul hA h2h (pow_nonneg h1y.le _) zero_le_one) hQ hQ0
          (by positivity)
    _ = (2 : ℝ) ^ (2 * h N) := by ring

theorem rowNodeWeight_two_le {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (hm : 1 ≤ m) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 0) :
    rowNodeWeight N y * |y| ^ g N / (|y| ^ p * |y| ^ (m - 1)) ≤
      (2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N) := by
  obtain ⟨hA, h2h, h1y⟩ := fixed_node_bounds hN hy
  have hy0 : y ≠ 0 := hy.2.ne
  have hdpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hd : (1 : ℝ) ≤ (1 + y ^ 2) ^ (Cdegree N - 1 + h N) :=
    one_le_pow₀ (by nlinarith [sq_nonneg y])
  have hexp : |y| ^ p * |y| ^ (m - 1) = |y| ^ (n N - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have heq : rowNodeWeight N y * |y| ^ g N / (|y| ^ p * |y| ^ (m - 1)) =
      (2 : ℝ) ^ (Cdegree N - 1) * (((|y| ^ (Cdegree N - 1) * |y| ^ g N) / |y| ^ (n N - 1)) *
        (1 - y) ^ (2 * h N) / (1 + y ^ 2) ^ (Cdegree N - 1 + h N)) := by
    rw [hexp, rowNodeWeight_coordinate]
    ring
  rw [heq, energy_abs_node_weight_two_cancel hN hy0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  calc |y| ^ A N * (1 - y) ^ (2 * h N) ≤ 1 * (2 : ℝ) ^ (2 * h N) :=
        mul_le_mul hA h2h (pow_nonneg h1y.le _) zero_le_one
    _ ≤ (2 : ℝ) ^ (2 * h N) * (1 + y ^ 2) ^ (Cdegree N - 1 + h N) := by
        rw [one_mul]
        exact le_mul_of_one_le_right (by positivity) hd

theorem cross_inv_bound {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0) :
    |∏ i : Fin p, ∏ j : Fin m, ((y j)⁻¹ - (x i)⁻¹)| * (∏ i, |x i| ^ m) * ∏ j, |y j| ^ p ≤
      (2 : ℝ) ^ (p * m) := by
  have hpt : ∀ i j, |(y j)⁻¹ - (x i)⁻¹| * |x i| * |y j| = |x i - y j| := by
    intro i j
    have hyj : y j ≠ 0 := (hy j).2.ne
    have : (y j)⁻¹ - (x i)⁻¹ = (x i - y j) / (x i * y j) := by
      field_simp [hx0 i, hyj]
    rw [this, abs_div, abs_mul]
    field_simp [abs_ne_zero.mpr (hx0 i), abs_ne_zero.mpr hyj]
  have hsplit : |∏ i : Fin p, ∏ j : Fin m, ((y j)⁻¹ - (x i)⁻¹)| * (∏ i, |x i| ^ m) *
      ∏ j, |y j| ^ p = ∏ i : Fin p, ∏ j : Fin m, (|(y j)⁻¹ - (x i)⁻¹| * |x i| * |y j|) := by
    simp only [prod_mul_distrib, abs_prod, prod_const, card_univ, Fintype.card_fin, Finset.prod_pow]
  rw [hsplit]
  simp_rw [hpt]
  calc ∏ i : Fin p, ∏ j : Fin m, |x i - y j| ≤ ∏ _i : Fin p, ∏ _j : Fin m, (2 : ℝ) := by
        apply prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => abs_nonneg _)
        intro i _
        apply prod_le_prod₀ (fun j _ => abs_nonneg _)
        intro j _
        rw [abs_le]
        constructor <;> linarith [(hx i).1, (hx i).2, (hy j).1, (hy j).2]
    _ = (2 : ℝ) ^ (p * m) := by
        simp only [prod_const, card_univ, Fintype.card_fin]
        rw [← pow_mul, mul_comm]

theorem fixed_vandermonde_inv_bound {m : ℕ} (y : Fin m → ℝ) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0) :
    |∏ j : Fin m, ∏ j' ∈ Ioi j, ((y j')⁻¹ - (y j)⁻¹)| * ∏ j, |y j| ^ (m - 1) ≤ 1 := by
  have hy0 : ∀ j, y j ≠ 0 := fun j => (hy j).2.ne
  rw [abs_vandermonde_inv y hy0, div_mul_cancel₀ _
    (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (abs_ne_zero.mpr (hy0 j))), abs_prod]
  apply prod_le_one₀ (fun j _ => abs_nonneg _)
  intro j _
  rw [abs_prod]
  apply prod_le_one₀ (fun j' _ => abs_nonneg _)
  intro j' _
  rw [abs_le]
  constructor <;> linarith [(hy j).1, (hy j).2, (hy j').1, (hy j').2]

/-! ### The two cases -/

theorem append_mem_of {p m : ℕ} {x : Fin p → ℝ} {y : Fin m → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0) (c : Fin (p + m)) :
    Fin.append x y c ∈ Ioo (-1 : ℝ) 1 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) c
  · simpa using hx i
  · simp only [Fin.append_right]
    exact ⟨(hy j).1, by linarith [(hy j).2]⟩

theorem append_ne_zero_of {p m : ℕ} {x : Fin p → ℝ} {y : Fin m → ℝ}
    (hx0 : ∀ i, x i ≠ 0) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0) (c : Fin (p + m)) :
    Fin.append x y c ≠ 0 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) c
  · simpa using hx0 i
  · simpa using (hy j).2.ne

theorem pinMajorantOne_pos {N : ℕ} (hN : 0 < N) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) : 0 < pinMajorantOne N x s := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := pin_s_weight_product_pos N s hs
  have hW : 0 < ∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N) *
      (1 + x i ^ 2) ^ (2 - (Cdegree N : ℝ) - (h N : ℝ) + ((n N : ℝ) - 1) / 2)) :=
    prod_pos fun i _ => pin_node_weight_pos N _ (hx i) (hx0 i)
  rw [pinMajorantOne_coordinate hN x s hx hx0]
  positivity

theorem pinMajorantTwo_pos {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ≤ n N) (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) : 0 < pinMajorantTwo N x s := by
  have hX := energy_abs_vandermonde_pos x hxi
  have hS := energy_abs_vandermonde_pos s hsi
  have hP := energy_pair_product_pos x hx
  have hK := energy_mixed_product_pos x s hs
  have hSW := pin_s_weight_product_pos N s hs
  have hW : 0 < ∏ i : Fin p, (|x i| ^ A N * (1 - x i) ^ (2 * h N)) := by
    have := prod_pos (s := (univ : Finset (Fin p))) fun i _ => pin_node_weight_pos N 0 (hx i) (hx0 i)
    simpa only [Real.rpow_zero, mul_one] using this
  have hD : 0 < ∏ i : Fin p, (1 + x i ^ 2) ^ (H N - 2) :=
    prod_pos fun i _ => pow_pos (realCoordinateInv_denominator_pos (x i)) _
  rw [pinMajorantTwo_coordinate hN hp x s hx hx0]
  positivity

theorem pinMajorantOne_eq_exp {N : ℕ} (hN : 0 < N) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    pinMajorantOne N x s = Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 1 x s + Real.log 2 / 2)) *
      ((2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) / (2 : ℝ) ^ (n N * (Cdegree N - 1))) := by
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  rw [← Real.exp_log (pinMajorantOne_pos hN x s hx hs hx0 hxi hsi),
    log_pinMajorantOne hN x s hx hs hx0 hxi hsi, Real.exp_add, ← exp_sub_mul_log_two]
  congr 3
  rw [Nat.cast_mul, Nat.cast_sub hC, Nat.cast_one]

theorem pinMajorantTwo_eq_exp {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ≤ n N) (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    pinMajorantTwo N x s = Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 2 x s + Real.log 2 / 2)) *
      ((2 : ℝ) ^ (p * (Cdegree N - 1) + p.choose 2) /
        (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2)) := by
  have hC : 1 ≤ Cdegree N := Cdegree_pos hN
  rw [← Real.exp_log (pinMajorantTwo_pos hN hp x s hx hs hx0 hxi hsi),
    log_pinMajorantTwo hN hp x s hx hs hx0 hxi hsi, Real.exp_add, ← exp_sub_mul_log_two]
  congr 3
  push_cast [Nat.cast_sub hC]
  ring

/-- **Case one.** -/
theorem abs_mixedDouble_le_caseOne {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E) pinKernel
        (realCoordinateInv ∘ x) s| ≤
      ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2)) * (2 : ℝ) ^ (n N * m) *
        ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 1 x s + Real.log 2 / 2)) := by
  have hz := append_mem_of hx hy
  have hz0 := append_ne_zero_of hx0 hy
  have h1 := abs_mixedDouble_le_sheet hN hpm E hE hEn x y s hz hz0 hs
  set z : Fin (n N) → ℝ := fun c => Fin.append x y (Fin.cast hpm.symm c) with hzdef
  have hsheet := realSheetDeterminant_abs_le hN z (fun c => hz _) (fun c => hz0 _)
  have hprod : (∏ c : Fin (n N), ((1 + z c ^ 2) ^ (((n N : ℝ) - 1) / 2) *
      |z c| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)))) =
      (∏ i, sheetOneWeight N (x i)) * ∏ j, sheetOneWeight N (y j) := by
    change ∏ c : Fin (n N), sheetOneWeight N (Fin.append x y (Fin.cast hpm.symm c)) = _
    rw [prod_fin_cast hpm (fun c => sheetOneWeight N (Fin.append x y c)), Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hprod] at hsheet
  set K₂ : ℝ := (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) with hK₂
  have hK₂0 : 0 ≤ K₂ := mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  set P := p * (Cdegree N - 1) + p.choose 2 with hP
  set Ex := Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 1 x s + Real.log 2 / 2)) with hEx
  have hpm1 := pinMajorantOne_eq_exp hN x s hx hs hx0 hxi hsi
  have hfix : (∏ j, rowNodeWeight N (y j)) * (∏ j, sheetOneWeight N (y j)) ≤
      ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m := by
    rw [← prod_mul_distrib]
    calc ∏ j, rowNodeWeight N (y j) * sheetOneWeight N (y j)
        ≤ ∏ _j : Fin m, ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) := by
          apply prod_le_prod₀
          · intro j _
            exact mul_nonneg (rowNodeWeight_nonneg N ⟨(hy j).1, by linarith [(hy j).2]⟩)
              (mul_nonneg (Real.rpow_nonneg (by positivity) _)
                (zpow_nonneg (abs_nonneg _) _))
          · intro j _
            exact rowNodeWeight_mul_sheetOneWeight_le hN (hy j)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
  have hPP0 := pinPrincipal_nonneg N x s hx hs
  have hsOW0 : 0 ≤ ∏ i, sheetOneWeight N (x i) := prod_nonneg fun i _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (zpow_nonneg (abs_nonneg _) _)
  have hrnw0 : 0 ≤ ∏ j, rowNodeWeight N (y j) := prod_nonneg fun j _ =>
    rowNodeWeight_nonneg N ⟨(hy j).1, by linarith [(hy j).2]⟩
  have hsOWy0 : 0 ≤ ∏ j, sheetOneWeight N (y j) := prod_nonneg fun j _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (zpow_nonneg (abs_nonneg _) _)
  have hexp2 : (2 : ℝ) ^ ((Cdegree N - 1) * m) * (2 : ℝ) ^ P ≤
      (2 : ℝ) ^ (n N * (Cdegree N - 1)) * (2 : ℝ) ^ ((n N).choose 2) := by
    rw [← pow_add, ← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have hch : p.choose 2 ≤ (n N).choose 2 := Nat.choose_le_choose 2 (by omega)
    have : (Cdegree N - 1) * m + p * (Cdegree N - 1) = n N * (Cdegree N - 1) := by
      rw [← hpm]
      ring
    omega
  calc _ ≤ (2 : ℝ) ^ (n N * m) * |realSheetDeterminant N z| *
        (∏ j, rowNodeWeight N (y j)) * pinPrincipal N x s := h1
    _ ≤ (2 : ℝ) ^ (n N * m) * (K₂ / 2 ^ (n N).choose 2 *
          ((∏ i, sheetOneWeight N (x i)) * ∏ j, sheetOneWeight N (y j))) *
        (∏ j, rowNodeWeight N (y j)) * pinPrincipal N x s := by
        gcongr
    _ = (2 : ℝ) ^ (n N * m) * K₂ / 2 ^ (n N).choose 2 *
          ((∏ j, rowNodeWeight N (y j)) * (∏ j, sheetOneWeight N (y j))) *
          pinMajorantOne N x s := by
        unfold pinMajorantOne
        ring
    _ ≤ (2 : ℝ) ^ (n N * m) * K₂ / 2 ^ (n N).choose 2 *
          (((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m) *
          (Ex * ((2 : ℝ) ^ P / (2 : ℝ) ^ (n N * (Cdegree N - 1)))) := by
        rw [hpm1]
        gcongr
    _ = (2 : ℝ) ^ (n N * m) * K₂ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex *
          ((2 : ℝ) ^ ((Cdegree N - 1) * m) * (2 : ℝ) ^ P /
            ((2 : ℝ) ^ (n N * (Cdegree N - 1)) * (2 : ℝ) ^ ((n N).choose 2))) := by
        rw [mul_pow, ← pow_mul]
        field_simp
    _ ≤ (2 : ℝ) ^ (n N * m) * K₂ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex * 1 := by
        have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (by positivity)).mpr hexp2
    _ = _ := by ring

/-- **Case two.** -/
theorem abs_mixedDouble_le_caseTwo {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hzi : Function.Injective (Fin.append x y))
    (hcase : (∑ c : Fin (n N), (1 - (Fin.append x y (Fin.cast hpm.symm c)) ^ 2) /
        (1 + (Fin.append x y (Fin.cast hpm.symm c)) ^ 2)) ≤ ((n N - 1 - 2 * g N : ℕ) : ℝ)) :
    |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E) pinKernel
        (realCoordinateInv ∘ x) s| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * (2 : ℝ) ^ (n N * m) *
        ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 2 x s + Real.log 2 / 2)) := by
  have hp : p ≤ n N := by omega
  have hz := append_mem_of hx hy
  have hz0 := append_ne_zero_of hx0 hy
  have hy0 : ∀ j, y j ≠ 0 := fun j => (hy j).2.ne
  have hy' : ∀ j, y j ∈ Ioo (-1 : ℝ) 1 := fun j => ⟨(hy j).1, by linarith [(hy j).2]⟩
  have h1 := abs_mixedDouble_le_sheet hN hpm E hE hEn x y s hz hz0 hs
  set z : Fin (n N) → ℝ := fun c => Fin.append x y (Fin.cast hpm.symm c) with hzdef
  have hsheet := realSheetDeterminant_first_sheet_bound hN z (fun c => hz _) (fun c => hz0 _)
    (injective_fin_cast_comp hpm hzi) hcase
  set K₁ : ℝ := (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- split the inverse Vandermonde and the node powers
  set cross : ℝ := ∏ i : Fin p, ∏ j : Fin m, ((y j)⁻¹ - (x i)⁻¹) with hcross
  have hV : (∏ c : Fin (n N), ∏ c' ∈ Ioi c, ((z c')⁻¹ - (z c)⁻¹)) =
      (∏ i : Fin p, ∏ i' ∈ Ioi i, ((x i')⁻¹ - (x i)⁻¹)) * cross *
        ∏ j : Fin m, ∏ j' ∈ Ioi j, ((y j')⁻¹ - (y j)⁻¹) := by
    rw [hzdef, prod_Ioi_fin_cast hpm (fun a b => (Fin.append x y b)⁻¹ - (Fin.append x y a)⁻¹),
      prod_Ioi_append (fun u v => v⁻¹ - u⁻¹) x y]
  have hG : (∏ c : Fin (n N), |z c| ^ g N) = (∏ i, |x i| ^ g N) * ∏ j, |y j| ^ g N := by
    rw [hzdef, prod_fin_cast hpm (fun c => |Fin.append x y c| ^ g N), Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hV, hG, abs_mul, abs_mul] at hsheet
  set Vx := |∏ i : Fin p, ∏ i' ∈ Ioi i, ((x i')⁻¹ - (x i)⁻¹)| with hVx
  set Vy := |∏ j : Fin m, ∏ j' ∈ Ioi j, ((y j')⁻¹ - (y j)⁻¹)| with hVy
  set Py := ∏ j, |y j| ^ g N with hPy
  set Rw := ∏ j, rowNodeWeight N (y j) with hRw
  set Xm := ∏ i, |x i| ^ m with hXm
  have hXm0 : 0 < Xm := prod_pos fun i _ => pow_pos (abs_pos.mpr (hx0 i)) _
  have hRw0 : 0 ≤ Rw := prod_nonneg fun j _ => rowNodeWeight_nonneg N (hy' j)
  have hPy0 : 0 ≤ Py := prod_nonneg fun j _ => pow_nonneg (abs_nonneg _) _
  have hPP0 := pinPrincipal_nonneg N x s hx hs
  -- the fixed factor
  have hfix : |cross| * Xm * Vy * Py * Rw ≤
      (2 : ℝ) ^ (p * m) * ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m := by
    have hYp : 0 < ∏ j, |y j| ^ p := prod_pos fun j _ => pow_pos (abs_pos.mpr (hy0 j)) _
    have hYm : 0 < ∏ j, |y j| ^ (m - 1) := prod_pos fun j _ => pow_pos (abs_pos.mpr (hy0 j)) _
    have hc := cross_inv_bound x y hx hx0 hy
    have hv := fixed_vandermonde_inv_bound y hy
    have hw : (∏ j, (rowNodeWeight N (y j) * |y j| ^ g N / (|y j| ^ p * |y j| ^ (m - 1)))) ≤
        ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m := by
      calc _ ≤ ∏ _j : Fin m, ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) := by
            apply prod_le_prod₀
            · intro j _
              exact div_nonneg (mul_nonneg (rowNodeWeight_nonneg N (hy' j))
                (pow_nonneg (abs_nonneg _) _)) (by positivity)
            · intro j _
              exact rowNodeWeight_two_le hN hpm
                (Nat.one_le_iff_ne_zero.mpr (Fin.pos j).ne') (hy j)
        _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
    have hsplit : |cross| * Xm * Vy * Py * Rw =
        (|cross| * Xm * ∏ j, |y j| ^ p) * (Vy * ∏ j, |y j| ^ (m - 1)) *
          ∏ j, (rowNodeWeight N (y j) * |y j| ^ g N / (|y j| ^ p * |y j| ^ (m - 1))) := by
      rw [prod_div_distrib, prod_mul_distrib, prod_mul_distrib]
      field_simp
      simp only [hPy, hRw]
      ring
    rw [hsplit]
    calc _ ≤ (2 : ℝ) ^ (p * m) * 1 *
          ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m := by
          apply mul_le_mul (mul_le_mul hc hv (mul_nonneg (abs_nonneg _) hYm.le) (by positivity))
            hw (prod_nonneg fun j _ => div_nonneg (mul_nonneg (rowNodeWeight_nonneg N (hy' j))
              (pow_nonneg (abs_nonneg _) _)) (by positivity)) (by positivity)
      _ = _ := by ring
  -- the majorant
  set Ex := Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 2 x s + Real.log 2 / 2)) with hEx
  have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
  set P := p * (Cdegree N - 1) + p.choose 2 with hP
  have hpm2 := pinMajorantTwo_eq_exp hN hp x s hx hs hx0 hxi hsi
  have hmaj : Vx * (∏ i, |x i| ^ g N) * pinPrincipal N x s = pinMajorantTwo N x s * Xm := by
    unfold pinMajorantTwo
    have hnp : n N - p = m := by omega
    rw [hnp, ← hXm, ← hVx, div_mul_cancel₀ _ hXm0.ne']
    ring
  have hexp2 : (2 : ℝ) ^ (p * m) * (2 : ℝ) ^ ((Cdegree N - 1) * m) * (2 : ℝ) ^ P ≤
      (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2) := by
    rw [← pow_add, ← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have hch := two_mul_choose_two_add p m
    rw [hpm] at hch
    have : (Cdegree N - 1) * m + p * (Cdegree N - 1) = n N * (Cdegree N - 1) := by
      rw [← hpm]
      ring
    omega
  calc _ ≤ (2 : ℝ) ^ (n N * m) * |realSheetDeterminant N z| * Rw * pinPrincipal N x s := h1
    _ ≤ (2 : ℝ) ^ (n N * m) * (K₁ * (Vx * |cross| * Vy) * ((∏ i, |x i| ^ g N) * Py)) * Rw *
          pinPrincipal N x s := by
        gcongr
    _ = (2 : ℝ) ^ (n N * m) * K₁ * (Vx * (∏ i, |x i| ^ g N) * pinPrincipal N x s) *
          (|cross| * Vy * Py * Rw) := by ring
    _ = (2 : ℝ) ^ (n N * m) * K₁ * pinMajorantTwo N x s * (|cross| * Xm * Vy * Py * Rw) := by
        rw [hmaj]
        ring
    _ ≤ (2 : ℝ) ^ (n N * m) * K₁ *
          (Ex * ((2 : ℝ) ^ P / (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2))) *
          ((2 : ℝ) ^ (p * m) * ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m) := by
        rw [hpm2]
        gcongr
    _ = (2 : ℝ) ^ (n N * m) * K₁ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex *
          ((2 : ℝ) ^ (p * m) * (2 : ℝ) ^ ((Cdegree N - 1) * m) * (2 : ℝ) ^ P /
            (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2)) := by
        rw [mul_pow, ← pow_mul]
        field_simp
    _ ≤ (2 : ℝ) ^ (n N * m) * K₁ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (by positivity)).mpr hexp2
    _ = _ := by ring

end OAI.InternalCatalan
