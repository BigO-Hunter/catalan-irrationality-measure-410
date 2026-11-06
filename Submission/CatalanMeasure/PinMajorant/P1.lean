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

end OAI.InternalCatalan
