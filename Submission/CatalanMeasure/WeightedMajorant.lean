module

public import Submission.CatalanMeasure.PinMajorant
public import Submission.CatalanMeasure.VandermondeProduct
public import Submission.CatalanMeasure.WeightedEnergy

@[expose] public section

open Finset Set
open scoped BigOperators

namespace OAI.InternalCatalan

theorem weighted_pin_exp {N p m : ℕ} (hN : 0 < N) (hpm : p + m = n N)
    (k : ℝ) (x s : Fin p → ℝ) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    (∏ j : Fin p, (1 + s j)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N k x s + Real.log 2 / 2)) =
      Real.exp ((n N : ℝ) ^ 2 *
        (pinWeightedValue N k (((n N : ℝ) - p) / (n N : ℝ)) x s + Real.log 2 / 2)) := by
  have hn : (0 : ℝ) < n N := Nat.cast_pos.mpr (by unfold n; omega)
  have hp : 0 < ∏ j : Fin p, (1 + s j) := prod_pos (fun j _ => by linarith [(hs j).1])
  have hlog : Real.log (∏ j : Fin p, (1 + s j)) = ∑ j, Real.log (1 + s j) :=
    Real.log_prod (fun j _ => by linarith [(hs j).1])
  have hmR : (m : ℝ) = (n N : ℝ) - p := by rw [← hpm]; push_cast; ring
  rw [← Real.exp_log hp, ← Real.exp_nat_mul, hlog, ← Real.exp_add]
  congr 1
  unfold pinWeightedValue
  rw [← hmR]
  field_simp
  ring

theorem weighted_pin_majorant_eq {N p m : ℕ} (hN : 0 < N) (hpm : p + m = n N)
    (K k : ℝ) (x s : Fin p → ℝ) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    K * (∏ j : Fin p, (1 + s j)) ^ m * ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N k x s + Real.log 2 / 2)) =
      K * ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 *
          (pinWeightedValue N k (((n N : ℝ) - p) / (n N : ℝ)) x s + Real.log 2 / 2)) := by
  calc
    _ = K * ((2 : ℝ) ^ (2 * h N)) ^ m *
        ((∏ j : Fin p, (1 + s j)) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N k x s + Real.log 2 / 2))) := by ring
    _ = _ := by rw [weighted_pin_exp hN hpm k x s hs]

theorem abs_mixedDouble_le_sheet_product {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hz : ∀ c, Fin.append x y c ∈ Ioo (-1 : ℝ) 1) (hz0 : ∀ c, Fin.append x y c ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E) pinKernel
        (realCoordinateInv ∘ x) s| ≤
      (∏ j : Fin p, (1 + s j)) ^ m *
        |realSheetDeterminant N (fun c => Fin.append x y (Fin.cast hpm.symm c))| *
        (∏ j, rowNodeWeight N (y j)) * pinPrincipal N x s := by
  have hweighted0 : 0 ≤ (∏ j : Fin p, (1 + s j)) ^ m :=
    pow_nonneg (prod_nonneg (fun j _ => by linarith [(hs j).1])) _
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
  have hGV0 := CatalanMeasure.genVandermonde_abs_le_product s (fun j => ⟨(hs j).1.le, (hs j).2.le⟩)
    E hE hEn
  have hm : n N - p = m := by omega
  rw [hm] at hGV0
  have hGV := hGV0
  have hGb : |(Matrix.of fun j i : Fin p => pinColFun N E i (s j)).det| ≤
      (∏ j, (s j ^ b N * (1 - s j) ^ q N)) *
        ((∏ j : Fin p, (1 + s j)) ^ m * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|) := by
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
          ((∏ j : Fin p, (1 + s j)) ^ m * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|)) :=
        mul_le_mul_of_nonneg_left hGb (mul_nonneg hS0 hK0)
    _ = _ := by
        unfold pinPrincipal
        ring


theorem abs_mixedDouble_le_caseOne_product {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E) pinKernel
        (realCoordinateInv ∘ x) s| ≤
      ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2)) * (∏ j : Fin p, (1 + s j)) ^ m *
        ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 1 x s + Real.log 2 / 2)) := by
  have hweighted0 : 0 ≤ (∏ j : Fin p, (1 + s j)) ^ m :=
    pow_nonneg (prod_nonneg (fun j _ => by linarith [(hs j).1])) _
  have hz := append_mem_of hx hy
  have hz0 := append_ne_zero_of hx0 hy
  have h1 := abs_mixedDouble_le_sheet_product hN hpm E hE hEn x y s hz hz0 hs
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
  calc _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * |realSheetDeterminant N z| *
        (∏ j, rowNodeWeight N (y j)) * pinPrincipal N x s := h1
    _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * (K₂ / 2 ^ (n N).choose 2 *
          ((∏ i, sheetOneWeight N (x i)) * ∏ j, sheetOneWeight N (y j))) *
        (∏ j, rowNodeWeight N (y j)) * pinPrincipal N x s := by
        gcongr
    _ = (∏ j : Fin p, (1 + s j)) ^ m * K₂ / 2 ^ (n N).choose 2 *
          ((∏ j, rowNodeWeight N (y j)) * (∏ j, sheetOneWeight N (y j))) *
          pinMajorantOne N x s := by
        unfold pinMajorantOne
        ring
    _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * K₂ / 2 ^ (n N).choose 2 *
          (((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m) *
          (Ex * ((2 : ℝ) ^ P / (2 : ℝ) ^ (n N * (Cdegree N - 1)))) := by
        rw [hpm1]
        gcongr
    _ = (∏ j : Fin p, (1 + s j)) ^ m * K₂ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex *
          ((2 : ℝ) ^ ((Cdegree N - 1) * m) * (2 : ℝ) ^ P /
            ((2 : ℝ) ^ (n N * (Cdegree N - 1)) * (2 : ℝ) ^ ((n N).choose 2))) := by
        rw [mul_pow, ← pow_mul]
        field_simp
    _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * K₂ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex * 1 := by
        have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (by positivity)).mpr hexp2
    _ = _ := by ring

/-- **Case two.** -/
theorem abs_mixedDouble_le_caseTwo_product {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (hzi : Function.Injective (Fin.append x y))
    (hcase : (∑ c : Fin (n N), (1 - (Fin.append x y (Fin.cast hpm.symm c)) ^ 2) /
        (1 + (Fin.append x y (Fin.cast hpm.symm c)) ^ 2)) ≤ ((n N - 1 - 2 * g N : ℕ) : ℝ)) :
    |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E) pinKernel
        (realCoordinateInv ∘ x) s| ≤
      (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N * (∏ j : Fin p, (1 + s j)) ^ m *
        ((2 : ℝ) ^ (2 * h N)) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (pinFiniteValue N 2 x s + Real.log 2 / 2)) := by
  have hweighted0 : 0 ≤ (∏ j : Fin p, (1 + s j)) ^ m :=
    pow_nonneg (prod_nonneg (fun j _ => by linarith [(hs j).1])) _
  have hp : p ≤ n N := by omega
  have hz := append_mem_of hx hy
  have hz0 := append_ne_zero_of hx0 hy
  have hy0 : ∀ j, y j ≠ 0 := fun j => (hy j).2.ne
  have hy' : ∀ j, y j ∈ Ioo (-1 : ℝ) 1 := fun j => ⟨(hy j).1, by linarith [(hy j).2]⟩
  have h1 := abs_mixedDouble_le_sheet_product hN hpm E hE hEn x y s hz hz0 hs
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
  calc _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * |realSheetDeterminant N z| * Rw * pinPrincipal N x s := h1
    _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * (K₁ * (Vx * |cross| * Vy) * ((∏ i, |x i| ^ g N) * Py)) * Rw *
          pinPrincipal N x s := by
        gcongr
    _ = (∏ j : Fin p, (1 + s j)) ^ m * K₁ * (Vx * (∏ i, |x i| ^ g N) * pinPrincipal N x s) *
          (|cross| * Vy * Py * Rw) := by ring
    _ = (∏ j : Fin p, (1 + s j)) ^ m * K₁ * pinMajorantTwo N x s * (|cross| * Xm * Vy * Py * Rw) := by
        rw [hmaj]
        ring
    _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * K₁ *
          (Ex * ((2 : ℝ) ^ P / (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2))) *
          ((2 : ℝ) ^ (p * m) * ((2 : ℝ) ^ (Cdegree N - 1) * (2 : ℝ) ^ (2 * h N)) ^ m) := by
        rw [hpm2]
        gcongr
    _ = (∏ j : Fin p, (1 + s j)) ^ m * K₁ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex *
          ((2 : ℝ) ^ (p * m) * (2 : ℝ) ^ ((Cdegree N - 1) * m) * (2 : ℝ) ^ P /
            (2 : ℝ) ^ (n N * (Cdegree N - 1) + (n N).choose 2)) := by
        rw [mul_pow, ← pow_mul]
        field_simp
    _ ≤ (∏ j : Fin p, (1 + s j)) ^ m * K₁ * ((2 : ℝ) ^ (2 * h N)) ^ m * Ex * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_one (by positivity)).mpr hexp2
    _ = _ := by ring

end OAI.InternalCatalan
