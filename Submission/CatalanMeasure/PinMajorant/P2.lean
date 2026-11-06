module

public import Submission.CatalanMeasure.PinSupDual
public import Submission.CatalanMeasure.GenVandermondeSharp
public import Submission.CatalanMeasure.MixedAndreief
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealDeterminantCore
public import Submission.OAI.NumberTheory.Catalan.Analysis.RealEnergyLogMajorants
public import Submission.OAI.NumberTheory.Catalan.Analysis.RealFactoredIntegral
public import Submission.CatalanMeasure.PinMajorant.P1

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
