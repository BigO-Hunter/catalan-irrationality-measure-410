module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Chebyshev nodes on `[-1, 0]`

The nodes `τ_a = (x_a - 1) / 2`, where `x_a = cos ((2a+1) π / (2J))` are the roots of the
Chebyshev polynomial `T_J`, satisfy the Lagrange-weight bound

  `∏_{c ≠ a} (1 - τ_c) / |∏_{c ≠ a} (τ_a - τ_c)| ≤ (3 + 2√2) ^ J`.

Indeed `T_J = 2^(J-1) ∏ (X - x_c)`.  The numerator is at most `∏_c (3 - x_c) / 2^J =
T_J(3) / 2^(2J-1)`, and `T_J(3) = cosh (J log (3 + 2√2)) ≤ (3 + 2√2)^J`.  The denominator is
`2^(1-J) |∏_{c ≠ a} (x_a - x_c)| = 2^(2-2J) J |U_{J-1}(x_a)|`, and
`|U_{J-1}(x_a) sin θ_a| = |sin (J θ_a)| = 1`, so `|U_{J-1}(x_a)| ≥ 1`.
-/

open Polynomial Polynomial.Chebyshev Real Finset

set_option autoImplicit false

namespace CatalanMeasure

/-- The Chebyshev angles. -/
noncomputable def chebAngle (J : ℕ) (a : ℕ) : ℝ := (2 * (a : ℝ) + 1) * π / (2 * J)

/-- The roots of `T_J`. -/
noncomputable def chebX (J : ℕ) (a : Fin J) : ℝ := cos (chebAngle J a)

/-- The Chebyshev nodes on `[-1, 0]`. -/
noncomputable def chebNode (J : ℕ) (a : Fin J) : ℝ := (chebX J a - 1) / 2

theorem chebAngle_mem {J a : ℕ} (ha : a < J) : chebAngle J a ∈ Set.Ioo 0 π := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have ha' : (2 * (a : ℝ) + 1) < 2 * J := by
    have : (a : ℝ) + 1 ≤ J := by exact_mod_cast ha
    linarith
  unfold chebAngle
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

theorem chebX_mem {J : ℕ} (a : Fin J) : chebX J a ∈ Set.Ioo (-1 : ℝ) 1 := by
  have h := chebAngle_mem a.isLt
  unfold chebX
  constructor
  · rw [← cos_pi]
    exact strictAntiOn_cos (Set.Ioo_subset_Icc_self h) ⟨pi_pos.le, le_rfl⟩ h.2
  · rw [← cos_zero]
    exact strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ (Set.Ioo_subset_Icc_self h) h.1

theorem chebNode_mem {J : ℕ} (a : Fin J) : chebNode J a ∈ Set.Ioo (-1 : ℝ) 0 := by
  have h := chebX_mem a
  unfold chebNode
  constructor <;> linarith [h.1, h.2]

theorem chebX_injective (J : ℕ) : Function.Injective (chebX J) := by
  intro a b hab
  have ha := chebAngle_mem a.isLt
  have hb := chebAngle_mem b.isLt
  have h := injOn_cos (Set.Ioo_subset_Icc_self ha) (Set.Ioo_subset_Icc_self hb) hab
  have hJ : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by have := a.isLt; omega)
  unfold chebAngle at h
  rw [div_left_inj' (by positivity)] at h
  have h' : ((a : ℕ) : ℝ) = (b : ℕ) := by nlinarith [pi_pos]
  exact Fin.ext (by exact_mod_cast h')

theorem chebNode_injective (J : ℕ) : Function.Injective (chebNode J) := by
  intro a b hab
  apply chebX_injective J
  unfold chebNode at hab
  linarith

/-- `T_J = 2^(J-1) ∏ (X - x_c)`. -/
theorem T_eq_nodal {J : ℕ} (hJ : 0 < J) :
    T ℝ (J : ℤ) = C ((2 : ℝ) ^ (J - 1)) * ∏ c : Fin J, (X - C (chebX J c)) := by
  have hcard : Multiset.card (T ℝ (J : ℤ)).roots = (T ℝ (J : ℤ)).natDegree := by
    rw [roots_T_real, natDegree_T, Int.natAbs_natCast, Finset.card_val,
      Finset.card_image_of_injOn, Finset.card_range]
    exact (Finset.range J).nodup_map_iff_injOn.mp (roots_T_real_nodup J)
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [leadingCoeff_T, Int.natAbs_natCast] at h
  conv_lhs => rw [← h]
  congr 1
  rw [roots_T_real, Finset.image_val_of_injOn
    ((Finset.range J).nodup_map_iff_injOn.mp (roots_T_real_nodup J)), Multiset.map_map,
    ← Finset.prod_eq_multiset_prod]
  simp only [Function.comp_def]
  rw [← Fin.prod_univ_eq_prod_range (fun k => X - C (cos ((2 * (k : ℝ) + 1) * π / (2 * J)))) J]
  rfl

/-- `T_J (3) ≤ (3 + 2√2)^J`. -/
theorem T_eval_three_le (J : ℕ) :
    (T ℝ (J : ℤ)).eval 3 ≤ (3 + 2 * √2) ^ J := by
  set z : ℝ := 3 + 2 * √2 with hz
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hz0 : 0 < z := by positivity
  have hzinv : z⁻¹ = 3 - 2 * √2 := by
    have hmul : z * (3 - 2 * √2) = 1 := by rw [hz]; nlinarith
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  have h3 : cosh (Real.log z) = 3 := by
    rw [cosh_eq, Real.exp_neg, Real.exp_log hz0, hzinv]
    ring
  rw [← h3, T_real_cosh, cosh_eq]
  have h1 : Real.exp (-((J : ℤ) * Real.log z)) ≤ Real.exp ((J : ℤ) * Real.log z) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Real.log z := Real.log_nonneg (by nlinarith)
    have : (0 : ℝ) ≤ ((J : ℤ) : ℝ) := by exact_mod_cast Int.natCast_nonneg J
    nlinarith
  have h2 : Real.exp ((J : ℤ) * Real.log z) = z ^ J := by
    rw [show ((J : ℤ) : ℝ) = (J : ℝ) by norm_cast, Real.exp_nat_mul, Real.exp_log hz0]
  linarith

/-- The Lagrange ratio at the Chebyshev nodes. -/
theorem chebNode_ratio_le {J : ℕ} (a : Fin J) :
    (∏ c ∈ univ.erase a, (1 - chebNode J c)) /
        |∏ c ∈ univ.erase a, (chebNode J a - chebNode J c)| ≤ (3 + 2 * √2) ^ J := by
  have hJ : 0 < J := by have := a.isLt; omega
  have hTeq := T_eq_nodal hJ
  set ω : ℝ[X] := ∏ c : Fin J, (X - C (chebX J c)) with hω
  have h2pos : (0 : ℝ) < 2 ^ (J - 1) := by positivity
  -- the numerator
  have hnum : ∏ c ∈ univ.erase a, (1 - chebNode J c) ≤
      (T ℝ (J : ℤ)).eval 3 / (2 ^ J * 2 ^ (J - 1)) := by
    have hge : ∀ c, 1 ≤ 1 - chebNode J c := fun c => by linarith [(chebNode_mem c).2]
    have hsub : ∏ c ∈ univ.erase a, (1 - chebNode J c) ≤ ∏ c, (1 - chebNode J c) := by
      rw [← Finset.prod_erase_mul _ _ (mem_univ a)]
      exact le_mul_of_one_le_right (prod_nonneg fun c _ => by linarith [hge c]) (hge a)
    have hfull : ∏ c, (1 - chebNode J c) = ω.eval 3 / 2 ^ J := by
      rw [hω, eval_prod]
      have hc : ∀ c, 1 - chebNode J c = (eval 3 (X - C (chebX J c))) / 2 := by
        intro c
        simp only [chebNode, eval_sub, eval_X, eval_C]
        ring
      rw [prod_congr rfl (fun c _ => hc c), prod_div_distrib, prod_const, card_univ,
        Fintype.card_fin]
    have hT3 : (T ℝ (J : ℤ)).eval 3 = 2 ^ (J - 1) * ω.eval 3 := by
      rw [hTeq, eval_mul, eval_C]
    rw [hT3]
    calc ∏ c ∈ univ.erase a, (1 - chebNode J c) ≤ ω.eval 3 / 2 ^ J := hfull ▸ hsub
      _ = 2 ^ (J - 1) * ω.eval 3 / (2 ^ J * 2 ^ (J - 1)) := by field_simp
  -- the denominator
  have hden : (J : ℝ) / (2 ^ (J - 1) * 2 ^ (J - 1)) ≤
      |∏ c ∈ univ.erase a, (chebNode J a - chebNode J c)| := by
    have hprod : ∏ c ∈ univ.erase a, (chebNode J a - chebNode J c) =
        (∏ c ∈ univ.erase a, (chebX J a - chebX J c)) / 2 ^ (J - 1) := by
      rw [eq_div_iff (by positivity)]
      have hcard : (univ.erase a).card = J - 1 := by simp
      rw [← hcard, ← prod_const (2 : ℝ), ← prod_mul_distrib]
      apply prod_congr rfl
      intro c _
      simp only [chebNode]
      ring
    have hderiv : ∏ c ∈ univ.erase a, (chebX J a - chebX J c) =
        (derivative ω).eval (chebX J a) := by
      have h1 := Lagrange.eval_nodal_derivative_eval_node_eq (s := (univ : Finset (Fin J)))
        (v := chebX J) (mem_univ a)
      rw [Lagrange.eval_nodal] at h1
      rw [← h1, Lagrange.nodal_eq]
    have hTd : (derivative (T ℝ (J : ℤ))).eval (chebX J a) =
        2 ^ (J - 1) * (derivative ω).eval (chebX J a) := by
      rw [hTeq, derivative_C_mul, eval_mul, eval_C]
    have hU : (derivative (T ℝ (J : ℤ))).eval (chebX J a) =
        J * (U ℝ ((J : ℤ) - 1)).eval (chebX J a) := by
      rw [T_derivative_eq_U, eval_mul]
      simp
    have hUabs : 1 ≤ |(U ℝ ((J : ℤ) - 1)).eval (chebX J a)| := by
      have h := U_real_cos (chebAngle J a) ((J : ℤ) - 1)
      have hsin : sin ((((J : ℤ) - 1 : ℤ) + 1) * chebAngle J a) =
          sin ((2 * (a : ℝ) + 1) * (π / 2)) := by
        congr 1
        have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
        unfold chebAngle
        push_cast
        field_simp
        ring
      have hsin1 : |sin ((2 * (a : ℝ) + 1) * (π / 2))| = 1 := by
        rw [show (2 * (a : ℝ) + 1) * (π / 2) = π / 2 + (a : ℕ) * π by ring,
          sin_add_nat_mul_pi, sin_pi_div_two, mul_one, abs_pow, abs_neg, abs_one, one_pow]
      unfold chebX
      have hprod := congrArg abs h
      rw [abs_mul, hsin, hsin1] at hprod
      have hs : |sin (chebAngle J a)| ≤ 1 := abs_sin_le_one _
      have hU0 : 0 ≤ |(U ℝ ((J : ℤ) - 1)).eval (cos (chebAngle J a))| := abs_nonneg _
      nlinarith
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    rw [hprod, hderiv, abs_div, abs_of_pos h2pos]
    have hω' : (derivative ω).eval (chebX J a) =
        J * (U ℝ ((J : ℤ) - 1)).eval (chebX J a) / 2 ^ (J - 1) := by
      rw [eq_div_iff h2pos.ne', mul_comm, ← hTd, hU]
    have : |(derivative ω).eval (chebX J a)| = J * |(U ℝ ((J : ℤ) - 1)).eval (chebX J a)| /
        2 ^ (J - 1) := by
      rw [hω', abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg J), abs_of_pos h2pos]
    rw [this, div_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  -- combine
  have hT3 := T_eval_three_le J
  have hdpos : 0 < (J : ℝ) / (2 ^ (J - 1) * 2 ^ (J - 1)) := by
    have : (0 : ℝ) < J := by exact_mod_cast hJ
    positivity
  have hnum0 : 0 ≤ ∏ c ∈ univ.erase a, (1 - chebNode J c) :=
    prod_nonneg fun c _ => by linarith [(chebNode_mem c).2]
  calc (∏ c ∈ univ.erase a, (1 - chebNode J c)) /
        |∏ c ∈ univ.erase a, (chebNode J a - chebNode J c)|
      ≤ ((T ℝ (J : ℤ)).eval 3 / (2 ^ J * 2 ^ (J - 1))) /
          ((J : ℝ) / (2 ^ (J - 1) * 2 ^ (J - 1))) :=
        div_le_div₀ (le_trans hnum0 hnum) hnum hdpos hden
    _ = (T ℝ (J : ℤ)).eval 3 / (2 * J) := by
        have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
        have h2J : (2 : ℝ) ^ J = 2 * 2 ^ (J - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h2J]
        field_simp
    _ ≤ (3 + 2 * √2) ^ J / 1 := by
        apply div_le_div₀ (by positivity) hT3 one_pos
        have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
        linarith
    _ = (3 + 2 * √2) ^ J := div_one _

end CatalanMeasure
