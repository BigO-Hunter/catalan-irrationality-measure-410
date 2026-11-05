module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Submission.CatalanMeasure.DeltaPoly
public import Submission.OAI.NumberTheory.Catalan.Determinants.RealRowAmplitude

@[expose] public section

/-!
# A quadrature formula for the coefficient of the constant

The coefficient matrix `L` of `Δ_N(X) = det (A₀ + X L)` only involves the polynomial rows
`rowP N r`, of degree `< H N`.  Lagrange interpolation at `J ≥ H N` distinct nodes
`τ_a ≤ 0` writes every coefficient of `rowP N r` through its values at the nodes, and for
`τ ≤ 0` OpenAI's real row amplitude is just the value of `rowP N r`.  So

  `L r k = ∑_a realRowAmplitude N r (τ_a) · β_{a,k}`,

with explicit weights `β`, bounded by `2 ^ (q + 2) ∏_{b ≠ a} (1 - τ_b) / |∏_{b ≠ a} (τ_a - τ_b)|`.
-/

open Polynomial Finset

namespace OAI.InternalCatalan

open scoped BigOperators

/-- Lagrange basis at the nodes `τ`. -/
noncomputable def quadBasis {J : ℕ} (τ : Fin J → ℝ) (a : Fin J) : ℝ[X] :=
  Lagrange.basis univ τ a

/-- The quadrature weights `β_{a,k}`. -/
noncomputable def quadWeight (N : ℕ) {J : ℕ} (τ : Fin J → ℝ) (a : Fin J) (k : ℕ) : ℝ :=
  ∑ v ∈ range (q N + 1), (filterCoeffRat N v : ℝ) *
    ∑ i ∈ range (H N), (quadBasis τ a).coeff i *
      (4 * (centralCoeffKernel ((i : ℤ) - ((b N + k + v : ℕ) : ℤ)) : ℝ))

theorem rowP_coeff_interpolate {N : ℕ} (hN : 0 < N) {J : ℕ} (hJ : H N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ) (r i : ℕ) :
    ((rowP N r).coeff i : ℝ) =
      ∑ a, (realPoly (rowP N r)).eval (τ a) * (quadBasis τ a).coeff i := by
  have hdeg : (realPoly (rowP N r)).degree < (#(univ : Finset (Fin J)) : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin]
    have h1 : (realPoly (rowP N r)).natDegree ≤ H N - 1 := by
      unfold realPoly
      exact (natDegree_map_le).trans (rowP_natDegree_le hN r)
    have hH : 0 < H N := by unfold H; omega
    calc (realPoly (rowP N r)).degree ≤ ((realPoly (rowP N r)).natDegree : WithBot ℕ) :=
          degree_le_natDegree
      _ < (J : WithBot ℕ) := by exact_mod_cast (show _ < J by omega)
  have h := Lagrange.eq_interpolate (s := (univ : Finset (Fin J))) (v := τ)
    (fun x _ y _ hxy => hτ hxy) hdeg
  rw [← realPoly_coeff]
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  apply sum_congr rfl
  intro a _
  rw [coeff_C_mul]
  rfl

/-- **Quadrature formula** for the coefficient of the constant. -/
theorem filteredCatalanCoeff_quadrature {N : ℕ} (hN : 0 < N) {J : ℕ} (hJ : H N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ) (hneg : ∀ a, τ a ≤ 0) (r k : ℕ) :
    (filteredCatalanCoeffRat N r k : ℝ) =
      ∑ a, realRowAmplitude N r (τ a) * quadWeight N τ a k := by
  unfold filteredCatalanCoeffRat rawCatalanCoeffRat quadWeight
  push_cast
  simp_rw [rowP_coeff_interpolate hN hJ hτ, realRowAmplitude_of_nonpos N r (hneg _)]
  calc _ = ∑ v ∈ range (q N + 1), ∑ i ∈ range (H N), ∑ a,
          (realPoly (rowP N r)).eval (τ a) * ((filterCoeffRat N v : ℝ) *
            ((quadBasis τ a).coeff i *
              (4 * (centralCoeffKernel ((i : ℤ) - ((b N : ℤ) + k + v)) : ℝ)))) := by
        apply sum_congr rfl
        intro v _
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [sum_mul, mul_sum]
        apply sum_congr rfl
        intro a _
        ring
    _ = ∑ v ∈ range (q N + 1), ∑ a, ∑ i ∈ range (H N),
          (realPoly (rowP N r)).eval (τ a) * ((filterCoeffRat N v : ℝ) *
            ((quadBasis τ a).coeff i *
              (4 * (centralCoeffKernel ((i : ℤ) - ((b N : ℤ) + k + v)) : ℝ)))) :=
        sum_congr rfl fun v _ => sum_comm
    _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        rw [mul_sum]
        apply sum_congr rfl
        intro v _
        rw [mul_sum, ← mul_sum]

theorem centralCoeffKernel_abs_le_one (d : ℤ) : |(centralCoeffKernel d : ℝ)| ≤ 1 := by
  unfold centralCoeffKernel
  split_ifs
  · unfold centralCoeff
    push_cast
    have h4 : (0 : ℝ) < 4 ^ (d.toNat / 2) := by positivity
    have hc : ((2 * (d.toNat / 2)).choose (d.toNat / 2) : ℝ) ≤ 4 ^ (d.toNat / 2) := by
      have h := Nat.choose_le_two_pow (2 * (d.toNat / 2)) (d.toNat / 2)
      have h' : ((2 * (d.toNat / 2)).choose (d.toNat / 2) : ℝ) ≤
          ((2 ^ (2 * (d.toNat / 2)) : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_pow, pow_mul] at h'
      norm_num at h'
      exact h'
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one h4).mpr hc
  · simp

theorem filterCoeffRat_abs (N v : ℕ) : |(filterCoeffRat N v : ℝ)| = ((q N).choose v : ℝ) := by
  unfold filterCoeffRat
  push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]

/-- Products of polynomials with nonnegative coefficients have nonnegative coefficients. -/
theorem coeff_prod_nonneg {ι : Type*} (s : Finset ι) (P : ι → ℝ[X])
    (hP : ∀ i ∈ s, ∀ j, 0 ≤ (P i).coeff j) (j : ℕ) : 0 ≤ (∏ i ∈ s, P i).coeff j := by
  revert j
  apply Finset.prod_induction _ (fun Q : ℝ[X] => ∀ j, 0 ≤ Q.coeff j)
  · intro Q R hQ hR j
    rw [coeff_mul]
    exact sum_nonneg fun x _ => mul_nonneg (hQ _) (hR _)
  · intro j
    rw [coeff_one]
    split_ifs <;> norm_num
  · exact hP

theorem quadBasis_eq {J : ℕ} (τ : Fin J → ℝ) (a : Fin J) :
    quadBasis τ a = C (∏ c ∈ univ.erase a, (τ a - τ c)⁻¹) *
      ∏ c ∈ univ.erase a, (X - C (τ c)) := by
  unfold quadBasis Lagrange.basis Lagrange.basisDivisor
  rw [prod_mul_distrib, map_prod]

theorem quadBasis_l1_le {J : ℕ} (τ : Fin J → ℝ) (hneg : ∀ a, τ a ≤ 0) (a : Fin J)
    {M : ℕ} (hM : M ≤ J) :
    ∑ i ∈ range M, |(quadBasis τ a).coeff i| ≤
      (∏ c ∈ univ.erase a, (1 - τ c)) / |∏ c ∈ univ.erase a, (τ a - τ c)| := by
  set P : ℝ[X] := ∏ c ∈ univ.erase a, (X - C (τ c)) with hP
  have hPnn : ∀ j, 0 ≤ P.coeff j := by
    apply coeff_prod_nonneg
    intro c _ j
    rw [coeff_sub, coeff_X, coeff_C]
    split_ifs <;> linarith [hneg c]
  have hPdeg : P.natDegree < J := by
    have h1 : P.natDegree ≤ ∑ c ∈ univ.erase a, (X - C (τ c)).natDegree := natDegree_prod_le _ _
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one] at h1
    have h2 : (univ.erase a).card = J - 1 := by
      rw [card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]
    have := a.isLt
    omega
  have heval : P.eval 1 = ∏ c ∈ univ.erase a, (1 - τ c) := by
    rw [hP, eval_prod]
    simp
  have hsum : ∑ i ∈ range M, P.coeff i ≤ P.eval 1 := by
    rw [eval_eq_sum_range' hPdeg]
    simp only [one_pow, mul_one]
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hM) (fun i _ _ => hPnn i)
  rw [quadBasis_eq]
  simp only [coeff_C_mul, abs_mul]
  rw [← mul_sum, ← heval, div_eq_inv_mul, ← abs_inv, ← prod_inv_distrib]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc ∑ i ∈ range M, |P.coeff i| = ∑ i ∈ range M, P.coeff i :=
        sum_congr rfl fun i _ => abs_of_nonneg (hPnn i)
    _ ≤ P.eval 1 := hsum

/-- Bound on the quadrature weights. -/
theorem quadWeight_abs_le {N : ℕ} {J : ℕ} (hJ : H N ≤ J) (τ : Fin J → ℝ)
    (hneg : ∀ a, τ a ≤ 0) (a : Fin J) (k : ℕ) :
    |quadWeight N τ a k| ≤ 2 ^ (q N + 2) *
      ((∏ c ∈ univ.erase a, (1 - τ c)) / |∏ c ∈ univ.erase a, (τ a - τ c)|) := by
  unfold quadWeight
  set B := (∏ c ∈ univ.erase a, (1 - τ c)) / |∏ c ∈ univ.erase a, (τ a - τ c)| with hB
  have hinner : ∀ v, |∑ i ∈ range (H N), (quadBasis τ a).coeff i *
      (4 * (centralCoeffKernel ((i : ℤ) - ((b N + k + v : ℕ) : ℤ)) : ℝ))| ≤ 4 * B := by
    intro v
    calc _ ≤ ∑ i ∈ range (H N), |(quadBasis τ a).coeff i *
          (4 * (centralCoeffKernel ((i : ℤ) - ((b N + k + v : ℕ) : ℤ)) : ℝ))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (H N), |(quadBasis τ a).coeff i| * 4 := by
          apply sum_le_sum
          intro i _
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have := centralCoeffKernel_abs_le_one ((i : ℤ) - ((b N + k + v : ℕ) : ℤ))
          linarith
      _ = 4 * ∑ i ∈ range (H N), |(quadBasis τ a).coeff i| := by rw [← sum_mul, mul_comm]
      _ ≤ 4 * B := mul_le_mul_of_nonneg_left (quadBasis_l1_le τ hneg a hJ) (by norm_num)
  have hB0 : 0 ≤ B := by
    rw [hB]
    apply div_nonneg _ (abs_nonneg _)
    exact prod_nonneg fun c _ => by linarith [hneg c]
  calc _ ≤ ∑ v ∈ range (q N + 1), |(filterCoeffRat N v : ℝ) *
        ∑ i ∈ range (H N), (quadBasis τ a).coeff i *
          (4 * (centralCoeffKernel ((i : ℤ) - ((b N + k + v : ℕ) : ℤ)) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ range (q N + 1), ((q N).choose v : ℝ) * (4 * B) := by
        apply sum_le_sum
        intro v _
        rw [abs_mul, filterCoeffRat_abs]
        exact mul_le_mul_of_nonneg_left (hinner v) (Nat.cast_nonneg _)
    _ = 2 ^ (q N) * (4 * B) := by
        rw [← sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ = 2 ^ (q N + 2) * B := by ring

end OAI.InternalCatalan
