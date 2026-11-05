module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Submission.OAI.NumberTheory.Catalan.Estimates.TwoAdicSelectorExponent
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.FinitePlacePartialAssembly
public import Submission.CatalanMeasure.Parametric.TwoAdicCoefficientEntryBounds

@[expose] public section

/-!
# The 2-adic bound for an arbitrary design (module 8 of the G-displacement Lean plan)

Design-free.  With `n = P.n N`, `H = P.H N`, `C = P.C N`, `b = P.b N` the 2-adic norm of the
determinant is at most `(8 F H²)^n · 2^(A2 + 3n/2)` where
`A2 = (n + H - b)²/8 - n²/2` (the minimum of the selector budget; derivation: the selector budget
`(3/2)m² + (1/2)l² - (H + C - b) m - C l + C n` on `m + l ≤ n`, `n ≤ C`, is bounded below by `-A2`,
with the sum-of-squares identity of `quad_bound`).  For `P20` this is `A2 = 42 N²`; for
`(58,9,3,5,3)` it is `2673/8 N²`, i.e. `a2 = 2673/26912` in units of `n²`.  The constants enter only
through `P`; the instance supplies nothing but `P`.
-/

namespace CatalanMeasure.GenD
namespace TwoAdic

open Polynomial CatalanMeasure.Parametric OAI.InternalCatalan Finset Filter
open scoped BigOperators Topology

noncomputable section

/-- The quadratic part of the selector budget minimum. -/
def A2 (n H b : ℝ) : ℝ := (n + H - b) ^ 2 / 8 - n ^ 2 / 2

/-- Sum-of-squares bound: the selector budget is at least `-A2`. -/
theorem quad_bound {n C H b m l : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l) (hml : m + l ≤ n)
    (hCn : n ≤ C) :
    -A2 n H b ≤ (3 / 2) * m ^ 2 + (1 / 2) * l ^ 2 - (H + C - b) * m - C * l + C * n := by
  unfold A2
  have hs : 0 ≤ n - m - l := by linarith only [hml]
  have hc : 0 ≤ C - n + m := by linarith only [hCn, hm]
  have key : (3 / 2) * m ^ 2 + (1 / 2) * l ^ 2 - (H + C - b) * m - C * l + C * n +
      ((n + H - b) ^ 2 / 8 - n ^ 2 / 2) =
      2 * (m - (n + H - b) / 4) ^ 2 + (n - m - l) * (C - n + m) + (1 / 2) * (n - m - l) ^ 2 := by
    ring
  have := mul_nonneg hs hc
  nlinarith only [key, this, sq_nonneg (m - (n + H - b) / 4), sq_nonneg (n - m - l)]

private theorem triangle_product (m : ℕ) :
    ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
  cases m with
  | zero => norm_num
  | succ m => simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring

private theorem distinct_twice {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f (s : Set ι)) (b : ℕ) (hb : ∀ i ∈ s, b ≤ f i) :
    2 * ((s.card : ℝ) * (b : ℝ)) + (s.card : ℝ) * ((s.card : ℝ) - 1) ≤ 2 * ∑ i ∈ s, (f i : ℝ) := by
  have hs : s.card * b + (∑ k ∈ range s.card, k) ≤ ∑ i ∈ s, f i := by
    rw [sum_range_id]
    exact distinct_indices_sum_lower_of_le s f hf b hb
  have hg := sum_range_id_mul_two s.card
  have hn : 2 * (s.card * b) + s.card * (s.card - 1) ≤ 2 * ∑ i ∈ s, f i := by omega
  have hr : 2 * ((s.card : ℝ) * (b : ℝ)) + ((s.card * (s.card - 1) : ℕ) : ℝ) ≤
      2 * ∑ i ∈ s, (f i : ℝ) := by exact_mod_cast hn
  rwa [triangle_product] at hr

/-- The exponent budget for selector data. -/
theorem selector_budget {ι : Type*} (n H C b : ℕ) (hCn : n ≤ C) (E B : Finset ι)
    (u j : ι → ℕ) (huE : Set.InjOn u (E : Set ι)) (huB : Set.InjOn u (B : Set ι))
    (hjE : Set.InjOn j (E : Set ι)) (hb : ∀ k ∈ E, b ≤ j k)
    (hcard : E.card + B.card ≤ n) :
    -A2 n H b - (3 / 2) * n ≤
      ((2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) - (H : ℤ) * (E.card : ℤ) +
        (∑ k ∈ B, (u k : ℤ)) + (C : ℤ) * ((n : ℤ) - (E.card : ℤ) - (B.card : ℤ)) : ℤ) : ℝ) := by
  have hE := distinct_twice E u huE 0 (by simp)
  have hB := distinct_twice B u huB 0 (by simp)
  have hJ := distinct_twice E j hjE b hb
  simp only [Nat.cast_zero, mul_zero, zero_add] at hE hB
  have hm : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hml : (E.card : ℝ) + (B.card : ℝ) ≤ n := by exact_mod_cast hcard
  have hCnR : (n : ℝ) ≤ C := by exact_mod_cast hCn
  have hq := quad_bound (n := (n : ℝ)) (C := (C : ℝ)) (H := (H : ℝ)) (b := (b : ℝ)) hm hl hml hCnR
  push_cast
  nlinarith only [hE, hB, hJ, hq, hm, hl, hml]

/-- Selector budget for a labelled family of `n` columns (`τ = 0` pole column, `1` exception,
`2` boundary). -/
theorem selector_exponent_lower (n H C b : ℕ) (hCn : n ≤ C)
    (τ : Fin n → Fin 3) (u j : Fin n → ℕ)
    (huE : Set.InjOn u {k | τ k = 1}) (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, b ≤ j k) :
    -A2 n H b - (3 / 2) * n ≤
      ((∑ k : Fin n,
        if τ k = 0 then (C : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ)
        else (u k : ℤ) : ℤ) : ℝ) := by
  classical
  let E : Finset (Fin n) := Finset.univ.filter (fun k => τ k = 1)
  let B : Finset (Fin n) := Finset.univ.filter (fun k => τ k = 2)
  have huE' : Set.InjOn u (E : Set (Fin n)) := by
    intro x hx y hy hxy
    exact huE (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have huB' : Set.InjOn u (B : Set (Fin n)) := by
    intro x hx y hy hxy
    exact huB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have hdisj : Disjoint E B := by
    apply Finset.disjoint_left.mpr
    intro k hkE hkB
    have he : τ k = 1 := (Finset.mem_filter.mp hkE).2
    have hb' : τ k = 2 := (Finset.mem_filter.mp hkB).2
    have hn : (1 : Fin 3) = 2 := he.symm.trans hb'
    norm_num at hn
  have hcard : E.card + B.card ≤ n := by
    have hc := Finset.card_le_card (Finset.subset_univ (E ∪ B))
    rw [Finset.card_union_of_disjoint hdisj] at hc
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have heach (k : Fin n) :
      (if τ k = 0 then (C : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ)
        else (u k : ℤ)) =
      (C : ℤ) +
        (if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ) - (C : ℤ) else 0) +
        (if τ k = 2 then (u k : ℤ) - (C : ℤ) else 0) := by
    by_cases h₀ : τ k = 0
    · simp [h₀]
    by_cases h₁ : τ k = 1
    · simp [h₁]
    have h₂ : τ k = 2 := by omega
    simp [h₂]
  have hsumE : (∑ k : Fin n,
      if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ) - (C : ℤ) else 0) =
      ∑ k ∈ E, (2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ) - (C : ℤ)) := by
    simp only [E, Finset.sum_filter]
  have hsumB : (∑ k : Fin n, if τ k = 2 then (u k : ℤ) - (C : ℤ) else 0) =
      ∑ k ∈ B, ((u k : ℤ) - (C : ℤ)) := by
    simp only [B, Finset.sum_filter]
  have hsumC : (∑ _ : Fin n, (C : ℤ)) = (n : ℤ) * (C : ℤ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Int.nsmul_eq_mul]
  have hsum : (∑ k : Fin n,
      if τ k = 0 then (C : ℤ)
      else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ)
      else (u k : ℤ)) =
      2 * (∑ k ∈ E, (u k : ℤ)) + (∑ k ∈ E, (j k : ℤ)) - (H : ℤ) * (E.card : ℤ) +
        (∑ k ∈ B, (u k : ℤ)) + (C : ℤ) * ((n : ℤ) - (E.card : ℤ) - (B.card : ℤ)) := by
    simp_rw [heach]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumE, hsumB, hsumC]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Int.nsmul_eq_mul]
    ring
  rw [hsum]
  exact selector_budget n H C b hCn E B u j huE' huB' (fun _ _ _ _ h => hj h)
    (fun k _ => hb k) hcard

theorem selector_zpow_le (n H C b : ℕ) (hCn : n ≤ C)
    (τ : Fin n → Fin 3) (u j : Fin n → ℕ)
    (huE : Set.InjOn u {k | τ k = 1}) (huB : Set.InjOn u {k | τ k = 2})
    (hj : Function.Injective j) (hb : ∀ k, b ≤ j k) :
    (2 : ℝ) ^ (-(∑ k : Fin n,
        if τ k = 0 then (C : ℤ)
        else if τ k = 1 then 2 * (u k : ℤ) + (j k : ℤ) - (H : ℤ)
        else (u k : ℤ))) ≤
      (2 : ℝ) ^ (A2 n H b + (3 / 2) * n) := by
  have h := selector_exponent_lower n H C b hCn τ u j huE huB hj hb
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  simp only [Int.cast_neg]
  linarith only [h]

/-! ### The norm bound for an admissible design -/

theorem n_le_C (P : Parameters) (N : ℕ) : P.n N ≤ P.C N := by
  simp only [Parameters.C, Parameters.L]
  omega

theorem rawCoefficientTerm_eq_det (P : Parameters) (z : ℚ) (N : ℕ)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k)) :
    (∏ k : Fin (P.n N), paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val) *
        paramRawCoefficientMinor P N c τ u =
      Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
        paramRawCoefficientVector P N r.val (c k).val (τ k) (u k).val *
          paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val) := by
  classical
  simp only [paramRawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.prod_mul_distrib]
  ring

private theorem prod_two_zpow_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    (∏ k, (2 : ℝ) ^ (-v k)) = (2 : ℝ) ^ (-(∑ k, v k)) := by
  classical
  calc
    _ = ∏ k, (2 : ℝ) ^ (((-v k) : ℤ) : ℝ) := by
      simp only [Real.rpow_intCast]
    _ = (2 : ℝ) ^ (∑ k, (((-v k) : ℤ) : ℝ)) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = (2 : ℝ) ^ (((-(∑ k, v k)) : ℤ) : ℝ) := by
      simp only [Int.cast_neg, Int.cast_sum, Finset.sum_neg_distrib]
    _ = _ := Real.rpow_intCast _ _

theorem rawCoefficientTerm_norm_le_zpow (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {N : ℕ} (hN : 0 < N)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N)))
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k)) :
    ‖(∏ k : Fin (P.n N), paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val) *
        paramRawCoefficientMinor P N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N *
        (2 : ℝ) ^ (-(∑ k : Fin (P.n N),
          if τ k = 0 then (P.C N : ℤ)
          else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (P.H N : ℤ)
          else ((u k).val : ℤ))) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawCoefficientTerm_eq_det]
  calc
    _ ≤ ∏ k : Fin (P.n N),
        (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) *
          (2 : ℝ) ^ (-(if τ k = 0 then (P.C N : ℤ)
            else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (P.H N : ℤ)
            else ((u k).val : ℤ))) := by
      apply padic_two_det_norm_le_prod_column
      · intro k
        positivity
      · intro r k
        exact paramRawCoefficientEntry_norm_le P hAdm z hN
          (Finset.mem_Ico.mp (c k).property).2 (τ k) (u k)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, prod_two_zpow_neg]

set_option backward.isDefEq.respectTransparency false in
theorem rawCoefficientTerm_norm_le (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {N : ℕ} (hN : 0 < N)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) (hc : Function.Injective c)
    (τ : Fin (P.n N) → Fin 3)
    (u : ∀ k : Fin (P.n N), paramRawCoefficientIndex P N (τ k)) :
    ‖(∏ k : Fin (P.n N), paramRawCoefficientScalar P z N (c k).val (τ k) (u k).val) *
        paramRawCoefficientMinor P N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N *
        (2 : ℝ) ^ (A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ)) := by
  have hF := discrepancyNormFactor_nonneg z
  by_cases hz : paramRawCoefficientMinor P N c τ u = 0
  · rw [hz, mul_zero, norm_zero]
    positivity
  have hj : Function.Injective (fun k => (c k).val) := by
    intro i j hij
    exact hc (Subtype.ext hij)
  have hp := selector_zpow_le (P.n N) (P.H N) (P.C N) (P.b N) (n_le_C P N) τ
    (fun k => (u k).val) (fun k => (c k).val)
    (paramRawCoefficientMinor_exception_injOn P N c τ u hz)
    (paramRawCoefficientMinor_boundary_injOn P N c τ u hz) hj
    (fun k => (Finset.mem_Ico.mp (c k).property).1)
  exact (rawCoefficientTerm_norm_le_zpow P hAdm z hN c τ u).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

theorem rawColumnMinor_norm_le (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {N : ℕ} (hN : 0 < N)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) (hc : Function.Injective c)
    (τ : Fin (P.n N) → Fin 3) :
    ‖Matrix.det (Matrix.of fun r k : Fin (P.n N) =>
      paramRawColumnTerm P z N r.val (c k).val (τ k))‖ ≤
      (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N *
        (2 : ℝ) ^ (A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [paramRawColumnMinor_coefficient_expansion]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro u hu
  exact rawCoefficientTerm_norm_le P hAdm z hN c hc τ u

theorem rawMinorRat_two_adic_norm_le (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {N : ℕ} (hN : 0 < N)
    (c : Fin (P.n N) → ↥(Finset.Ico (P.b N) (P.L N))) (hc : Function.Injective c) :
    ‖(paramRawMinorRat P z N c : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N *
        (2 : ℝ) ^ (A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [paramRawMinorRat_two_adic_column_expansion P hAdm z hN c]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro τ hτ
  exact rawColumnMinor_norm_le P hAdm z hN c hc τ

/-- The 2-adic norm of the determinant of an admissible design. -/
theorem determinantRat_two_adic_norm_le (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {N : ℕ} (hN : 0 < N) :
    ‖(determinantRat P z N : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N *
        (2 : ℝ) ^ (A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [paramDeterminantRat_eq_sum_raw_minors]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro c hc
  rw [norm_mul]
  calc
    _ ≤ 1 * ((8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N *
        (2 : ℝ) ^ (A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ))) :=
      mul_le_mul (Padic.norm_int_le_one _)
        (rawMinorRat_two_adic_norm_le P hAdm z hN c (Finset.mem_filter.mp hc).2)
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The 2-adic valuation lower bound.  The positivity of `A2 + 3n/2` is not needed. -/
theorem determinantRat_two_adic_valuation_lower (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {N : ℕ} (hN : 0 < N) (hHpos : 0 < P.H N) (hd : determinantRat P z N ≠ 0) :
    -(A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ)) -
        (P.n N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ≤
      (padicValRat 2 (determinantRat P z N) : ℝ) := by
  have hd₂ : (determinantRat P z N : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hH : 0 < (P.H N : ℝ) := by exact_mod_cast hHpos
  have hA : 0 < 8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2 := by positivity
  have hApow : (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2) ^ P.n N ≠ 0 :=
    ne_of_gt (pow_pos hA _)
  have hE : (2 : ℝ) ^ (A2 (P.n N) (P.H N) (P.b N) + (3 / 2) * (P.n N : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (norm_pos_iff.mpr hd₂) (determinantRat_two_adic_norm_le P hAdm z hN)
  rw [Padic.norm_eq_zpow_neg_valuation hd₂, Padic.valuation_ratCast] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [← Real.rpow_intCast, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1),
    Real.logb_mul hApow hE, Real.logb_pow,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hl
  simp only [Int.cast_neg] at hl
  nlinarith only [hl]

/-! ### Normalised constant and the asymptotic form -/

theorem A2_scale (n H b N : ℝ) : A2 (n * N) (H * N) (b * N) = A2 n H b * N ^ 2 := by
  unfold A2; ring

/-- The normalised 2-adic constant `a2 = A2(n0, H0, b0) / n0²`. -/
def a2 (P : Parameters) : ℝ := A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) / (P.n0 : ℝ) ^ 2

theorem cast_n (P : Parameters) (N : ℕ) : (P.n N : ℝ) = (P.n0 : ℝ) * N := by
  simp [Parameters.n]

theorem cast_b (P : Parameters) (N : ℕ) : (P.b N : ℝ) = (P.b0 : ℝ) * N := by
  simp [Parameters.b]

theorem cast_H (P : Parameters) (N : ℕ) : (P.H N : ℝ) = (P.H 1 : ℝ) * N := by
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h]
  push_cast
  ring

theorem A2_eq_a2 (P : Parameters) (hn0 : 0 < P.n0) (N : ℕ) :
    A2 (P.n N : ℝ) (P.H N : ℝ) (P.b N : ℝ) = a2 P * (P.n N : ℝ) ^ 2 := by
  have h0 : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [cast_n, cast_H, cast_b, A2_scale, a2]
  field_simp

theorem tendsto_two_adic_log_error (P : Parameters) (hn0 : 0 < P.n0) (z : ℚ) :
    Tendsto (fun N : ℕ =>
      (3 / 2 + Real.logb 2 (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2)) / (P.n N : ℝ))
      atTop (𝓝 0) := by
  have hn0R : (0 : ℝ) < P.n0 := by exact_mod_cast hn0
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ) / ((P.n0 : ℝ) * (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) (P.n0 : ℝ) 0 1 hn0R.ne').comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hs := (hi.const_mul
    ((3 / 2 + Real.logb 2 (8 * discrepancyNormFactor z * (P.H 1 : ℝ) ^ 2)) / (P.n0 : ℝ))).add
      (hl.const_mul 2)
  simp only [mul_zero, add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hH1 : (0 : ℝ) < (P.H 1 : ℝ) := by
    have : 0 < P.H 1 := by
      simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n]
      omega
    exact_mod_cast this
  have hconst : 8 * discrepancyNormFactor z * (P.H 1 : ℝ) ^ 2 ≠ 0 := by positivity
  have hfactor : 8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2 =
      (8 * discrepancyNormFactor z * (P.H 1 : ℝ) ^ 2) * (N : ℝ) ^ 2 := by
    rw [cast_H]; ring
  rw [hfactor, Real.logb_mul hconst (pow_ne_zero _ hNr), Real.logb_pow, cast_n]
  push_cast
  field_simp
  ring

/-- Asymptotic 2-adic bound: `v_2(det) ≥ -(a2 + ε) n²` eventually, for every admissible design. -/
theorem determinantRat_two_adic_eventually_lower (P : Parameters) (hAdm : Admissible P) (z : ℚ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat P z N ≠ 0 →
      -(a2 P) - ε ≤ (padicValRat 2 (determinantRat P z N) : ℝ) / (P.n N : ℝ) ^ 2 := by
  have he : ∀ᶠ N : ℕ in atTop,
      (3 / 2 + Real.logb 2 (8 * discrepancyNormFactor z * (P.H N : ℝ) ^ 2)) / (P.n N : ℝ) < ε :=
    (tendsto_order.mp (tendsto_two_adic_log_error P hAdm.1 z)).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  intro hd
  have hnN : 0 < P.n N := Nat.mul_pos hAdm.1 hN
  have hn : 0 < (P.n N : ℝ) := by exact_mod_cast hnN
  have hHpos : 0 < P.H N := by
    have : P.n N ≤ P.H N := by
      simp only [Parameters.H, Parameters.C, Parameters.L]
      omega
    omega
  have herr := mul_le_mul_of_nonneg_left (le_of_lt ((div_lt_iff₀ hn).mp heN)) (le_of_lt hn)
  have hv := determinantRat_two_adic_valuation_lower P hAdm z hN hHpos hd
  rw [A2_eq_a2 P hAdm.1] at hv
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith only [herr, hv]

end
end TwoAdic
end CatalanMeasure.GenD
