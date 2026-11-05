module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A generalized Vandermonde bound

For nodes `s₀, …, s_{p-1} ∈ [0, 1]` and distinct exponents `E₀, …, E_{p-1} < n`,

  `|det [s_l ^ E_i]| ≤ 4 ^ (n (n - p)) · |∏_{i<j} (s_j - s_i)|`.

Proof.  Write `X ^ e = ∑_{k<p} c_{e,k} W_k + W_p Q_{e,p}` (Newton's divided differences:
`W_k = ∏_{l<k} (X - s_l)` and `Q_{e,k+1} = Q_{e,k} / (X - s_k)`).  Since `W_p` vanishes at every
node, `s_l ^ e = R_e(s_l)` for the polynomial `R_e = ∑_{k<p} c_{e,k} W_k` of degree `< p`.  So
`[s_l ^ E_i] = V · T` with `V` the Vandermonde matrix and `T` the coefficient matrix of the
`R_{E_i}` (with `R_e = X ^ e` when `e < p`).  Columns of `T` with `E_i < p` are unit vectors,
the others have `ℓ¹` norm at most `4 ^ n`, and at most `n - p` exponents are `≥ p`.
-/

open Polynomial Finset

namespace CatalanMeasure

/-- A determinant is bounded by the product of the `ℓ¹` norms of its columns. -/
theorem abs_det_le_prod_col_sum {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) :
    |M.det| ≤ ∏ i, ∑ a, |M a i| := by
  classical
  rw [Matrix.det_apply]
  let emb : Equiv.Perm (Fin p) ↪ (Fin p → Fin p) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
  calc |∑ σ : Equiv.Perm (Fin p), Equiv.Perm.sign σ • ∏ i, M (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin p), |Equiv.Perm.sign σ • ∏ i, M (σ i) i| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin p), ∏ i, |M (σ i) i| := by
        refine sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with sg | sg
        · rw [sg, one_smul, abs_prod]
        · rw [sg, Units.neg_smul, one_smul, abs_neg, abs_prod]
    _ = ∑ g ∈ (univ : Finset (Equiv.Perm (Fin p))).map emb, ∏ i, |M (g i) i| := by
        rw [sum_map]
        rfl
    _ ≤ ∑ g : Fin p → Fin p, ∏ i, |M (g i) i| :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun g _ _ => prod_nonneg fun i _ => abs_nonneg _)
    _ = ∏ i, ∑ a, |M a i| := (Fintype.prod_sum (fun i a => |M a i|)).symm

section Newton

variable (σ : ℕ → ℝ)

/-- Newton quotients of `X ^ e` along the nodes `σ 0, σ 1, …`. -/
noncomputable def newtonQuot (e : ℕ) : ℕ → ℝ[X]
  | 0 => X ^ e
  | k + 1 => newtonQuot e k /ₘ (X - C (σ k))

/-- `W_k = ∏_{l<k} (X - σ l)`. -/
noncomputable def newtonBasis (k : ℕ) : ℝ[X] := ∏ l ∈ range k, (X - C (σ l))

theorem newtonBasis_succ (k : ℕ) :
    newtonBasis σ (k + 1) = newtonBasis σ k * (X - C (σ k)) := prod_range_succ _ _

theorem newton_expansion (e K : ℕ) :
    (X ^ e : ℝ[X]) =
      ∑ k ∈ range K, C ((newtonQuot σ e k).eval (σ k)) * newtonBasis σ k +
        newtonBasis σ K * newtonQuot σ e K := by
  induction K with
  | zero => simp [newtonQuot, newtonBasis]
  | succ K ih =>
    have hstep : newtonQuot σ e K = C ((newtonQuot σ e K).eval (σ K)) +
        (X - C (σ K)) * newtonQuot σ e (K + 1) := by
      conv_lhs => rw [← modByMonic_add_div (newtonQuot σ e K) (X - C (σ K))]
      rw [modByMonic_X_sub_C_eq_C_eval]
      rfl
    rw [sum_range_succ, newtonBasis_succ]
    conv_lhs => rw [ih]
    linear_combination (newtonBasis σ K) * hstep

theorem geom_tail_le (e j D : ℕ) :
    ∑ i ∈ Icc (j + 1) D, (2 : ℝ) ^ e * (1 / 2) ^ i ≤ (2 : ℝ) ^ e * (1 / 2) ^ j := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  have hrw : ∀ t ∈ range (D + 1 - (j + 1)), (2 : ℝ) ^ e * (1 / 2) ^ (j + 1 + t) =
      (2 : ℝ) ^ e * (1 / 2) ^ j * (1 / 2) * (1 / 2) ^ t := by
    intro t _
    rw [pow_add, pow_add, pow_one]
    ring
  rw [sum_congr rfl hrw, ← mul_sum]
  have hg := sum_geometric_two_le (D + 1 - (j + 1))
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ e * (1 / 2) ^ j * (1 / 2) := by positivity
  calc (2 : ℝ) ^ e * (1 / 2) ^ j * (1 / 2) *
        ∑ t ∈ range (D + 1 - (j + 1)), (1 / 2 : ℝ) ^ t
      ≤ (2 : ℝ) ^ e * (1 / 2) ^ j * (1 / 2) * 2 := mul_le_mul_of_nonneg_left hg h0
    _ = (2 : ℝ) ^ e * (1 / 2) ^ j := by ring

theorem newtonQuot_bounds {e : ℕ} (hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (newtonQuot σ e k).natDegree ≤ e ∧
      ∀ i, 0 ≤ (newtonQuot σ e k).coeff i ∧
        (newtonQuot σ e k).coeff i ≤ (2 : ℝ) ^ e * (1 / 2) ^ i := by
  induction k with
  | zero =>
    refine ⟨by simp [newtonQuot], fun i => ?_⟩
    simp only [newtonQuot, coeff_X_pow]
    split_ifs with h
    · subst h
      refine ⟨zero_le_one, ?_⟩
      rw [← mul_pow]
      norm_num
    · exact ⟨le_rfl, by positivity⟩
  | succ k ih =>
    obtain ⟨hdeg, hc⟩ := ih
    refine ⟨?_, fun j => ?_⟩
    · simp only [newtonQuot]
      rw [natDegree_divByMonic _ (monic_X_sub_C _)]
      omega
    · simp only [newtonQuot]
      rw [coeff_divByMonic_X_sub_C]
      constructor
      · exact sum_nonneg fun i _ => mul_nonneg (pow_nonneg (hσ k).1 _) (hc i).1
      · calc ∑ i ∈ Icc (j + 1) (newtonQuot σ e k).natDegree,
              σ k ^ (i - (j + 1)) * (newtonQuot σ e k).coeff i
            ≤ ∑ i ∈ Icc (j + 1) (newtonQuot σ e k).natDegree, (2 : ℝ) ^ e * (1 / 2) ^ i := by
              apply sum_le_sum
              intro i _
              have h1 : σ k ^ (i - (j + 1)) ≤ 1 := pow_le_one₀ (hσ k).1 (hσ k).2
              calc σ k ^ (i - (j + 1)) * (newtonQuot σ e k).coeff i
                  ≤ 1 * (newtonQuot σ e k).coeff i :=
                    mul_le_mul_of_nonneg_right h1 (hc i).1
                _ ≤ _ := by rw [one_mul]; exact (hc i).2
          _ ≤ (2 : ℝ) ^ e * (1 / 2) ^ j := geom_tail_le e j _

theorem newtonQuot_eval_bounds {e : ℕ} (hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ (newtonQuot σ e k).eval (σ k) ∧
      (newtonQuot σ e k).eval (σ k) ≤ (2 : ℝ) ^ (e + 1) := by
  obtain ⟨hdeg, hc⟩ := newtonQuot_bounds σ hσ (e := e) k
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (hc i).1 (pow_nonneg (hσ k).1 _)
  · calc ∑ i ∈ range (e + 1), (newtonQuot σ e k).coeff i * σ k ^ i
        ≤ ∑ i ∈ range (e + 1), (2 : ℝ) ^ e * (1 / 2) ^ i := by
          apply sum_le_sum
          intro i _
          have h1 : σ k ^ i ≤ 1 := pow_le_one₀ (hσ k).1 (hσ k).2
          calc (newtonQuot σ e k).coeff i * σ k ^ i ≤ (newtonQuot σ e k).coeff i * 1 :=
                mul_le_mul_of_nonneg_left h1 (hc i).1
            _ ≤ _ := by rw [mul_one]; exact (hc i).2
      _ = (2 : ℝ) ^ e * ∑ i ∈ range (e + 1), (1 / 2 : ℝ) ^ i := by rw [mul_sum]
      _ ≤ (2 : ℝ) ^ e * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = (2 : ℝ) ^ (e + 1) := by rw [pow_succ]

theorem newtonBasis_bounds (hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (newtonBasis σ k).natDegree ≤ k ∧
      ∀ a, |(newtonBasis σ k).coeff a| ≤ (k.choose a : ℝ) := by
  induction k with
  | zero =>
    refine ⟨by simp [newtonBasis], fun a => ?_⟩
    simp only [newtonBasis, range_zero, prod_empty, coeff_one]
    rcases a with _ | a <;> simp
  | succ k ih =>
    obtain ⟨hdeg, hc⟩ := ih
    rw [newtonBasis_succ]
    refine ⟨?_, fun a => ?_⟩
    · calc (newtonBasis σ k * (X - C (σ k))).natDegree
          ≤ (newtonBasis σ k).natDegree + (X - C (σ k)).natDegree := natDegree_mul_le
        _ ≤ k + 1 := by rw [natDegree_X_sub_C]; omega
    · have hσa : |σ k| ≤ 1 := abs_le.mpr ⟨by linarith [(hσ k).1], (hσ k).2⟩
      rcases a with _ | a
      · rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg, abs_neg,
          abs_mul]
        have := hc 0
        simp only [Nat.choose_zero_right, Nat.cast_one] at this ⊢
        calc |(newtonBasis σ k).coeff 0| * |σ k| ≤ 1 * 1 :=
              mul_le_mul this hσa (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · rw [coeff_mul_X_sub_C, Nat.choose_succ_succ', Nat.cast_add]
        calc |(newtonBasis σ k).coeff a - (newtonBasis σ k).coeff (a + 1) * σ k|
            ≤ |(newtonBasis σ k).coeff a| + |(newtonBasis σ k).coeff (a + 1) * σ k| :=
              abs_sub _ _
          _ ≤ (k.choose a : ℝ) + (k.choose (a + 1) : ℝ) := by
              apply add_le_add (hc a)
              rw [abs_mul]
              calc |(newtonBasis σ k).coeff (a + 1)| * |σ k|
                  ≤ (k.choose (a + 1) : ℝ) * 1 :=
                    mul_le_mul (hc (a + 1)) hσa (abs_nonneg _) (Nat.cast_nonneg _)
                _ = _ := mul_one _

theorem newtonBasis_l1 (hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) (k p : ℕ) :
    ∑ a ∈ range p, |(newtonBasis σ k).coeff a| ≤ (2 : ℝ) ^ k := by
  have hc := (newtonBasis_bounds σ hσ k).2
  calc ∑ a ∈ range p, |(newtonBasis σ k).coeff a|
      ≤ ∑ a ∈ range (max p (k + 1)), (k.choose a : ℝ) := by
        apply le_trans (sum_le_sum fun a _ => hc a)
        exact sum_le_sum_of_subset_of_nonneg
          (range_subset_range.mpr (le_max_left _ _)) (fun _ _ _ => Nat.cast_nonneg _)
    _ = ∑ a ∈ range (k + 1), (k.choose a : ℝ) := by
        symm
        apply sum_subset (range_subset_range.mpr (le_max_right _ _))
        intro a _ ha
        have : k < a := by simp only [mem_range, not_lt] at ha; omega
        simp [Nat.choose_eq_zero_of_lt this]
    _ = (2 : ℝ) ^ k := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

/-- The reduced polynomial `R_e` with `R_e(σ l) = σ l ^ e` for `l < p` and degree `< p`. -/
noncomputable def remPoly (p e : ℕ) : ℝ[X] :=
  if e < p then X ^ e
  else ∑ k ∈ range p, C ((newtonQuot σ e k).eval (σ k)) * newtonBasis σ k

theorem remPoly_eval (p e : ℕ) {l : ℕ} (hl : l < p) :
    (remPoly σ p e).eval (σ l) = σ l ^ e := by
  unfold remPoly
  split_ifs with he
  · simp
  · have h := congrArg (eval (σ l)) (newton_expansion σ e p)
    rw [eval_add, eval_mul] at h
    have hW : (newtonBasis σ p).eval (σ l) = 0 := by
      unfold newtonBasis
      rw [eval_prod]
      exact prod_eq_zero (mem_range.mpr hl) (by simp)
    rw [hW, zero_mul, add_zero, eval_pow, eval_X] at h
    exact h.symm

theorem remPoly_natDegree_lt (hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) {p : ℕ} (hp : 0 < p)
    (e : ℕ) : (remPoly σ p e).natDegree < p := by
  unfold remPoly
  split_ifs with he
  · rw [natDegree_X_pow]
    exact he
  · have : (∑ k ∈ range p, C ((newtonQuot σ e k).eval (σ k)) * newtonBasis σ k).natDegree ≤
        p - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro k hk
      have hk' := mem_range.mp hk
      exact natDegree_C_mul_le _ _ |>.trans
        ((newtonBasis_bounds σ hσ k).1.trans (by omega))
    omega

theorem remPoly_l1 (hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1) {p e n : ℕ} (hp : p ≤ n)
    (hen : e < n) :
    ∑ a ∈ range p, |(remPoly σ p e).coeff a| ≤ if e < p then 1 else (4 : ℝ) ^ n := by
  unfold remPoly
  split_ifs with he
  · simp only [coeff_X_pow]
    rw [sum_eq_single e]
    · simp
    · intro a _ hae
      simp [hae]
    · intro h
      exact absurd (mem_range.mpr he) h
  · simp only [finsetSum_coeff, coeff_C_mul]
    calc ∑ a ∈ range p, |∑ k ∈ range p,
            (newtonQuot σ e k).eval (σ k) * (newtonBasis σ k).coeff a|
        ≤ ∑ a ∈ range p, ∑ k ∈ range p,
            (newtonQuot σ e k).eval (σ k) * |(newtonBasis σ k).coeff a| := by
          apply sum_le_sum
          intro a _
          apply (abs_sum_le_sum_abs _ _).trans
          apply le_of_eq
          apply sum_congr rfl
          intro k _
          rw [abs_mul, abs_of_nonneg (newtonQuot_eval_bounds σ hσ k).1]
      _ = ∑ k ∈ range p, (newtonQuot σ e k).eval (σ k) *
            ∑ a ∈ range p, |(newtonBasis σ k).coeff a| := by
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ ∑ k ∈ range p, (2 : ℝ) ^ (e + 1) * (2 : ℝ) ^ k := by
          apply sum_le_sum
          intro k _
          exact mul_le_mul (newtonQuot_eval_bounds σ hσ k).2 (newtonBasis_l1 σ hσ k p)
            (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (e + 1) * ((2 : ℝ) ^ p - 1) := by
          rw [← mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
          norm_num
      _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
          apply mul_le_mul
          · exact pow_le_pow_right₀ (by norm_num) (by omega)
          · have : (2 : ℝ) ^ p ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hp
            linarith
          · have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
            linarith
          · positivity
      _ = (4 : ℝ) ^ n := by rw [← mul_pow]; norm_num

end Newton

/-- **Generalized Vandermonde bound.** -/
theorem genVandermonde_abs_le {p n : ℕ} (s : Fin p → ℝ) (hs : ∀ l, s l ∈ Set.Icc (0 : ℝ) 1)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n) :
    |(Matrix.of fun l i : Fin p => s l ^ E i).det| ≤
      (4 : ℝ) ^ (n * (n - p)) * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| := by
  classical
  have hpn : p ≤ n := by
    have h := Finset.card_le_card_of_injOn E (s := (univ : Finset (Fin p))) (t := range n)
      (fun i _ => mem_range.mpr (hEn i)) (fun a _ b _ h => hE h)
    simpa using h
  let σ : ℕ → ℝ := fun k => if h : k < p then s ⟨k, h⟩ else 0
  have hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    simp only [σ]
    split_ifs
    · exact hs _
    · exact ⟨le_rfl, zero_le_one⟩
  have hσs : ∀ l : Fin p, σ l.val = s l := by
    intro l
    simp [σ, l.isLt]
  let T : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a i => (remPoly σ p (E i)).coeff a.val
  have hM : (Matrix.of fun l i : Fin p => s l ^ E i) = Matrix.vandermonde s * T := by
    ext l i
    have hp : 0 < p := Fin.pos l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply, T]
    rw [← hσs l, ← remPoly_eval σ p (E i) l.isLt,
      eval_eq_sum_range' (remPoly_natDegree_lt σ hσ hp (E i))]
    rw [← Fin.sum_univ_eq_sum_range (fun a => (remPoly σ p (E i)).coeff a * σ l.val ^ a)]
    apply sum_congr rfl
    intro a _
    rw [hσs l]
    ring
  rw [hM, Matrix.det_mul, abs_mul, Matrix.det_vandermonde, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |T.det| ≤ ∏ i, ∑ a, |T a i| := abs_det_le_prod_col_sum T
    _ ≤ ∏ i : Fin p, (if p ≤ E i then (4 : ℝ) ^ n else 1) := by
        apply prod_le_prod₀
        · intro i _
          exact sum_nonneg fun _ _ => abs_nonneg _
        · intro i _
          have h := remPoly_l1 σ hσ hpn (hEn i) (e := E i)
          rw [← Fin.sum_univ_eq_sum_range (fun a => |(remPoly σ p (E i)).coeff a|)] at h
          simp only [T, Matrix.of_apply]
          refine h.trans (le_of_eq ?_)
          by_cases hi : E i < p
          · rw [if_pos hi, if_neg (by omega)]
          · rw [if_neg hi, if_pos (by omega)]
    _ = ((4 : ℝ) ^ n) ^ (univ.filter fun i : Fin p => p ≤ E i).card := by
        rw [prod_ite, prod_const, prod_const_one, mul_one]
    _ ≤ ((4 : ℝ) ^ n) ^ (n - p) := by
        apply pow_le_pow_right₀ (one_le_pow₀ (by norm_num))
        have h := Finset.card_le_card_of_injOn E
          (s := univ.filter fun i : Fin p => p ≤ E i) (t := Ico p n)
          (fun i hi => mem_Ico.mpr ⟨(mem_filter.mp hi).2, hEn i⟩)
          (fun a _ b _ h => hE h)
        simpa using h
    _ = (4 : ℝ) ^ (n * (n - p)) := by rw [← pow_mul]

end CatalanMeasure
