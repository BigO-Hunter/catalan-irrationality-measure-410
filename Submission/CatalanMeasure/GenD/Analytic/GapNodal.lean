module

public import Submission.CatalanMeasure.GenD.Analytic.GapNodes
public import Submission.CatalanMeasure.QuadCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section

/-!
# Analytic layer (group 4): the nodal polynomial of the gap nodes, any `J`

Generic port of `Parametric.GapNodal` / `GapQuadrature`.  With `K = (J+1)/2`,
`T_K((2t^2-(1+a^2))/(1-a^2)) = lead * gapNodal * gapExtra`, where `gapNodal = prod (X - node)` over
the `J` nodes and `gapExtra` is the product of the at most one dropped factor `X + p_i`
(`J` odd) and `1` (`J` even).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

def gapArgument (a : ℝ) : ℝ[X] :=
  C (2 / (1 - a ^ 2)) * X ^ 2 - C ((1 + a ^ 2) / (1 - a ^ 2))

/-- `T_K` of the quadratic argument: degree `2K`. -/
def gapPolyK (a : ℝ) (K : ℕ) : ℝ[X] := (T ℝ (K : ℤ)).comp (gapArgument a)

def gapLead (a : ℝ) (K : ℕ) : ℝ := 2 ^ (K - 1) * (2 / (1 - a ^ 2)) ^ K

/-- The monic nodal polynomial of the `J` nodes. -/
def gapNodal (a : ℝ) (J : ℕ) : ℝ[X] := ∏ j : Fin J, (X - C (gapNodesGen a J j))

/-- The dropped factors: `X + p_i` for the positive roots with index `>= J/2`. -/
def gapExtra (a : ℝ) (J : ℕ) : ℝ[X] :=
  ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
    (X + C (posNode a ((J + 1) / 2) i))

theorem gap_argument_at_positive {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) (i : Fin K) :
    (gapArgument a).eval (posNode a K i) = CatalanMeasure.chebX K i := by
  have hs := pos_node_sq ha0 ha1 K i
  have hd : 1 - a ^ 2 ≠ 0 := (gapSq_pos ha0 ha1).ne'
  simp only [gapArgument, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  rw [hs]
  field_simp
  ring

theorem gap_argument_factor {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) (i : Fin K) :
    gapArgument a - C (CatalanMeasure.chebX K i) =
      C (2 / (1 - a ^ 2)) * ((X - C (posNode a K i)) * (X + C (posNode a K i))) := by
  have hs := pos_node_sq ha0 ha1 K i
  have hd : 1 - a ^ 2 ≠ 0 := (gapSq_pos ha0 ha1).ne'
  have hc : (1 + a ^ 2) / (1 - a ^ 2) + CatalanMeasure.chebX K i =
      (2 / (1 - a ^ 2)) * (posNode a K i) ^ 2 := by
    rw [hs]; field_simp; ring
  unfold gapArgument
  rw [sub_sub, ← map_add, hc]
  simp only [map_mul, map_pow]
  ring

theorem gapPolyK_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {K : ℕ} (hK : 0 < K) :
    gapPolyK a K = C (gapLead a K) *
      ∏ i : Fin K, ((X - C (posNode a K i)) * (X + C (posNode a K i))) := by
  unfold gapPolyK
  rw [CatalanMeasure.T_eq_nodal hK, C_mul_comp, Polynomial.prod_comp]
  simp only [sub_comp, X_comp, C_comp]
  simp_rw [gap_argument_factor ha0 ha1 K]
  rw [Finset.prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← map_pow,
    ← mul_assoc, ← map_mul]
  rfl

theorem gapLead_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) : 0 < gapLead a K := by
  have hd := gapSq_pos ha0 ha1
  unfold gapLead
  positivity

/-- Splitting a product over `Fin K` along the first `L <= K` indices. -/
theorem prod_fin_split {M : Type*} [CommMonoid M] {K L : ℕ} (hL : L ≤ K) (f : Fin K → M) :
    ∏ i, f i = (∏ i : Fin L, f (Fin.castLE hL i)) *
      ∏ i ∈ univ.filter (fun i : Fin K => L ≤ i.val), f i := by
  have h1 := prod_filter_mul_prod_filter_not (univ : Finset (Fin K)) (fun i : Fin K => i.val < L) f
  have h2 : ∏ i ∈ univ.filter (fun i : Fin K => i.val < L), f i =
      ∏ i : Fin L, f (Fin.castLE hL i) := by
    symm
    apply Finset.prod_bij (fun i _ => Fin.castLE hL i)
    · intro i _; simp
    · intro i _ j _ h; exact Fin.castLE_injective hL h
    · intro b hb
      have hb2 : b.val < L := by simpa using hb
      exact ⟨⟨b.val, hb2⟩, mem_univ _, Fin.ext rfl⟩
    · intro i _; rfl
  have h3 : univ.filter (fun i : Fin K => ¬ i.val < L) =
      univ.filter (fun i : Fin K => L ≤ i.val) := by
    ext i; simp
  rw [h3, h2] at h1
  exact h1.symm

theorem gapNodal_eq (a : ℝ) (J : ℕ) :
    gapNodal a J = (∏ i : Fin ((J + 1) / 2), (X - C (posNode a ((J + 1) / 2) i))) *
      ∏ i : Fin (J / 2), (X + C (posNode a ((J + 1) / 2) (Fin.castLE (by omega) i))) := by
  unfold gapNodal
  have hJ : J = (J + 1) / 2 + J / 2 := by omega
  have hq := Fintype.prod_equiv (finCongr hJ) (fun x : Fin J => X - C (gapNodesGen a J x))
    (fun jj : Fin ((J + 1) / 2 + J / 2) =>
      (X - C (gapNodesKL a ((J + 1) / 2) (J / 2) (by omega) jj))) (fun x => rfl)
  rw [hq]
  rw [Fin.prod_univ_add]
  simp only [gapNodesKL_left, gapNodesKL_right, map_neg, sub_neg_eq_add]

theorem gap_pair_product (a : ℝ) (J : ℕ) :
    (∏ i : Fin ((J + 1) / 2), ((X - C (posNode a ((J + 1) / 2) i)) *
        (X + C (posNode a ((J + 1) / 2) i)))) = gapNodal a J * gapExtra a J := by
  rw [prod_mul_distrib, gapNodal_eq, gapExtra]
  have := prod_fin_split (K := (J + 1) / 2) (L := J / 2) (by omega)
    (fun i => X + C (posNode a ((J + 1) / 2) i))
  rw [this]
  ring

theorem gapPolyK_eq_nodal {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {J : ℕ} (hJ : 0 < J) :
    gapPolyK a ((J + 1) / 2) = C (gapLead a ((J + 1) / 2)) * (gapNodal a J * gapExtra a J) := by
  rw [gapPolyK_eq ha0 ha1 (by omega), gap_pair_product]

theorem gapExtra_card_le (a : ℝ) (J : ℕ) :
    (univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [mem_filter, mem_univ, true_and] at hi hj
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  omega

/-- On `|z| = r` (`1 < r <= 2`) the dropped factor is bounded below by `r - 1`. -/
theorem gapExtra_norm_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) {r : ℝ}
    (hr1 : 1 < r) (hr2 : r ≤ 2) (z : ℂ) (hz : ‖z‖ = r) :
    r - 1 ≤ ‖((gapExtra a J).map (algebraMap ℝ ℂ)).eval z‖ := by
  unfold gapExtra
  rw [Polynomial.map_prod, eval_prod, norm_prod]
  have hf : ∀ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
      r - 1 ≤ ‖(((X + C (posNode a ((J + 1) / 2) i) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ := by
    intro i _
    have hp := pos_node_bounds ha0 ha1 ((J + 1) / 2) i
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, eval_add, eval_X, eval_C,
      Complex.coe_algebraMap]
    have hh := norm_sub_norm_le z (-(posNode a ((J + 1) / 2) i : ℂ))
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, hz,
      abs_of_pos (by linarith only [ha0, hp.1])] at hh
    rw [sub_neg_eq_add] at hh
    linarith only [hh, hp.2]
  have hc : ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val), (r - 1) ≤
      ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
        ‖(((X + C (posNode a ((J + 1) / 2) i) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ :=
    Finset.prod_le_prod₀ (fun _ _ => by linarith only [hr1]) hf
  rw [prod_const] at hc
  have hcard := gapExtra_card_le a J
  have hle : (r - 1) ^ 1 ≤
      (r - 1) ^ (univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val)).card :=
    pow_le_pow_of_le_one (by linarith only [hr1]) (by linarith only [hr2]) hcard
  simpa using hle.trans hc

theorem gapExtra_eval_abs_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) {t : ℝ}
    (ht : |t| ≤ 1) : |(gapExtra a J).eval t| ≤ 2 := by
  unfold gapExtra
  rw [eval_prod, abs_prod]
  have hf : ∀ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
      |(X + C (posNode a ((J + 1) / 2) i) : ℝ[X]).eval t| ≤ 2 := by
    intro i _
    have hp := pos_node_bounds ha0 ha1 ((J + 1) / 2) i
    simp only [eval_add, eval_X, eval_C]
    have := abs_le.mp ht
    rw [abs_le]
    constructor <;> linarith only [this.1, this.2, hp.1, hp.2, ha0]
  have hc : ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
      |(X + C (posNode a ((J + 1) / 2) i) : ℝ[X]).eval t| ≤
      ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val), (2 : ℝ) :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hf
  rw [prod_const] at hc
  have hcard := gapExtra_card_le a J
  calc _ ≤ _ := hc
    _ ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hcard
    _ = 2 := by norm_num

theorem chebX_den_ge {J : ℕ} (a : Fin J) :
    (J : ℝ) / 2 ^ (J - 1) ≤
      |∏ c ∈ univ.erase a, (CatalanMeasure.chebX J a - CatalanMeasure.chebX J c)| := by
  have h := CatalanMeasure.chebNode_den_ge a
  have he : (∏ c ∈ univ.erase a,
      (CatalanMeasure.chebNode J a - CatalanMeasure.chebNode J c)) =
      (∏ c ∈ univ.erase a,
        (CatalanMeasure.chebX J a - CatalanMeasure.chebX J c)) / 2 ^ (J - 1) := by
    rw [eq_div_iff (by positivity)]
    have hcard : (univ.erase a).card = J - 1 := by simp
    rw [← hcard, ← prod_const (2 : ℝ), ← prod_mul_distrib]
    apply prod_congr rfl
    intro c _
    simp only [CatalanMeasure.chebNode]
    ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (J - 1))] at h
  have h2 : (0 : ℝ) < 2 ^ (J - 1) := by positivity
  rw [← div_div, div_le_div_iff_of_pos_right h2] at h
  exact h

theorem cheb_derivative_eval_ge {J : ℕ} (i : Fin J) :
    (J : ℝ) ≤ |(derivative (T ℝ (J : ℤ))).eval (CatalanMeasure.chebX J i)| := by
  have hJ : 0 < J := by have := i.isLt; omega
  have hd := chebX_den_ge i
  have he := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := (univ : Finset (Fin J))) (v := CatalanMeasure.chebX J) (mem_univ i)
  rw [Lagrange.eval_nodal] at he
  rw [CatalanMeasure.T_eq_nodal hJ, derivative_C_mul, eval_mul, eval_C]
  rw [Lagrange.nodal_eq] at he
  rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (J - 1))]
  have hp : (0 : ℝ) < 2 ^ (J - 1) := by positivity
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hd

theorem gap_argument_at_node {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) (j : Fin J) :
    ∃ i : Fin ((J + 1) / 2),
      (gapArgument a).eval (gapNodesGen a J j) = CatalanMeasure.chebX ((J + 1) / 2) i := by
  unfold gapNodesGen
  generalize Fin.cast (show J = (J + 1) / 2 + J / 2 by omega) j = jj
  induction jj using Fin.addCases with
  | left i => exact ⟨i, by rw [gapNodesKL_left]; exact gap_argument_at_positive ha0 ha1 _ i⟩
  | right i =>
    refine ⟨Fin.castLE (show J / 2 ≤ (J + 1) / 2 by omega) i, ?_⟩
    rw [gapNodesKL_right]
    simpa only [gapArgument, eval_sub, eval_mul, eval_C, eval_pow, eval_X, neg_sq]
      using gap_argument_at_positive ha0 ha1 _ (Fin.castLE (show J / 2 ≤ (J + 1) / 2 by omega) i)

theorem gapPolyK_derivative_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) (j : Fin J) :
    4 * (((J + 1) / 2 : ℕ) : ℝ) * a / (1 - a ^ 2) ≤
      |(derivative (gapPolyK a ((J + 1) / 2))).eval (gapNodesGen a J j)| := by
  have hd := gapSq_pos ha0 ha1
  obtain ⟨i, hi⟩ := gap_argument_at_node ha0 ha1 J j
  have hT := cheb_derivative_eval_ge i
  have hn := (gap_nodes_bounds ha0 ha1 J j).2.le
  have he : (derivative (gapArgument a)).eval (gapNodesGen a J j) =
      4 * gapNodesGen a J j / (1 - a ^ 2) := by
    simp [gapArgument, derivative_mul, derivative_pow]; ring
  rw [gapPolyK, derivative_comp, eval_mul, eval_comp, hi, he,
    abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hd]
  calc
    _ = (4 * a / (1 - a ^ 2)) * (((J + 1) / 2 : ℕ) : ℝ) := by ring
    _ ≤ (4 * |gapNodesGen a J j| / (1 - a ^ 2)) *
        |(derivative (T ℝ ((((J + 1) / 2 : ℕ)) : ℤ))).eval
          (CatalanMeasure.chebX ((J + 1) / 2) i)| :=
      mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hd.le)
        hT (by positivity) (by positivity)

/-- `P = lead * Q * E`, hence at a node `P' = lead * Q' * E`. -/
theorem gapPolyK_derivative_node {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {J : ℕ} (hJ : 0 < J)
    (j : Fin J) :
    (derivative (gapPolyK a ((J + 1) / 2))).eval (gapNodesGen a J j) =
      gapLead a ((J + 1) / 2) * ((derivative (gapNodal a J)).eval (gapNodesGen a J j) *
        (gapExtra a J).eval (gapNodesGen a J j)) := by
  have hQ : (gapNodal a J).eval (gapNodesGen a J j) = 0 := by
    unfold gapNodal
    rw [eval_prod]
    exact prod_eq_zero (mem_univ j) (by simp)
  rw [gapPolyK_eq_nodal ha0 ha1 hJ, derivative_C_mul, derivative_mul, eval_mul, eval_C,
    eval_add, eval_mul, eval_mul, hQ]
  ring

end

end Analytic
end CatalanMeasure.GenD
