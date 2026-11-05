module

public import Submission.CatalanMeasure.GenD.Analytic.GapNodal
public import Submission.CatalanMeasure.GenD.Analytic.FullInterval
public import Submission.CatalanMeasure.Parametric.RestrictedWeights
public import Submission.CatalanMeasure.Parametric.PolynomialFunctional

@[expose] public section

/-!
# Analytic layer (group 4): gap weight bounds for any design and any parity of `d0 * N`

Generic port of `Parametric.GapQuadrature`, `GapWeights`.  The nodes are `gapNodesD P a N`
(`d0 * N` of them, `d0 = n0 - g0`).  The circle estimate for `T_K(arg)`, `K = (d0 N + 1)/2`, is
a hypothesis `GapCircleBound` (per-design cover certificate); the weight bound
`GapWeightBounds P tau w` is derived from it with `w > wc`.  For odd `d0 N` the dropped root costs
a constant factor only (derivative factor `2`, circle factor `1/(r-1)`, half a degree in `T_K`),
which is absorbed by the margin `w - wc` for large `N`: the exponent is unchanged.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Finset OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

/-- Nodes of the design: `d0 * N` points, `d0 = n0 - g0`. -/
def gapNodesD (P : Parameters) (a : ℝ) (N : ℕ) : Fin ((P.n0 - P.g0) * N) → ℝ :=
  gapNodesGen a ((P.n0 - P.g0) * N)

/-- Circle estimate (`r = |z|`): `|T_K(arg z)| |1-z|^(h+q) <= C exp(wc N)`, `K = (d0 N + 1)/2`. -/
def GapCircleBound (P : Parameters) (a r C wc : ℝ) : Prop :=
  ∀ (N : ℕ) (z : ℂ), 0 < N → ‖z‖ = r →
    ‖((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) ≤ C * Real.exp (wc * N)

/-- The weight bound consumed by the atom-cost layer. -/
def GapWeightBounds (P : Parameters) (tau : ∀ N : ℕ, Fin ((P.n0 - P.g0) * N) → ℝ) (w : ℝ) :
    Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ (k : ℕ) (a : Fin ((P.n0 - P.g0) * N)),
    |(rowCommonFactor P N).eval (tau N a)| * |restrictedWeight P N k (tau N) a| ≤
      108000 * N * Real.exp (w * N)

/-- A cardinal polynomial times its nodal derivative and linear denominator
recovers any nonzero scalar multiple of the full nodal polynomial. -/
theorem quad_basis_mul_derivative_eq {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (i : Fin J) {P : ℝ[X]} {c : ℝ}
    (hP : P = C c * ∏ j : Fin J, (X - C (τ j))) :
    quadBasis τ i * C ((derivative P).eval (τ i)) * (X - C (τ i)) = P := by
  classical
  let D : ℝ := ∏ j ∈ univ.erase i, (τ i - τ j)
  have hD : D ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun h => (mem_erase.mp hj).1 (hτ h).symm)
  have he := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := (univ : Finset (Fin J))) (v := τ) (mem_univ i)
  rw [Lagrange.eval_nodal, Lagrange.nodal_eq] at he
  have hder : (derivative P).eval (τ i) = c * D := by
    rw [hP, derivative_C_mul, eval_mul, eval_C, he]
  rw [quadBasis_eq, hder, hP, prod_inv_distrib]
  change (C D⁻¹ * (∏ j ∈ univ.erase i, (X - C (τ j)))) * C (c * D) * (X - C (τ i)) = _
  calc
    _ = C (D⁻¹ * (c * D)) * ((∏ j ∈ univ.erase i, (X - C (τ j))) * (X - C (τ i))) := by
      simp only [map_mul]; ring
    _ = _ := by
      rw [show D⁻¹ * (c * D) = c by field_simp]
      rw [prod_erase_mul _ _ (mem_univ i)]

theorem norm_cardinal_le_of_nodal {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (hmem : ∀ j, τ j ∈ Set.Ioo (-1 : ℝ) 1)
    (i : Fin J) {P : ℝ[X]} {c d radius : ℝ}
    (hP : P = C c * ∏ j : Fin J, (X - C (τ j)))
    (hd : 0 < d) (hder : d ≤ |(derivative P).eval (τ i)|)
    (hr : 1 < radius) (z : ℂ) (hz : ‖z‖ = radius) :
    ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      ‖(P.map (algebraMap ℝ ℂ)).eval z‖ / (d * (radius - 1)) := by
  have he := congrArg (fun Q : ℝ[X] => (Q.map (algebraMap ℝ ℂ)).eval z)
    (quad_basis_mul_derivative_eq hτ i hP)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X,
    eval_mul, eval_C, eval_sub, eval_X, Complex.coe_algebraMap] at he
  have hn := congrArg norm he
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn
  have hdist : radius - 1 ≤ ‖z - (τ i : ℂ)‖ := by
    have hh := norm_sub_norm_le z (τ i : ℂ)
    rw [hz, Complex.norm_real, Real.norm_eq_abs] at hh
    have hi := abs_lt.mpr (hmem i)
    linarith only [hh, hi]
  apply (le_div_iff₀ (mul_pos hd (sub_pos.mpr hr))).mpr
  calc
    _ ≤ ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ *
        |(derivative P).eval (τ i)| * ‖z - (τ i : ℂ)‖ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hder hdist (sub_pos.mpr hr).le (abs_nonneg _)) (norm_nonneg _)
    _ = _ := hn

/-- Cardinal polynomial of the gap nodes on `|z| = r`, in terms of `T_K(arg z)`. -/
theorem gap_cardinal_norm_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {J : ℕ} (hJ : 0 < J)
    (hD : 1 ≤ 4 * (((J + 1) / 2 : ℕ) : ℝ) * a / (1 - a ^ 2))
    {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) (i : Fin J) (z : ℂ) (hz : ‖z‖ = r) :
    ‖((quadBasis (gapNodesGen a J) i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      2 * ‖((gapPolyK a ((J + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ / (r - 1) ^ 2 := by
  set lead := gapLead a ((J + 1) / 2) with hlead
  have hl : 0 < lead := gapLead_pos ha0 ha1 _
  have hr : 0 < r - 1 := sub_pos.mpr hr1
  have hQ : gapNodal a J = C 1 * ∏ j : Fin J, (X - C (gapNodesGen a J j)) := by
    simp [gapNodal]
  have hτ := gap_nodes_injective ha0 ha1 J
  have hmem : ∀ j, gapNodesGen a J j ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun j => (gap_nodes_bounds ha0 ha1 J j).1
  -- derivative lower bound for the nodal polynomial
  have hE2 := gapExtra_eval_abs_le ha0 ha1 J (t := gapNodesGen a J i)
    (abs_le.mpr ⟨by linarith only [(hmem i).1], by linarith only [(hmem i).2]⟩)
  have hPd := gapPolyK_derivative_ge ha0 ha1 J i
  have hPn := gapPolyK_derivative_node ha0 ha1 hJ i
  have hder : 1 / (2 * lead) ≤ |(derivative (gapNodal a J)).eval (gapNodesGen a J i)| := by
    rw [hPn, abs_mul, abs_mul, abs_of_pos hl] at hPd
    have h1 : 1 ≤ lead * (|(derivative (gapNodal a J)).eval (gapNodesGen a J i)| *
        |(gapExtra a J).eval (gapNodesGen a J i)|) := hD.trans hPd
    have h2 : lead * (|(derivative (gapNodal a J)).eval (gapNodesGen a J i)| *
        |(gapExtra a J).eval (gapNodesGen a J i)|) ≤
        lead * (|(derivative (gapNodal a J)).eval (gapNodesGen a J i)| * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 (abs_nonneg _)) hl.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [h1, h2]
  have hcard := norm_cardinal_le_of_nodal hτ hmem i hQ (by positivity) hder hr1 z hz
  -- relate the nodal polynomial to `T_K` on the circle
  have hP := congrArg (fun Q : ℝ[X] => ‖(Q.map (algebraMap ℝ ℂ)).eval z‖)
    (gapPolyK_eq_nodal ha0 ha1 hJ)
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, norm_mul,
    Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl] at hP
  have hE := gapExtra_norm_ge ha0 ha1 J hr1 hr2 z hz
  set A := ‖((gapPolyK a ((J + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ with hA
  set q := ‖((gapNodal a J).map (algebraMap ℝ ℂ)).eval z‖ with hq
  set e := ‖((gapExtra a J).map (algebraMap ℝ ℂ)).eval z‖ with he
  have hq0 : 0 ≤ q := norm_nonneg _
  have hlq : lead * q * (r - 1) ≤ A := by
    rw [hP, abs_of_pos (gapLead_pos ha0 ha1 _)]
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hl.le hq0)
    nlinarith only [this]
  have hstep : q / (1 / (2 * lead) * (r - 1)) ≤ 2 * A / (r - 1) ^ 2 := by
    rw [show q / (1 / (2 * lead) * (r - 1)) = 2 * (lead * q) / (r - 1) by field_simp]
    rw [div_le_div_iff₀ hr (by positivity)]
    nlinarith only [hlq, hr]
  exact hcard.trans hstep

/-- Coefficients of `rowCommonFactor * (cardinal polynomial)` vanish from `H N` on. -/
theorem gap_common_basis_coeff_zero (P : Parameters) (hg : P.g0 ≤ P.n0) (N : ℕ)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : Fin ((P.n0 - P.g0) * N)) (i : ℕ)
    (hi : P.H N ≤ i) :
    (rowCommonFactor P N * quadBasis (gapNodesD P a N) j).coeff i = 0 := by
  have hf := rowCommonFactor_natDegree_le P N
  have hb : (quadBasis (gapNodesD P a N) j).natDegree ≤ (P.n0 - P.g0) * N - 1 :=
    quadBasis_natDegree_le (gap_nodes_injective ha0 ha1 ((P.n0 - P.g0) * N)) j
  have hd : (rowCommonFactor P N * quadBasis (gapNodesD P a N) j).natDegree ≤
      (rowCommonFactor P N).natDegree + (quadBasis (gapNodesD P a N) j).natDegree :=
    natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  have hJ : (P.n0 - P.g0) * N + P.g0 * N = P.n0 * N := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hg]
  have hpos : 0 < (P.n0 - P.g0) * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.A, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h] at hi hf
  obtain ⟨t, ht⟩ : ∃ t, t = (P.n0 - P.g0) * N := ⟨_, rfl⟩
  rw [← ht] at hJ hpos
  have hb2 : (quadBasis (gapNodesD P a N) j).natDegree ≤ t - 1 := by rw [ht]; exact hb
  obtain ⟨nn, hnn⟩ : ∃ nn, nn = P.n0 * N := ⟨_, rfl⟩
  rw [← hnn] at hJ hi
  omega

/-- Weight functional of the cardinal polynomial. -/
theorem gap_functional_le (P : Parameters) (hg : P.g0 ≤ P.n0) {a r C wc : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (ha4 : 1 - a ^ 2 ≤ 4 * a)
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hcirc : GapCircleBound P a r C wc)
    (N k : ℕ) (j : Fin ((P.n0 - P.g0) * N)) :
    |polynomialFunctional P N k (rowCommonFactor P N * quadBasis (gapNodesD P a N) j)| ≤
      4 * (P.H N : ℝ) * (2 * (C * Real.exp (wc * N)) / (r - 1) ^ 2) := by
  have hJ : 0 < (P.n0 - P.g0) * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hJ)
  have hd := gapSq_pos ha0 ha1
  have hD : 1 ≤ 4 * ((((P.n0 - P.g0) * N + 1) / 2 : ℕ) : ℝ) * a / (1 - a ^ 2) := by
    rw [le_div_iff₀ hd]
    have : (1 : ℝ) ≤ ((((P.n0 - P.g0) * N + 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ ((P.n0 - P.g0) * N + 1) / 2 by omega)
    nlinarith only [this, ha4, ha0]
  apply polynomialFunctional_common_factor_le P N k _
    (gap_common_basis_coeff_zero P hg N ha0 ha1 j) (radius := r) hr1.le
  intro z hz
  have hc := gap_cardinal_norm_le ha0 ha1 hJ hD hr1 hr2 j z hz
  have hb := hcirc N z hN hz
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, eval_mul, eval_pow, eval_sub, eval_one, eval_X, norm_mul, norm_pow,
    Complex.coe_algebraMap]
  have hr : 0 < (r - 1) ^ 2 := by positivity
  calc _ ≤ (2 * ‖((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ /
        (r - 1) ^ 2) * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 / (r - 1) ^ 2 * (‖((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map
          (algebraMap ℝ ℂ)).eval z‖ * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N)) := by ring
    _ ≤ 2 / (r - 1) ^ 2 * (C * Real.exp (wc * N)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem gap_weight_joint_le (P : Parameters) (hg : P.g0 ≤ P.n0) {a r C wc : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (ha4 : 1 - a ^ 2 ≤ 4 * a)
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hcirc : GapCircleBound P a r C wc)
    (N k : ℕ) (j : Fin ((P.n0 - P.g0) * N)) :
    |(rowCommonFactor P N).eval (gapNodesD P a N j)| *
      |restrictedWeight P N k (gapNodesD P a N) j| ≤
      4 * (P.H N : ℝ) * (2 * (C * Real.exp (wc * N)) / (r - 1) ^ 2) := by
  have hn := rowCommonFactor_eval_ne_zero_of P N (gap_nodes_ne_zero ha0 ha1 _ j)
    (gap_nodes_ne_one ha0 ha1 _ j)
  have key : ∀ x y : ℝ, x ≠ 0 → |x| * (|y| / |x|) = |y| := fun x y hx => by
    have := abs_ne_zero.mpr hx
    field_simp
  rw [restrictedWeight, abs_div]
  exact le_of_eq_of_le (key _ _ hn) (gap_functional_le P hg ha0 ha1 ha4 hr1 hr2 hcirc N k j)

/-- The weight bound `108000 N exp(w N)` for any `w > wc`, eventually in `N`; any parity of `d0 N`. -/
theorem gap_weight_bounds (P : Parameters) (hg : P.g0 ≤ P.n0) {a r C wc w : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (ha4 : 1 - a ^ 2 ≤ 4 * a)
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hcirc : GapCircleBound P a r C wc) (hw : wc < w) :
    GapWeightBounds P (gapNodesD P a) w := by
  set c0 : ℝ := 8 * (P.H 1 : ℝ) * C / (r - 1) ^ 2 with hc0
  have ht : Filter.Tendsto (fun N : ℕ => Real.exp ((w - wc) * N)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop (sub_pos.mpr hw) tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (c0 / 108000), Filter.eventually_gt_atTop 0]
    with N hN hN0 k j
  refine (gap_weight_joint_le P hg ha0 ha1 ha4 hr1 hr2 hcirc N k j).trans ?_
  have hH : (P.H N : ℝ) = (P.H 1 : ℝ) * N := by
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
      Parameters.q, Parameters.g, Parameters.h]
    push_cast; ring
  have hexp : Real.exp (w * N) = Real.exp (wc * N) * Real.exp ((w - wc) * N) := by
    rw [← Real.exp_add]; congr 1; ring
  have hN1 : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [hH, hexp]
  have he := Real.exp_pos (wc * N)
  have hmul := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by norm_num : (0 : ℝ) < 108000)).mp hN)
    (mul_nonneg hN1.le he.le)
  have hr : 0 < (r - 1) ^ 2 := by positivity
  have : 4 * ((P.H 1 : ℝ) * N) * (2 * (C * Real.exp (wc * N)) / (r - 1) ^ 2) =
      c0 * (N * Real.exp (wc * N)) := by
    rw [hc0]; field_simp; ring
  rw [this]
  nlinarith only [hmul]

end

end Analytic
end CatalanMeasure.GenD
