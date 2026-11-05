module

public import Submission.CatalanMeasure.GenD.Analytic.MarkedSheet
public import Submission.CatalanMeasure.GenD.Analytic.Prefactor
public import Submission.CatalanMeasure.Parametric.RealIntegral
public import Submission.CatalanMeasure.JointDetExpansion

@[expose] public section

/-!
# Analytic layer, group 3: atom data of the node expansion

Generic versions (design `P`, node count `J = (n0 - g0) N`) of
`TwentyAtomDeterminants` / `TargetAtomCost` / `GapAtomCost` (data part) / `TwentyCostPerturbation`:

* `realBaseMatrix P N`, `nodeAtomVectors`, `nodeAtomWeights`, `node_delta_matrix_eq`
  (`Δ_N(x) = det(B + (x - G) Σ_a Φ_a β_a)`);
* `atomBaseBoundAt P target N δ = 2^n · prefactor · exp((n0 N)² (-target + log 2 / 2 + δ))`,
  `atomColumnCost ρ N = 540000 N e^{ρ N}`;
* `joint_factor_of_cost_eventually`: at the critical radius the joint binomial factor is
  `exp (ε (n0 N)²)` (the constant `18 N` of P20 becomes `(n0 - g0) N`).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial OAI.InternalCatalan Set Finset MeasureTheory Matrix Filter CatalanMeasure.Parametric
open scoped Topology BigOperators

noncomputable section

/-- `C (N^d) ≤ exp (ε N)` eventually (restated from `TwentyPerturbationSetup`). -/
theorem positive_polynomial_factor_eventually (C : ℝ) (hC : 0 < C) (d : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ d ≤ Real.exp (ε * (N : ℝ)) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have ht := (hi.const_mul (Real.log C)).add (hl.const_mul (d : ℝ))
  simp only [mul_zero, add_zero] at ht
  have he := (tendsto_order.mp ht).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log C + (d : ℝ) * Real.log (N : ℝ) < ε * (N : ℝ) := by
    have hh := (div_lt_iff₀ hn).mp
      (show (Real.log C + (d : ℝ) * Real.log (N : ℝ)) / (N : ℝ) < ε by
        simpa only [add_div, div_eq_mul_inv, add_mul, mul_assoc] using heN)
    exact hh
  have hx : C * (N : ℝ) ^ d = Real.exp (Real.log C + (d : ℝ) * Real.log (N : ℝ)) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hC, Real.exp_log hn]
  rw [hx]
  exact Real.exp_le_exp.mpr hlog.le

/-- The real base matrix `(realEntry P N r k)`. -/
def realBaseMatrix (P : Parameters) (N : ℕ) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ :=
  fun r k => realEntry P N r.val k.val

/-- Atom base bound `2^n · prefactor · exp ((n0 N)² (-target + log 2 / 2 + δ))`. -/
def atomBaseBoundAt (P : Parameters) (target : ℝ) (N : ℕ) (δ : ℝ) : ℝ :=
  (2 : ℝ) ^ P.n N * sheetPrefactor P N *
    Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + δ))

/-- Column cost of an atom: `540000 N e^{ρ N}`. -/
def atomColumnCost (ρ : ℝ) (N : ℕ) : ℝ :=
  540000 * (N : ℝ) * Real.exp (ρ * N)

/-- Row vectors of the atoms: original polynomial values at the nodes. -/
def nodeAtomVectors (P : Parameters) (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (N : ℕ) :
    Fin (P.n N) → Fin ((P.n0 - P.g0) * N) → ℝ :=
  fun r a => (realPoly (rowP P N r.val)).eval (τ N a)

/-- Column weights of the atoms: restricted quadrature weights. -/
def nodeAtomWeights (P : Parameters) (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (N : ℕ) :
    Fin ((P.n0 - P.g0) * N) → Fin (P.n N) → ℝ :=
  fun a k => restrictedWeight P N k.val (τ N) a

theorem node_count_le (P : Parameters) (N : ℕ) : P.n N - P.g N ≤ (P.n0 - P.g0) * N :=
  le_of_eq (by simp only [Parameters.n, Parameters.g]; rw [Nat.sub_mul])

theorem node_delta_matrix_eq (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτzero : ∀ N i, τ N i ≠ 0) (hτone : ∀ N i, τ N i ≠ 1)
    {N : ℕ} (hN : 0 < N) (x : ℝ) :
    aeval x (deltaPoly P N) =
      (Matrix.of fun r k : Fin (P.n N) => realBaseMatrix P N r k +
        (x - catalan) * ∑ a, nodeAtomVectors P τ N r a * nodeAtomWeights P τ N a k).det := by
  have hh := AlgHom.map_det (aeval (R := ℚ) x)
    ((X : ℚ[X]) • (measureCatalanMatrix P N).map C + (measureBaseMatrix P N).map C)
  unfold Parametric.deltaPoly
  rw [hh]
  congr 1
  ext r k
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Parametric.deltaPoly_matrix_entry]
  simp only [map_add, map_mul, aeval_X, aeval_C, eq_ratCast, Matrix.of_apply,
    realBaseMatrix, nodeAtomVectors, nodeAtomWeights]
  have hw := filteredCatalanCoeff_full_weights hP hN r.isLt (node_count_le P N)
    (hτinj N) (hτzero N) (hτone N) k.val
  rw [← hw, ← filteredEntry_real_affine hP hN r.isLt k.isLt]
  ring

/-- At the critical radius the joint binomial factor has logarithm `O(N log N)`. -/
theorem joint_factor_of_cost_eventually (P : Parameters) (hn0 : 0 < P.n0) (ρ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ δ : ℝ, |δ| ≤ Real.exp (-(ρ * (N : ℝ))) →
      (1 + (((P.n0 - P.g0) * N : ℕ) : ℝ) * (|δ| * atomColumnCost ρ N)) ^ P.n N ≤
        Real.exp (ε * ((P.n0 : ℝ) * (N : ℝ)) ^ 2) := by
  have hc : (0 : ℝ) < P.n0 := by exact_mod_cast hn0
  generalize hd : ((P.n0 - P.g0 : ℕ) : ℝ) = d
  have hd0 : 0 ≤ d := by rw [← hd]; exact Nat.cast_nonneg _
  have hh := positive_polynomial_factor_eventually (540000 * d + 1) (by linarith only [hd0]) 2
    (ε := (P.n0 : ℝ) * ε) (by positivity)
  filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hpoly hN δ hδ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : |δ| * Real.exp (ρ * (N : ℝ)) ≤ 1 := by
    calc
      _ ≤ Real.exp (-(ρ * (N : ℝ))) * Real.exp (ρ * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hδ (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; simp
  have hin : 1 + (((P.n0 - P.g0) * N : ℕ) : ℝ) * (|δ| * atomColumnCost ρ N) ≤
      Real.exp ((P.n0 : ℝ) * ε * (N : ℝ)) := by
    calc
      _ = 1 + 540000 * d * (N : ℝ) ^ 2 * (|δ| * Real.exp (ρ * (N : ℝ))) := by
        unfold atomColumnCost
        push_cast
        rw [hd]
        ring
      _ ≤ 1 + 540000 * d * (N : ℝ) ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_left he
          (mul_nonneg (mul_nonneg (by norm_num) hd0) (sq_nonneg (N : ℝ)) : (0 : ℝ) ≤ 540000 * d * (N : ℝ) ^ 2)]
      _ ≤ (540000 * d + 1) * (N : ℝ) ^ 2 := by
        nlinarith only [hN1, hd0]
      _ ≤ _ := hpoly
  calc
    _ ≤ (Real.exp ((P.n0 : ℝ) * ε * (N : ℝ))) ^ P.n N :=
      pow_le_pow_left₀ (by unfold atomColumnCost; positivity) hin _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      change ((P.n0 * N : ℕ) : ℝ) * ((P.n0 : ℝ) * ε * (N : ℝ)) = ε * ((P.n0 : ℝ) * (N : ℝ)) ^ 2
      push_cast
      ring

end

end Analytic
end CatalanMeasure.GenD
