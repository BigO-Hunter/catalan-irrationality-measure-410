module

public import Submission.CatalanMeasure.GenD.Analytic.WeightedAtom

@[expose] public section

/-!
# Analytic layer, group 3: base bound, perturbation, and `delta_small`

Generic versions of `GapSmallness.base_bound_on` / `perturbation_on` and the combination used by
`GenD.D58.Final`: for a design `P` (admissible) and a weighted atom point at rate `ρ`,

`|Δ_N(x)| ≤ exp (-((tΔ - ε) N²))` for `|x - G| ≤ exp (-ρ N)`, with `tΔ = n0² (target - log 2 / 2)`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open OAI.InternalCatalan Polynomial Filter Real Finset CatalanMeasure.Parametric
open scoped Nat Topology BigOperators

noncomputable section

/-- The atom-determinant bound produced by `weighted_atom_det` (from `WeightedAtomPoint`) or by
`weighted_atom_det_binom` (from `WeightedAtomPointBinom`); `base_bound`, `perturbation` and
`delta_small` only use this consequence of the weighted atom point. -/
def AtomDetBound (P : Parameters) (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ)
    (target ρ : ℝ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ f : Fin (P.n N) → Option (Fin ((P.n0 - P.g0) * N)),
    (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) *
      |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
    atomBaseBoundAt P target N ε * ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N)

theorem atomDetBound_of_point (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPoint P τ G target ρ) : AtomDetBound P τ target ρ :=
  fun hε => weighted_atom_det P τ G hτinj hτmem hτzero hτG target ρ hpoint hε

theorem atomDetBound_of_point_binom (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointBinom P τ G target ρ) : AtomDetBound P τ target ρ :=
  fun hε => weighted_atom_det_binom P τ G hτinj hτmem hτzero hτG target ρ hpoint hε

theorem base_bound_of_det (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (target ρ : ℝ) (hdet : AtomDetBound P τ target ρ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,|aeval catalan (deltaPoly P N)| ≤
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)) := by
  have hn0 : 0 < P.n0 := hP.1
  filter_upwards [hdet (show 0<ε/2 by positivity),
    sheet_prefactor_eventually P hn0 (show 0<ε/2 by positivity),eventually_gt_atTop (0:ℕ)]
    with N hd hp hN
  have hh :=hd (fun _ =>none)
  simp only [Option.elim,prod_const_one,mul_one,one_mul,CatalanMeasure.atomMatrix]
    at hh
  rw [aeval_catalan_deltaPoly hP hN]
  have hb : |(realBaseMatrix P N).det| ≤ atomBaseBoundAt P target N (ε/2) :=by
    have he : (Matrix.of fun r k =>realBaseMatrix P N r k)=realBaseMatrix P N :=rfl
    rw [he] at hh
    exact hh
  refine hb.trans ?_
  unfold atomBaseBoundAt
  calc
    _ ≤ Real.exp (ε/2*((P.n0 : ℝ) * (N : ℝ)) ^ 2)*
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε/2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ :=by rw [← Real.exp_add];congr 1;ring

theorem perturbation_of_det (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0) (target ρ : ℝ)
    (hdet : AtomDetBound P τ target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(ρ*(N : ℝ))) →
      |aeval x (deltaPoly P N)-aeval catalan (deltaPoly P N)| ≤
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)) := by
  have hn0 : 0 < P.n0 := hP.1
  filter_upwards [hdet (show 0 < ε/3 by positivity),
    sheet_prefactor_eventually P hn0 (show 0 < ε/3 by positivity),
    joint_factor_of_cost_eventually P hn0 ρ (show 0 < ε/3 by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hd hp hf hN x hx
  let δ : ℝ := x-catalan
  let M : ℝ := atomBaseBoundAt P target N (ε/3)
  let c : ℝ := atomColumnCost ρ N
  have hM : 0 ≤ M := by unfold M atomBaseBoundAt sheetPrefactor; positivity
  have hc : 0 ≤ c := by unfold c atomColumnCost; positivity
  have hmain := CatalanMeasure.abs_det_add_atoms_sub_le_joint
    (realBaseMatrix P N) (nodeAtomVectors P τ N) (nodeAtomWeights P τ N)
    δ hM hc hd
  rw [node_delta_matrix_eq P hP τ hτinj hτzero (fun N i => (hτmem N i).2.ne) hN x, aeval_catalan_deltaPoly hP hN]
  change |_-(realBaseMatrix P N).det| ≤ _
  have hfactor : (1+(((P.n0 - P.g0) * N : ℕ) : ℝ)*(|δ| * c))^(P.n N)-1 ≤
      Real.exp (ε/3*((P.n0 : ℝ) * (N : ℝ)) ^ 2) := by
    have hh := hf δ hx
    dsimp [c]
    linarith only [hh]
  calc
    _ ≤ M*Real.exp (ε/3*((P.n0 : ℝ) * (N : ℝ)) ^ 2) :=
      hmain.trans (mul_le_mul_of_nonneg_left hfactor hM)
    _ ≤ (Real.exp (ε/3*((P.n0 : ℝ) * (N : ℝ)) ^ 2)*
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε/3)))*
          Real.exp (ε/3*((P.n0 : ℝ) * (N : ℝ)) ^ 2) := by
      unfold M atomBaseBoundAt
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


theorem base_bound (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ) (hpoint : WeightedAtomPoint P τ G target ρ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,|aeval catalan (deltaPoly P N)| ≤
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)) :=
  base_bound_of_det P hP τ target ρ
    (atomDetBound_of_point P τ G hτinj hτmem hτzero hτG target ρ hpoint) hε

/-- `base_bound` from the binomial weighted atom point. -/
theorem base_bound_binom (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointBinom P τ G target ρ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,|aeval catalan (deltaPoly P N)| ≤
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)) :=
  base_bound_of_det P hP τ target ρ
    (atomDetBound_of_point_binom P τ G hτinj hτmem hτzero hτG target ρ hpoint) hε

theorem perturbation (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPoint P τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(ρ*(N : ℝ))) →
      |aeval x (deltaPoly P N)-aeval catalan (deltaPoly P N)| ≤
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)) :=
  perturbation_of_det P hP τ hτinj hτmem hτzero target ρ
    (atomDetBound_of_point P τ G hτinj hτmem hτzero hτG target ρ hpoint) hε

/-- `perturbation` from the binomial weighted atom point. -/
theorem perturbation_binom (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointBinom P τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(ρ*(N : ℝ))) →
      |aeval x (deltaPoly P N)-aeval catalan (deltaPoly P N)| ≤
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)) :=
  perturbation_of_det P hP τ hτinj hτmem hτzero target ρ
    (atomDetBound_of_point_binom P τ G hτinj hτmem hτzero hτG target ρ hpoint) hε

/-- **`delta_small`** from the atom-determinant bound, i.e. from either weighted atom point
(the hypothesis consumed by `GenD.measure_of_design` / `D58.Final`):
with `tΔ = n0² (target - log 2 / 2)`, `|Δ_N(x)| ≤ exp (-((tΔ - ε) N²))` for `|x - G| ≤ exp (-ρ N)`. -/
theorem delta_small_of_det (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0) (target ρ tΔ : ℝ)
    (hT : tΔ = (P.n0 : ℝ) ^ 2 * (target - Real.log 2 / 2))
    (hdet : AtomDetBound P τ target ρ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * (N : ℝ))) →
        |aeval x (deltaPoly P N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)) := by
  intro ε hε
  have hc : (0 : ℝ) < P.n0 := by exact_mod_cast hP.1
  set e : ℝ := ε / (2 * (P.n0 : ℝ) ^ 2) with he
  have he0 : 0 < e := by positivity
  have h2 := positive_polynomial_factor_eventually (2 : ℝ) (by norm_num) 0 (ε := ε / 2)
    (by positivity)
  filter_upwards [perturbation_of_det P hP τ hτinj hτmem hτzero target ρ hdet he0,
    base_bound_of_det P hP τ target ρ hdet he0, h2,
    eventually_gt_atTop (0 : ℕ)] with N hpert hbase htwo hN x hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let E : ℝ := ((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + e)
  have hΔ : |aeval x (deltaPoly P N)| ≤ 2 * Real.exp E := by
    calc
      _ = |(aeval x (deltaPoly P N) - aeval catalan (deltaPoly P N)) +
          aeval catalan (deltaPoly P N)| := by rw [sub_add_cancel]
      _ ≤ |aeval x (deltaPoly P N) - aeval catalan (deltaPoly P N)| +
          |aeval catalan (deltaPoly P N)| := abs_add_le _ _
      _ ≤ Real.exp E + Real.exp E := add_le_add (hpert x hx) hbase
      _ = _ := by ring
  have htwo' : (2 : ℝ) ≤ Real.exp (ε / 2 * (N : ℝ) ^ 2) := by
    simp only [pow_zero, mul_one] at htwo
    exact htwo.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by nlinarith only [hN1]) (by positivity)))
  calc
    _ ≤ 2 * Real.exp E := hΔ
    _ ≤ Real.exp (ε / 2 * (N : ℝ) ^ 2) * Real.exp E :=
      mul_le_mul_of_nonneg_right htwo' (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      simp only [E, he, hT]
      field_simp
      ring

theorem delta_small (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ tΔ : ℝ)
    (hT : tΔ = (P.n0 : ℝ) ^ 2 * (target - Real.log 2 / 2))
    (hpoint : WeightedAtomPoint P τ G target ρ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * (N : ℝ))) →
        |aeval x (deltaPoly P N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)) :=
  delta_small_of_det P hP τ hτinj hτmem hτzero target ρ tΔ hT
    (atomDetBound_of_point P τ G hτinj hτmem hτzero hτG target ρ hpoint)

/-- **`delta_small` for the binomial route** (S1): the same conclusion from
`WeightedAtomPointBinom`, as produced by `weighted_atom_point_binom_of_signed`. -/
theorem delta_small_binom (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ tΔ : ℝ)
    (hT : tΔ = (P.n0 : ℝ) ^ 2 * (target - Real.log 2 / 2))
    (hpoint : WeightedAtomPointBinom P τ G target ρ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * (N : ℝ))) →
        |aeval x (deltaPoly P N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)) :=
  delta_small_of_det P hP τ hτinj hτmem hτzero target ρ tΔ hT
    (atomDetBound_of_point_binom P τ G hτinj hτmem hτzero hτG target ρ hpoint)
