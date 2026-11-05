module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Nodes
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Psi
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.TrialEnd
public import Submission.CatalanMeasure.GenD.Analytic.DeltaChain
public import Submission.CatalanMeasure.GenD.Analytic.WeightedAtom
public import Submission.CatalanMeasure.GenD.D58.Budget590

@[expose] public section

/-!
# 410 assembly, G6: `delta_small` from the three cases and the weight side

`delta_small_410`: given the first-case bound (`FreeFirstBound`), the second case with `m ≥ α₁ n`
(`FreeLargeBound`, `α₁ = 1/16`) and the signed near bound `FreeNearBound` with the node-set predicate
`NodeSub τ` of the real gap nodes, the weight side `Psi.s1_hweights_Psi0` (`w = 87.9663`) gives
`delta_small` with `ρ = K590.rhoEnd 87.9663 = 58 · secondCost' + 87.9663` and
`tΔ = 58² (target0 - log 2 / 2)`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Polynomial
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Signed CatalanMeasure.GenD.Signed.Data.S1

open CatalanMeasure.GenD.D58

noncomputable section

/-- The second-population gap predicate: `g ≤ |u|` with `g = 401/2500`. -/
def G410 : ℝ → Prop := fun u => (401 / 2500 : ℝ) ≤ |u|

/-- The cost of the near case: `c2 = 58 · secondCost'`. -/
def c2_410 : ℝ := 58 * K590.secondCost'

/-- **`delta_small` of the 410 design**, from the three cases. -/
theorem delta_small_410
    (hfirst : FreeFirstBound D58.Odd.design K590.target0 ((D58.Odd.design.n0 : ℝ) * K590.secondCost'))
    (hnear : FreeNearBound D58.Odd.design G410 (NodeSub nodesτ) K590.target0 c2_410 (1 / 16))
    (hlarge : FreeLargeBound D58.Odd.design G410 K590.target0
      ((D58.Odd.design.n0 : ℝ) * K590.secondCost') (1 / 16)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K590.rhoEnd (879663 / 10000) * (N : ℝ))) →
        |aeval x (deltaPoly D58.Odd.design N)| ≤
          Real.exp (-((58 ^ 2 * (K590.target0 - Real.log 2 / 2) - ε) * (N : ℝ) ^ 2)) := by
  have h58 : ((D58.Odd.design.n0 : ℕ) : ℝ) = 58 := by norm_num [D58.Odd.design]
  have hr : (58 : ℝ) * K590.secondCost' + 879663 / 10000 = K590.rhoEnd (879663 / 10000) := by
    rw [K590.rhoEnd_eq]
  have hpoint : WeightedAtomPointBinom D58.Odd.design nodesτ G410 K590.target0
      (58 * K590.secondCost' + 879663 / 10000) := by
    have := weighted_atom_point_binom_of_signed (target := K590.target0)
      (r := 58 * K590.secondCost') (w := 879663 / 10000)
      (c₁ := (D58.Odd.design.n0 : ℝ) * K590.secondCost') (c₂ := c2_410)
      (c₃ := (D58.Odd.design.n0 : ℝ) * K590.secondCost') (α₁ := 1 / 16)
      D58.Odd.design D58.Odd.design_admissible nodesτ G410 (NodeSub nodesτ)
      (fun N m y a ha h => ⟨a, ha, h⟩) hfirst hnear hlarge
      (by rw [h58]) le_rfl (by rw [h58]) S1.Psi.s1_hweights_Psi0
    exact this
  have hd := delta_small_binom D58.Odd.design D58.Odd.design_admissible nodesτ G410
    (fun N => gap_nodes_injective aGap_pos aGap_lt_one _)
    (fun N i => (gap_nodes_bounds aGap_pos aGap_lt_one _ i).1)
    (fun N i => gap_nodes_ne_zero aGap_pos aGap_lt_one _ i)
    (fun N i => by
      have h := (gap_nodes_coordinate (g := 401 / 2500) (by norm_num) (by norm_num)
        ((D58.Odd.design.n0 - D58.Odd.design.g0) * N) i).2
      rw [← aGap_eq] at h
      exact h)
    K590.target0 (58 * K590.secondCost' + 879663 / 10000)
    (58 ^ 2 * (K590.target0 - Real.log 2 / 2))
    (by rw [h58]) hpoint
  rw [hr] at hd
  intro ε hε
  filter_upwards [hd ε hε] with N hN x hx
  exact hN x hx

end

end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.delta_small_410
