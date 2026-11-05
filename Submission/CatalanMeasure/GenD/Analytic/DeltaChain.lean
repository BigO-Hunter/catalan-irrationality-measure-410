module

public import Submission.CatalanMeasure.GenD.Analytic.DeltaSmall
public import Submission.CatalanMeasure.GenD.Analytic.MarkedSheetOn
public import Submission.CatalanMeasure.GenD.Analytic.GapWeights
public import Submission.CatalanMeasure.GenD.Analytic.Glue

@[expose] public section

/-!
# Analytic layer: the wired chain  sups -> `delta_small` (design-generic)

* `weighted_atom_point`: G2's `marked_sheet_on` feeds G3's `weighted_atom_point_of_sheet`
  (`ρ = r + w`);
* `SecondFieldCert`: the arguments of `secondTrial_of_fields` (three suprema, trial norms,
  near cap, budget) bundled as one structure, with the weights `α β γ b q` written out;
* `delta_small_of_certificates`: gap nodes `gapNodesD P (2g/(1+g²))` with the weight bounds of
  `gap_weight_bounds` (node count `(n0 - g0) N`, any parity of `d0`), the first-trial bounds `F`
  and the second-trial bounds built from a `SecondFieldCert`, give the `delta_small` shape
  consumed by `GenD.measure_of_design`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric CatalanMeasure.CellCert OAI.InternalCatalan Filter Set Polynomial
open scoped Topology BigOperators

noncomputable section

/-- G2's marked-sheet bound feeds G3's weighted-atom point (`ρ = r + w`). -/
theorem weighted_atom_point {P : Parameters} (hP : Admissible P)
    {target c residual nearCap cost r w : ℝ}
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ)
    (F : FirstTrialBounds P target c) (G : ℝ → Prop)
    (D : SecondTrialBounds P target residual nearCap cost G)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| ≤
        108000 * (N : ℝ) * Real.exp (w * N))
    (hfc : (P.n0 : ℝ) * c ≤ r) (hsc : (P.n0 : ℝ) * cost ≤ r) :
    WeightedAtomPoint P τ G target (r + w) :=
  weighted_atom_point_of_sheet P hP τ G
    (fun _ hε => marked_sheet_on hP F G D hfc hsc hε) hweights

/-- The certificate data of the second population: all arguments of `secondTrial_of_fields`
(the three suprema `row_sup`, `column_sup`, `residual_sup`, the near cap, the trial norms and the
numerical budget), with the weights written out in terms of `P`. -/
structure SecondFieldCert (P : Parameters) (target residual nearCap cost : ℝ) (G : ℝ → Prop) where
  u : ℕ → ℝ
  v : ℕ → ℝ
  hu : Summable (fun k => |u k|)
  hv : Summable (fun k => |v k|)
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes P * Real.log (1 + y ^ 2) + (((P.n0 : ℝ) - 2 * P.g0 - 1) / P.n0) * Real.log y -
      u 1 * y ≤ nearCap
  norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) (2 * (P.h0 : ℝ) / P.n0)
      (((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0) u v x ≤ MX
  column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG ((P.b0 : ℝ) / P.n0) ((P.q0 : ℝ) / P.n0) v s ≤ MY
  residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) u x ≤ residual
  budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
    (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * residual + t * nearCap ≤
        -target + Real.log 2 / 2 + cost * a

/-- The second-trial bounds of a `SecondFieldCert`. -/
def SecondFieldCert.bounds {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (C : SecondFieldCert P target residual nearCap cost G) :
    SecondTrialBounds P target residual nearCap cost G :=
  secondTrial_of_fields hP C.u C.v C.hu C.hv _ _ _ _ _ rfl rfl rfl rfl rfl C.MX C.MY nearCap
    C.near_sup C.norm_le C.field_sum C.row_sup C.column_sup C.residual_sup C.budget

/-- **The wired chain.**  With `a = 2g/(1+g²)` (the gap `g ≤ |realCoordinate τ|`), the circle
certificate `GapCircleBound P a rc C wc` with `wc < w`, the first-trial bounds `F` and the
second-population certificate `S` (with `G u := g ≤ |u|`), `delta_small` holds with
`tΔ = n0² (target - log 2 / 2)` and every `ρ ≥ r + w`, `r ≥ n0 · max(c, cost)`. -/
theorem delta_small_of_certificates {P : Parameters} (hP : Admissible P)
    {g rc C wc w : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (ha4 : 1 - (2 * g / (1 + g ^ 2)) ^ 2 ≤ 4 * (2 * g / (1 + g ^ 2)))
    (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : GapCircleBound P (2 * g / (1 + g ^ 2)) rc C wc) (hw : wc < w)
    {target c residual nearCap cost r ρ tΔ : ℝ}
    (F : FirstTrialBounds P target c)
    (S : SecondFieldCert P target residual nearCap cost (fun u => g ≤ |u|))
    (hfc : (P.n0 : ℝ) * c ≤ r) (hsc : (P.n0 : ℝ) * cost ≤ r) (hρ : r + w ≤ ρ)
    (hT : tΔ = (P.n0 : ℝ) ^ 2 * (target - Real.log 2 / 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * (N : ℝ))) →
        |aeval x (CatalanMeasure.Parametric.deltaPoly P N)| ≤
          Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2)) := by
  have hd : 0 < 1 + g ^ 2 := by positivity
  have ha0 : 0 < 2 * g / (1 + g ^ 2) := by positivity
  have ha1 : 2 * g / (1 + g ^ 2) < 1 := by
    rw [div_lt_one hd]; nlinarith only [pow_pos (sub_pos.mpr hg1) 2]
  have hg : P.g0 ≤ P.n0 := by have := hP.2.2.2.2; omega
  have hweights : GapWeightBounds P (gapNodesD P (2 * g / (1 + g ^ 2))) w :=
    gap_weight_bounds P hg ha0 ha1 ha4 hr1 hr2 hcirc hw
  have hpoint := weighted_atom_point hP (gapNodesD P (2 * g / (1 + g ^ 2))) F
    (fun u => g ≤ |u|) (S.bounds hP) hweights hfc hsc
  have hd0 := delta_small P hP (gapNodesD P (2 * g / (1 + g ^ 2))) (fun u => g ≤ |u|)
    (fun N => gap_nodes_injective ha0 ha1 _)
    (fun N i => (gap_nodes_bounds ha0 ha1 _ i).1)
    (fun N i => gap_nodes_ne_zero ha0 ha1 _ i)
    (fun N i => (gap_nodes_coordinate hg0 hg1 _ i).2) target (r + w) tΔ hT hpoint
  intro ε hε
  filter_upwards [hd0 ε hε] with N hN x hx
  refine hN x (hx.trans (Real.exp_le_exp.mpr ?_))
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith only [hρ, this]

end

end Analytic
end CatalanMeasure.GenD
