module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Phase2
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Decay

@[expose] public section

/-!
# 410 assembly: `FreeNearBound` from the Phase 2 data and the class link

`hnear410`: `Phase2Data.signedSecondSheetNearNd_nearOpt_of_cert` for `D := phase2 R`, with the node
predicate `Nd := NodeSub nodesτ` of the real gap nodes (`markedCap_real`).  The remaining inputs are
the second-population End trial `D0`, the damping data `δ, e` and the `LinkCert` term `L`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter
open CatalanMeasure.Signed OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic

open CatalanMeasure.GenD.D58

noncomputable section

theorem hnear410 (R : Rows410) {residual nearCap : ℝ}
    (D0 : SecondTrialBoundsEnd P410 0 K590.target residual nearCap K590.secondCost' G410)
    {δ e : ℝ} (hδ : 0 < δ) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (L : LinkCert (phase2 R) P410 K590.target residual nearCap K590.secondCost' G410 D0 δ e
      K590.target0 c2_410) :
    FreeNearBound P410 G410 (NodeSub nodesτ) K590.target0 c2_410 (1 / 16) := by
  have hP : Admissible P410 := D58.Odd.design_admissible
  refine Phase2Data.signedSecondSheetNearNd_nearOpt_of_cert (phase2 R) hP G410 K590.target0 c2_410
    (fun N => by simp [phase2, Parameters.n, P410, D58.Odd.design])
    (fun N r a b h => Glue410.hconst_closed hP N r a b h)
    (fun N => rfl) (fun N => rfl) (fun N => rfl) (fun N => rfl)
    (fun N k q m1 m2' xn gp yn yp' => by
      show logRatioZ (q + m2' - 5 * N) _ _ = _
      simp [Parameters.g, P410, D58.Odd.design])
    rfl
    (by
      show K590.secondCost' * (P410.n0 : ℝ) ≤ c2_410
      simp [c2_410, P410, D58.Odd.design]; linarith)
    (NodeSub nodesτ)
    (fun N m y hy h => by
      show MarkedCap (401 / 2500) (999 / 1000) (9631 / 20000) (((58 * N : ℕ) : ℝ)) (umin410 N) y
      push_cast
      exact markedCap_real N hy h)
    D0 hδ he hec L

end

end CatalanMeasure.GenD.Signed.Data.Assembly
