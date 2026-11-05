module

public import Submission.CatalanMeasure.GenD.Uniform.LedgerW.Saving
public import Submission.CatalanMeasure.GenD.Uniform.Arithmetic.CorrectedGrowth

@[expose] public section

/-!
# Design-generic growth of the denominator from a nullity profile (lane G4)

`D_growth_of_nullityLB` is the `D_growth` field of `DesignData` for the canonical
(recycling-safe) normalizer of an arbitrary `NullityLB`, with the leading constant

  gD = A2(n0, H1, b0) log 2 + (kappa0 + int_1^{H1} f_D) - sum_w int_w (K_w + G_w - 2 n0),

i.e. the 2-adic selector budget `B2`, the odd-prime pool majorant `f_D`, and the exact
piecewise-linear integrals of the compatible saving
`kappa = (a_D - (2 n0 - f_D))_+ >= K + G - 2 n0` over finitely many ordered windows.  Each window
carries a PL lower profile `K` of the nullity bound (with a finitely supported exceptional
charge) and a PL lower profile `G` of the safe odd pool.
-/

namespace CatalanMeasure.GenD.Uniform.LedgerW

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Arithmetic
open scoped Topology BigOperators

noncomputable section

/-- A window `[a,b]` (in units of `N`) with a PL lower profile `K` for the nullity bound and a
PL lower profile `G` for the safe odd pool. -/
structure KapWindow where
  a : ℝ
  b : ℝ
  K : PL.Prof
  G : PL.Prof

/-- The saving profile `K + G - 2 n0` of a window, as a segment. -/
def KapWindow.seg (n0 : ℝ) (w : KapWindow) : PrimeGrowth.Seg :=
  ⟨w.a, w.b, fun x => w.K.eval x + w.G.eval x - 2 * n0⟩

/-- The exact area of the saving profile of a window. -/
def KapWindow.area (n0 : ℝ) (w : KapWindow) : ℝ :=
  w.K.area w.a w.b + w.G.area w.a w.b - 2 * n0 * (w.b - w.a)

theorem KapWindow.seg_continuousOn (n0 : ℝ) (w : KapWindow) :
    ContinuousOn (w.seg n0).F (Set.Icc w.a w.b) :=
  ((w.K.continuous.add w.G.continuous).sub continuous_const).continuousOn

theorem KapWindow.seg_area (n0 : ℝ) (w : KapWindow) (h : w.a ≤ w.b) :
    (w.seg n0).area = w.area n0 := by
  unfold PrimeGrowth.Seg.area KapWindow.seg KapWindow.area
  simp only
  rw [intervalIntegral.integral_sub (f := fun x => w.K.eval x + w.G.eval x)
    (g := fun _ => 2 * n0)
    ((w.K.continuous.add w.G.continuous).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_add (f := w.K.eval) (g := w.G.eval)
      (w.K.continuous.intervalIntegrable _ _) (w.G.continuous.intervalIntegrable _ _),
    w.K.integral_eval h, w.G.integral_eval h]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem totalArea_kapSegs (n0 : ℝ) (ws : List KapWindow) (h : ∀ w ∈ ws, w.a ≤ w.b) :
    PrimeGrowth.totalArea (ws.map (KapWindow.seg n0)) = (ws.map (KapWindow.area n0)).sum := by
  unfold PrimeGrowth.totalArea
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact KapWindow.seg_area n0 w (h w hw)

/-- The leading constant of the denominator growth. -/
def gD (P : Parameters) (f : PL.Prof) (κ0 : ℝ) (ws : List KapWindow) : ℝ :=
  TwoAdic.A2 (P.n0 : ℝ) (P.H 1 : ℝ) (P.b0 : ℝ) * Real.log 2 +
    (κ0 + f.area 1 (P.H 1 : ℝ)) - (ws.map (KapWindow.area (P.n0 : ℝ))).sum

end

end CatalanMeasure.GenD.Uniform.LedgerW
