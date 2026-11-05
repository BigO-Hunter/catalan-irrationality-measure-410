module

public import Submission.CatalanMeasure.GenD.Signed.Phase2Contract
public import Submission.CatalanMeasure.GenD.Analytic.DeltaChain
public import Submission.CatalanMeasure.GenD.Analytic.FirstGlue
public import Submission.CatalanMeasure.GenD.Analytic.Instances
public import Submission.CatalanMeasure.GenD.D58.Budget590
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# S1: the K590 trials in factor-free (End) form (lane D3)

The 532/540 trial certificates (`Cert590`, `FirstStrongTrial`) are NOT rebuilt.  The S1 contracts
`SecondTrialBoundsEnd` / `FirstTrialBoundsEnd` differ from the old ones only in the budget field
(no `a (1 - a) log 2`, cost `secondCost'` / `firstCost'`).  Hence:

* `FirstTrialBounds.toEnd` (output target free), `SecondTrialBounds.toEndAt` (output target and
  `α1` free; `SecondTrialBounds.toEnd` of `Phase2Contract` is the instance `α1 = 0`),
* `secondEnd_budget_K590`, `firstEnd_budget_K590`: the End budgets from
  `K590.second_budget'_log2` / `K590.first_budget'_log2`, for any trial whose caps are those of K590,
* `secondEnd` / `firstEnd`: the End trials from the old `SecondFieldCert` / `FirstTrialBounds` of
  Providers540 (`Bank540.second`, `Bank540.first`), with `rfl` for the cap equalities.

The final build assembles them with
`secondEnd Bank540.second rfl rfl` and `firstEnd Bank540.first rfl rfl rfl`
(see `TrialEnd590`, which imports the certificate data and is not built in this lane).
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.D58 CatalanMeasure.Parametric
open Filter Set

noncomputable section

/-- The factor-free first-population trial from an old one and an endpoint budget without
`a (1 - a) log 2`.  The output target `target'` is free: only the budget field mentions it. -/
def _root_.CatalanMeasure.GenD.Analytic.FirstTrialBounds.toEnd {P : Parameters} {target cost : ℝ} (D : FirstTrialBounds P target cost)
    {target' : ℝ} (cost' : ℝ)
    (hbud : ∀ a : ℝ, (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 + D.normCap +
      (1 - a) * D.fieldCap + a * (2 * D.lambda * ((P.g0 : ℝ) / P.n0)) ≤
        -target' + Real.log 2 / 2 + cost' * a) :
    FirstTrialBoundsEnd P target' cost' where
  p := D.p
  v := D.v
  lambda := D.lambda
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  lambda_nonneg := D.lambda_nonneg
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  budget := hbud

-- `SecondTrialBounds.toEndAt` is defined in `Phase2Contract` (with `toEnd` its instance `α1 = 0`).

theorem secondEnd_budget_K590 {normCap fieldCap : ℝ} (hN : normCap = K590.normCap)
    (hF : fieldCap = K590.fieldCap) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 + normCap +
      (1 - a) * fieldCap + (a - t) * K590.residualCap + t * nearCap ≤
        -K590.target + Real.log 2 / 2 + K590.secondCost' * a := by
  subst hN hF
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K590.second_budget'_log2 ha ht
  norm_num [c07, c26] at h
  linarith

theorem firstEnd_budget_K590 {normCap fieldCap lambda : ℝ} (hN : normCap = n1) (hF : fieldCap = F1)
    (hl : lambda = 168493357 / 100000000) (a : ℝ) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2) * Real.log 2 + normCap + (1 - a) * fieldCap +
      a * (2 * lambda * ((Odd.design.g0 : ℝ) / Odd.design.n0)) ≤
        -K590.target + Real.log 2 / 2 + K590.firstCost' * a := by
  subst hN hF hl
  rw [Instances.d58_gC0, Instances.d58_gC1, Instances.d58_g_ratio]
  have h := K590.first_budget'_log2 a
  have e : c07 - 1 / 2 = 6 / 29 := by norm_num [c07]
  have e2 : c26 - 1 = 47 / 29 := by norm_num [c26]
  have e3 : Lm = 168493357 / 100000000 * (5 / 29) := by norm_num [Lm]
  rw [e, e2, e3] at h
  linarith only [h]

/-- The S1 second trial from the old certificate (`Bank540.second`): cost `secondCost'`. -/
def secondEnd (S : SecondFieldCert Odd.design K590.target K590.residualCap nearCap K590.secondCost
      (fun x => (401 / 2500 : ℝ) ≤ |x|))
    (hN : S.normCap = K590.normCap) (hF : S.fieldCap = K590.fieldCap) :
    SecondTrialBoundsEnd Odd.design 0 K590.target K590.residualCap nearCap K590.secondCost'
      (fun x => (401 / 2500 : ℝ) ≤ |x|) :=
  CatalanMeasure.Signed.SecondTrialBounds.toEnd (S.bounds Odd.design_admissible) K590.secondCost'
    (fun ha ht => secondEnd_budget_K590 hN hF ha ht)

/-- The S1 first trial from the old certificate (`Bank540.first`): cost `firstCost'`. -/
def firstEnd (F : FirstTrialBounds Odd.design K590.target K590.firstCost)
    (hN : F.normCap = n1) (hF : F.fieldCap = F1) (hl : F.lambda = 168493357 / 100000000) :
    FirstTrialBoundsEnd Odd.design K590.target K590.firstCost' :=
  F.toEnd K590.firstCost' (fun a => firstEnd_budget_K590 hN hF hl a)

/-! ### Theorem A: the End trials at `target0 = K590.target + A / 58²` (`A = 8.29824`)

First case: every `a`, cost `K590.secondCost'` (the cost of `rhoEnd`).  Second case: marked
fraction `a ≥ α₁ = 1/16`, cost `K590.secondCost'`, from `K590.secondCost'_ge_alpha1`. -/

theorem secondEnd_budget_K590_target0 {normCap fieldCap : ℝ} (hN : normCap = K590.normCap)
    (hF : fieldCap = K590.fieldCap) {a t : ℝ} (ha : 1 / 16 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 + normCap +
      (1 - a) * fieldCap + (a - t) * K590.residualCap + t * nearCap ≤
        -K590.target0 + Real.log 2 / 2 + K590.secondCost' * a := by
  subst hN hF
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K590.second_budget'_log2_target0 ha ht
  norm_num [c07, c26] at h
  linarith

theorem firstEnd_budget_K590_target0 {normCap fieldCap lambda : ℝ} (hN : normCap = n1)
    (hF : fieldCap = F1) (hl : lambda = 168493357 / 100000000) (a : ℝ) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2) * Real.log 2 + normCap + (1 - a) * fieldCap +
      a * (2 * lambda * ((Odd.design.g0 : ℝ) / Odd.design.n0)) ≤
        -K590.target0 + Real.log 2 / 2 + K590.secondCost' * a := by
  subst hN hF hl
  rw [Instances.d58_gC0, Instances.d58_gC1, Instances.d58_g_ratio]
  have h := K590.first_budget'_log2_target0 a
  have e : c07 - 1 / 2 = 6 / 29 := by norm_num [c07]
  have e2 : c26 - 1 = 47 / 29 := by norm_num [c26]
  have e3 : Lm = 168493357 / 100000000 * (5 / 29) := by norm_num [Lm]
  rw [e, e2, e3] at h
  linarith only [h]

/-- The Theorem A second trial at `target0`, `a ≥ 1/16`: from the old certificate. -/
def secondEnd0 (S : SecondFieldCert Odd.design K590.target K590.residualCap nearCap K590.secondCost
      (fun x => (401 / 2500 : ℝ) ≤ |x|))
    (hN : S.normCap = K590.normCap) (hF : S.fieldCap = K590.fieldCap) :
    SecondTrialBoundsEnd Odd.design (1 / 16) K590.target0 K590.residualCap nearCap K590.secondCost'
      (fun x => (401 / 2500 : ℝ) ≤ |x|) :=
  (S.bounds Odd.design_admissible).toEndAt K590.secondCost'
    (fun ha _ ht => secondEnd_budget_K590_target0 hN hF ha ht)

/-- The Theorem A first trial at `target0` (cost `secondCost'`, see `first_budget'_log2_target0`). -/
def firstEnd0 (F : FirstTrialBounds Odd.design K590.target K590.firstCost)
    (hN : F.normCap = n1) (hF : F.fieldCap = F1) (hl : F.lambda = 168493357 / 100000000) :
    FirstTrialBoundsEnd Odd.design K590.target0 K590.secondCost' :=
  F.toEnd K590.secondCost' (fun a => firstEnd_budget_K590_target0 hN hF hl a)

/-- `FreeFirstBound` at `target0`, in the form `weighted_atom_point_binom_of_signed` consumes
(`c₁ = n0 * secondCost'`). -/
theorem freeFirst0 (F : FirstTrialBounds Odd.design K590.target K590.firstCost)
    (hN : F.normCap = n1) (hF : F.fieldCap = F1) (hl : F.lambda = 168493357 / 100000000) :
    FreeFirstBound Odd.design K590.target0 ((Odd.design.n0 : ℝ) * K590.secondCost') :=
  freeFirstBound_of_end Odd.design_admissible (firstEnd0 F hN hF hl)

/-- `FreeLargeBound` at `target0` and `α₁ = 1/16` (`c₃ = n0 * secondCost'`). -/
theorem freeLarge0 (S : SecondFieldCert Odd.design K590.target K590.residualCap nearCap
      K590.secondCost (fun x => (401 / 2500 : ℝ) ≤ |x|))
    (hN : S.normCap = K590.normCap) (hF : S.fieldCap = K590.fieldCap) :
    FreeLargeBound Odd.design (fun x => (401 / 2500 : ℝ) ≤ |x|) K590.target0
      ((Odd.design.n0 : ℝ) * K590.secondCost') (1 / 16) :=
  freeLargeBound_of_end Odd.design_admissible (secondEnd0 S hN hF)

end

end CatalanMeasure.GenD.Signed.Data.S1
