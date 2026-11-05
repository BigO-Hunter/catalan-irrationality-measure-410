module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB015
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB016
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB017
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB018
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB019
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB020
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB021
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB022
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB023
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB024
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB025
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB026
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB027
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB028
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB029
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB030
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB031
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB032
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB033
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB034
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB035
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB036
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB037
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB038
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB039
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB040
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB041
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB042
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB043
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.FrB044

@[expose] public section

/-! **FR, alpha = 0.005: the sup statement.**  `fieldTower q1frFq ... x <= q1frT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = 0.007130564889, K = 0.084770292001 (NOTES-TRIAL; kappa_old = 0.084770292001). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q1frGlue0 : ∀ x ∈ Icc ((q1frBd.getD 0 0 : ℚ) : ℝ) ((q1frBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frE000Bound x hx
theorem q1frGlue1 : ∀ x ∈ Icc ((q1frBd.getD 1 0 : ℚ) : ℝ) ((q1frBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB001Bound x hx
theorem q1frGlue2 : ∀ x ∈ Icc ((q1frBd.getD 2 0 : ℚ) : ℝ) ((q1frBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB002Bound x hx
theorem q1frGlue3 : ∀ x ∈ Icc ((q1frBd.getD 3 0 : ℚ) : ℝ) ((q1frBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB003Bound x hx
theorem q1frGlue4 : ∀ x ∈ Icc ((q1frBd.getD 4 0 : ℚ) : ℝ) ((q1frBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB004Bound x hx
theorem q1frGlue5 : ∀ x ∈ Icc ((q1frBd.getD 5 0 : ℚ) : ℝ) ((q1frBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB005Bound x hx
theorem q1frGlue6 : ∀ x ∈ Icc ((q1frBd.getD 6 0 : ℚ) : ℝ) ((q1frBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB006Bound x hx
theorem q1frGlue7 : ∀ x ∈ Icc ((q1frBd.getD 7 0 : ℚ) : ℝ) ((q1frBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB007Bound x hx
theorem q1frGlue8 : ∀ x ∈ Icc ((q1frBd.getD 8 0 : ℚ) : ℝ) ((q1frBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB008Bound x hx
theorem q1frGlue9 : ∀ x ∈ Icc ((q1frBd.getD 9 0 : ℚ) : ℝ) ((q1frBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB009Bound x hx
theorem q1frGlue10 : ∀ x ∈ Icc ((q1frBd.getD 10 0 : ℚ) : ℝ) ((q1frBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB010Bound x hx
theorem q1frGlue11 : ∀ x ∈ Icc ((q1frBd.getD 11 0 : ℚ) : ℝ) ((q1frBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB011Bound x hx
theorem q1frGlue12 : ∀ x ∈ Icc ((q1frBd.getD 12 0 : ℚ) : ℝ) ((q1frBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB012Bound x hx
theorem q1frGlue13 : ∀ x ∈ Icc ((q1frBd.getD 13 0 : ℚ) : ℝ) ((q1frBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB013Bound x hx
theorem q1frGlue14 : ∀ x ∈ Icc ((q1frBd.getD 14 0 : ℚ) : ℝ) ((q1frBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB014Bound x hx
theorem q1frGlue15 : ∀ x ∈ Icc ((q1frBd.getD 15 0 : ℚ) : ℝ) ((q1frBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB015Bound x hx
theorem q1frGlue16 : ∀ x ∈ Icc ((q1frBd.getD 16 0 : ℚ) : ℝ) ((q1frBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB016Bound x hx
theorem q1frGlue17 : ∀ x ∈ Icc ((q1frBd.getD 17 0 : ℚ) : ℝ) ((q1frBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB017Bound x hx
theorem q1frGlue18 : ∀ x ∈ Icc ((q1frBd.getD 18 0 : ℚ) : ℝ) ((q1frBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB018Bound x hx
theorem q1frGlue19 : ∀ x ∈ Icc ((q1frBd.getD 19 0 : ℚ) : ℝ) ((q1frBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB019Bound x hx
theorem q1frGlue20 : ∀ x ∈ Icc ((q1frBd.getD 20 0 : ℚ) : ℝ) ((q1frBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB020Bound x hx
theorem q1frGlue21 : ∀ x ∈ Icc ((q1frBd.getD 21 0 : ℚ) : ℝ) ((q1frBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB021Bound x hx
theorem q1frGlue22 : ∀ x ∈ Icc ((q1frBd.getD 22 0 : ℚ) : ℝ) ((q1frBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB022Bound x hx
theorem q1frGlue23 : ∀ x ∈ Icc ((q1frBd.getD 23 0 : ℚ) : ℝ) ((q1frBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB023Bound x hx
theorem q1frGlue24 : ∀ x ∈ Icc ((q1frBd.getD 24 0 : ℚ) : ℝ) ((q1frBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB024Bound x hx
theorem q1frGlue25 : ∀ x ∈ Icc ((q1frBd.getD 25 0 : ℚ) : ℝ) ((q1frBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB025Bound x hx
theorem q1frGlue26 : ∀ x ∈ Icc ((q1frBd.getD 26 0 : ℚ) : ℝ) ((q1frBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB026Bound x hx
theorem q1frGlue27 : ∀ x ∈ Icc ((q1frBd.getD 27 0 : ℚ) : ℝ) ((q1frBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB027Bound x hx
theorem q1frGlue28 : ∀ x ∈ Icc ((q1frBd.getD 28 0 : ℚ) : ℝ) ((q1frBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB028Bound x hx
theorem q1frGlue29 : ∀ x ∈ Icc ((q1frBd.getD 29 0 : ℚ) : ℝ) ((q1frBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB029Bound x hx
theorem q1frGlue30 : ∀ x ∈ Icc ((q1frBd.getD 30 0 : ℚ) : ℝ) ((q1frBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB030Bound x hx
theorem q1frGlue31 : ∀ x ∈ Icc ((q1frBd.getD 31 0 : ℚ) : ℝ) ((q1frBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB031Bound x hx
theorem q1frGlue32 : ∀ x ∈ Icc ((q1frBd.getD 32 0 : ℚ) : ℝ) ((q1frBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB032Bound x hx
theorem q1frGlue33 : ∀ x ∈ Icc ((q1frBd.getD 33 0 : ℚ) : ℝ) ((q1frBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB033Bound x hx
theorem q1frGlue34 : ∀ x ∈ Icc ((q1frBd.getD 34 0 : ℚ) : ℝ) ((q1frBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB034Bound x hx
theorem q1frGlue35 : ∀ x ∈ Icc ((q1frBd.getD 35 0 : ℚ) : ℝ) ((q1frBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB035Bound x hx
theorem q1frGlue36 : ∀ x ∈ Icc ((q1frBd.getD 36 0 : ℚ) : ℝ) ((q1frBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB036Bound x hx
theorem q1frGlue37 : ∀ x ∈ Icc ((q1frBd.getD 37 0 : ℚ) : ℝ) ((q1frBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB037Bound x hx
theorem q1frGlue38 : ∀ x ∈ Icc ((q1frBd.getD 38 0 : ℚ) : ℝ) ((q1frBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB038Bound x hx
theorem q1frGlue39 : ∀ x ∈ Icc ((q1frBd.getD 39 0 : ℚ) : ℝ) ((q1frBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB039Bound x hx
theorem q1frGlue40 : ∀ x ∈ Icc ((q1frBd.getD 40 0 : ℚ) : ℝ) ((q1frBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB040Bound x hx
theorem q1frGlue41 : ∀ x ∈ Icc ((q1frBd.getD 41 0 : ℚ) : ℝ) ((q1frBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB041Bound x hx
theorem q1frGlue42 : ∀ x ∈ Icc ((q1frBd.getD 42 0 : ℚ) : ℝ) ((q1frBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB042Bound x hx
theorem q1frGlue43 : ∀ x ∈ Icc ((q1frBd.getD 43 0 : ℚ) : ℝ) ((q1frBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB043Bound x hx
theorem q1frGlue44 : ∀ x ∈ Icc ((q1frBd.getD 44 0 : ℚ) : ℝ) ((q1frBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx _ _ => q1frB044Bound x hx
theorem q1frGlueAll : ∀ x ∈ Icc ((q1frBd.getD 0 0 : ℚ) : ℝ) ((q1frBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q1frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1frGlue0) q1frGlue1) q1frGlue2) q1frGlue3) q1frGlue4) q1frGlue5) q1frGlue6) q1frGlue7) q1frGlue8) q1frGlue9) q1frGlue10) q1frGlue11) q1frGlue12) q1frGlue13) q1frGlue14) q1frGlue15) q1frGlue16) q1frGlue17) q1frGlue18) q1frGlue19) q1frGlue20) q1frGlue21) q1frGlue22) q1frGlue23) q1frGlue24) q1frGlue25) q1frGlue26) q1frGlue27) q1frGlue28) q1frGlue29) q1frGlue30) q1frGlue31) q1frGlue32) q1frGlue33) q1frGlue34) q1frGlue35) q1frGlue36) q1frGlue37) q1frGlue38) q1frGlue39) q1frGlue40) q1frGlue41) q1frGlue42) q1frGlue43) q1frGlue44
/-- **Sup statement (FR, alpha = 0.005).** -/
theorem q1frSup : ∀ x ∈ Ioo ((q1frBd.getD 0 0 : ℚ) : ℝ) ((q1frBd.getD 45 0 : ℚ) : ℝ), fieldTower q1frFq (poleF q1frFq.poles) 0 x ≤ (q1frT : ℝ) :=
  fun x hx => q1frGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
