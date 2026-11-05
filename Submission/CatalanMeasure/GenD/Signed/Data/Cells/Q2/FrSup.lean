module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB015
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB016
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB017
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB018
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB019
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB020
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB021
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB022
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB023
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB024
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB025
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB026
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB027
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB028
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB029
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB030
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB031
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB032
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB033
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB034
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB035
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB036
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB037
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB038
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB039
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB040
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB041
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB042
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB043
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.FrB044

@[expose] public section

/-! **FR, alpha = 0.0625: the sup statement.**  `fieldTower q2frFq ... x <= q2frT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = 0.007871172158, K = 0.082794672001 (NOTES-TRIAL; kappa_old = 0.082794672001). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q2frGlue0 : ∀ x ∈ Icc ((q2frBd.getD 0 0 : ℚ) : ℝ) ((q2frBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frE000Bound x hx
theorem q2frGlue1 : ∀ x ∈ Icc ((q2frBd.getD 1 0 : ℚ) : ℝ) ((q2frBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB001Bound x hx
theorem q2frGlue2 : ∀ x ∈ Icc ((q2frBd.getD 2 0 : ℚ) : ℝ) ((q2frBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB002Bound x hx
theorem q2frGlue3 : ∀ x ∈ Icc ((q2frBd.getD 3 0 : ℚ) : ℝ) ((q2frBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB003Bound x hx
theorem q2frGlue4 : ∀ x ∈ Icc ((q2frBd.getD 4 0 : ℚ) : ℝ) ((q2frBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB004Bound x hx
theorem q2frGlue5 : ∀ x ∈ Icc ((q2frBd.getD 5 0 : ℚ) : ℝ) ((q2frBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB005Bound x hx
theorem q2frGlue6 : ∀ x ∈ Icc ((q2frBd.getD 6 0 : ℚ) : ℝ) ((q2frBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB006Bound x hx
theorem q2frGlue7 : ∀ x ∈ Icc ((q2frBd.getD 7 0 : ℚ) : ℝ) ((q2frBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB007Bound x hx
theorem q2frGlue8 : ∀ x ∈ Icc ((q2frBd.getD 8 0 : ℚ) : ℝ) ((q2frBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB008Bound x hx
theorem q2frGlue9 : ∀ x ∈ Icc ((q2frBd.getD 9 0 : ℚ) : ℝ) ((q2frBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB009Bound x hx
theorem q2frGlue10 : ∀ x ∈ Icc ((q2frBd.getD 10 0 : ℚ) : ℝ) ((q2frBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB010Bound x hx
theorem q2frGlue11 : ∀ x ∈ Icc ((q2frBd.getD 11 0 : ℚ) : ℝ) ((q2frBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB011Bound x hx
theorem q2frGlue12 : ∀ x ∈ Icc ((q2frBd.getD 12 0 : ℚ) : ℝ) ((q2frBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB012Bound x hx
theorem q2frGlue13 : ∀ x ∈ Icc ((q2frBd.getD 13 0 : ℚ) : ℝ) ((q2frBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB013Bound x hx
theorem q2frGlue14 : ∀ x ∈ Icc ((q2frBd.getD 14 0 : ℚ) : ℝ) ((q2frBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB014Bound x hx
theorem q2frGlue15 : ∀ x ∈ Icc ((q2frBd.getD 15 0 : ℚ) : ℝ) ((q2frBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB015Bound x hx
theorem q2frGlue16 : ∀ x ∈ Icc ((q2frBd.getD 16 0 : ℚ) : ℝ) ((q2frBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB016Bound x hx
theorem q2frGlue17 : ∀ x ∈ Icc ((q2frBd.getD 17 0 : ℚ) : ℝ) ((q2frBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB017Bound x hx
theorem q2frGlue18 : ∀ x ∈ Icc ((q2frBd.getD 18 0 : ℚ) : ℝ) ((q2frBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB018Bound x hx
theorem q2frGlue19 : ∀ x ∈ Icc ((q2frBd.getD 19 0 : ℚ) : ℝ) ((q2frBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB019Bound x hx
theorem q2frGlue20 : ∀ x ∈ Icc ((q2frBd.getD 20 0 : ℚ) : ℝ) ((q2frBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB020Bound x hx
theorem q2frGlue21 : ∀ x ∈ Icc ((q2frBd.getD 21 0 : ℚ) : ℝ) ((q2frBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB021Bound x hx
theorem q2frGlue22 : ∀ x ∈ Icc ((q2frBd.getD 22 0 : ℚ) : ℝ) ((q2frBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB022Bound x hx
theorem q2frGlue23 : ∀ x ∈ Icc ((q2frBd.getD 23 0 : ℚ) : ℝ) ((q2frBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB023Bound x hx
theorem q2frGlue24 : ∀ x ∈ Icc ((q2frBd.getD 24 0 : ℚ) : ℝ) ((q2frBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB024Bound x hx
theorem q2frGlue25 : ∀ x ∈ Icc ((q2frBd.getD 25 0 : ℚ) : ℝ) ((q2frBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB025Bound x hx
theorem q2frGlue26 : ∀ x ∈ Icc ((q2frBd.getD 26 0 : ℚ) : ℝ) ((q2frBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB026Bound x hx
theorem q2frGlue27 : ∀ x ∈ Icc ((q2frBd.getD 27 0 : ℚ) : ℝ) ((q2frBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB027Bound x hx
theorem q2frGlue28 : ∀ x ∈ Icc ((q2frBd.getD 28 0 : ℚ) : ℝ) ((q2frBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB028Bound x hx
theorem q2frGlue29 : ∀ x ∈ Icc ((q2frBd.getD 29 0 : ℚ) : ℝ) ((q2frBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB029Bound x hx
theorem q2frGlue30 : ∀ x ∈ Icc ((q2frBd.getD 30 0 : ℚ) : ℝ) ((q2frBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB030Bound x hx
theorem q2frGlue31 : ∀ x ∈ Icc ((q2frBd.getD 31 0 : ℚ) : ℝ) ((q2frBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB031Bound x hx
theorem q2frGlue32 : ∀ x ∈ Icc ((q2frBd.getD 32 0 : ℚ) : ℝ) ((q2frBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB032Bound x hx
theorem q2frGlue33 : ∀ x ∈ Icc ((q2frBd.getD 33 0 : ℚ) : ℝ) ((q2frBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB033Bound x hx
theorem q2frGlue34 : ∀ x ∈ Icc ((q2frBd.getD 34 0 : ℚ) : ℝ) ((q2frBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB034Bound x hx
theorem q2frGlue35 : ∀ x ∈ Icc ((q2frBd.getD 35 0 : ℚ) : ℝ) ((q2frBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB035Bound x hx
theorem q2frGlue36 : ∀ x ∈ Icc ((q2frBd.getD 36 0 : ℚ) : ℝ) ((q2frBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB036Bound x hx
theorem q2frGlue37 : ∀ x ∈ Icc ((q2frBd.getD 37 0 : ℚ) : ℝ) ((q2frBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB037Bound x hx
theorem q2frGlue38 : ∀ x ∈ Icc ((q2frBd.getD 38 0 : ℚ) : ℝ) ((q2frBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB038Bound x hx
theorem q2frGlue39 : ∀ x ∈ Icc ((q2frBd.getD 39 0 : ℚ) : ℝ) ((q2frBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB039Bound x hx
theorem q2frGlue40 : ∀ x ∈ Icc ((q2frBd.getD 40 0 : ℚ) : ℝ) ((q2frBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB040Bound x hx
theorem q2frGlue41 : ∀ x ∈ Icc ((q2frBd.getD 41 0 : ℚ) : ℝ) ((q2frBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB041Bound x hx
theorem q2frGlue42 : ∀ x ∈ Icc ((q2frBd.getD 42 0 : ℚ) : ℝ) ((q2frBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB042Bound x hx
theorem q2frGlue43 : ∀ x ∈ Icc ((q2frBd.getD 43 0 : ℚ) : ℝ) ((q2frBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB043Bound x hx
theorem q2frGlue44 : ∀ x ∈ Icc ((q2frBd.getD 44 0 : ℚ) : ℝ) ((q2frBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx _ _ => q2frB044Bound x hx
theorem q2frGlueAll : ∀ x ∈ Icc ((q2frBd.getD 0 0 : ℚ) : ℝ) ((q2frBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q2frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2frGlue0) q2frGlue1) q2frGlue2) q2frGlue3) q2frGlue4) q2frGlue5) q2frGlue6) q2frGlue7) q2frGlue8) q2frGlue9) q2frGlue10) q2frGlue11) q2frGlue12) q2frGlue13) q2frGlue14) q2frGlue15) q2frGlue16) q2frGlue17) q2frGlue18) q2frGlue19) q2frGlue20) q2frGlue21) q2frGlue22) q2frGlue23) q2frGlue24) q2frGlue25) q2frGlue26) q2frGlue27) q2frGlue28) q2frGlue29) q2frGlue30) q2frGlue31) q2frGlue32) q2frGlue33) q2frGlue34) q2frGlue35) q2frGlue36) q2frGlue37) q2frGlue38) q2frGlue39) q2frGlue40) q2frGlue41) q2frGlue42) q2frGlue43) q2frGlue44
/-- **Sup statement (FR, alpha = 0.0625).** -/
theorem q2frSup : ∀ x ∈ Ioo ((q2frBd.getD 0 0 : ℚ) : ℝ) ((q2frBd.getD 45 0 : ℚ) : ℝ), fieldTower q2frFq (poleF q2frFq.poles) 0 x ≤ (q2frT : ℝ) :=
  fun x hx => q2frGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
