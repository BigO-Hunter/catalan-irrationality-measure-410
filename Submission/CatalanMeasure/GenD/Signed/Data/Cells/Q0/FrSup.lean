module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB015
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB016
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB017
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB018
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB019
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB020
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB021
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB022
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB023
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB024
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB025
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB026
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB027
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB028
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB029
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB030
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB031
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB032
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB033
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB034
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB035
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB036
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB037
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB038
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB039
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB040
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB041
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB042
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB043
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrB044

@[expose] public section

/-! **FR, alpha = 0.0: the sup statement.**  `fieldTower q0frFq ... x <= q0frT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = 0.007076884853, K = 0.100977292001 (NOTES-TRIAL; kappa_old = 0.100977292001). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q0frGlue0 : ∀ x ∈ Icc ((q0frBd.getD 0 0 : ℚ) : ℝ) ((q0frBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frE000Bound x hx
theorem q0frGlue1 : ∀ x ∈ Icc ((q0frBd.getD 1 0 : ℚ) : ℝ) ((q0frBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB001Bound x hx
theorem q0frGlue2 : ∀ x ∈ Icc ((q0frBd.getD 2 0 : ℚ) : ℝ) ((q0frBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB002Bound x hx
theorem q0frGlue3 : ∀ x ∈ Icc ((q0frBd.getD 3 0 : ℚ) : ℝ) ((q0frBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB003Bound x hx
theorem q0frGlue4 : ∀ x ∈ Icc ((q0frBd.getD 4 0 : ℚ) : ℝ) ((q0frBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB004Bound x hx
theorem q0frGlue5 : ∀ x ∈ Icc ((q0frBd.getD 5 0 : ℚ) : ℝ) ((q0frBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB005Bound x hx
theorem q0frGlue6 : ∀ x ∈ Icc ((q0frBd.getD 6 0 : ℚ) : ℝ) ((q0frBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB006Bound x hx
theorem q0frGlue7 : ∀ x ∈ Icc ((q0frBd.getD 7 0 : ℚ) : ℝ) ((q0frBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB007Bound x hx
theorem q0frGlue8 : ∀ x ∈ Icc ((q0frBd.getD 8 0 : ℚ) : ℝ) ((q0frBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB008Bound x hx
theorem q0frGlue9 : ∀ x ∈ Icc ((q0frBd.getD 9 0 : ℚ) : ℝ) ((q0frBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB009Bound x hx
theorem q0frGlue10 : ∀ x ∈ Icc ((q0frBd.getD 10 0 : ℚ) : ℝ) ((q0frBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB010Bound x hx
theorem q0frGlue11 : ∀ x ∈ Icc ((q0frBd.getD 11 0 : ℚ) : ℝ) ((q0frBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB011Bound x hx
theorem q0frGlue12 : ∀ x ∈ Icc ((q0frBd.getD 12 0 : ℚ) : ℝ) ((q0frBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB012Bound x hx
theorem q0frGlue13 : ∀ x ∈ Icc ((q0frBd.getD 13 0 : ℚ) : ℝ) ((q0frBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB013Bound x hx
theorem q0frGlue14 : ∀ x ∈ Icc ((q0frBd.getD 14 0 : ℚ) : ℝ) ((q0frBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB014Bound x hx
theorem q0frGlue15 : ∀ x ∈ Icc ((q0frBd.getD 15 0 : ℚ) : ℝ) ((q0frBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB015Bound x hx
theorem q0frGlue16 : ∀ x ∈ Icc ((q0frBd.getD 16 0 : ℚ) : ℝ) ((q0frBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB016Bound x hx
theorem q0frGlue17 : ∀ x ∈ Icc ((q0frBd.getD 17 0 : ℚ) : ℝ) ((q0frBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB017Bound x hx
theorem q0frGlue18 : ∀ x ∈ Icc ((q0frBd.getD 18 0 : ℚ) : ℝ) ((q0frBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB018Bound x hx
theorem q0frGlue19 : ∀ x ∈ Icc ((q0frBd.getD 19 0 : ℚ) : ℝ) ((q0frBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB019Bound x hx
theorem q0frGlue20 : ∀ x ∈ Icc ((q0frBd.getD 20 0 : ℚ) : ℝ) ((q0frBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB020Bound x hx
theorem q0frGlue21 : ∀ x ∈ Icc ((q0frBd.getD 21 0 : ℚ) : ℝ) ((q0frBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB021Bound x hx
theorem q0frGlue22 : ∀ x ∈ Icc ((q0frBd.getD 22 0 : ℚ) : ℝ) ((q0frBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB022Bound x hx
theorem q0frGlue23 : ∀ x ∈ Icc ((q0frBd.getD 23 0 : ℚ) : ℝ) ((q0frBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB023Bound x hx
theorem q0frGlue24 : ∀ x ∈ Icc ((q0frBd.getD 24 0 : ℚ) : ℝ) ((q0frBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB024Bound x hx
theorem q0frGlue25 : ∀ x ∈ Icc ((q0frBd.getD 25 0 : ℚ) : ℝ) ((q0frBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB025Bound x hx
theorem q0frGlue26 : ∀ x ∈ Icc ((q0frBd.getD 26 0 : ℚ) : ℝ) ((q0frBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB026Bound x hx
theorem q0frGlue27 : ∀ x ∈ Icc ((q0frBd.getD 27 0 : ℚ) : ℝ) ((q0frBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB027Bound x hx
theorem q0frGlue28 : ∀ x ∈ Icc ((q0frBd.getD 28 0 : ℚ) : ℝ) ((q0frBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB028Bound x hx
theorem q0frGlue29 : ∀ x ∈ Icc ((q0frBd.getD 29 0 : ℚ) : ℝ) ((q0frBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB029Bound x hx
theorem q0frGlue30 : ∀ x ∈ Icc ((q0frBd.getD 30 0 : ℚ) : ℝ) ((q0frBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB030Bound x hx
theorem q0frGlue31 : ∀ x ∈ Icc ((q0frBd.getD 31 0 : ℚ) : ℝ) ((q0frBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB031Bound x hx
theorem q0frGlue32 : ∀ x ∈ Icc ((q0frBd.getD 32 0 : ℚ) : ℝ) ((q0frBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB032Bound x hx
theorem q0frGlue33 : ∀ x ∈ Icc ((q0frBd.getD 33 0 : ℚ) : ℝ) ((q0frBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB033Bound x hx
theorem q0frGlue34 : ∀ x ∈ Icc ((q0frBd.getD 34 0 : ℚ) : ℝ) ((q0frBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB034Bound x hx
theorem q0frGlue35 : ∀ x ∈ Icc ((q0frBd.getD 35 0 : ℚ) : ℝ) ((q0frBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB035Bound x hx
theorem q0frGlue36 : ∀ x ∈ Icc ((q0frBd.getD 36 0 : ℚ) : ℝ) ((q0frBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB036Bound x hx
theorem q0frGlue37 : ∀ x ∈ Icc ((q0frBd.getD 37 0 : ℚ) : ℝ) ((q0frBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB037Bound x hx
theorem q0frGlue38 : ∀ x ∈ Icc ((q0frBd.getD 38 0 : ℚ) : ℝ) ((q0frBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB038Bound x hx
theorem q0frGlue39 : ∀ x ∈ Icc ((q0frBd.getD 39 0 : ℚ) : ℝ) ((q0frBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB039Bound x hx
theorem q0frGlue40 : ∀ x ∈ Icc ((q0frBd.getD 40 0 : ℚ) : ℝ) ((q0frBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB040Bound x hx
theorem q0frGlue41 : ∀ x ∈ Icc ((q0frBd.getD 41 0 : ℚ) : ℝ) ((q0frBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB041Bound x hx
theorem q0frGlue42 : ∀ x ∈ Icc ((q0frBd.getD 42 0 : ℚ) : ℝ) ((q0frBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB042Bound x hx
theorem q0frGlue43 : ∀ x ∈ Icc ((q0frBd.getD 43 0 : ℚ) : ℝ) ((q0frBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB043Bound x hx
theorem q0frGlue44 : ∀ x ∈ Icc ((q0frBd.getD 44 0 : ℚ) : ℝ) ((q0frBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx _ _ => q0frB044Bound x hx
theorem q0frGlueAll : ∀ x ∈ Icc ((q0frBd.getD 0 0 : ℚ) : ℝ) ((q0frBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q0frBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0frBd.getD 45 0 : ℚ) : ℝ) → fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0frGlue0) q0frGlue1) q0frGlue2) q0frGlue3) q0frGlue4) q0frGlue5) q0frGlue6) q0frGlue7) q0frGlue8) q0frGlue9) q0frGlue10) q0frGlue11) q0frGlue12) q0frGlue13) q0frGlue14) q0frGlue15) q0frGlue16) q0frGlue17) q0frGlue18) q0frGlue19) q0frGlue20) q0frGlue21) q0frGlue22) q0frGlue23) q0frGlue24) q0frGlue25) q0frGlue26) q0frGlue27) q0frGlue28) q0frGlue29) q0frGlue30) q0frGlue31) q0frGlue32) q0frGlue33) q0frGlue34) q0frGlue35) q0frGlue36) q0frGlue37) q0frGlue38) q0frGlue39) q0frGlue40) q0frGlue41) q0frGlue42) q0frGlue43) q0frGlue44
/-- **Sup statement (FR, alpha = 0.0).** -/
theorem q0frSup : ∀ x ∈ Ioo ((q0frBd.getD 0 0 : ℚ) : ℝ) ((q0frBd.getD 45 0 : ℚ) : ℝ), fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  fun x hx => q0frGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
