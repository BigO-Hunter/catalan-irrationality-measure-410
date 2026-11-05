module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SmE054

@[expose] public section

/-! **SM, alpha = 0.005: the sup statement.**  `fieldTower q1smFq ... x <= q1smT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -0.454552532174, K = -9.289570897999 (NOTES-TRIAL; kappa_old = -9.289570897999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q1smGlue0 : ∀ x ∈ Icc ((q1smBd.getD 0 0 : ℚ) : ℝ) ((q1smBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smE000Full x hx
theorem q1smGlue1 : ∀ x ∈ Icc ((q1smBd.getD 1 0 : ℚ) : ℝ) ((q1smBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB001Bound x hx
theorem q1smGlue2 : ∀ x ∈ Icc ((q1smBd.getD 2 0 : ℚ) : ℝ) ((q1smBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB002Bound x hx
theorem q1smGlue3 : ∀ x ∈ Icc ((q1smBd.getD 3 0 : ℚ) : ℝ) ((q1smBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB003Bound x hx
theorem q1smGlue4 : ∀ x ∈ Icc ((q1smBd.getD 4 0 : ℚ) : ℝ) ((q1smBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB004Bound x hx
theorem q1smGlue5 : ∀ x ∈ Icc ((q1smBd.getD 5 0 : ℚ) : ℝ) ((q1smBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB005Bound x hx
theorem q1smGlue6 : ∀ x ∈ Icc ((q1smBd.getD 6 0 : ℚ) : ℝ) ((q1smBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB006Bound x hx
theorem q1smGlue7 : ∀ x ∈ Icc ((q1smBd.getD 7 0 : ℚ) : ℝ) ((q1smBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB007Bound x hx
theorem q1smGlue8 : ∀ x ∈ Icc ((q1smBd.getD 8 0 : ℚ) : ℝ) ((q1smBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB008Bound x hx
theorem q1smGlue9 : ∀ x ∈ Icc ((q1smBd.getD 9 0 : ℚ) : ℝ) ((q1smBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB009Bound x hx
theorem q1smGlue10 : ∀ x ∈ Icc ((q1smBd.getD 10 0 : ℚ) : ℝ) ((q1smBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB010Bound x hx
theorem q1smGlue11 : ∀ x ∈ Icc ((q1smBd.getD 11 0 : ℚ) : ℝ) ((q1smBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB011Bound x hx
theorem q1smGlue12 : ∀ x ∈ Icc ((q1smBd.getD 12 0 : ℚ) : ℝ) ((q1smBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB012Bound x hx
theorem q1smGlue13 : ∀ x ∈ Icc ((q1smBd.getD 13 0 : ℚ) : ℝ) ((q1smBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB013Bound x hx
theorem q1smGlue14 : ∀ x ∈ Icc ((q1smBd.getD 14 0 : ℚ) : ℝ) ((q1smBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB014Bound x hx
theorem q1smGlue15 : ∀ x ∈ Icc ((q1smBd.getD 15 0 : ℚ) : ℝ) ((q1smBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB015Bound x hx
theorem q1smGlue16 : ∀ x ∈ Icc ((q1smBd.getD 16 0 : ℚ) : ℝ) ((q1smBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB016Bound x hx
theorem q1smGlue17 : ∀ x ∈ Icc ((q1smBd.getD 17 0 : ℚ) : ℝ) ((q1smBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB017Bound x hx
theorem q1smGlue18 : ∀ x ∈ Icc ((q1smBd.getD 18 0 : ℚ) : ℝ) ((q1smBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB018Bound x hx
theorem q1smGlue19 : ∀ x ∈ Icc ((q1smBd.getD 19 0 : ℚ) : ℝ) ((q1smBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB019Bound x hx
theorem q1smGlue20 : ∀ x ∈ Icc ((q1smBd.getD 20 0 : ℚ) : ℝ) ((q1smBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB020Bound x hx
theorem q1smGlue21 : ∀ x ∈ Icc ((q1smBd.getD 21 0 : ℚ) : ℝ) ((q1smBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB021Bound x hx
theorem q1smGlue22 : ∀ x ∈ Icc ((q1smBd.getD 22 0 : ℚ) : ℝ) ((q1smBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB022Bound x hx
theorem q1smGlue23 : ∀ x ∈ Icc ((q1smBd.getD 23 0 : ℚ) : ℝ) ((q1smBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB023Bound x hx
theorem q1smGlue24 : ∀ x ∈ Icc ((q1smBd.getD 24 0 : ℚ) : ℝ) ((q1smBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB024Bound x hx
theorem q1smGlue25 : ∀ x ∈ Icc ((q1smBd.getD 25 0 : ℚ) : ℝ) ((q1smBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB025Bound x hx
theorem q1smGlue26 : ∀ x ∈ Icc ((q1smBd.getD 26 0 : ℚ) : ℝ) ((q1smBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB026Bound x hx
theorem q1smGlue27 : ∀ x ∈ Icc ((q1smBd.getD 27 0 : ℚ) : ℝ) ((q1smBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB027Bound x hx
theorem q1smGlue28 : ∀ x ∈ Icc ((q1smBd.getD 28 0 : ℚ) : ℝ) ((q1smBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB028Bound x hx
theorem q1smGlue29 : ∀ x ∈ Icc ((q1smBd.getD 29 0 : ℚ) : ℝ) ((q1smBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB029Bound x hx
theorem q1smGlue30 : ∀ x ∈ Icc ((q1smBd.getD 30 0 : ℚ) : ℝ) ((q1smBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB030Bound x hx
theorem q1smGlue31 : ∀ x ∈ Icc ((q1smBd.getD 31 0 : ℚ) : ℝ) ((q1smBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB031Bound x hx
theorem q1smGlue32 : ∀ x ∈ Icc ((q1smBd.getD 32 0 : ℚ) : ℝ) ((q1smBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB032Bound x hx
theorem q1smGlue33 : ∀ x ∈ Icc ((q1smBd.getD 33 0 : ℚ) : ℝ) ((q1smBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB033Bound x hx
theorem q1smGlue34 : ∀ x ∈ Icc ((q1smBd.getD 34 0 : ℚ) : ℝ) ((q1smBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB034Bound x hx
theorem q1smGlue35 : ∀ x ∈ Icc ((q1smBd.getD 35 0 : ℚ) : ℝ) ((q1smBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB035Bound x hx
theorem q1smGlue36 : ∀ x ∈ Icc ((q1smBd.getD 36 0 : ℚ) : ℝ) ((q1smBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB036Bound x hx
theorem q1smGlue37 : ∀ x ∈ Icc ((q1smBd.getD 37 0 : ℚ) : ℝ) ((q1smBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB037Bound x hx
theorem q1smGlue38 : ∀ x ∈ Icc ((q1smBd.getD 38 0 : ℚ) : ℝ) ((q1smBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB038Bound x hx
theorem q1smGlue39 : ∀ x ∈ Icc ((q1smBd.getD 39 0 : ℚ) : ℝ) ((q1smBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB039Bound x hx
theorem q1smGlue40 : ∀ x ∈ Icc ((q1smBd.getD 40 0 : ℚ) : ℝ) ((q1smBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB040Bound x hx
theorem q1smGlue41 : ∀ x ∈ Icc ((q1smBd.getD 41 0 : ℚ) : ℝ) ((q1smBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB041Bound x hx
theorem q1smGlue42 : ∀ x ∈ Icc ((q1smBd.getD 42 0 : ℚ) : ℝ) ((q1smBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB042Bound x hx
theorem q1smGlue43 : ∀ x ∈ Icc ((q1smBd.getD 43 0 : ℚ) : ℝ) ((q1smBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB043Bound x hx
theorem q1smGlue44 : ∀ x ∈ Icc ((q1smBd.getD 44 0 : ℚ) : ℝ) ((q1smBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB044Bound x hx
theorem q1smGlue45 : ∀ x ∈ Icc ((q1smBd.getD 45 0 : ℚ) : ℝ) ((q1smBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB045Bound x hx
theorem q1smGlue46 : ∀ x ∈ Icc ((q1smBd.getD 46 0 : ℚ) : ℝ) ((q1smBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB046Bound x hx
theorem q1smGlue47 : ∀ x ∈ Icc ((q1smBd.getD 47 0 : ℚ) : ℝ) ((q1smBd.getD 48 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB047Bound x hx
theorem q1smGlue48 : ∀ x ∈ Icc ((q1smBd.getD 48 0 : ℚ) : ℝ) ((q1smBd.getD 49 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB048Bound x hx
theorem q1smGlue49 : ∀ x ∈ Icc ((q1smBd.getD 49 0 : ℚ) : ℝ) ((q1smBd.getD 50 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB049Bound x hx
theorem q1smGlue50 : ∀ x ∈ Icc ((q1smBd.getD 50 0 : ℚ) : ℝ) ((q1smBd.getD 51 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB050Bound x hx
theorem q1smGlue51 : ∀ x ∈ Icc ((q1smBd.getD 51 0 : ℚ) : ℝ) ((q1smBd.getD 52 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB051Bound x hx
theorem q1smGlue52 : ∀ x ∈ Icc ((q1smBd.getD 52 0 : ℚ) : ℝ) ((q1smBd.getD 53 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB052Bound x hx
theorem q1smGlue53 : ∀ x ∈ Icc ((q1smBd.getD 53 0 : ℚ) : ℝ) ((q1smBd.getD 54 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smB053Bound x hx
theorem q1smGlue54 : ∀ x ∈ Icc ((q1smBd.getD 54 0 : ℚ) : ℝ) ((q1smBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx _ _ => q1smE054Full x hx
theorem q1smGlueAll : ∀ x ∈ Icc ((q1smBd.getD 0 0 : ℚ) : ℝ) ((q1smBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q1smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1smBd.getD 55 0 : ℚ) : ℝ) → fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1smGlue0) q1smGlue1) q1smGlue2) q1smGlue3) q1smGlue4) q1smGlue5) q1smGlue6) q1smGlue7) q1smGlue8) q1smGlue9) q1smGlue10) q1smGlue11) q1smGlue12) q1smGlue13) q1smGlue14) q1smGlue15) q1smGlue16) q1smGlue17) q1smGlue18) q1smGlue19) q1smGlue20) q1smGlue21) q1smGlue22) q1smGlue23) q1smGlue24) q1smGlue25) q1smGlue26) q1smGlue27) q1smGlue28) q1smGlue29) q1smGlue30) q1smGlue31) q1smGlue32) q1smGlue33) q1smGlue34) q1smGlue35) q1smGlue36) q1smGlue37) q1smGlue38) q1smGlue39) q1smGlue40) q1smGlue41) q1smGlue42) q1smGlue43) q1smGlue44) q1smGlue45) q1smGlue46) q1smGlue47) q1smGlue48) q1smGlue49) q1smGlue50) q1smGlue51) q1smGlue52) q1smGlue53) q1smGlue54
/-- **Sup statement (SM, alpha = 0.005).** -/
theorem q1smSup : ∀ x ∈ Ioo ((q1smBd.getD 0 0 : ℚ) : ℝ) ((q1smBd.getD 55 0 : ℚ) : ℝ), fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) :=
  fun x hx => q1smGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

/-- **Sup statement on (-1, -gs]** (closed right end: the window's `Full` bound, c = 0). -/
theorem q1smSupIoc : ∀ x ∈ Ioc ((q1smBd.getD 0 0 : ℚ) : ℝ) ((q1smBd.getD 55 0 : ℚ) : ℝ), fieldTower q1smFq (poleF q1smFq.poles) 0 x ≤ (q1smT : ℝ) := by
  intro x hx
  rcases hx.2.lt_or_eq with h | h
  · exact q1smSup x ⟨hx.1, h⟩
  · rw [h]
    exact q1smE054Full _ ⟨by exact_mod_cast (by decide +kernel : (q1smE054Blo : ℚ) ≤ q1smE054Bhi), le_rfl⟩

end CatalanMeasure.GenD.Signed.Data.Cells
