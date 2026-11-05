module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SmE057

@[expose] public section

/-! **SM, alpha = 0.0625: the sup statement.**  `fieldTower q2smFq ... x <= q2smT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -0.466801345348, K = -9.294867983999 (NOTES-TRIAL; kappa_old = -9.294867983999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q2smGlue0 : ∀ x ∈ Icc ((q2smBd.getD 0 0 : ℚ) : ℝ) ((q2smBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smE000Full x hx
theorem q2smGlue1 : ∀ x ∈ Icc ((q2smBd.getD 1 0 : ℚ) : ℝ) ((q2smBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB001Bound x hx
theorem q2smGlue2 : ∀ x ∈ Icc ((q2smBd.getD 2 0 : ℚ) : ℝ) ((q2smBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB002Bound x hx
theorem q2smGlue3 : ∀ x ∈ Icc ((q2smBd.getD 3 0 : ℚ) : ℝ) ((q2smBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB003Bound x hx
theorem q2smGlue4 : ∀ x ∈ Icc ((q2smBd.getD 4 0 : ℚ) : ℝ) ((q2smBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB004Bound x hx
theorem q2smGlue5 : ∀ x ∈ Icc ((q2smBd.getD 5 0 : ℚ) : ℝ) ((q2smBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB005Bound x hx
theorem q2smGlue6 : ∀ x ∈ Icc ((q2smBd.getD 6 0 : ℚ) : ℝ) ((q2smBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB006Bound x hx
theorem q2smGlue7 : ∀ x ∈ Icc ((q2smBd.getD 7 0 : ℚ) : ℝ) ((q2smBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB007Bound x hx
theorem q2smGlue8 : ∀ x ∈ Icc ((q2smBd.getD 8 0 : ℚ) : ℝ) ((q2smBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB008Bound x hx
theorem q2smGlue9 : ∀ x ∈ Icc ((q2smBd.getD 9 0 : ℚ) : ℝ) ((q2smBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB009Bound x hx
theorem q2smGlue10 : ∀ x ∈ Icc ((q2smBd.getD 10 0 : ℚ) : ℝ) ((q2smBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB010Bound x hx
theorem q2smGlue11 : ∀ x ∈ Icc ((q2smBd.getD 11 0 : ℚ) : ℝ) ((q2smBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB011Bound x hx
theorem q2smGlue12 : ∀ x ∈ Icc ((q2smBd.getD 12 0 : ℚ) : ℝ) ((q2smBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB012Bound x hx
theorem q2smGlue13 : ∀ x ∈ Icc ((q2smBd.getD 13 0 : ℚ) : ℝ) ((q2smBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB013Bound x hx
theorem q2smGlue14 : ∀ x ∈ Icc ((q2smBd.getD 14 0 : ℚ) : ℝ) ((q2smBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB014Bound x hx
theorem q2smGlue15 : ∀ x ∈ Icc ((q2smBd.getD 15 0 : ℚ) : ℝ) ((q2smBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB015Bound x hx
theorem q2smGlue16 : ∀ x ∈ Icc ((q2smBd.getD 16 0 : ℚ) : ℝ) ((q2smBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB016Bound x hx
theorem q2smGlue17 : ∀ x ∈ Icc ((q2smBd.getD 17 0 : ℚ) : ℝ) ((q2smBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB017Bound x hx
theorem q2smGlue18 : ∀ x ∈ Icc ((q2smBd.getD 18 0 : ℚ) : ℝ) ((q2smBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB018Bound x hx
theorem q2smGlue19 : ∀ x ∈ Icc ((q2smBd.getD 19 0 : ℚ) : ℝ) ((q2smBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB019Bound x hx
theorem q2smGlue20 : ∀ x ∈ Icc ((q2smBd.getD 20 0 : ℚ) : ℝ) ((q2smBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB020Bound x hx
theorem q2smGlue21 : ∀ x ∈ Icc ((q2smBd.getD 21 0 : ℚ) : ℝ) ((q2smBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB021Bound x hx
theorem q2smGlue22 : ∀ x ∈ Icc ((q2smBd.getD 22 0 : ℚ) : ℝ) ((q2smBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB022Bound x hx
theorem q2smGlue23 : ∀ x ∈ Icc ((q2smBd.getD 23 0 : ℚ) : ℝ) ((q2smBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB023Bound x hx
theorem q2smGlue24 : ∀ x ∈ Icc ((q2smBd.getD 24 0 : ℚ) : ℝ) ((q2smBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB024Bound x hx
theorem q2smGlue25 : ∀ x ∈ Icc ((q2smBd.getD 25 0 : ℚ) : ℝ) ((q2smBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB025Bound x hx
theorem q2smGlue26 : ∀ x ∈ Icc ((q2smBd.getD 26 0 : ℚ) : ℝ) ((q2smBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB026Bound x hx
theorem q2smGlue27 : ∀ x ∈ Icc ((q2smBd.getD 27 0 : ℚ) : ℝ) ((q2smBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB027Bound x hx
theorem q2smGlue28 : ∀ x ∈ Icc ((q2smBd.getD 28 0 : ℚ) : ℝ) ((q2smBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB028Bound x hx
theorem q2smGlue29 : ∀ x ∈ Icc ((q2smBd.getD 29 0 : ℚ) : ℝ) ((q2smBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB029Bound x hx
theorem q2smGlue30 : ∀ x ∈ Icc ((q2smBd.getD 30 0 : ℚ) : ℝ) ((q2smBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB030Bound x hx
theorem q2smGlue31 : ∀ x ∈ Icc ((q2smBd.getD 31 0 : ℚ) : ℝ) ((q2smBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB031Bound x hx
theorem q2smGlue32 : ∀ x ∈ Icc ((q2smBd.getD 32 0 : ℚ) : ℝ) ((q2smBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB032Bound x hx
theorem q2smGlue33 : ∀ x ∈ Icc ((q2smBd.getD 33 0 : ℚ) : ℝ) ((q2smBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB033Bound x hx
theorem q2smGlue34 : ∀ x ∈ Icc ((q2smBd.getD 34 0 : ℚ) : ℝ) ((q2smBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB034Bound x hx
theorem q2smGlue35 : ∀ x ∈ Icc ((q2smBd.getD 35 0 : ℚ) : ℝ) ((q2smBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB035Bound x hx
theorem q2smGlue36 : ∀ x ∈ Icc ((q2smBd.getD 36 0 : ℚ) : ℝ) ((q2smBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB036Bound x hx
theorem q2smGlue37 : ∀ x ∈ Icc ((q2smBd.getD 37 0 : ℚ) : ℝ) ((q2smBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB037Bound x hx
theorem q2smGlue38 : ∀ x ∈ Icc ((q2smBd.getD 38 0 : ℚ) : ℝ) ((q2smBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB038Bound x hx
theorem q2smGlue39 : ∀ x ∈ Icc ((q2smBd.getD 39 0 : ℚ) : ℝ) ((q2smBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB039Bound x hx
theorem q2smGlue40 : ∀ x ∈ Icc ((q2smBd.getD 40 0 : ℚ) : ℝ) ((q2smBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB040Bound x hx
theorem q2smGlue41 : ∀ x ∈ Icc ((q2smBd.getD 41 0 : ℚ) : ℝ) ((q2smBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB041Bound x hx
theorem q2smGlue42 : ∀ x ∈ Icc ((q2smBd.getD 42 0 : ℚ) : ℝ) ((q2smBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB042Bound x hx
theorem q2smGlue43 : ∀ x ∈ Icc ((q2smBd.getD 43 0 : ℚ) : ℝ) ((q2smBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB043Bound x hx
theorem q2smGlue44 : ∀ x ∈ Icc ((q2smBd.getD 44 0 : ℚ) : ℝ) ((q2smBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB044Bound x hx
theorem q2smGlue45 : ∀ x ∈ Icc ((q2smBd.getD 45 0 : ℚ) : ℝ) ((q2smBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB045Bound x hx
theorem q2smGlue46 : ∀ x ∈ Icc ((q2smBd.getD 46 0 : ℚ) : ℝ) ((q2smBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB046Bound x hx
theorem q2smGlue47 : ∀ x ∈ Icc ((q2smBd.getD 47 0 : ℚ) : ℝ) ((q2smBd.getD 48 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB047Bound x hx
theorem q2smGlue48 : ∀ x ∈ Icc ((q2smBd.getD 48 0 : ℚ) : ℝ) ((q2smBd.getD 49 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB048Bound x hx
theorem q2smGlue49 : ∀ x ∈ Icc ((q2smBd.getD 49 0 : ℚ) : ℝ) ((q2smBd.getD 50 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB049Bound x hx
theorem q2smGlue50 : ∀ x ∈ Icc ((q2smBd.getD 50 0 : ℚ) : ℝ) ((q2smBd.getD 51 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB050Bound x hx
theorem q2smGlue51 : ∀ x ∈ Icc ((q2smBd.getD 51 0 : ℚ) : ℝ) ((q2smBd.getD 52 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB051Bound x hx
theorem q2smGlue52 : ∀ x ∈ Icc ((q2smBd.getD 52 0 : ℚ) : ℝ) ((q2smBd.getD 53 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB052Bound x hx
theorem q2smGlue53 : ∀ x ∈ Icc ((q2smBd.getD 53 0 : ℚ) : ℝ) ((q2smBd.getD 54 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB053Bound x hx
theorem q2smGlue54 : ∀ x ∈ Icc ((q2smBd.getD 54 0 : ℚ) : ℝ) ((q2smBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB054Bound x hx
theorem q2smGlue55 : ∀ x ∈ Icc ((q2smBd.getD 55 0 : ℚ) : ℝ) ((q2smBd.getD 56 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB055Bound x hx
theorem q2smGlue56 : ∀ x ∈ Icc ((q2smBd.getD 56 0 : ℚ) : ℝ) ((q2smBd.getD 57 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smB056Bound x hx
theorem q2smGlue57 : ∀ x ∈ Icc ((q2smBd.getD 57 0 : ℚ) : ℝ) ((q2smBd.getD 58 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx _ _ => q2smE057Full x hx
theorem q2smGlueAll : ∀ x ∈ Icc ((q2smBd.getD 0 0 : ℚ) : ℝ) ((q2smBd.getD 58 0 : ℚ) : ℝ), x ≠ ((q2smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2smBd.getD 58 0 : ℚ) : ℝ) → fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2smGlue0) q2smGlue1) q2smGlue2) q2smGlue3) q2smGlue4) q2smGlue5) q2smGlue6) q2smGlue7) q2smGlue8) q2smGlue9) q2smGlue10) q2smGlue11) q2smGlue12) q2smGlue13) q2smGlue14) q2smGlue15) q2smGlue16) q2smGlue17) q2smGlue18) q2smGlue19) q2smGlue20) q2smGlue21) q2smGlue22) q2smGlue23) q2smGlue24) q2smGlue25) q2smGlue26) q2smGlue27) q2smGlue28) q2smGlue29) q2smGlue30) q2smGlue31) q2smGlue32) q2smGlue33) q2smGlue34) q2smGlue35) q2smGlue36) q2smGlue37) q2smGlue38) q2smGlue39) q2smGlue40) q2smGlue41) q2smGlue42) q2smGlue43) q2smGlue44) q2smGlue45) q2smGlue46) q2smGlue47) q2smGlue48) q2smGlue49) q2smGlue50) q2smGlue51) q2smGlue52) q2smGlue53) q2smGlue54) q2smGlue55) q2smGlue56) q2smGlue57
/-- **Sup statement (SM, alpha = 0.0625).** -/
theorem q2smSup : ∀ x ∈ Ioo ((q2smBd.getD 0 0 : ℚ) : ℝ) ((q2smBd.getD 58 0 : ℚ) : ℝ), fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) :=
  fun x hx => q2smGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

/-- **Sup statement on (-1, -gs]** (closed right end: the window's `Full` bound, c = 0). -/
theorem q2smSupIoc : ∀ x ∈ Ioc ((q2smBd.getD 0 0 : ℚ) : ℝ) ((q2smBd.getD 58 0 : ℚ) : ℝ), fieldTower q2smFq (poleF q2smFq.poles) 0 x ≤ (q2smT : ℝ) := by
  intro x hx
  rcases hx.2.lt_or_eq with h | h
  · exact q2smSup x ⟨hx.1, h⟩
  · rw [h]
    exact q2smE057Full _ ⟨by exact_mod_cast (by decide +kernel : (q2smE057Blo : ℚ) ≤ q2smE057Bhi), le_rfl⟩

end CatalanMeasure.GenD.Signed.Data.Cells
