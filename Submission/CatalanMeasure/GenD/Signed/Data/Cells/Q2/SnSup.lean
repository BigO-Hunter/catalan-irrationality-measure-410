module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE053
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE074
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP015
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP016
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP017
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE082
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP018
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP019
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP020
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP021
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP022
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE098
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP023
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP024
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP025
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE106
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP026
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP027
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnP028
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.SnE120

@[expose] public section

/-! **SN, alpha = 0.0625: the sup statement.**  `fieldTower q2snFq ... x <= q2snT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.708836763856, K = -18.931537618999 (NOTES-TRIAL; kappa_old = -18.931537618999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q2snGlue0 : ∀ x ∈ Icc ((q2snBd.getD 0 0 : ℚ) : ℝ) ((q2snBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snE000Full x hx
theorem q2snGlue1 : ∀ x ∈ Icc ((q2snBd.getD 1 0 : ℚ) : ℝ) ((q2snBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB001Bound x hx
theorem q2snGlue2 : ∀ x ∈ Icc ((q2snBd.getD 2 0 : ℚ) : ℝ) ((q2snBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB002Bound x hx
theorem q2snGlue3 : ∀ x ∈ Icc ((q2snBd.getD 3 0 : ℚ) : ℝ) ((q2snBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB003Bound x hx
theorem q2snGlue4 : ∀ x ∈ Icc ((q2snBd.getD 4 0 : ℚ) : ℝ) ((q2snBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB004Bound x hx
theorem q2snGlue5 : ∀ x ∈ Icc ((q2snBd.getD 5 0 : ℚ) : ℝ) ((q2snBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB005Bound x hx
theorem q2snGlue6 : ∀ x ∈ Icc ((q2snBd.getD 6 0 : ℚ) : ℝ) ((q2snBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB006Bound x hx
theorem q2snGlue7 : ∀ x ∈ Icc ((q2snBd.getD 7 0 : ℚ) : ℝ) ((q2snBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB007Bound x hx
theorem q2snGlue8 : ∀ x ∈ Icc ((q2snBd.getD 8 0 : ℚ) : ℝ) ((q2snBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB008Bound x hx
theorem q2snGlue9 : ∀ x ∈ Icc ((q2snBd.getD 9 0 : ℚ) : ℝ) ((q2snBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB009Bound x hx
theorem q2snGlue10 : ∀ x ∈ Icc ((q2snBd.getD 10 0 : ℚ) : ℝ) ((q2snBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB010Bound x hx
theorem q2snGlue11 : ∀ x ∈ Icc ((q2snBd.getD 11 0 : ℚ) : ℝ) ((q2snBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB011Bound x hx
theorem q2snGlue12 : ∀ x ∈ Icc ((q2snBd.getD 12 0 : ℚ) : ℝ) ((q2snBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB012Bound x hx
theorem q2snGlue13 : ∀ x ∈ Icc ((q2snBd.getD 13 0 : ℚ) : ℝ) ((q2snBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB013Bound x hx
theorem q2snGlue14 : ∀ x ∈ Icc ((q2snBd.getD 14 0 : ℚ) : ℝ) ((q2snBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB014Bound x hx
theorem q2snGlue15 : ∀ x ∈ Icc ((q2snBd.getD 15 0 : ℚ) : ℝ) ((q2snBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB015Bound x hx
theorem q2snGlue16 : ∀ x ∈ Icc ((q2snBd.getD 16 0 : ℚ) : ℝ) ((q2snBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB016Bound x hx
theorem q2snGlue17 : ∀ x ∈ Icc ((q2snBd.getD 17 0 : ℚ) : ℝ) ((q2snBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB017Bound x hx
theorem q2snGlue18 : ∀ x ∈ Icc ((q2snBd.getD 18 0 : ℚ) : ℝ) ((q2snBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB018Bound x hx
theorem q2snGlue19 : ∀ x ∈ Icc ((q2snBd.getD 19 0 : ℚ) : ℝ) ((q2snBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB019Bound x hx
theorem q2snGlue20 : ∀ x ∈ Icc ((q2snBd.getD 20 0 : ℚ) : ℝ) ((q2snBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB020Bound x hx
theorem q2snGlue21 : ∀ x ∈ Icc ((q2snBd.getD 21 0 : ℚ) : ℝ) ((q2snBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB021Bound x hx
theorem q2snGlue22 : ∀ x ∈ Icc ((q2snBd.getD 22 0 : ℚ) : ℝ) ((q2snBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB022Bound x hx
theorem q2snGlue23 : ∀ x ∈ Icc ((q2snBd.getD 23 0 : ℚ) : ℝ) ((q2snBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB023Bound x hx
theorem q2snGlue24 : ∀ x ∈ Icc ((q2snBd.getD 24 0 : ℚ) : ℝ) ((q2snBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB024Bound x hx
theorem q2snGlue25 : ∀ x ∈ Icc ((q2snBd.getD 25 0 : ℚ) : ℝ) ((q2snBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB025Bound x hx
theorem q2snGlue26 : ∀ x ∈ Icc ((q2snBd.getD 26 0 : ℚ) : ℝ) ((q2snBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB026Bound x hx
theorem q2snGlue27 : ∀ x ∈ Icc ((q2snBd.getD 27 0 : ℚ) : ℝ) ((q2snBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB027Bound x hx
theorem q2snGlue28 : ∀ x ∈ Icc ((q2snBd.getD 28 0 : ℚ) : ℝ) ((q2snBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB028Bound x hx
theorem q2snGlue29 : ∀ x ∈ Icc ((q2snBd.getD 29 0 : ℚ) : ℝ) ((q2snBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB029Bound x hx
theorem q2snGlue30 : ∀ x ∈ Icc ((q2snBd.getD 30 0 : ℚ) : ℝ) ((q2snBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB030Bound x hx
theorem q2snGlue31 : ∀ x ∈ Icc ((q2snBd.getD 31 0 : ℚ) : ℝ) ((q2snBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB031Bound x hx
theorem q2snGlue32 : ∀ x ∈ Icc ((q2snBd.getD 32 0 : ℚ) : ℝ) ((q2snBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB032Bound x hx
theorem q2snGlue33 : ∀ x ∈ Icc ((q2snBd.getD 33 0 : ℚ) : ℝ) ((q2snBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB033Bound x hx
theorem q2snGlue34 : ∀ x ∈ Icc ((q2snBd.getD 34 0 : ℚ) : ℝ) ((q2snBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB034Bound x hx
theorem q2snGlue35 : ∀ x ∈ Icc ((q2snBd.getD 35 0 : ℚ) : ℝ) ((q2snBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB035Bound x hx
theorem q2snGlue36 : ∀ x ∈ Icc ((q2snBd.getD 36 0 : ℚ) : ℝ) ((q2snBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB036Bound x hx
theorem q2snGlue37 : ∀ x ∈ Icc ((q2snBd.getD 37 0 : ℚ) : ℝ) ((q2snBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB037Bound x hx
theorem q2snGlue38 : ∀ x ∈ Icc ((q2snBd.getD 38 0 : ℚ) : ℝ) ((q2snBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB038Bound x hx
theorem q2snGlue39 : ∀ x ∈ Icc ((q2snBd.getD 39 0 : ℚ) : ℝ) ((q2snBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB039Bound x hx
theorem q2snGlue40 : ∀ x ∈ Icc ((q2snBd.getD 40 0 : ℚ) : ℝ) ((q2snBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB040Bound x hx
theorem q2snGlue41 : ∀ x ∈ Icc ((q2snBd.getD 41 0 : ℚ) : ℝ) ((q2snBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB041Bound x hx
theorem q2snGlue42 : ∀ x ∈ Icc ((q2snBd.getD 42 0 : ℚ) : ℝ) ((q2snBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB042Bound x hx
theorem q2snGlue43 : ∀ x ∈ Icc ((q2snBd.getD 43 0 : ℚ) : ℝ) ((q2snBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB043Bound x hx
theorem q2snGlue44 : ∀ x ∈ Icc ((q2snBd.getD 44 0 : ℚ) : ℝ) ((q2snBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB044Bound x hx
theorem q2snGlue45 : ∀ x ∈ Icc ((q2snBd.getD 45 0 : ℚ) : ℝ) ((q2snBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB045Bound x hx
theorem q2snGlue46 : ∀ x ∈ Icc ((q2snBd.getD 46 0 : ℚ) : ℝ) ((q2snBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB046Bound x hx
theorem q2snGlue47 : ∀ x ∈ Icc ((q2snBd.getD 47 0 : ℚ) : ℝ) ((q2snBd.getD 48 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB047Bound x hx
theorem q2snGlue48 : ∀ x ∈ Icc ((q2snBd.getD 48 0 : ℚ) : ℝ) ((q2snBd.getD 49 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB048Bound x hx
theorem q2snGlue49 : ∀ x ∈ Icc ((q2snBd.getD 49 0 : ℚ) : ℝ) ((q2snBd.getD 50 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB049Bound x hx
theorem q2snGlue50 : ∀ x ∈ Icc ((q2snBd.getD 50 0 : ℚ) : ℝ) ((q2snBd.getD 51 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB050Bound x hx
theorem q2snGlue51 : ∀ x ∈ Icc ((q2snBd.getD 51 0 : ℚ) : ℝ) ((q2snBd.getD 52 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB051Bound x hx
theorem q2snGlue52 : ∀ x ∈ Icc ((q2snBd.getD 52 0 : ℚ) : ℝ) ((q2snBd.getD 53 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB052Bound x hx
theorem q2snGlue53 : ∀ x ∈ Icc ((q2snBd.getD 53 0 : ℚ) : ℝ) ((q2snBd.getD 54 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snE053Full x hx
theorem q2snGlue54 : ∀ x ∈ Icc ((q2snBd.getD 54 0 : ℚ) : ℝ) ((q2snBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB054Bound x hx
theorem q2snGlue55 : ∀ x ∈ Icc ((q2snBd.getD 55 0 : ℚ) : ℝ) ((q2snBd.getD 56 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB055Bound x hx
theorem q2snGlue56 : ∀ x ∈ Icc ((q2snBd.getD 56 0 : ℚ) : ℝ) ((q2snBd.getD 57 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB056Bound x hx
theorem q2snGlue57 : ∀ x ∈ Icc ((q2snBd.getD 57 0 : ℚ) : ℝ) ((q2snBd.getD 58 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB057Bound x hx
theorem q2snGlue58 : ∀ x ∈ Icc ((q2snBd.getD 58 0 : ℚ) : ℝ) ((q2snBd.getD 59 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB058Bound x hx
theorem q2snGlue59 : ∀ x ∈ Icc ((q2snBd.getD 59 0 : ℚ) : ℝ) ((q2snBd.getD 60 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB059Bound x hx
theorem q2snGlue60 : ∀ x ∈ Icc ((q2snBd.getD 60 0 : ℚ) : ℝ) ((q2snBd.getD 61 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB060Bound x hx
theorem q2snGlue61 : ∀ x ∈ Icc ((q2snBd.getD 61 0 : ℚ) : ℝ) ((q2snBd.getD 62 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB061Bound x hx
theorem q2snGlue62 : ∀ x ∈ Icc ((q2snBd.getD 62 0 : ℚ) : ℝ) ((q2snBd.getD 63 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB062Bound x hx
theorem q2snGlue63 : ∀ x ∈ Icc ((q2snBd.getD 63 0 : ℚ) : ℝ) ((q2snBd.getD 64 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB063Bound x hx
theorem q2snGlue64 : ∀ x ∈ Icc ((q2snBd.getD 64 0 : ℚ) : ℝ) ((q2snBd.getD 65 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB064Bound x hx
theorem q2snGlue65 : ∀ x ∈ Icc ((q2snBd.getD 65 0 : ℚ) : ℝ) ((q2snBd.getD 66 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB065Bound x hx
theorem q2snGlue66 : ∀ x ∈ Icc ((q2snBd.getD 66 0 : ℚ) : ℝ) ((q2snBd.getD 67 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB066Bound x hx
theorem q2snGlue67 : ∀ x ∈ Icc ((q2snBd.getD 67 0 : ℚ) : ℝ) ((q2snBd.getD 68 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB067Bound x hx
theorem q2snGlue68 : ∀ x ∈ Icc ((q2snBd.getD 68 0 : ℚ) : ℝ) ((q2snBd.getD 69 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB068Bound x hx
theorem q2snGlue69 : ∀ x ∈ Icc ((q2snBd.getD 69 0 : ℚ) : ℝ) ((q2snBd.getD 70 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB069Bound x hx
theorem q2snGlue70 : ∀ x ∈ Icc ((q2snBd.getD 70 0 : ℚ) : ℝ) ((q2snBd.getD 71 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB070Bound x hx
theorem q2snGlue71 : ∀ x ∈ Icc ((q2snBd.getD 71 0 : ℚ) : ℝ) ((q2snBd.getD 72 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB071Bound x hx
theorem q2snGlue72 : ∀ x ∈ Icc ((q2snBd.getD 72 0 : ℚ) : ℝ) ((q2snBd.getD 73 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB072Bound x hx
theorem q2snGlue73 : ∀ x ∈ Icc ((q2snBd.getD 73 0 : ℚ) : ℝ) ((q2snBd.getD 74 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB073Bound x hx
theorem q2snGlue74 : ∀ x ∈ Icc ((q2snBd.getD 74 0 : ℚ) : ℝ) ((q2snBd.getD 75 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snE074Full x hx
theorem q2snGlue75 : ∀ x ∈ Icc ((q2snBd.getD 75 0 : ℚ) : ℝ) ((q2snBd.getD 76 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB075Bound x hx
theorem q2snGlue76 : ∀ x ∈ Icc ((q2snBd.getD 76 0 : ℚ) : ℝ) ((q2snBd.getD 77 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB076Bound x hx
theorem q2snGlue77 : ∀ x ∈ Icc ((q2snBd.getD 77 0 : ℚ) : ℝ) ((q2snBd.getD 78 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB077Bound x hx
theorem q2snGlue78 : ∀ x ∈ Icc ((q2snBd.getD 78 0 : ℚ) : ℝ) ((q2snBd.getD 79 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB078Bound x hx
theorem q2snGlue79 : ∀ x ∈ Icc ((q2snBd.getD 79 0 : ℚ) : ℝ) ((q2snBd.getD 80 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB079Bound x hx
theorem q2snGlue80 : ∀ x ∈ Icc ((q2snBd.getD 80 0 : ℚ) : ℝ) ((q2snBd.getD 81 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB080Bound x hx
theorem q2snGlue81 : ∀ x ∈ Icc ((q2snBd.getD 81 0 : ℚ) : ℝ) ((q2snBd.getD 82 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB081Bound x hx
theorem q2snGlue82 : ∀ x ∈ Icc ((q2snBd.getD 82 0 : ℚ) : ℝ) ((q2snBd.getD 83 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snE082Full x hx
theorem q2snGlue83 : ∀ x ∈ Icc ((q2snBd.getD 83 0 : ℚ) : ℝ) ((q2snBd.getD 84 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB083Bound x hx
theorem q2snGlue84 : ∀ x ∈ Icc ((q2snBd.getD 84 0 : ℚ) : ℝ) ((q2snBd.getD 85 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB084Bound x hx
theorem q2snGlue85 : ∀ x ∈ Icc ((q2snBd.getD 85 0 : ℚ) : ℝ) ((q2snBd.getD 86 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB085Bound x hx
theorem q2snGlue86 : ∀ x ∈ Icc ((q2snBd.getD 86 0 : ℚ) : ℝ) ((q2snBd.getD 87 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB086Bound x hx
theorem q2snGlue87 : ∀ x ∈ Icc ((q2snBd.getD 87 0 : ℚ) : ℝ) ((q2snBd.getD 88 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB087Bound x hx
theorem q2snGlue88 : ∀ x ∈ Icc ((q2snBd.getD 88 0 : ℚ) : ℝ) ((q2snBd.getD 89 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB088Bound x hx
theorem q2snGlue89 : ∀ x ∈ Icc ((q2snBd.getD 89 0 : ℚ) : ℝ) ((q2snBd.getD 90 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB089Bound x hx
theorem q2snGlue90 : ∀ x ∈ Icc ((q2snBd.getD 90 0 : ℚ) : ℝ) ((q2snBd.getD 91 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB090Bound x hx
theorem q2snGlue91 : ∀ x ∈ Icc ((q2snBd.getD 91 0 : ℚ) : ℝ) ((q2snBd.getD 92 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB091Bound x hx
theorem q2snGlue92 : ∀ x ∈ Icc ((q2snBd.getD 92 0 : ℚ) : ℝ) ((q2snBd.getD 93 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB092Bound x hx
theorem q2snGlue93 : ∀ x ∈ Icc ((q2snBd.getD 93 0 : ℚ) : ℝ) ((q2snBd.getD 94 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB093Bound x hx
theorem q2snGlue94 : ∀ x ∈ Icc ((q2snBd.getD 94 0 : ℚ) : ℝ) ((q2snBd.getD 95 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB094Bound x hx
theorem q2snGlue95 : ∀ x ∈ Icc ((q2snBd.getD 95 0 : ℚ) : ℝ) ((q2snBd.getD 96 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB095Bound x hx
theorem q2snGlue96 : ∀ x ∈ Icc ((q2snBd.getD 96 0 : ℚ) : ℝ) ((q2snBd.getD 97 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB096Bound x hx
theorem q2snGlue97 : ∀ x ∈ Icc ((q2snBd.getD 97 0 : ℚ) : ℝ) ((q2snBd.getD 98 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB097Bound x hx
theorem q2snGlue98 : ∀ x ∈ Icc ((q2snBd.getD 98 0 : ℚ) : ℝ) ((q2snBd.getD 99 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snE098Full x hx
theorem q2snGlue99 : ∀ x ∈ Icc ((q2snBd.getD 99 0 : ℚ) : ℝ) ((q2snBd.getD 100 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB099Bound x hx
theorem q2snGlue100 : ∀ x ∈ Icc ((q2snBd.getD 100 0 : ℚ) : ℝ) ((q2snBd.getD 101 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB100Bound x hx
theorem q2snGlue101 : ∀ x ∈ Icc ((q2snBd.getD 101 0 : ℚ) : ℝ) ((q2snBd.getD 102 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB101Bound x hx
theorem q2snGlue102 : ∀ x ∈ Icc ((q2snBd.getD 102 0 : ℚ) : ℝ) ((q2snBd.getD 103 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB102Bound x hx
theorem q2snGlue103 : ∀ x ∈ Icc ((q2snBd.getD 103 0 : ℚ) : ℝ) ((q2snBd.getD 104 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB103Bound x hx
theorem q2snGlue104 : ∀ x ∈ Icc ((q2snBd.getD 104 0 : ℚ) : ℝ) ((q2snBd.getD 105 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB104Bound x hx
theorem q2snGlue105 : ∀ x ∈ Icc ((q2snBd.getD 105 0 : ℚ) : ℝ) ((q2snBd.getD 106 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB105Bound x hx
theorem q2snGlue106 : ∀ x ∈ Icc ((q2snBd.getD 106 0 : ℚ) : ℝ) ((q2snBd.getD 107 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snE106Full x hx
theorem q2snGlue107 : ∀ x ∈ Icc ((q2snBd.getD 107 0 : ℚ) : ℝ) ((q2snBd.getD 108 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB107Bound x hx
theorem q2snGlue108 : ∀ x ∈ Icc ((q2snBd.getD 108 0 : ℚ) : ℝ) ((q2snBd.getD 109 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB108Bound x hx
theorem q2snGlue109 : ∀ x ∈ Icc ((q2snBd.getD 109 0 : ℚ) : ℝ) ((q2snBd.getD 110 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB109Bound x hx
theorem q2snGlue110 : ∀ x ∈ Icc ((q2snBd.getD 110 0 : ℚ) : ℝ) ((q2snBd.getD 111 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB110Bound x hx
theorem q2snGlue111 : ∀ x ∈ Icc ((q2snBd.getD 111 0 : ℚ) : ℝ) ((q2snBd.getD 112 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB111Bound x hx
theorem q2snGlue112 : ∀ x ∈ Icc ((q2snBd.getD 112 0 : ℚ) : ℝ) ((q2snBd.getD 113 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB112Bound x hx
theorem q2snGlue113 : ∀ x ∈ Icc ((q2snBd.getD 113 0 : ℚ) : ℝ) ((q2snBd.getD 114 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB113Bound x hx
theorem q2snGlue114 : ∀ x ∈ Icc ((q2snBd.getD 114 0 : ℚ) : ℝ) ((q2snBd.getD 115 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB114Bound x hx
theorem q2snGlue115 : ∀ x ∈ Icc ((q2snBd.getD 115 0 : ℚ) : ℝ) ((q2snBd.getD 116 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB115Bound x hx
theorem q2snGlue116 : ∀ x ∈ Icc ((q2snBd.getD 116 0 : ℚ) : ℝ) ((q2snBd.getD 117 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB116Bound x hx
theorem q2snGlue117 : ∀ x ∈ Icc ((q2snBd.getD 117 0 : ℚ) : ℝ) ((q2snBd.getD 118 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB117Bound x hx
theorem q2snGlue118 : ∀ x ∈ Icc ((q2snBd.getD 118 0 : ℚ) : ℝ) ((q2snBd.getD 119 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB118Bound x hx
theorem q2snGlue119 : ∀ x ∈ Icc ((q2snBd.getD 119 0 : ℚ) : ℝ) ((q2snBd.getD 120 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx _ _ => q2snB119Bound x hx
theorem q2snGlue120 : ∀ x ∈ Icc ((q2snBd.getD 120 0 : ℚ) : ℝ) ((q2snBd.getD 121 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx hA hB => q2snE120Unif x hx (by rw [q2snE120Eq]; exact hB)
theorem q2snGlueAll : ∀ x ∈ Icc ((q2snBd.getD 0 0 : ℚ) : ℝ) ((q2snBd.getD 121 0 : ℚ) : ℝ), x ≠ ((q2snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2snBd.getD 121 0 : ℚ) : ℝ) → fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2snGlue0) q2snGlue1) q2snGlue2) q2snGlue3) q2snGlue4) q2snGlue5) q2snGlue6) q2snGlue7) q2snGlue8) q2snGlue9) q2snGlue10) q2snGlue11) q2snGlue12) q2snGlue13) q2snGlue14) q2snGlue15) q2snGlue16) q2snGlue17) q2snGlue18) q2snGlue19) q2snGlue20) q2snGlue21) q2snGlue22) q2snGlue23) q2snGlue24) q2snGlue25) q2snGlue26) q2snGlue27) q2snGlue28) q2snGlue29) q2snGlue30) q2snGlue31) q2snGlue32) q2snGlue33) q2snGlue34) q2snGlue35) q2snGlue36) q2snGlue37) q2snGlue38) q2snGlue39) q2snGlue40) q2snGlue41) q2snGlue42) q2snGlue43) q2snGlue44) q2snGlue45) q2snGlue46) q2snGlue47) q2snGlue48) q2snGlue49) q2snGlue50) q2snGlue51) q2snGlue52) q2snGlue53) q2snGlue54) q2snGlue55) q2snGlue56) q2snGlue57) q2snGlue58) q2snGlue59) q2snGlue60) q2snGlue61) q2snGlue62) q2snGlue63) q2snGlue64) q2snGlue65) q2snGlue66) q2snGlue67) q2snGlue68) q2snGlue69) q2snGlue70) q2snGlue71) q2snGlue72) q2snGlue73) q2snGlue74) q2snGlue75) q2snGlue76) q2snGlue77) q2snGlue78) q2snGlue79) q2snGlue80) q2snGlue81) q2snGlue82) q2snGlue83) q2snGlue84) q2snGlue85) q2snGlue86) q2snGlue87) q2snGlue88) q2snGlue89) q2snGlue90) q2snGlue91) q2snGlue92) q2snGlue93) q2snGlue94) q2snGlue95) q2snGlue96) q2snGlue97) q2snGlue98) q2snGlue99) q2snGlue100) q2snGlue101) q2snGlue102) q2snGlue103) q2snGlue104) q2snGlue105) q2snGlue106) q2snGlue107) q2snGlue108) q2snGlue109) q2snGlue110) q2snGlue111) q2snGlue112) q2snGlue113) q2snGlue114) q2snGlue115) q2snGlue116) q2snGlue117) q2snGlue118) q2snGlue119) q2snGlue120
/-- **Sup statement (SN, alpha = 0.0625).** -/
theorem q2snSup : ∀ x ∈ Ioo ((q2snBd.getD 0 0 : ℚ) : ℝ) ((q2snBd.getD 121 0 : ℚ) : ℝ), fieldTower q2snFq (poleF q2snFq.poles) 0 x ≤ (q2snT : ℝ) :=
  fun x hx => q2snGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
