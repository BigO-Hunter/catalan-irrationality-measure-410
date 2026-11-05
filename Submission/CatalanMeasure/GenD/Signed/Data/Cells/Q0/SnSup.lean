module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE049
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP015
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE057
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP016
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP017
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP018
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP019
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP020
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE073
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP021
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP022
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE079
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP023
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP024
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP025
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP026
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE094
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnP027
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE096

@[expose] public section

/-! **SN, alpha = 0.0: the sup statement.**  `fieldTower q0snFq ... x <= q0snT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.740490366702, K = -18.914421677999 (NOTES-TRIAL; kappa_old = -18.914421677999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q0snGlue0 : ∀ x ∈ Icc ((q0snBd.getD 0 0 : ℚ) : ℝ) ((q0snBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE000Full x hx
theorem q0snGlue1 : ∀ x ∈ Icc ((q0snBd.getD 1 0 : ℚ) : ℝ) ((q0snBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB001Bound x hx
theorem q0snGlue2 : ∀ x ∈ Icc ((q0snBd.getD 2 0 : ℚ) : ℝ) ((q0snBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB002Bound x hx
theorem q0snGlue3 : ∀ x ∈ Icc ((q0snBd.getD 3 0 : ℚ) : ℝ) ((q0snBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB003Bound x hx
theorem q0snGlue4 : ∀ x ∈ Icc ((q0snBd.getD 4 0 : ℚ) : ℝ) ((q0snBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB004Bound x hx
theorem q0snGlue5 : ∀ x ∈ Icc ((q0snBd.getD 5 0 : ℚ) : ℝ) ((q0snBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB005Bound x hx
theorem q0snGlue6 : ∀ x ∈ Icc ((q0snBd.getD 6 0 : ℚ) : ℝ) ((q0snBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB006Bound x hx
theorem q0snGlue7 : ∀ x ∈ Icc ((q0snBd.getD 7 0 : ℚ) : ℝ) ((q0snBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB007Bound x hx
theorem q0snGlue8 : ∀ x ∈ Icc ((q0snBd.getD 8 0 : ℚ) : ℝ) ((q0snBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB008Bound x hx
theorem q0snGlue9 : ∀ x ∈ Icc ((q0snBd.getD 9 0 : ℚ) : ℝ) ((q0snBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB009Bound x hx
theorem q0snGlue10 : ∀ x ∈ Icc ((q0snBd.getD 10 0 : ℚ) : ℝ) ((q0snBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB010Bound x hx
theorem q0snGlue11 : ∀ x ∈ Icc ((q0snBd.getD 11 0 : ℚ) : ℝ) ((q0snBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB011Bound x hx
theorem q0snGlue12 : ∀ x ∈ Icc ((q0snBd.getD 12 0 : ℚ) : ℝ) ((q0snBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB012Bound x hx
theorem q0snGlue13 : ∀ x ∈ Icc ((q0snBd.getD 13 0 : ℚ) : ℝ) ((q0snBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB013Bound x hx
theorem q0snGlue14 : ∀ x ∈ Icc ((q0snBd.getD 14 0 : ℚ) : ℝ) ((q0snBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB014Bound x hx
theorem q0snGlue15 : ∀ x ∈ Icc ((q0snBd.getD 15 0 : ℚ) : ℝ) ((q0snBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB015Bound x hx
theorem q0snGlue16 : ∀ x ∈ Icc ((q0snBd.getD 16 0 : ℚ) : ℝ) ((q0snBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB016Bound x hx
theorem q0snGlue17 : ∀ x ∈ Icc ((q0snBd.getD 17 0 : ℚ) : ℝ) ((q0snBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB017Bound x hx
theorem q0snGlue18 : ∀ x ∈ Icc ((q0snBd.getD 18 0 : ℚ) : ℝ) ((q0snBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB018Bound x hx
theorem q0snGlue19 : ∀ x ∈ Icc ((q0snBd.getD 19 0 : ℚ) : ℝ) ((q0snBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB019Bound x hx
theorem q0snGlue20 : ∀ x ∈ Icc ((q0snBd.getD 20 0 : ℚ) : ℝ) ((q0snBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB020Bound x hx
theorem q0snGlue21 : ∀ x ∈ Icc ((q0snBd.getD 21 0 : ℚ) : ℝ) ((q0snBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB021Bound x hx
theorem q0snGlue22 : ∀ x ∈ Icc ((q0snBd.getD 22 0 : ℚ) : ℝ) ((q0snBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB022Bound x hx
theorem q0snGlue23 : ∀ x ∈ Icc ((q0snBd.getD 23 0 : ℚ) : ℝ) ((q0snBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB023Bound x hx
theorem q0snGlue24 : ∀ x ∈ Icc ((q0snBd.getD 24 0 : ℚ) : ℝ) ((q0snBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB024Bound x hx
theorem q0snGlue25 : ∀ x ∈ Icc ((q0snBd.getD 25 0 : ℚ) : ℝ) ((q0snBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB025Bound x hx
theorem q0snGlue26 : ∀ x ∈ Icc ((q0snBd.getD 26 0 : ℚ) : ℝ) ((q0snBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB026Bound x hx
theorem q0snGlue27 : ∀ x ∈ Icc ((q0snBd.getD 27 0 : ℚ) : ℝ) ((q0snBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB027Bound x hx
theorem q0snGlue28 : ∀ x ∈ Icc ((q0snBd.getD 28 0 : ℚ) : ℝ) ((q0snBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB028Bound x hx
theorem q0snGlue29 : ∀ x ∈ Icc ((q0snBd.getD 29 0 : ℚ) : ℝ) ((q0snBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB029Bound x hx
theorem q0snGlue30 : ∀ x ∈ Icc ((q0snBd.getD 30 0 : ℚ) : ℝ) ((q0snBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB030Bound x hx
theorem q0snGlue31 : ∀ x ∈ Icc ((q0snBd.getD 31 0 : ℚ) : ℝ) ((q0snBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB031Bound x hx
theorem q0snGlue32 : ∀ x ∈ Icc ((q0snBd.getD 32 0 : ℚ) : ℝ) ((q0snBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB032Bound x hx
theorem q0snGlue33 : ∀ x ∈ Icc ((q0snBd.getD 33 0 : ℚ) : ℝ) ((q0snBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB033Bound x hx
theorem q0snGlue34 : ∀ x ∈ Icc ((q0snBd.getD 34 0 : ℚ) : ℝ) ((q0snBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB034Bound x hx
theorem q0snGlue35 : ∀ x ∈ Icc ((q0snBd.getD 35 0 : ℚ) : ℝ) ((q0snBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB035Bound x hx
theorem q0snGlue36 : ∀ x ∈ Icc ((q0snBd.getD 36 0 : ℚ) : ℝ) ((q0snBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB036Bound x hx
theorem q0snGlue37 : ∀ x ∈ Icc ((q0snBd.getD 37 0 : ℚ) : ℝ) ((q0snBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB037Bound x hx
theorem q0snGlue38 : ∀ x ∈ Icc ((q0snBd.getD 38 0 : ℚ) : ℝ) ((q0snBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB038Bound x hx
theorem q0snGlue39 : ∀ x ∈ Icc ((q0snBd.getD 39 0 : ℚ) : ℝ) ((q0snBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB039Bound x hx
theorem q0snGlue40 : ∀ x ∈ Icc ((q0snBd.getD 40 0 : ℚ) : ℝ) ((q0snBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB040Bound x hx
theorem q0snGlue41 : ∀ x ∈ Icc ((q0snBd.getD 41 0 : ℚ) : ℝ) ((q0snBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB041Bound x hx
theorem q0snGlue42 : ∀ x ∈ Icc ((q0snBd.getD 42 0 : ℚ) : ℝ) ((q0snBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB042Bound x hx
theorem q0snGlue43 : ∀ x ∈ Icc ((q0snBd.getD 43 0 : ℚ) : ℝ) ((q0snBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB043Bound x hx
theorem q0snGlue44 : ∀ x ∈ Icc ((q0snBd.getD 44 0 : ℚ) : ℝ) ((q0snBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB044Bound x hx
theorem q0snGlue45 : ∀ x ∈ Icc ((q0snBd.getD 45 0 : ℚ) : ℝ) ((q0snBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB045Bound x hx
theorem q0snGlue46 : ∀ x ∈ Icc ((q0snBd.getD 46 0 : ℚ) : ℝ) ((q0snBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB046Bound x hx
theorem q0snGlue47 : ∀ x ∈ Icc ((q0snBd.getD 47 0 : ℚ) : ℝ) ((q0snBd.getD 48 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB047Bound x hx
theorem q0snGlue48 : ∀ x ∈ Icc ((q0snBd.getD 48 0 : ℚ) : ℝ) ((q0snBd.getD 49 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB048Bound x hx
theorem q0snGlue49 : ∀ x ∈ Icc ((q0snBd.getD 49 0 : ℚ) : ℝ) ((q0snBd.getD 50 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE049Full x hx
theorem q0snGlue50 : ∀ x ∈ Icc ((q0snBd.getD 50 0 : ℚ) : ℝ) ((q0snBd.getD 51 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB050Bound x hx
theorem q0snGlue51 : ∀ x ∈ Icc ((q0snBd.getD 51 0 : ℚ) : ℝ) ((q0snBd.getD 52 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB051Bound x hx
theorem q0snGlue52 : ∀ x ∈ Icc ((q0snBd.getD 52 0 : ℚ) : ℝ) ((q0snBd.getD 53 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB052Bound x hx
theorem q0snGlue53 : ∀ x ∈ Icc ((q0snBd.getD 53 0 : ℚ) : ℝ) ((q0snBd.getD 54 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB053Bound x hx
theorem q0snGlue54 : ∀ x ∈ Icc ((q0snBd.getD 54 0 : ℚ) : ℝ) ((q0snBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB054Bound x hx
theorem q0snGlue55 : ∀ x ∈ Icc ((q0snBd.getD 55 0 : ℚ) : ℝ) ((q0snBd.getD 56 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB055Bound x hx
theorem q0snGlue56 : ∀ x ∈ Icc ((q0snBd.getD 56 0 : ℚ) : ℝ) ((q0snBd.getD 57 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB056Bound x hx
theorem q0snGlue57 : ∀ x ∈ Icc ((q0snBd.getD 57 0 : ℚ) : ℝ) ((q0snBd.getD 58 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE057Full x hx
theorem q0snGlue58 : ∀ x ∈ Icc ((q0snBd.getD 58 0 : ℚ) : ℝ) ((q0snBd.getD 59 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB058Bound x hx
theorem q0snGlue59 : ∀ x ∈ Icc ((q0snBd.getD 59 0 : ℚ) : ℝ) ((q0snBd.getD 60 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB059Bound x hx
theorem q0snGlue60 : ∀ x ∈ Icc ((q0snBd.getD 60 0 : ℚ) : ℝ) ((q0snBd.getD 61 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB060Bound x hx
theorem q0snGlue61 : ∀ x ∈ Icc ((q0snBd.getD 61 0 : ℚ) : ℝ) ((q0snBd.getD 62 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB061Bound x hx
theorem q0snGlue62 : ∀ x ∈ Icc ((q0snBd.getD 62 0 : ℚ) : ℝ) ((q0snBd.getD 63 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB062Bound x hx
theorem q0snGlue63 : ∀ x ∈ Icc ((q0snBd.getD 63 0 : ℚ) : ℝ) ((q0snBd.getD 64 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB063Bound x hx
theorem q0snGlue64 : ∀ x ∈ Icc ((q0snBd.getD 64 0 : ℚ) : ℝ) ((q0snBd.getD 65 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB064Bound x hx
theorem q0snGlue65 : ∀ x ∈ Icc ((q0snBd.getD 65 0 : ℚ) : ℝ) ((q0snBd.getD 66 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB065Bound x hx
theorem q0snGlue66 : ∀ x ∈ Icc ((q0snBd.getD 66 0 : ℚ) : ℝ) ((q0snBd.getD 67 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB066Bound x hx
theorem q0snGlue67 : ∀ x ∈ Icc ((q0snBd.getD 67 0 : ℚ) : ℝ) ((q0snBd.getD 68 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB067Bound x hx
theorem q0snGlue68 : ∀ x ∈ Icc ((q0snBd.getD 68 0 : ℚ) : ℝ) ((q0snBd.getD 69 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB068Bound x hx
theorem q0snGlue69 : ∀ x ∈ Icc ((q0snBd.getD 69 0 : ℚ) : ℝ) ((q0snBd.getD 70 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB069Bound x hx
theorem q0snGlue70 : ∀ x ∈ Icc ((q0snBd.getD 70 0 : ℚ) : ℝ) ((q0snBd.getD 71 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB070Bound x hx
theorem q0snGlue71 : ∀ x ∈ Icc ((q0snBd.getD 71 0 : ℚ) : ℝ) ((q0snBd.getD 72 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB071Bound x hx
theorem q0snGlue72 : ∀ x ∈ Icc ((q0snBd.getD 72 0 : ℚ) : ℝ) ((q0snBd.getD 73 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB072Bound x hx
theorem q0snGlue73 : ∀ x ∈ Icc ((q0snBd.getD 73 0 : ℚ) : ℝ) ((q0snBd.getD 74 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE073Full x hx
theorem q0snGlue74 : ∀ x ∈ Icc ((q0snBd.getD 74 0 : ℚ) : ℝ) ((q0snBd.getD 75 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB074Bound x hx
theorem q0snGlue75 : ∀ x ∈ Icc ((q0snBd.getD 75 0 : ℚ) : ℝ) ((q0snBd.getD 76 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB075Bound x hx
theorem q0snGlue76 : ∀ x ∈ Icc ((q0snBd.getD 76 0 : ℚ) : ℝ) ((q0snBd.getD 77 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB076Bound x hx
theorem q0snGlue77 : ∀ x ∈ Icc ((q0snBd.getD 77 0 : ℚ) : ℝ) ((q0snBd.getD 78 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB077Bound x hx
theorem q0snGlue78 : ∀ x ∈ Icc ((q0snBd.getD 78 0 : ℚ) : ℝ) ((q0snBd.getD 79 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB078Bound x hx
theorem q0snGlue79 : ∀ x ∈ Icc ((q0snBd.getD 79 0 : ℚ) : ℝ) ((q0snBd.getD 80 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE079Full x hx
theorem q0snGlue80 : ∀ x ∈ Icc ((q0snBd.getD 80 0 : ℚ) : ℝ) ((q0snBd.getD 81 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB080Bound x hx
theorem q0snGlue81 : ∀ x ∈ Icc ((q0snBd.getD 81 0 : ℚ) : ℝ) ((q0snBd.getD 82 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB081Bound x hx
theorem q0snGlue82 : ∀ x ∈ Icc ((q0snBd.getD 82 0 : ℚ) : ℝ) ((q0snBd.getD 83 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB082Bound x hx
theorem q0snGlue83 : ∀ x ∈ Icc ((q0snBd.getD 83 0 : ℚ) : ℝ) ((q0snBd.getD 84 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB083Bound x hx
theorem q0snGlue84 : ∀ x ∈ Icc ((q0snBd.getD 84 0 : ℚ) : ℝ) ((q0snBd.getD 85 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB084Bound x hx
theorem q0snGlue85 : ∀ x ∈ Icc ((q0snBd.getD 85 0 : ℚ) : ℝ) ((q0snBd.getD 86 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB085Bound x hx
theorem q0snGlue86 : ∀ x ∈ Icc ((q0snBd.getD 86 0 : ℚ) : ℝ) ((q0snBd.getD 87 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB086Bound x hx
theorem q0snGlue87 : ∀ x ∈ Icc ((q0snBd.getD 87 0 : ℚ) : ℝ) ((q0snBd.getD 88 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB087Bound x hx
theorem q0snGlue88 : ∀ x ∈ Icc ((q0snBd.getD 88 0 : ℚ) : ℝ) ((q0snBd.getD 89 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB088Bound x hx
theorem q0snGlue89 : ∀ x ∈ Icc ((q0snBd.getD 89 0 : ℚ) : ℝ) ((q0snBd.getD 90 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB089Bound x hx
theorem q0snGlue90 : ∀ x ∈ Icc ((q0snBd.getD 90 0 : ℚ) : ℝ) ((q0snBd.getD 91 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB090Bound x hx
theorem q0snGlue91 : ∀ x ∈ Icc ((q0snBd.getD 91 0 : ℚ) : ℝ) ((q0snBd.getD 92 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB091Bound x hx
theorem q0snGlue92 : ∀ x ∈ Icc ((q0snBd.getD 92 0 : ℚ) : ℝ) ((q0snBd.getD 93 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB092Bound x hx
theorem q0snGlue93 : ∀ x ∈ Icc ((q0snBd.getD 93 0 : ℚ) : ℝ) ((q0snBd.getD 94 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB093Bound x hx
theorem q0snGlue94 : ∀ x ∈ Icc ((q0snBd.getD 94 0 : ℚ) : ℝ) ((q0snBd.getD 95 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE094Full x hx
theorem q0snGlue95 : ∀ x ∈ Icc ((q0snBd.getD 95 0 : ℚ) : ℝ) ((q0snBd.getD 96 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB095Bound x hx
theorem q0snGlue96 : ∀ x ∈ Icc ((q0snBd.getD 96 0 : ℚ) : ℝ) ((q0snBd.getD 97 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx hA hB => q0snE096Unif x hx (by rw [q0snE096Eq]; exact hB)
theorem q0snGlueAll : ∀ x ∈ Icc ((q0snBd.getD 0 0 : ℚ) : ℝ) ((q0snBd.getD 97 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 97 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0snGlue0) q0snGlue1) q0snGlue2) q0snGlue3) q0snGlue4) q0snGlue5) q0snGlue6) q0snGlue7) q0snGlue8) q0snGlue9) q0snGlue10) q0snGlue11) q0snGlue12) q0snGlue13) q0snGlue14) q0snGlue15) q0snGlue16) q0snGlue17) q0snGlue18) q0snGlue19) q0snGlue20) q0snGlue21) q0snGlue22) q0snGlue23) q0snGlue24) q0snGlue25) q0snGlue26) q0snGlue27) q0snGlue28) q0snGlue29) q0snGlue30) q0snGlue31) q0snGlue32) q0snGlue33) q0snGlue34) q0snGlue35) q0snGlue36) q0snGlue37) q0snGlue38) q0snGlue39) q0snGlue40) q0snGlue41) q0snGlue42) q0snGlue43) q0snGlue44) q0snGlue45) q0snGlue46) q0snGlue47) q0snGlue48) q0snGlue49) q0snGlue50) q0snGlue51) q0snGlue52) q0snGlue53) q0snGlue54) q0snGlue55) q0snGlue56) q0snGlue57) q0snGlue58) q0snGlue59) q0snGlue60) q0snGlue61) q0snGlue62) q0snGlue63) q0snGlue64) q0snGlue65) q0snGlue66) q0snGlue67) q0snGlue68) q0snGlue69) q0snGlue70) q0snGlue71) q0snGlue72) q0snGlue73) q0snGlue74) q0snGlue75) q0snGlue76) q0snGlue77) q0snGlue78) q0snGlue79) q0snGlue80) q0snGlue81) q0snGlue82) q0snGlue83) q0snGlue84) q0snGlue85) q0snGlue86) q0snGlue87) q0snGlue88) q0snGlue89) q0snGlue90) q0snGlue91) q0snGlue92) q0snGlue93) q0snGlue94) q0snGlue95) q0snGlue96
/-- **Sup statement (SN, alpha = 0.0).** -/
theorem q0snSup : ∀ x ∈ Ioo ((q0snBd.getD 0 0 : ℚ) : ℝ) ((q0snBd.getD 97 0 : ℚ) : ℝ), fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx => q0snGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
