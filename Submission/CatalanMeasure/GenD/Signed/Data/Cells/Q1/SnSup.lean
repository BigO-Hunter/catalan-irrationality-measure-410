module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE052
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP015
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE072
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP016
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP017
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP018
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE080
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP019
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP020
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP021
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP022
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP023
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE095
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP024
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP025
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP026
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE103
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP027
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP028
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnP029
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE117

@[expose] public section

/-! **SN, alpha = 0.005: the sup statement.**  `fieldTower q1snFq ... x <= q1snT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.738056127246, K = -18.926240532999 (NOTES-TRIAL; kappa_old = -18.926240532999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q1snGlue0 : ∀ x ∈ Icc ((q1snBd.getD 0 0 : ℚ) : ℝ) ((q1snBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE000Full x hx
theorem q1snGlue1 : ∀ x ∈ Icc ((q1snBd.getD 1 0 : ℚ) : ℝ) ((q1snBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB001Bound x hx
theorem q1snGlue2 : ∀ x ∈ Icc ((q1snBd.getD 2 0 : ℚ) : ℝ) ((q1snBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB002Bound x hx
theorem q1snGlue3 : ∀ x ∈ Icc ((q1snBd.getD 3 0 : ℚ) : ℝ) ((q1snBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB003Bound x hx
theorem q1snGlue4 : ∀ x ∈ Icc ((q1snBd.getD 4 0 : ℚ) : ℝ) ((q1snBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB004Bound x hx
theorem q1snGlue5 : ∀ x ∈ Icc ((q1snBd.getD 5 0 : ℚ) : ℝ) ((q1snBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB005Bound x hx
theorem q1snGlue6 : ∀ x ∈ Icc ((q1snBd.getD 6 0 : ℚ) : ℝ) ((q1snBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB006Bound x hx
theorem q1snGlue7 : ∀ x ∈ Icc ((q1snBd.getD 7 0 : ℚ) : ℝ) ((q1snBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB007Bound x hx
theorem q1snGlue8 : ∀ x ∈ Icc ((q1snBd.getD 8 0 : ℚ) : ℝ) ((q1snBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB008Bound x hx
theorem q1snGlue9 : ∀ x ∈ Icc ((q1snBd.getD 9 0 : ℚ) : ℝ) ((q1snBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB009Bound x hx
theorem q1snGlue10 : ∀ x ∈ Icc ((q1snBd.getD 10 0 : ℚ) : ℝ) ((q1snBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB010Bound x hx
theorem q1snGlue11 : ∀ x ∈ Icc ((q1snBd.getD 11 0 : ℚ) : ℝ) ((q1snBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB011Bound x hx
theorem q1snGlue12 : ∀ x ∈ Icc ((q1snBd.getD 12 0 : ℚ) : ℝ) ((q1snBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB012Bound x hx
theorem q1snGlue13 : ∀ x ∈ Icc ((q1snBd.getD 13 0 : ℚ) : ℝ) ((q1snBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB013Bound x hx
theorem q1snGlue14 : ∀ x ∈ Icc ((q1snBd.getD 14 0 : ℚ) : ℝ) ((q1snBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB014Bound x hx
theorem q1snGlue15 : ∀ x ∈ Icc ((q1snBd.getD 15 0 : ℚ) : ℝ) ((q1snBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB015Bound x hx
theorem q1snGlue16 : ∀ x ∈ Icc ((q1snBd.getD 16 0 : ℚ) : ℝ) ((q1snBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB016Bound x hx
theorem q1snGlue17 : ∀ x ∈ Icc ((q1snBd.getD 17 0 : ℚ) : ℝ) ((q1snBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB017Bound x hx
theorem q1snGlue18 : ∀ x ∈ Icc ((q1snBd.getD 18 0 : ℚ) : ℝ) ((q1snBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB018Bound x hx
theorem q1snGlue19 : ∀ x ∈ Icc ((q1snBd.getD 19 0 : ℚ) : ℝ) ((q1snBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB019Bound x hx
theorem q1snGlue20 : ∀ x ∈ Icc ((q1snBd.getD 20 0 : ℚ) : ℝ) ((q1snBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB020Bound x hx
theorem q1snGlue21 : ∀ x ∈ Icc ((q1snBd.getD 21 0 : ℚ) : ℝ) ((q1snBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB021Bound x hx
theorem q1snGlue22 : ∀ x ∈ Icc ((q1snBd.getD 22 0 : ℚ) : ℝ) ((q1snBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB022Bound x hx
theorem q1snGlue23 : ∀ x ∈ Icc ((q1snBd.getD 23 0 : ℚ) : ℝ) ((q1snBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB023Bound x hx
theorem q1snGlue24 : ∀ x ∈ Icc ((q1snBd.getD 24 0 : ℚ) : ℝ) ((q1snBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB024Bound x hx
theorem q1snGlue25 : ∀ x ∈ Icc ((q1snBd.getD 25 0 : ℚ) : ℝ) ((q1snBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB025Bound x hx
theorem q1snGlue26 : ∀ x ∈ Icc ((q1snBd.getD 26 0 : ℚ) : ℝ) ((q1snBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB026Bound x hx
theorem q1snGlue27 : ∀ x ∈ Icc ((q1snBd.getD 27 0 : ℚ) : ℝ) ((q1snBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB027Bound x hx
theorem q1snGlue28 : ∀ x ∈ Icc ((q1snBd.getD 28 0 : ℚ) : ℝ) ((q1snBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB028Bound x hx
theorem q1snGlue29 : ∀ x ∈ Icc ((q1snBd.getD 29 0 : ℚ) : ℝ) ((q1snBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB029Bound x hx
theorem q1snGlue30 : ∀ x ∈ Icc ((q1snBd.getD 30 0 : ℚ) : ℝ) ((q1snBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB030Bound x hx
theorem q1snGlue31 : ∀ x ∈ Icc ((q1snBd.getD 31 0 : ℚ) : ℝ) ((q1snBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB031Bound x hx
theorem q1snGlue32 : ∀ x ∈ Icc ((q1snBd.getD 32 0 : ℚ) : ℝ) ((q1snBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB032Bound x hx
theorem q1snGlue33 : ∀ x ∈ Icc ((q1snBd.getD 33 0 : ℚ) : ℝ) ((q1snBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB033Bound x hx
theorem q1snGlue34 : ∀ x ∈ Icc ((q1snBd.getD 34 0 : ℚ) : ℝ) ((q1snBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB034Bound x hx
theorem q1snGlue35 : ∀ x ∈ Icc ((q1snBd.getD 35 0 : ℚ) : ℝ) ((q1snBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB035Bound x hx
theorem q1snGlue36 : ∀ x ∈ Icc ((q1snBd.getD 36 0 : ℚ) : ℝ) ((q1snBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB036Bound x hx
theorem q1snGlue37 : ∀ x ∈ Icc ((q1snBd.getD 37 0 : ℚ) : ℝ) ((q1snBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB037Bound x hx
theorem q1snGlue38 : ∀ x ∈ Icc ((q1snBd.getD 38 0 : ℚ) : ℝ) ((q1snBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB038Bound x hx
theorem q1snGlue39 : ∀ x ∈ Icc ((q1snBd.getD 39 0 : ℚ) : ℝ) ((q1snBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB039Bound x hx
theorem q1snGlue40 : ∀ x ∈ Icc ((q1snBd.getD 40 0 : ℚ) : ℝ) ((q1snBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB040Bound x hx
theorem q1snGlue41 : ∀ x ∈ Icc ((q1snBd.getD 41 0 : ℚ) : ℝ) ((q1snBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB041Bound x hx
theorem q1snGlue42 : ∀ x ∈ Icc ((q1snBd.getD 42 0 : ℚ) : ℝ) ((q1snBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB042Bound x hx
theorem q1snGlue43 : ∀ x ∈ Icc ((q1snBd.getD 43 0 : ℚ) : ℝ) ((q1snBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB043Bound x hx
theorem q1snGlue44 : ∀ x ∈ Icc ((q1snBd.getD 44 0 : ℚ) : ℝ) ((q1snBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB044Bound x hx
theorem q1snGlue45 : ∀ x ∈ Icc ((q1snBd.getD 45 0 : ℚ) : ℝ) ((q1snBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB045Bound x hx
theorem q1snGlue46 : ∀ x ∈ Icc ((q1snBd.getD 46 0 : ℚ) : ℝ) ((q1snBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB046Bound x hx
theorem q1snGlue47 : ∀ x ∈ Icc ((q1snBd.getD 47 0 : ℚ) : ℝ) ((q1snBd.getD 48 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB047Bound x hx
theorem q1snGlue48 : ∀ x ∈ Icc ((q1snBd.getD 48 0 : ℚ) : ℝ) ((q1snBd.getD 49 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB048Bound x hx
theorem q1snGlue49 : ∀ x ∈ Icc ((q1snBd.getD 49 0 : ℚ) : ℝ) ((q1snBd.getD 50 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB049Bound x hx
theorem q1snGlue50 : ∀ x ∈ Icc ((q1snBd.getD 50 0 : ℚ) : ℝ) ((q1snBd.getD 51 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB050Bound x hx
theorem q1snGlue51 : ∀ x ∈ Icc ((q1snBd.getD 51 0 : ℚ) : ℝ) ((q1snBd.getD 52 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB051Bound x hx
theorem q1snGlue52 : ∀ x ∈ Icc ((q1snBd.getD 52 0 : ℚ) : ℝ) ((q1snBd.getD 53 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE052Full x hx
theorem q1snGlue53 : ∀ x ∈ Icc ((q1snBd.getD 53 0 : ℚ) : ℝ) ((q1snBd.getD 54 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB053Bound x hx
theorem q1snGlue54 : ∀ x ∈ Icc ((q1snBd.getD 54 0 : ℚ) : ℝ) ((q1snBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB054Bound x hx
theorem q1snGlue55 : ∀ x ∈ Icc ((q1snBd.getD 55 0 : ℚ) : ℝ) ((q1snBd.getD 56 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB055Bound x hx
theorem q1snGlue56 : ∀ x ∈ Icc ((q1snBd.getD 56 0 : ℚ) : ℝ) ((q1snBd.getD 57 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB056Bound x hx
theorem q1snGlue57 : ∀ x ∈ Icc ((q1snBd.getD 57 0 : ℚ) : ℝ) ((q1snBd.getD 58 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB057Bound x hx
theorem q1snGlue58 : ∀ x ∈ Icc ((q1snBd.getD 58 0 : ℚ) : ℝ) ((q1snBd.getD 59 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB058Bound x hx
theorem q1snGlue59 : ∀ x ∈ Icc ((q1snBd.getD 59 0 : ℚ) : ℝ) ((q1snBd.getD 60 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB059Bound x hx
theorem q1snGlue60 : ∀ x ∈ Icc ((q1snBd.getD 60 0 : ℚ) : ℝ) ((q1snBd.getD 61 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB060Bound x hx
theorem q1snGlue61 : ∀ x ∈ Icc ((q1snBd.getD 61 0 : ℚ) : ℝ) ((q1snBd.getD 62 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB061Bound x hx
theorem q1snGlue62 : ∀ x ∈ Icc ((q1snBd.getD 62 0 : ℚ) : ℝ) ((q1snBd.getD 63 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB062Bound x hx
theorem q1snGlue63 : ∀ x ∈ Icc ((q1snBd.getD 63 0 : ℚ) : ℝ) ((q1snBd.getD 64 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB063Bound x hx
theorem q1snGlue64 : ∀ x ∈ Icc ((q1snBd.getD 64 0 : ℚ) : ℝ) ((q1snBd.getD 65 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB064Bound x hx
theorem q1snGlue65 : ∀ x ∈ Icc ((q1snBd.getD 65 0 : ℚ) : ℝ) ((q1snBd.getD 66 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB065Bound x hx
theorem q1snGlue66 : ∀ x ∈ Icc ((q1snBd.getD 66 0 : ℚ) : ℝ) ((q1snBd.getD 67 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB066Bound x hx
theorem q1snGlue67 : ∀ x ∈ Icc ((q1snBd.getD 67 0 : ℚ) : ℝ) ((q1snBd.getD 68 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB067Bound x hx
theorem q1snGlue68 : ∀ x ∈ Icc ((q1snBd.getD 68 0 : ℚ) : ℝ) ((q1snBd.getD 69 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB068Bound x hx
theorem q1snGlue69 : ∀ x ∈ Icc ((q1snBd.getD 69 0 : ℚ) : ℝ) ((q1snBd.getD 70 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB069Bound x hx
theorem q1snGlue70 : ∀ x ∈ Icc ((q1snBd.getD 70 0 : ℚ) : ℝ) ((q1snBd.getD 71 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB070Bound x hx
theorem q1snGlue71 : ∀ x ∈ Icc ((q1snBd.getD 71 0 : ℚ) : ℝ) ((q1snBd.getD 72 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB071Bound x hx
theorem q1snGlue72 : ∀ x ∈ Icc ((q1snBd.getD 72 0 : ℚ) : ℝ) ((q1snBd.getD 73 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE072Full x hx
theorem q1snGlue73 : ∀ x ∈ Icc ((q1snBd.getD 73 0 : ℚ) : ℝ) ((q1snBd.getD 74 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB073Bound x hx
theorem q1snGlue74 : ∀ x ∈ Icc ((q1snBd.getD 74 0 : ℚ) : ℝ) ((q1snBd.getD 75 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB074Bound x hx
theorem q1snGlue75 : ∀ x ∈ Icc ((q1snBd.getD 75 0 : ℚ) : ℝ) ((q1snBd.getD 76 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB075Bound x hx
theorem q1snGlue76 : ∀ x ∈ Icc ((q1snBd.getD 76 0 : ℚ) : ℝ) ((q1snBd.getD 77 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB076Bound x hx
theorem q1snGlue77 : ∀ x ∈ Icc ((q1snBd.getD 77 0 : ℚ) : ℝ) ((q1snBd.getD 78 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB077Bound x hx
theorem q1snGlue78 : ∀ x ∈ Icc ((q1snBd.getD 78 0 : ℚ) : ℝ) ((q1snBd.getD 79 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB078Bound x hx
theorem q1snGlue79 : ∀ x ∈ Icc ((q1snBd.getD 79 0 : ℚ) : ℝ) ((q1snBd.getD 80 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB079Bound x hx
theorem q1snGlue80 : ∀ x ∈ Icc ((q1snBd.getD 80 0 : ℚ) : ℝ) ((q1snBd.getD 81 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE080Full x hx
theorem q1snGlue81 : ∀ x ∈ Icc ((q1snBd.getD 81 0 : ℚ) : ℝ) ((q1snBd.getD 82 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB081Bound x hx
theorem q1snGlue82 : ∀ x ∈ Icc ((q1snBd.getD 82 0 : ℚ) : ℝ) ((q1snBd.getD 83 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB082Bound x hx
theorem q1snGlue83 : ∀ x ∈ Icc ((q1snBd.getD 83 0 : ℚ) : ℝ) ((q1snBd.getD 84 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB083Bound x hx
theorem q1snGlue84 : ∀ x ∈ Icc ((q1snBd.getD 84 0 : ℚ) : ℝ) ((q1snBd.getD 85 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB084Bound x hx
theorem q1snGlue85 : ∀ x ∈ Icc ((q1snBd.getD 85 0 : ℚ) : ℝ) ((q1snBd.getD 86 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB085Bound x hx
theorem q1snGlue86 : ∀ x ∈ Icc ((q1snBd.getD 86 0 : ℚ) : ℝ) ((q1snBd.getD 87 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB086Bound x hx
theorem q1snGlue87 : ∀ x ∈ Icc ((q1snBd.getD 87 0 : ℚ) : ℝ) ((q1snBd.getD 88 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB087Bound x hx
theorem q1snGlue88 : ∀ x ∈ Icc ((q1snBd.getD 88 0 : ℚ) : ℝ) ((q1snBd.getD 89 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB088Bound x hx
theorem q1snGlue89 : ∀ x ∈ Icc ((q1snBd.getD 89 0 : ℚ) : ℝ) ((q1snBd.getD 90 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB089Bound x hx
theorem q1snGlue90 : ∀ x ∈ Icc ((q1snBd.getD 90 0 : ℚ) : ℝ) ((q1snBd.getD 91 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB090Bound x hx
theorem q1snGlue91 : ∀ x ∈ Icc ((q1snBd.getD 91 0 : ℚ) : ℝ) ((q1snBd.getD 92 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB091Bound x hx
theorem q1snGlue92 : ∀ x ∈ Icc ((q1snBd.getD 92 0 : ℚ) : ℝ) ((q1snBd.getD 93 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB092Bound x hx
theorem q1snGlue93 : ∀ x ∈ Icc ((q1snBd.getD 93 0 : ℚ) : ℝ) ((q1snBd.getD 94 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB093Bound x hx
theorem q1snGlue94 : ∀ x ∈ Icc ((q1snBd.getD 94 0 : ℚ) : ℝ) ((q1snBd.getD 95 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB094Bound x hx
theorem q1snGlue95 : ∀ x ∈ Icc ((q1snBd.getD 95 0 : ℚ) : ℝ) ((q1snBd.getD 96 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE095Full x hx
theorem q1snGlue96 : ∀ x ∈ Icc ((q1snBd.getD 96 0 : ℚ) : ℝ) ((q1snBd.getD 97 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB096Bound x hx
theorem q1snGlue97 : ∀ x ∈ Icc ((q1snBd.getD 97 0 : ℚ) : ℝ) ((q1snBd.getD 98 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB097Bound x hx
theorem q1snGlue98 : ∀ x ∈ Icc ((q1snBd.getD 98 0 : ℚ) : ℝ) ((q1snBd.getD 99 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB098Bound x hx
theorem q1snGlue99 : ∀ x ∈ Icc ((q1snBd.getD 99 0 : ℚ) : ℝ) ((q1snBd.getD 100 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB099Bound x hx
theorem q1snGlue100 : ∀ x ∈ Icc ((q1snBd.getD 100 0 : ℚ) : ℝ) ((q1snBd.getD 101 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB100Bound x hx
theorem q1snGlue101 : ∀ x ∈ Icc ((q1snBd.getD 101 0 : ℚ) : ℝ) ((q1snBd.getD 102 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB101Bound x hx
theorem q1snGlue102 : ∀ x ∈ Icc ((q1snBd.getD 102 0 : ℚ) : ℝ) ((q1snBd.getD 103 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB102Bound x hx
theorem q1snGlue103 : ∀ x ∈ Icc ((q1snBd.getD 103 0 : ℚ) : ℝ) ((q1snBd.getD 104 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE103Full x hx
theorem q1snGlue104 : ∀ x ∈ Icc ((q1snBd.getD 104 0 : ℚ) : ℝ) ((q1snBd.getD 105 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB104Bound x hx
theorem q1snGlue105 : ∀ x ∈ Icc ((q1snBd.getD 105 0 : ℚ) : ℝ) ((q1snBd.getD 106 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB105Bound x hx
theorem q1snGlue106 : ∀ x ∈ Icc ((q1snBd.getD 106 0 : ℚ) : ℝ) ((q1snBd.getD 107 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB106Bound x hx
theorem q1snGlue107 : ∀ x ∈ Icc ((q1snBd.getD 107 0 : ℚ) : ℝ) ((q1snBd.getD 108 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB107Bound x hx
theorem q1snGlue108 : ∀ x ∈ Icc ((q1snBd.getD 108 0 : ℚ) : ℝ) ((q1snBd.getD 109 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB108Bound x hx
theorem q1snGlue109 : ∀ x ∈ Icc ((q1snBd.getD 109 0 : ℚ) : ℝ) ((q1snBd.getD 110 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB109Bound x hx
theorem q1snGlue110 : ∀ x ∈ Icc ((q1snBd.getD 110 0 : ℚ) : ℝ) ((q1snBd.getD 111 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB110Bound x hx
theorem q1snGlue111 : ∀ x ∈ Icc ((q1snBd.getD 111 0 : ℚ) : ℝ) ((q1snBd.getD 112 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB111Bound x hx
theorem q1snGlue112 : ∀ x ∈ Icc ((q1snBd.getD 112 0 : ℚ) : ℝ) ((q1snBd.getD 113 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB112Bound x hx
theorem q1snGlue113 : ∀ x ∈ Icc ((q1snBd.getD 113 0 : ℚ) : ℝ) ((q1snBd.getD 114 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB113Bound x hx
theorem q1snGlue114 : ∀ x ∈ Icc ((q1snBd.getD 114 0 : ℚ) : ℝ) ((q1snBd.getD 115 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB114Bound x hx
theorem q1snGlue115 : ∀ x ∈ Icc ((q1snBd.getD 115 0 : ℚ) : ℝ) ((q1snBd.getD 116 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB115Bound x hx
theorem q1snGlue116 : ∀ x ∈ Icc ((q1snBd.getD 116 0 : ℚ) : ℝ) ((q1snBd.getD 117 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB116Bound x hx
theorem q1snGlue117 : ∀ x ∈ Icc ((q1snBd.getD 117 0 : ℚ) : ℝ) ((q1snBd.getD 118 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx hA hB => q1snE117Unif x hx (by rw [q1snE117Eq]; exact hB)
theorem q1snGlueAll : ∀ x ∈ Icc ((q1snBd.getD 0 0 : ℚ) : ℝ) ((q1snBd.getD 118 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 118 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1snGlue0) q1snGlue1) q1snGlue2) q1snGlue3) q1snGlue4) q1snGlue5) q1snGlue6) q1snGlue7) q1snGlue8) q1snGlue9) q1snGlue10) q1snGlue11) q1snGlue12) q1snGlue13) q1snGlue14) q1snGlue15) q1snGlue16) q1snGlue17) q1snGlue18) q1snGlue19) q1snGlue20) q1snGlue21) q1snGlue22) q1snGlue23) q1snGlue24) q1snGlue25) q1snGlue26) q1snGlue27) q1snGlue28) q1snGlue29) q1snGlue30) q1snGlue31) q1snGlue32) q1snGlue33) q1snGlue34) q1snGlue35) q1snGlue36) q1snGlue37) q1snGlue38) q1snGlue39) q1snGlue40) q1snGlue41) q1snGlue42) q1snGlue43) q1snGlue44) q1snGlue45) q1snGlue46) q1snGlue47) q1snGlue48) q1snGlue49) q1snGlue50) q1snGlue51) q1snGlue52) q1snGlue53) q1snGlue54) q1snGlue55) q1snGlue56) q1snGlue57) q1snGlue58) q1snGlue59) q1snGlue60) q1snGlue61) q1snGlue62) q1snGlue63) q1snGlue64) q1snGlue65) q1snGlue66) q1snGlue67) q1snGlue68) q1snGlue69) q1snGlue70) q1snGlue71) q1snGlue72) q1snGlue73) q1snGlue74) q1snGlue75) q1snGlue76) q1snGlue77) q1snGlue78) q1snGlue79) q1snGlue80) q1snGlue81) q1snGlue82) q1snGlue83) q1snGlue84) q1snGlue85) q1snGlue86) q1snGlue87) q1snGlue88) q1snGlue89) q1snGlue90) q1snGlue91) q1snGlue92) q1snGlue93) q1snGlue94) q1snGlue95) q1snGlue96) q1snGlue97) q1snGlue98) q1snGlue99) q1snGlue100) q1snGlue101) q1snGlue102) q1snGlue103) q1snGlue104) q1snGlue105) q1snGlue106) q1snGlue107) q1snGlue108) q1snGlue109) q1snGlue110) q1snGlue111) q1snGlue112) q1snGlue113) q1snGlue114) q1snGlue115) q1snGlue116) q1snGlue117
/-- **Sup statement (SN, alpha = 0.005).** -/
theorem q1snSup : ∀ x ∈ Ioo ((q1snBd.getD 0 0 : ℚ) : ℝ) ((q1snBd.getD 118 0 : ℚ) : ℝ), fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx => q1snGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
