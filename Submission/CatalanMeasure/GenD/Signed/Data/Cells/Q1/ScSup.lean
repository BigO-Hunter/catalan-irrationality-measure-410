module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScP013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q1.ScE041

@[expose] public section

/-! **SC, alpha = 0.005: the sup statement.**  `fieldTower q1scFq ... x <= q1scT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.561979008517, K = 14.899936356001 (NOTES-TRIAL; kappa_old = 14.899936356001). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q1scGlue0 : ∀ x ∈ Icc ((q1scBd.getD 0 0 : ℚ) : ℝ) ((q1scBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx hA hB => q1scE000Unif x hx (by rw [q1scE000Eq]; exact hA)
theorem q1scGlue1 : ∀ x ∈ Icc ((q1scBd.getD 1 0 : ℚ) : ℝ) ((q1scBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB001Bound x hx
theorem q1scGlue2 : ∀ x ∈ Icc ((q1scBd.getD 2 0 : ℚ) : ℝ) ((q1scBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB002Bound x hx
theorem q1scGlue3 : ∀ x ∈ Icc ((q1scBd.getD 3 0 : ℚ) : ℝ) ((q1scBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB003Bound x hx
theorem q1scGlue4 : ∀ x ∈ Icc ((q1scBd.getD 4 0 : ℚ) : ℝ) ((q1scBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB004Bound x hx
theorem q1scGlue5 : ∀ x ∈ Icc ((q1scBd.getD 5 0 : ℚ) : ℝ) ((q1scBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB005Bound x hx
theorem q1scGlue6 : ∀ x ∈ Icc ((q1scBd.getD 6 0 : ℚ) : ℝ) ((q1scBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB006Bound x hx
theorem q1scGlue7 : ∀ x ∈ Icc ((q1scBd.getD 7 0 : ℚ) : ℝ) ((q1scBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB007Bound x hx
theorem q1scGlue8 : ∀ x ∈ Icc ((q1scBd.getD 8 0 : ℚ) : ℝ) ((q1scBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB008Bound x hx
theorem q1scGlue9 : ∀ x ∈ Icc ((q1scBd.getD 9 0 : ℚ) : ℝ) ((q1scBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB009Bound x hx
theorem q1scGlue10 : ∀ x ∈ Icc ((q1scBd.getD 10 0 : ℚ) : ℝ) ((q1scBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB010Bound x hx
theorem q1scGlue11 : ∀ x ∈ Icc ((q1scBd.getD 11 0 : ℚ) : ℝ) ((q1scBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB011Bound x hx
theorem q1scGlue12 : ∀ x ∈ Icc ((q1scBd.getD 12 0 : ℚ) : ℝ) ((q1scBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB012Bound x hx
theorem q1scGlue13 : ∀ x ∈ Icc ((q1scBd.getD 13 0 : ℚ) : ℝ) ((q1scBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB013Bound x hx
theorem q1scGlue14 : ∀ x ∈ Icc ((q1scBd.getD 14 0 : ℚ) : ℝ) ((q1scBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB014Bound x hx
theorem q1scGlue15 : ∀ x ∈ Icc ((q1scBd.getD 15 0 : ℚ) : ℝ) ((q1scBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB015Bound x hx
theorem q1scGlue16 : ∀ x ∈ Icc ((q1scBd.getD 16 0 : ℚ) : ℝ) ((q1scBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB016Bound x hx
theorem q1scGlue17 : ∀ x ∈ Icc ((q1scBd.getD 17 0 : ℚ) : ℝ) ((q1scBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB017Bound x hx
theorem q1scGlue18 : ∀ x ∈ Icc ((q1scBd.getD 18 0 : ℚ) : ℝ) ((q1scBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB018Bound x hx
theorem q1scGlue19 : ∀ x ∈ Icc ((q1scBd.getD 19 0 : ℚ) : ℝ) ((q1scBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB019Bound x hx
theorem q1scGlue20 : ∀ x ∈ Icc ((q1scBd.getD 20 0 : ℚ) : ℝ) ((q1scBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB020Bound x hx
theorem q1scGlue21 : ∀ x ∈ Icc ((q1scBd.getD 21 0 : ℚ) : ℝ) ((q1scBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB021Bound x hx
theorem q1scGlue22 : ∀ x ∈ Icc ((q1scBd.getD 22 0 : ℚ) : ℝ) ((q1scBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB022Bound x hx
theorem q1scGlue23 : ∀ x ∈ Icc ((q1scBd.getD 23 0 : ℚ) : ℝ) ((q1scBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB023Bound x hx
theorem q1scGlue24 : ∀ x ∈ Icc ((q1scBd.getD 24 0 : ℚ) : ℝ) ((q1scBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB024Bound x hx
theorem q1scGlue25 : ∀ x ∈ Icc ((q1scBd.getD 25 0 : ℚ) : ℝ) ((q1scBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB025Bound x hx
theorem q1scGlue26 : ∀ x ∈ Icc ((q1scBd.getD 26 0 : ℚ) : ℝ) ((q1scBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB026Bound x hx
theorem q1scGlue27 : ∀ x ∈ Icc ((q1scBd.getD 27 0 : ℚ) : ℝ) ((q1scBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB027Bound x hx
theorem q1scGlue28 : ∀ x ∈ Icc ((q1scBd.getD 28 0 : ℚ) : ℝ) ((q1scBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB028Bound x hx
theorem q1scGlue29 : ∀ x ∈ Icc ((q1scBd.getD 29 0 : ℚ) : ℝ) ((q1scBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB029Bound x hx
theorem q1scGlue30 : ∀ x ∈ Icc ((q1scBd.getD 30 0 : ℚ) : ℝ) ((q1scBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB030Bound x hx
theorem q1scGlue31 : ∀ x ∈ Icc ((q1scBd.getD 31 0 : ℚ) : ℝ) ((q1scBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB031Bound x hx
theorem q1scGlue32 : ∀ x ∈ Icc ((q1scBd.getD 32 0 : ℚ) : ℝ) ((q1scBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB032Bound x hx
theorem q1scGlue33 : ∀ x ∈ Icc ((q1scBd.getD 33 0 : ℚ) : ℝ) ((q1scBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB033Bound x hx
theorem q1scGlue34 : ∀ x ∈ Icc ((q1scBd.getD 34 0 : ℚ) : ℝ) ((q1scBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB034Bound x hx
theorem q1scGlue35 : ∀ x ∈ Icc ((q1scBd.getD 35 0 : ℚ) : ℝ) ((q1scBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB035Bound x hx
theorem q1scGlue36 : ∀ x ∈ Icc ((q1scBd.getD 36 0 : ℚ) : ℝ) ((q1scBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB036Bound x hx
theorem q1scGlue37 : ∀ x ∈ Icc ((q1scBd.getD 37 0 : ℚ) : ℝ) ((q1scBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB037Bound x hx
theorem q1scGlue38 : ∀ x ∈ Icc ((q1scBd.getD 38 0 : ℚ) : ℝ) ((q1scBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB038Bound x hx
theorem q1scGlue39 : ∀ x ∈ Icc ((q1scBd.getD 39 0 : ℚ) : ℝ) ((q1scBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB039Bound x hx
theorem q1scGlue40 : ∀ x ∈ Icc ((q1scBd.getD 40 0 : ℚ) : ℝ) ((q1scBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx _ _ => q1scB040Bound x hx
theorem q1scGlue41 : ∀ x ∈ Icc ((q1scBd.getD 41 0 : ℚ) : ℝ) ((q1scBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx hA hB => q1scE041Unif x hx (by rw [q1scE041Eq]; exact hB)
theorem q1scGlueAll : ∀ x ∈ Icc ((q1scBd.getD 0 0 : ℚ) : ℝ) ((q1scBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q1scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1scBd.getD 42 0 : ℚ) : ℝ) → fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1scGlue0) q1scGlue1) q1scGlue2) q1scGlue3) q1scGlue4) q1scGlue5) q1scGlue6) q1scGlue7) q1scGlue8) q1scGlue9) q1scGlue10) q1scGlue11) q1scGlue12) q1scGlue13) q1scGlue14) q1scGlue15) q1scGlue16) q1scGlue17) q1scGlue18) q1scGlue19) q1scGlue20) q1scGlue21) q1scGlue22) q1scGlue23) q1scGlue24) q1scGlue25) q1scGlue26) q1scGlue27) q1scGlue28) q1scGlue29) q1scGlue30) q1scGlue31) q1scGlue32) q1scGlue33) q1scGlue34) q1scGlue35) q1scGlue36) q1scGlue37) q1scGlue38) q1scGlue39) q1scGlue40) q1scGlue41
/-- **Sup statement (SC, alpha = 0.005).** -/
theorem q1scSup : ∀ x ∈ Ioo ((q1scBd.getD 0 0 : ℚ) : ℝ) ((q1scBd.getD 42 0 : ℚ) : ℝ), fieldTower q1scFq (poleF q1scFq.poles) 0 x ≤ (q1scT : ℝ) :=
  fun x hx => q1scGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
