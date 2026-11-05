module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScP011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q2.ScE046

@[expose] public section

/-! **SC, alpha = 0.0625: the sup statement.**  `fieldTower q2scFq ... x <= q2scT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.485878649232, K = 14.899936356001 (NOTES-TRIAL; kappa_old = 14.899936356001). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q2scGlue0 : ∀ x ∈ Icc ((q2scBd.getD 0 0 : ℚ) : ℝ) ((q2scBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx hA hB => q2scE000Unif x hx (by rw [q2scE000Eq]; exact hA)
theorem q2scGlue1 : ∀ x ∈ Icc ((q2scBd.getD 1 0 : ℚ) : ℝ) ((q2scBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB001Bound x hx
theorem q2scGlue2 : ∀ x ∈ Icc ((q2scBd.getD 2 0 : ℚ) : ℝ) ((q2scBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB002Bound x hx
theorem q2scGlue3 : ∀ x ∈ Icc ((q2scBd.getD 3 0 : ℚ) : ℝ) ((q2scBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB003Bound x hx
theorem q2scGlue4 : ∀ x ∈ Icc ((q2scBd.getD 4 0 : ℚ) : ℝ) ((q2scBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB004Bound x hx
theorem q2scGlue5 : ∀ x ∈ Icc ((q2scBd.getD 5 0 : ℚ) : ℝ) ((q2scBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB005Bound x hx
theorem q2scGlue6 : ∀ x ∈ Icc ((q2scBd.getD 6 0 : ℚ) : ℝ) ((q2scBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB006Bound x hx
theorem q2scGlue7 : ∀ x ∈ Icc ((q2scBd.getD 7 0 : ℚ) : ℝ) ((q2scBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB007Bound x hx
theorem q2scGlue8 : ∀ x ∈ Icc ((q2scBd.getD 8 0 : ℚ) : ℝ) ((q2scBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB008Bound x hx
theorem q2scGlue9 : ∀ x ∈ Icc ((q2scBd.getD 9 0 : ℚ) : ℝ) ((q2scBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB009Bound x hx
theorem q2scGlue10 : ∀ x ∈ Icc ((q2scBd.getD 10 0 : ℚ) : ℝ) ((q2scBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB010Bound x hx
theorem q2scGlue11 : ∀ x ∈ Icc ((q2scBd.getD 11 0 : ℚ) : ℝ) ((q2scBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB011Bound x hx
theorem q2scGlue12 : ∀ x ∈ Icc ((q2scBd.getD 12 0 : ℚ) : ℝ) ((q2scBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB012Bound x hx
theorem q2scGlue13 : ∀ x ∈ Icc ((q2scBd.getD 13 0 : ℚ) : ℝ) ((q2scBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB013Bound x hx
theorem q2scGlue14 : ∀ x ∈ Icc ((q2scBd.getD 14 0 : ℚ) : ℝ) ((q2scBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB014Bound x hx
theorem q2scGlue15 : ∀ x ∈ Icc ((q2scBd.getD 15 0 : ℚ) : ℝ) ((q2scBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB015Bound x hx
theorem q2scGlue16 : ∀ x ∈ Icc ((q2scBd.getD 16 0 : ℚ) : ℝ) ((q2scBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB016Bound x hx
theorem q2scGlue17 : ∀ x ∈ Icc ((q2scBd.getD 17 0 : ℚ) : ℝ) ((q2scBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB017Bound x hx
theorem q2scGlue18 : ∀ x ∈ Icc ((q2scBd.getD 18 0 : ℚ) : ℝ) ((q2scBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB018Bound x hx
theorem q2scGlue19 : ∀ x ∈ Icc ((q2scBd.getD 19 0 : ℚ) : ℝ) ((q2scBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB019Bound x hx
theorem q2scGlue20 : ∀ x ∈ Icc ((q2scBd.getD 20 0 : ℚ) : ℝ) ((q2scBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB020Bound x hx
theorem q2scGlue21 : ∀ x ∈ Icc ((q2scBd.getD 21 0 : ℚ) : ℝ) ((q2scBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB021Bound x hx
theorem q2scGlue22 : ∀ x ∈ Icc ((q2scBd.getD 22 0 : ℚ) : ℝ) ((q2scBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB022Bound x hx
theorem q2scGlue23 : ∀ x ∈ Icc ((q2scBd.getD 23 0 : ℚ) : ℝ) ((q2scBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB023Bound x hx
theorem q2scGlue24 : ∀ x ∈ Icc ((q2scBd.getD 24 0 : ℚ) : ℝ) ((q2scBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB024Bound x hx
theorem q2scGlue25 : ∀ x ∈ Icc ((q2scBd.getD 25 0 : ℚ) : ℝ) ((q2scBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB025Bound x hx
theorem q2scGlue26 : ∀ x ∈ Icc ((q2scBd.getD 26 0 : ℚ) : ℝ) ((q2scBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB026Bound x hx
theorem q2scGlue27 : ∀ x ∈ Icc ((q2scBd.getD 27 0 : ℚ) : ℝ) ((q2scBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB027Bound x hx
theorem q2scGlue28 : ∀ x ∈ Icc ((q2scBd.getD 28 0 : ℚ) : ℝ) ((q2scBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB028Bound x hx
theorem q2scGlue29 : ∀ x ∈ Icc ((q2scBd.getD 29 0 : ℚ) : ℝ) ((q2scBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB029Bound x hx
theorem q2scGlue30 : ∀ x ∈ Icc ((q2scBd.getD 30 0 : ℚ) : ℝ) ((q2scBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB030Bound x hx
theorem q2scGlue31 : ∀ x ∈ Icc ((q2scBd.getD 31 0 : ℚ) : ℝ) ((q2scBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB031Bound x hx
theorem q2scGlue32 : ∀ x ∈ Icc ((q2scBd.getD 32 0 : ℚ) : ℝ) ((q2scBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB032Bound x hx
theorem q2scGlue33 : ∀ x ∈ Icc ((q2scBd.getD 33 0 : ℚ) : ℝ) ((q2scBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB033Bound x hx
theorem q2scGlue34 : ∀ x ∈ Icc ((q2scBd.getD 34 0 : ℚ) : ℝ) ((q2scBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB034Bound x hx
theorem q2scGlue35 : ∀ x ∈ Icc ((q2scBd.getD 35 0 : ℚ) : ℝ) ((q2scBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB035Bound x hx
theorem q2scGlue36 : ∀ x ∈ Icc ((q2scBd.getD 36 0 : ℚ) : ℝ) ((q2scBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB036Bound x hx
theorem q2scGlue37 : ∀ x ∈ Icc ((q2scBd.getD 37 0 : ℚ) : ℝ) ((q2scBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB037Bound x hx
theorem q2scGlue38 : ∀ x ∈ Icc ((q2scBd.getD 38 0 : ℚ) : ℝ) ((q2scBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB038Bound x hx
theorem q2scGlue39 : ∀ x ∈ Icc ((q2scBd.getD 39 0 : ℚ) : ℝ) ((q2scBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB039Bound x hx
theorem q2scGlue40 : ∀ x ∈ Icc ((q2scBd.getD 40 0 : ℚ) : ℝ) ((q2scBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB040Bound x hx
theorem q2scGlue41 : ∀ x ∈ Icc ((q2scBd.getD 41 0 : ℚ) : ℝ) ((q2scBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB041Bound x hx
theorem q2scGlue42 : ∀ x ∈ Icc ((q2scBd.getD 42 0 : ℚ) : ℝ) ((q2scBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB042Bound x hx
theorem q2scGlue43 : ∀ x ∈ Icc ((q2scBd.getD 43 0 : ℚ) : ℝ) ((q2scBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB043Bound x hx
theorem q2scGlue44 : ∀ x ∈ Icc ((q2scBd.getD 44 0 : ℚ) : ℝ) ((q2scBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB044Bound x hx
theorem q2scGlue45 : ∀ x ∈ Icc ((q2scBd.getD 45 0 : ℚ) : ℝ) ((q2scBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx _ _ => q2scB045Bound x hx
theorem q2scGlue46 : ∀ x ∈ Icc ((q2scBd.getD 46 0 : ℚ) : ℝ) ((q2scBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx hA hB => q2scE046Unif x hx (by rw [q2scE046Eq]; exact hB)
theorem q2scGlueAll : ∀ x ∈ Icc ((q2scBd.getD 0 0 : ℚ) : ℝ) ((q2scBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q2scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q2scBd.getD 47 0 : ℚ) : ℝ) → fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q2scGlue0) q2scGlue1) q2scGlue2) q2scGlue3) q2scGlue4) q2scGlue5) q2scGlue6) q2scGlue7) q2scGlue8) q2scGlue9) q2scGlue10) q2scGlue11) q2scGlue12) q2scGlue13) q2scGlue14) q2scGlue15) q2scGlue16) q2scGlue17) q2scGlue18) q2scGlue19) q2scGlue20) q2scGlue21) q2scGlue22) q2scGlue23) q2scGlue24) q2scGlue25) q2scGlue26) q2scGlue27) q2scGlue28) q2scGlue29) q2scGlue30) q2scGlue31) q2scGlue32) q2scGlue33) q2scGlue34) q2scGlue35) q2scGlue36) q2scGlue37) q2scGlue38) q2scGlue39) q2scGlue40) q2scGlue41) q2scGlue42) q2scGlue43) q2scGlue44) q2scGlue45) q2scGlue46
/-- **Sup statement (SC, alpha = 0.0625).** -/
theorem q2scSup : ∀ x ∈ Ioo ((q2scBd.getD 0 0 : ℚ) : ℝ) ((q2scBd.getD 47 0 : ℚ) : ℝ), fieldTower q2scFq (poleF q2scFq.poles) 0 x ≤ (q2scT : ℝ) :=
  fun x hx => q2scGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
