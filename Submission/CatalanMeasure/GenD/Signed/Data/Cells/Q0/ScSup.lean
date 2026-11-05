module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP006
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP007
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP008
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP009
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP010
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP011
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP012
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP013
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScP014
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.ScE040

@[expose] public section

/-! **SC, alpha = 0.0: the sup statement.**  `fieldTower q0scFq ... x <= q0scT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.568502323350, K = 14.899936356001 (NOTES-TRIAL; kappa_old = 14.899936356001). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q0scGlue0 : ∀ x ∈ Icc ((q0scBd.getD 0 0 : ℚ) : ℝ) ((q0scBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx hA hB => q0scE000Unif x hx (by rw [q0scE000Eq]; exact hA)
theorem q0scGlue1 : ∀ x ∈ Icc ((q0scBd.getD 1 0 : ℚ) : ℝ) ((q0scBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB001Bound x hx
theorem q0scGlue2 : ∀ x ∈ Icc ((q0scBd.getD 2 0 : ℚ) : ℝ) ((q0scBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB002Bound x hx
theorem q0scGlue3 : ∀ x ∈ Icc ((q0scBd.getD 3 0 : ℚ) : ℝ) ((q0scBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB003Bound x hx
theorem q0scGlue4 : ∀ x ∈ Icc ((q0scBd.getD 4 0 : ℚ) : ℝ) ((q0scBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB004Bound x hx
theorem q0scGlue5 : ∀ x ∈ Icc ((q0scBd.getD 5 0 : ℚ) : ℝ) ((q0scBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB005Bound x hx
theorem q0scGlue6 : ∀ x ∈ Icc ((q0scBd.getD 6 0 : ℚ) : ℝ) ((q0scBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB006Bound x hx
theorem q0scGlue7 : ∀ x ∈ Icc ((q0scBd.getD 7 0 : ℚ) : ℝ) ((q0scBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB007Bound x hx
theorem q0scGlue8 : ∀ x ∈ Icc ((q0scBd.getD 8 0 : ℚ) : ℝ) ((q0scBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB008Bound x hx
theorem q0scGlue9 : ∀ x ∈ Icc ((q0scBd.getD 9 0 : ℚ) : ℝ) ((q0scBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB009Bound x hx
theorem q0scGlue10 : ∀ x ∈ Icc ((q0scBd.getD 10 0 : ℚ) : ℝ) ((q0scBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB010Bound x hx
theorem q0scGlue11 : ∀ x ∈ Icc ((q0scBd.getD 11 0 : ℚ) : ℝ) ((q0scBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB011Bound x hx
theorem q0scGlue12 : ∀ x ∈ Icc ((q0scBd.getD 12 0 : ℚ) : ℝ) ((q0scBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB012Bound x hx
theorem q0scGlue13 : ∀ x ∈ Icc ((q0scBd.getD 13 0 : ℚ) : ℝ) ((q0scBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB013Bound x hx
theorem q0scGlue14 : ∀ x ∈ Icc ((q0scBd.getD 14 0 : ℚ) : ℝ) ((q0scBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB014Bound x hx
theorem q0scGlue15 : ∀ x ∈ Icc ((q0scBd.getD 15 0 : ℚ) : ℝ) ((q0scBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB015Bound x hx
theorem q0scGlue16 : ∀ x ∈ Icc ((q0scBd.getD 16 0 : ℚ) : ℝ) ((q0scBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB016Bound x hx
theorem q0scGlue17 : ∀ x ∈ Icc ((q0scBd.getD 17 0 : ℚ) : ℝ) ((q0scBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB017Bound x hx
theorem q0scGlue18 : ∀ x ∈ Icc ((q0scBd.getD 18 0 : ℚ) : ℝ) ((q0scBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB018Bound x hx
theorem q0scGlue19 : ∀ x ∈ Icc ((q0scBd.getD 19 0 : ℚ) : ℝ) ((q0scBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB019Bound x hx
theorem q0scGlue20 : ∀ x ∈ Icc ((q0scBd.getD 20 0 : ℚ) : ℝ) ((q0scBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB020Bound x hx
theorem q0scGlue21 : ∀ x ∈ Icc ((q0scBd.getD 21 0 : ℚ) : ℝ) ((q0scBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB021Bound x hx
theorem q0scGlue22 : ∀ x ∈ Icc ((q0scBd.getD 22 0 : ℚ) : ℝ) ((q0scBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB022Bound x hx
theorem q0scGlue23 : ∀ x ∈ Icc ((q0scBd.getD 23 0 : ℚ) : ℝ) ((q0scBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB023Bound x hx
theorem q0scGlue24 : ∀ x ∈ Icc ((q0scBd.getD 24 0 : ℚ) : ℝ) ((q0scBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB024Bound x hx
theorem q0scGlue25 : ∀ x ∈ Icc ((q0scBd.getD 25 0 : ℚ) : ℝ) ((q0scBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB025Bound x hx
theorem q0scGlue26 : ∀ x ∈ Icc ((q0scBd.getD 26 0 : ℚ) : ℝ) ((q0scBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB026Bound x hx
theorem q0scGlue27 : ∀ x ∈ Icc ((q0scBd.getD 27 0 : ℚ) : ℝ) ((q0scBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB027Bound x hx
theorem q0scGlue28 : ∀ x ∈ Icc ((q0scBd.getD 28 0 : ℚ) : ℝ) ((q0scBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB028Bound x hx
theorem q0scGlue29 : ∀ x ∈ Icc ((q0scBd.getD 29 0 : ℚ) : ℝ) ((q0scBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB029Bound x hx
theorem q0scGlue30 : ∀ x ∈ Icc ((q0scBd.getD 30 0 : ℚ) : ℝ) ((q0scBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB030Bound x hx
theorem q0scGlue31 : ∀ x ∈ Icc ((q0scBd.getD 31 0 : ℚ) : ℝ) ((q0scBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB031Bound x hx
theorem q0scGlue32 : ∀ x ∈ Icc ((q0scBd.getD 32 0 : ℚ) : ℝ) ((q0scBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB032Bound x hx
theorem q0scGlue33 : ∀ x ∈ Icc ((q0scBd.getD 33 0 : ℚ) : ℝ) ((q0scBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB033Bound x hx
theorem q0scGlue34 : ∀ x ∈ Icc ((q0scBd.getD 34 0 : ℚ) : ℝ) ((q0scBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB034Bound x hx
theorem q0scGlue35 : ∀ x ∈ Icc ((q0scBd.getD 35 0 : ℚ) : ℝ) ((q0scBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB035Bound x hx
theorem q0scGlue36 : ∀ x ∈ Icc ((q0scBd.getD 36 0 : ℚ) : ℝ) ((q0scBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB036Bound x hx
theorem q0scGlue37 : ∀ x ∈ Icc ((q0scBd.getD 37 0 : ℚ) : ℝ) ((q0scBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB037Bound x hx
theorem q0scGlue38 : ∀ x ∈ Icc ((q0scBd.getD 38 0 : ℚ) : ℝ) ((q0scBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB038Bound x hx
theorem q0scGlue39 : ∀ x ∈ Icc ((q0scBd.getD 39 0 : ℚ) : ℝ) ((q0scBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx _ _ => q0scB039Bound x hx
theorem q0scGlue40 : ∀ x ∈ Icc ((q0scBd.getD 40 0 : ℚ) : ℝ) ((q0scBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx hA hB => q0scE040Unif x hx (by rw [q0scE040Eq]; exact hB)
theorem q0scGlueAll : ∀ x ∈ Icc ((q0scBd.getD 0 0 : ℚ) : ℝ) ((q0scBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0scBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0scBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0scGlue0) q0scGlue1) q0scGlue2) q0scGlue3) q0scGlue4) q0scGlue5) q0scGlue6) q0scGlue7) q0scGlue8) q0scGlue9) q0scGlue10) q0scGlue11) q0scGlue12) q0scGlue13) q0scGlue14) q0scGlue15) q0scGlue16) q0scGlue17) q0scGlue18) q0scGlue19) q0scGlue20) q0scGlue21) q0scGlue22) q0scGlue23) q0scGlue24) q0scGlue25) q0scGlue26) q0scGlue27) q0scGlue28) q0scGlue29) q0scGlue30) q0scGlue31) q0scGlue32) q0scGlue33) q0scGlue34) q0scGlue35) q0scGlue36) q0scGlue37) q0scGlue38) q0scGlue39) q0scGlue40
/-- **Sup statement (SC, alpha = 0.0).** -/
theorem q0scSup : ∀ x ∈ Ioo ((q0scBd.getD 0 0 : ℚ) : ℝ) ((q0scBd.getD 41 0 : ℚ) : ℝ), fieldTower q0scFq (poleF q0scFq.poles) 0 x ≤ (q0scT : ℝ) :=
  fun x hx => q0scGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
