module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmE000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP000
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP001
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP002
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP003
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP004
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP005
public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Q0.SmP006

@[expose] public section

/-! **SM, alpha = 0.0: the sup statement.**  `fieldTower q0smFq ... x <= q0smT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -0.455390951596, K = -9.277752042999 (NOTES-TRIAL; kappa_old = -9.277752042999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

theorem q0smGlue0 : ∀ x ∈ Icc ((q0smBd.getD 0 0 : ℚ) : ℝ) ((q0smBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smE000Full x hx
theorem q0smGlue1 : ∀ x ∈ Icc ((q0smBd.getD 1 0 : ℚ) : ℝ) ((q0smBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB001Bound x hx
theorem q0smGlue2 : ∀ x ∈ Icc ((q0smBd.getD 2 0 : ℚ) : ℝ) ((q0smBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB002Bound x hx
theorem q0smGlue3 : ∀ x ∈ Icc ((q0smBd.getD 3 0 : ℚ) : ℝ) ((q0smBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB003Bound x hx
theorem q0smGlue4 : ∀ x ∈ Icc ((q0smBd.getD 4 0 : ℚ) : ℝ) ((q0smBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB004Bound x hx
theorem q0smGlue5 : ∀ x ∈ Icc ((q0smBd.getD 5 0 : ℚ) : ℝ) ((q0smBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB005Bound x hx
theorem q0smGlue6 : ∀ x ∈ Icc ((q0smBd.getD 6 0 : ℚ) : ℝ) ((q0smBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB006Bound x hx
theorem q0smGlue7 : ∀ x ∈ Icc ((q0smBd.getD 7 0 : ℚ) : ℝ) ((q0smBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB007Bound x hx
theorem q0smGlue8 : ∀ x ∈ Icc ((q0smBd.getD 8 0 : ℚ) : ℝ) ((q0smBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB008Bound x hx
theorem q0smGlue9 : ∀ x ∈ Icc ((q0smBd.getD 9 0 : ℚ) : ℝ) ((q0smBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB009Bound x hx
theorem q0smGlue10 : ∀ x ∈ Icc ((q0smBd.getD 10 0 : ℚ) : ℝ) ((q0smBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB010Bound x hx
theorem q0smGlue11 : ∀ x ∈ Icc ((q0smBd.getD 11 0 : ℚ) : ℝ) ((q0smBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB011Bound x hx
theorem q0smGlue12 : ∀ x ∈ Icc ((q0smBd.getD 12 0 : ℚ) : ℝ) ((q0smBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB012Bound x hx
theorem q0smGlue13 : ∀ x ∈ Icc ((q0smBd.getD 13 0 : ℚ) : ℝ) ((q0smBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB013Bound x hx
theorem q0smGlue14 : ∀ x ∈ Icc ((q0smBd.getD 14 0 : ℚ) : ℝ) ((q0smBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB014Bound x hx
theorem q0smGlue15 : ∀ x ∈ Icc ((q0smBd.getD 15 0 : ℚ) : ℝ) ((q0smBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB015Bound x hx
theorem q0smGlue16 : ∀ x ∈ Icc ((q0smBd.getD 16 0 : ℚ) : ℝ) ((q0smBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB016Bound x hx
theorem q0smGlue17 : ∀ x ∈ Icc ((q0smBd.getD 17 0 : ℚ) : ℝ) ((q0smBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB017Bound x hx
theorem q0smGlue18 : ∀ x ∈ Icc ((q0smBd.getD 18 0 : ℚ) : ℝ) ((q0smBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB018Bound x hx
theorem q0smGlue19 : ∀ x ∈ Icc ((q0smBd.getD 19 0 : ℚ) : ℝ) ((q0smBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB019Bound x hx
theorem q0smGlue20 : ∀ x ∈ Icc ((q0smBd.getD 20 0 : ℚ) : ℝ) ((q0smBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB020Bound x hx
theorem q0smGlue21 : ∀ x ∈ Icc ((q0smBd.getD 21 0 : ℚ) : ℝ) ((q0smBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB021Bound x hx
theorem q0smGlue22 : ∀ x ∈ Icc ((q0smBd.getD 22 0 : ℚ) : ℝ) ((q0smBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB022Bound x hx
theorem q0smGlue23 : ∀ x ∈ Icc ((q0smBd.getD 23 0 : ℚ) : ℝ) ((q0smBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB023Bound x hx
theorem q0smGlue24 : ∀ x ∈ Icc ((q0smBd.getD 24 0 : ℚ) : ℝ) ((q0smBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB024Bound x hx
theorem q0smGlue25 : ∀ x ∈ Icc ((q0smBd.getD 25 0 : ℚ) : ℝ) ((q0smBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB025Bound x hx
theorem q0smGlue26 : ∀ x ∈ Icc ((q0smBd.getD 26 0 : ℚ) : ℝ) ((q0smBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB026Bound x hx
theorem q0smGlue27 : ∀ x ∈ Icc ((q0smBd.getD 27 0 : ℚ) : ℝ) ((q0smBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB027Bound x hx
theorem q0smGlue28 : ∀ x ∈ Icc ((q0smBd.getD 28 0 : ℚ) : ℝ) ((q0smBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB028Bound x hx
theorem q0smGlue29 : ∀ x ∈ Icc ((q0smBd.getD 29 0 : ℚ) : ℝ) ((q0smBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB029Bound x hx
theorem q0smGlue30 : ∀ x ∈ Icc ((q0smBd.getD 30 0 : ℚ) : ℝ) ((q0smBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB030Bound x hx
theorem q0smGlue31 : ∀ x ∈ Icc ((q0smBd.getD 31 0 : ℚ) : ℝ) ((q0smBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB031Bound x hx
theorem q0smGlue32 : ∀ x ∈ Icc ((q0smBd.getD 32 0 : ℚ) : ℝ) ((q0smBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB032Bound x hx
theorem q0smGlue33 : ∀ x ∈ Icc ((q0smBd.getD 33 0 : ℚ) : ℝ) ((q0smBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB033Bound x hx
theorem q0smGlue34 : ∀ x ∈ Icc ((q0smBd.getD 34 0 : ℚ) : ℝ) ((q0smBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB034Bound x hx
theorem q0smGlue35 : ∀ x ∈ Icc ((q0smBd.getD 35 0 : ℚ) : ℝ) ((q0smBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB035Bound x hx
theorem q0smGlue36 : ∀ x ∈ Icc ((q0smBd.getD 36 0 : ℚ) : ℝ) ((q0smBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB036Bound x hx
theorem q0smGlue37 : ∀ x ∈ Icc ((q0smBd.getD 37 0 : ℚ) : ℝ) ((q0smBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB037Bound x hx
theorem q0smGlue38 : ∀ x ∈ Icc ((q0smBd.getD 38 0 : ℚ) : ℝ) ((q0smBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB038Bound x hx
theorem q0smGlue39 : ∀ x ∈ Icc ((q0smBd.getD 39 0 : ℚ) : ℝ) ((q0smBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB039Bound x hx
theorem q0smGlue40 : ∀ x ∈ Icc ((q0smBd.getD 40 0 : ℚ) : ℝ) ((q0smBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB040Bound x hx
theorem q0smGlue41 : ∀ x ∈ Icc ((q0smBd.getD 41 0 : ℚ) : ℝ) ((q0smBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx _ _ => q0smB041Bound x hx
theorem q0smGlueAll : ∀ x ∈ Icc ((q0smBd.getD 0 0 : ℚ) : ℝ) ((q0smBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q0smBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0smBd.getD 42 0 : ℚ) : ℝ) → fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0smGlue0) q0smGlue1) q0smGlue2) q0smGlue3) q0smGlue4) q0smGlue5) q0smGlue6) q0smGlue7) q0smGlue8) q0smGlue9) q0smGlue10) q0smGlue11) q0smGlue12) q0smGlue13) q0smGlue14) q0smGlue15) q0smGlue16) q0smGlue17) q0smGlue18) q0smGlue19) q0smGlue20) q0smGlue21) q0smGlue22) q0smGlue23) q0smGlue24) q0smGlue25) q0smGlue26) q0smGlue27) q0smGlue28) q0smGlue29) q0smGlue30) q0smGlue31) q0smGlue32) q0smGlue33) q0smGlue34) q0smGlue35) q0smGlue36) q0smGlue37) q0smGlue38) q0smGlue39) q0smGlue40) q0smGlue41
/-- **Sup statement (SM, alpha = 0.0).** -/
theorem q0smSup : ∀ x ∈ Ioo ((q0smBd.getD 0 0 : ℚ) : ℝ) ((q0smBd.getD 42 0 : ℚ) : ℝ), fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) :=
  fun x hx => q0smGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

/-- **Sup statement on (-1, -gs]** (closed right end: the last block's bound). -/
theorem q0smSupIoc : ∀ x ∈ Ioc ((q0smBd.getD 0 0 : ℚ) : ℝ) ((q0smBd.getD 42 0 : ℚ) : ℝ), fieldTower q0smFq (poleF q0smFq.poles) 0 x ≤ (q0smT : ℝ) := by
  intro x hx
  rcases hx.2.lt_or_eq with h | h
  · exact q0smSup x ⟨hx.1, h⟩
  · rw [h]
    exact q0smB041Bound _ ⟨by exact_mod_cast (by decide +kernel : (q0smB041Blo : ℚ) ≤ q0smB041Bhi), le_rfl⟩

end CatalanMeasure.GenD.Signed.Data.Cells
