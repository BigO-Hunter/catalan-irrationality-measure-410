module

public import Submission.CatalanMeasure.GenD.D58.Cert590.XM000
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM001
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM002
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM003
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM004
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM005
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM006
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM007
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM008
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM009
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM010
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM011
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM012
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM013
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM014
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM015
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM016
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM017
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM018
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM019
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM020
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM021
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM022
public import Submission.CatalanMeasure.GenD.D58.Cert590.XM023
public import Submission.CatalanMeasure.GenD.D58.Cert590.XTab
public import Submission.CatalanMeasure.GenD.D58.Cert590.XZ
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data
public import Submission.CatalanMeasure.GenD.Cert.WLogSpec
public import Submission.CatalanMeasure.GenD.Cert.Assembly

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
open Set
def blocksX : List Block := [XB000, XB001, XB002, XB003, XB004, XB005, XB006, XB007, XB008, XB009, XB010, XB011, XB012, XB013, XB014, XB015, XB016, XB017, XB018, XB019, XB020, XB021, XB022, XB023, XB024, XB025, XB026, XB027, XB028, XB029, XB030, XB031, XB032, XB033, XB034, XB035, XB036, XB037, XB038, XB039, XB040, XB041, XB042, XB043, XB044, XB045, XB046]
theorem blocksX_ok : ∀ b ∈ blocksX, blockOK (rowSpecW R Pc Vc P V) D_X.toD 5 65 MGL_X MX b = true := by
  intro b hb
  simp only [blocksX, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact XB000_ok
  · exact XB001_ok
  · exact XB002_ok
  · exact XB003_ok
  · exact XB004_ok
  · exact XB005_ok
  · exact XB006_ok
  · exact XB007_ok
  · exact XB008_ok
  · exact XB009_ok
  · exact XB010_ok
  · exact XB011_ok
  · exact XB012_ok
  · exact XB013_ok
  · exact XB014_ok
  · exact XB015_ok
  · exact XB016_ok
  · exact XB017_ok
  · exact XB018_ok
  · exact XB019_ok
  · exact XB020_ok
  · exact XB021_ok
  · exact XB022_ok
  · exact XB023_ok
  · exact XB024_ok
  · exact XB025_ok
  · exact XB026_ok
  · exact XB027_ok
  · exact XB028_ok
  · exact XB029_ok
  · exact XB030_ok
  · exact XB031_ok
  · exact XB032_ok
  · exact XB033_ok
  · exact XB034_ok
  · exact XB035_ok
  · exact XB036_ok
  · exact XB037_ok
  · exact XB038_ok
  · exact XB039_ok
  · exact XB040_ok
  · exact XB041_ok
  · exact XB042_ok
  · exact XB043_ok
  · exact XB044_ok
  · exact XB045_ok
  · exact XB046_ok
theorem sound_X (t : ℕ) : (rowSpecW R Pc Vc P V t).Sound D_X.toD (rowFieldS R Pc Vc P V) :=
  rowSpecW_sound R tailsP tailsV P_nonzero V_nonzero D_X.toD hZ_X (by norm_num [R]) (by norm_num [R]) t
theorem TT_real : ((TT : ℤ) : ℝ) = 1099511627776 := by unfold TT; norm_num
theorem peel_pt_X (t : ℕ) (pr : ℚ × ℚ) (h : rowPeel R t = some pr) : pr.2 = 0 ∨ pr.2 = 1 := by
  unfold rowPeel at h
  split at h <;> first | (cases h; simp) | simp_all
theorem cover_X_neg : coverFrom 0 (-1099511627776) (blocksCells blocksX) = true := by decide +kernel
theorem cover_X_pos : coverFrom 1 0 (blocksCells blocksX) = true := by decide +kernel
theorem row_sup_S : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ (MX : ℝ) := by
  intro x hx
  have hx01 : x ≠ 0 ∧ x ≠ 1 := by
    rcases hx with hx | hx
    · exact ⟨hx.2.ne, by linarith [hx.2]⟩
    · exact ⟨hx.1.ne', hx.2.ne⟩
  have hxp : ∀ c ∈ blocksCells blocksX, ∀ pr, (rowSpecW R Pc Vc P V c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c _ pr h
    rcases peel_pt_X c.2.2 pr h with h0 | h1
    · rw [h0]; simpa using hx01.1
    · rw [h1]; simpa using hx01.2
  rcases hx with hx | hx
  · refine field_le_of_blocks _ (rowSpecW R Pc Vc P V) D_X.toD D_X_ok 5 65 MGL_X hMGL_X MX blocksX
      (fun c _ => sound_X c.2.2) (-1099511627776) 0 cover_X_neg blocksX_ok x ?_ ?_ hxp
    · rw [TT_real]; push_cast; rw [div_le_iff₀ (by norm_num)]; linarith [hx.1]
    · simpa using hx.2.le
  · refine field_le_of_blocks _ (rowSpecW R Pc Vc P V) D_X.toD D_X_ok 5 65 MGL_X hMGL_X MX blocksX
      (fun c _ => sound_X c.2.2) 0 1 cover_X_pos blocksX_ok x ?_ ?_ hxp
    · simpa using hx.1.le
    · simpa using hx.2.le
end CatalanMeasure.GenD.D58.Cert590
