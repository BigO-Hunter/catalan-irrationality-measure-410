module

public import Submission.CatalanMeasure.GenD.D58.Cert590.YM000
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM001
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM002
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM003
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM004
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM005
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM006
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM007
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM008
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM009
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM010
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM011
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM012
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM013
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM014
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM015
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM016
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM017
public import Submission.CatalanMeasure.GenD.D58.Cert590.YM018
public import Submission.CatalanMeasure.GenD.D58.Cert590.YTab
public import Submission.CatalanMeasure.GenD.D58.Cert590.YZ
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
def blocksY : List Block := [YB000, YB001, YB002, YB003, YB004, YB005, YB006, YB007, YB008, YB009, YB010, YB011, YB012, YB013, YB014, YB015, YB016, YB017, YB018, YB019, YB020, YB021, YB022, YB023, YB024, YB025, YB026, YB027, YB028, YB029, YB030, YB031, YB032, YB033, YB034, YB035, YB036, YB037]
theorem blocksY_ok : ∀ b ∈ blocksY, blockOK (colSpecW C Vc V) D_Y.toD 5 65 MGL_Y MY b = true := by
  intro b hb
  simp only [blocksY, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact YB000_ok
  · exact YB001_ok
  · exact YB002_ok
  · exact YB003_ok
  · exact YB004_ok
  · exact YB005_ok
  · exact YB006_ok
  · exact YB007_ok
  · exact YB008_ok
  · exact YB009_ok
  · exact YB010_ok
  · exact YB011_ok
  · exact YB012_ok
  · exact YB013_ok
  · exact YB014_ok
  · exact YB015_ok
  · exact YB016_ok
  · exact YB017_ok
  · exact YB018_ok
  · exact YB019_ok
  · exact YB020_ok
  · exact YB021_ok
  · exact YB022_ok
  · exact YB023_ok
  · exact YB024_ok
  · exact YB025_ok
  · exact YB026_ok
  · exact YB027_ok
  · exact YB028_ok
  · exact YB029_ok
  · exact YB030_ok
  · exact YB031_ok
  · exact YB032_ok
  · exact YB033_ok
  · exact YB034_ok
  · exact YB035_ok
  · exact YB036_ok
  · exact YB037_ok
theorem sound_Y (t : ℕ) : (colSpecW C Vc V t).Sound D_Y.toD (colFieldS C Vc V) :=
  colSpecW_sound C tailsV V_nonzero D_Y.toD hZ_Y (by norm_num [C]) (by norm_num [C]) t
theorem peel_pt_Y (t : ℕ) (pr : ℚ × ℚ) (h : colPeel C t = some pr) : pr.2 = 0 ∨ pr.2 = 1 := by
  unfold colPeel at h
  split at h <;> first | (cases h; simp) | simp_all
theorem cover_Y : coverFrom 1 0 (blocksCells blocksY) = true := by decide +kernel
theorem column_sup_S : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ (MY : ℝ) := by
  intro x hx
  have hxp : ∀ c ∈ blocksCells blocksY, ∀ pr, (colSpecW C Vc V c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c _ pr h
    rcases peel_pt_Y c.2.2 pr h with h0 | h1
    · rw [h0]; simpa using hx.1.ne'
    · rw [h1]; simpa using hx.2.ne
  refine field_le_of_blocks _ (colSpecW C Vc V) D_Y.toD D_Y_ok 5 65 MGL_Y hMGL_Y MY blocksY
    (fun c _ => sound_Y c.2.2) 0 1 cover_Y blocksY_ok x ?_ ?_ hxp
  · simpa using hx.1.le
  · simpa using hx.2.le
end CatalanMeasure.GenD.D58.Cert590
