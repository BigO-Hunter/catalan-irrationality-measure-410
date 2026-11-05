module

public import Submission.CatalanMeasure.GenD.D58.Cert590.RM000
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM001
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM002
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM003
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM004
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM005
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM006
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM007
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM008
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM009
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM010
public import Submission.CatalanMeasure.GenD.D58.Cert590.RM011
public import Submission.CatalanMeasure.GenD.D58.Cert590.RTab
public import Submission.CatalanMeasure.GenD.D58.Cert590.RZ
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
def blocksR : List Block := [RB000, RB001, RB002, RB003, RB004, RB005, RB006, RB007, RB008, RB009, RB010, RB011, RB012, RB013, RB014, RB015, RB016, RB017, RB018, RB019, RB020, RB021, RB022]
theorem blocksR_ok : ∀ b ∈ blocksR, blockOK (resSpecW (53/58 : ℚ) Pc P) D_R.toD 5 65 MGL_R MR b = true := by
  intro b hb
  simp only [blocksR, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact RB000_ok
  · exact RB001_ok
  · exact RB002_ok
  · exact RB003_ok
  · exact RB004_ok
  · exact RB005_ok
  · exact RB006_ok
  · exact RB007_ok
  · exact RB008_ok
  · exact RB009_ok
  · exact RB010_ok
  · exact RB011_ok
  · exact RB012_ok
  · exact RB013_ok
  · exact RB014_ok
  · exact RB015_ok
  · exact RB016_ok
  · exact RB017_ok
  · exact RB018_ok
  · exact RB019_ok
  · exact RB020_ok
  · exact RB021_ok
  · exact RB022_ok
theorem sound_R (t : ℕ) : (resSpecW (53/58 : ℚ) Pc P t).Sound D_R.toD (resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P)) :=
  resSpecW_sound (53/58 : ℚ) tailsP P_nonzero D_R.toD hZ_R t
theorem TT_real : ((TT : ℤ) : ℝ) = 1099511627776 := by unfold TT; norm_num
theorem cover_R1 : coverFrom (-401/2500) (-1099511627776) (blocksCells (blocksR.take 12)) = true := by decide +kernel
theorem cover_R2 : coverFrom 1 (qfloor ((401/2500 : ℚ) * (TT : ℚ))) (blocksCells (blocksR.drop 12)) = true := by decide +kernel
theorem residual_sup_S : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| → resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x ≤ (MR : ℝ) := by
  intro x hx hg
  have hxp : ∀ c : TCell, ∀ pr, (resSpecW (53/58 : ℚ) Pc P c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c pr h
    simp [resSpecW] at h
  rcases le_abs'.mp hg with h | h
  · refine field_le_of_blocks _ (resSpecW (53/58 : ℚ) Pc P) D_R.toD D_R_ok 5 65 MGL_R hMGL_R MR (blocksR.take 12)
      (fun c _ => sound_R c.2.2) (-1099511627776) (-401/2500) cover_R1
      (fun b hb => blocksR_ok b (List.mem_of_mem_take hb)) x ?_ ?_ (fun c _ => hxp c)
    · rw [TT_real]; push_cast; rw [div_le_iff₀ (by norm_num)]; linarith [hx.1]
    · push_cast; linarith
  · refine field_le_of_blocks _ (resSpecW (53/58 : ℚ) Pc P) D_R.toD D_R_ok 5 65 MGL_R hMGL_R MR (blocksR.drop 12)
      (fun c _ => sound_R c.2.2) (qfloor ((401/2500 : ℚ) * (TT : ℚ))) 1 cover_R2
      (fun b hb => blocksR_ok b (List.mem_of_mem_drop hb)) x
      (floor_le_of_ge (401/2500) x (by push_cast; linarith)) ?_ (fun c _ => hxp c)
    simpa using hx.2
end CatalanMeasure.GenD.D58.Cert590
