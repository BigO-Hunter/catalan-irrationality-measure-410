module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX0
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX2
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX3
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX4
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX5
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX6
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX7
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX8
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX9
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX10
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX12
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX13
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX15
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX16
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsX17
public import Submission.CatalanMeasure.GenD.D58.FirstCert.ValuesX0
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY0
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY2
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY4
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY6
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY8
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY10
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY12
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY14
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY16
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY18
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY20
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY22
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY24
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY26
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY28
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY30
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY31
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY32
public import Submission.CatalanMeasure.GenD.D58.FirstCert.GapsY33
public import Submission.CatalanMeasure.GenD.D58.FirstCert.ValuesY0
public import Submission.CatalanMeasure.GenD.D58.FirstCert.ValuesY1
public import Submission.CatalanMeasure.GenD.D58.FirstCert.ValuesY2
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hGapsX : NoRootGaps AX planX := by
  simp only [planX,noRootGaps_cons,noRootGaps_nil]
  exact ⟨gapX_0,(by intro h; cases h),gapX_2,gapX_3,gapX_4,gapX_5,gapX_6,gapX_7,gapX_8,gapX_9,gapX_10,(by intro h; cases h),gapX_12,gapX_13,(by intro h; cases h),gapX_15,gapX_16,gapX_17,True.intro⟩
theorem hBracketsX : planX.all (shiftedRowBracketOK R Pc Vc P V AX QX MX)=true := by
  simp only [planX,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketX_1,(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),bracketX_11,(by decide +kernel),(by decide +kernel),bracketX_14,(by decide +kernel),(by decide +kernel),(by decide +kernel),True.intro⟩
theorem hGapsY : NoRootGaps AY planY := by
  simp only [planY,noRootGaps_cons,noRootGaps_nil]
  exact ⟨gapY_0,(by intro h; cases h),gapY_2,(by intro h; cases h),gapY_4,(by intro h; cases h),gapY_6,(by intro h; cases h),gapY_8,(by intro h; cases h),gapY_10,(by intro h; cases h),gapY_12,(by intro h; cases h),gapY_14,(by intro h; cases h),gapY_16,(by intro h; cases h),gapY_18,(by intro h; cases h),gapY_20,(by intro h; cases h),gapY_22,(by intro h; cases h),gapY_24,(by intro h; cases h),gapY_26,(by intro h; cases h),gapY_28,(by intro h; cases h),gapY_30,gapY_31,gapY_32,gapY_33,True.intro⟩
theorem hBracketsY : planY.all (shiftedColumnBracketOK C Vc V AY QY MY)=true := by
  simp only [planY,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨(by decide +kernel),bracketY_1,(by decide +kernel),bracketY_3,(by decide +kernel),bracketY_5,(by decide +kernel),bracketY_7,(by decide +kernel),bracketY_9,(by decide +kernel),bracketY_11,(by decide +kernel),bracketY_13,(by decide +kernel),bracketY_15,(by decide +kernel),bracketY_17,(by decide +kernel),bracketY_19,(by decide +kernel),bracketY_21,(by decide +kernel),bracketY_23,(by decide +kernel),bracketY_25,(by decide +kernel),bracketY_27,(by decide +kernel),bracketY_29,(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),True.intro⟩

theorem row_sup : ∀ x ∈ Set.Ico (-1:ℝ) 0 ∪ Set.Ioo 0 1,
    shiftedRowField R Pc Vc P V x ≤ (MX:ℝ) :=
  shiftedRowCheck_spec (by norm_num [R]) (by norm_num [R]) hAQX hchainX
    hGapsX hBracketsX hendX

theorem column_sup : ∀ s ∈ Set.Ioo (0:ℝ) 1,
    shiftedColumnField C Vc V s ≤ (MY:ℝ) :=
  shiftedColumnCheck_spec (by norm_num [C]) (by norm_num [C]) hAQY hchainY
    hGapsY hBracketsY
end CatalanMeasure.GenD.D58.FirstCert
