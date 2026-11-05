module

public import Submission.CatalanMeasure.Dual.AQ
public import Submission.CatalanMeasure.Dual.Norms
public import Submission.CatalanMeasure.Dual.ChecksX0
public import Submission.CatalanMeasure.Dual.ChecksX1
public import Submission.CatalanMeasure.Dual.ChecksX2
public import Submission.CatalanMeasure.Dual.ChecksX3
public import Submission.CatalanMeasure.Dual.ChecksX4
public import Submission.CatalanMeasure.Dual.ChecksX5
public import Submission.CatalanMeasure.Dual.ChecksX6
public import Submission.CatalanMeasure.Dual.ChecksX7
public import Submission.CatalanMeasure.Dual.ChecksX8
public import Submission.CatalanMeasure.Dual.ChecksY0
public import Submission.CatalanMeasure.Dual.ChecksY1
public import Submission.CatalanMeasure.Dual.ChecksY2
public import Submission.CatalanMeasure.Dual.ChecksY3
public import Submission.CatalanMeasure.Dual.ChecksY4
public import Submission.CatalanMeasure.Dual.ChecksY5

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert OAI.InternalCatalan

theorem allX : planX.all okX = true := by
  simp only [planX, List.all_cons, List.all_nil, okX_0, okX_1, okX_2, okX_3, okX_4, okX_5, okX_6, okX_7, okX_8, okX_9, okX_10, okX_11, okX_12, okX_13, okX_14, okX_15, okX_16, okX_17, okX_18, okX_19, okX_20, okX_21, okX_22, okX_23, okX_24, okX_25, okX_26, okX_27, okX_28, okX_29, okX_30, okX_31, okX_32, okX_33, okX_34, okX_35, okX_36, okX_37, okX_38, okX_39, okX_40, okX_41, okX_42, okX_43, okX_44, okX_45, okX_46, okX_47, okX_48, okX_49, okX_50, okX_51, okX_52, okX_53, okX_54, okX_55, okX_56, okX_57, okX_58, okX_59, okX_60, okX_61, okX_62, okX_63, okX_64, okX_65, okX_66, okX_67, okX_68, okX_69, okX_70, okX_71, okX_72, okX_73, okX_74, okX_75, okX_76, okX_77, okX_78, okX_79, okX_80, okX_81, okX_82, okX_83, okX_84, okX_85, okX_86, okX_87, okX_88, okX_89, okX_90, okX_91, okX_92, okX_93, okX_94, okX_95, okX_96, okX_97, okX_98, okX_99, okX_100, okX_101, okX_102, okX_103, okX_104, okX_105, okX_106, okX_107, okX_108, okX_109, okX_110, okX_111, okX_112, okX_113, okX_114, okX_115, okX_116, okX_117, okX_118, okX_119, okX_120, okX_121, okX_122, okX_123, okX_124, okX_125, okX_126, okX_127, okX_128, okX_129, okX_130, okX_131, okX_132, okX_133, okX_134, okX_135, okX_136, okX_137, okX_138, okX_139, okX_140, okX_141, okX_142, okX_143, okX_144, okX_145, okX_146, okX_147, okX_148, okX_149, okX_150, okX_151, okX_152, okX_153, Bool.and_true]

theorem allY : planY.all okY = true := by
  simp only [planY, List.all_cons, List.all_nil, okY_0, okY_1, okY_2, okY_3, okY_4, okY_5, okY_6, okY_7, okY_8, okY_9, okY_10, okY_11, okY_12, okY_13, okY_14, okY_15, okY_16, okY_17, okY_18, okY_19, okY_20, okY_21, okY_22, okY_23, okY_24, okY_25, okY_26, okY_27, okY_28, okY_29, okY_30, okY_31, okY_32, okY_33, okY_34, okY_35, okY_36, okY_37, okY_38, okY_39, okY_40, okY_41, okY_42, okY_43, okY_44, okY_45, okY_46, okY_47, okY_48, okY_49, okY_50, okY_51, okY_52, okY_53, okY_54, okY_55, okY_56, okY_57, okY_58, okY_59, okY_60, okY_61, okY_62, okY_63, okY_64, okY_65, okY_66, okY_67, okY_68, okY_69, okY_70, okY_71, okY_72, okY_73, okY_74, okY_75, okY_76, okY_77, okY_78, okY_79, okY_80, okY_81, okY_82, okY_83, okY_84, okY_85, okY_86, okY_87, okY_88, okY_89, okY_90, okY_91, okY_92, okY_93, Bool.and_true]

theorem row_sup : ∀ x ∈ Set.Ico (-1 : ℝ) 0 ∪ Set.Ioo 0 1,
    realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x ≤ (MX : ℝ) :=
  rowCheck_spec_integer hIntAX hIntQX hAQX hchainX (integerGaps_spec hScaleX hIntAX (all_and_left (f := integerGapOK AXZ) (g := integerRowBracketOK Pc Vc P V AXZ QXZ scaleX scaleQX MX) allX))
    (all_and_right (f := integerGapOK AXZ) (g := integerRowBracketOK Pc Vc P V AXZ QXZ scaleX scaleQX MX) allX) hendX

theorem col_sup : ∀ x ∈ Set.Ioo (0 : ℝ) 1, realEnergyColumnTrialField (trialSeq Vc V) x ≤ (MY : ℝ) :=
  colCheck_spec_integer hIntAY hIntQY hAQY hchainY (integerGaps_spec hScaleY hIntAY (all_and_left (f := integerGapOK AYZ) (g := integerColBracketOK Vc V AYZ QYZ scaleY scaleQY MY) allY))
    (all_and_right (f := integerGapOK AYZ) (g := integerColBracketOK Vc V AYZ QYZ scaleY scaleQY MY) allY)

theorem normP_le : barrierTrialNormSq (trialSeq Pc P) ≤ (NP : ℝ) := normOK_spec hNP
theorem normV_le : barrierTrialNormSq (trialSeq Vc V) ≤ (NV : ℝ) := normOK_spec hNV

theorem MX_eq : (MX : ℝ) = (-98572217 / 100000000 : ℝ) := by norm_num [MX]
theorem MY_eq : (MY : ℝ) = (-160942387 / 100000000 : ℝ) := by norm_num [MY]
theorem NP_eq : (NP : ℝ) = (33361987 / 500000000 : ℝ) := by norm_num [NP]
theorem NV_eq : (NV : ℝ) = (1292855037 / 1000000000 : ℝ) := by norm_num [NV]

end CatalanMeasure.Dual
