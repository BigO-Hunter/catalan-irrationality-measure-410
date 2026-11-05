module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSlope
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkStatP

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed

theorem slope0_stat : Hq gS0 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44262364356690289 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope1_stat : Hq gS1 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44085058945642727 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope2_stat : Hq gS2 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43924903296079385 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope3_stat : Hq gS3 (1 / 2 ^ 20) * (3 / 1000) ≤ ((2737192102190911 / 72057594037927936 : ℚ)) ^ 2 := by decide +kernel
theorem slope4_stat : Hq gS4 (1 / 2 ^ 20) * (3 / 1000) ≤ ((1365705215671109 / 36028797018963968 : ℚ)) ^ 2 := by decide +kernel
theorem slope5_stat : Hq gS5 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43649544539328125 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope6_stat : Hq gS6 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43634517020379795 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope7_stat : Hq gS7 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43653451785908229 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope8_stat : Hq gS8 (1 / 2 ^ 20) * (3 / 1000) ≤ ((5462594465280421 / 144115188075855872 : ℚ)) ^ 2 := by decide +kernel
theorem slope9_stat : Hq gS9 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43770095140288341 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope10_stat : Hq gS10 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43855035824395397 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope11_stat : Hq gS11 (1 / 2 ^ 20) * (3 / 1000) ≤ ((43949505039869305 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope12_stat : Hq gS12 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44048092415460849 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope13_stat : Hq gS13 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44146215800592473 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope14_stat : Hq gS14 (1 / 2 ^ 20) * (3 / 1000) ≤ ((22120090910996035 / 576460752303423488 : ℚ)) ^ 2 := by decide +kernel
theorem slope15_stat : Hq gS15 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44327170212707003 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope16_stat : Hq gS16 (1 / 2 ^ 20) * (3 / 1000) ≤ ((2775322976326637 / 72057594037927936 : ℚ)) ^ 2 := by decide +kernel
theorem slope17_stat : Hq gS17 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44472871925198423 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope18_stat : Hq gS18 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44529583117655019 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope19_stat : Hq gS19 (1 / 2 ^ 20) * (3 / 1000) ≤ ((11143773061287733 / 288230376151711744 : ℚ)) ^ 2 := by decide +kernel
theorem slope20_stat : Hq gS20 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44609576004829639 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
theorem slope21_stat : Hq gS21 (1 / 2 ^ 20) * (3 / 1000) ≤ ((11158375385669819 / 288230376151711744 : ℚ)) ^ 2 := by decide +kernel
theorem slope22_stat : Hq gS22 (1 / 2 ^ 20) * (3 / 1000) ≤ ((1395235741153435 / 36028797018963968 : ℚ)) ^ 2 := by decide +kernel
theorem slope23_stat : Hq gS23 (1 / 2 ^ 20) * (3 / 1000) ≤ ((44652515488083947 / 1152921504606846976 : ℚ)) ^ 2 := by decide +kernel
end CatalanMeasure.Signed.Consts
