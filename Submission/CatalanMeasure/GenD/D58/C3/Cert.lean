module

public import Submission.CatalanMeasure.GenD.ResInv
public import Submission.CatalanMeasure.GenD.D58.OddProfile
public import Submission.CatalanMeasure.GenD.D58.C3.Data
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-! # D58.C3: the three base-matrix determinants of the design (58,9,3,5,3) are nonzero mod 1009.
Every check is a small Nat-level kernel computation on residue tables (see `gen_c3b.py`, `gen_cert.py`). -/

namespace CatalanMeasure.GenD
namespace D58
namespace C3

open ResCheck ResBase ResInv ResRec CatalanMeasure.Parametric

set_option maxRecDepth 100000

instance fact1009' : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

theorem cIV : chkIV 1009 79 ivT = true := by decide +kernel
theorem cMS : chkMS 1009 78 msT = true := by decide +kernel
theorem cBM : chkBM 1009 78 msT bmT = true := by decide +kernel
theorem cBP : chkBP 1009 70 bpT ivT = true := by decide +kernel
theorem cH1 : chkH1 1009 78 h1T ivT = true := by decide +kernel
theorem cMT : chkMT 1009 78 70 msT bmT bpT ivT momT = true := by decide +kernel
theorem cZT : chkZT 1009 78 70 h1T ivT zetT = true := by decide +kernel
theorem cPoly : chkPoly Odd.design 1009 prT drT = true := by decide +kernel
theorem cFM : chkF 1009 3 9 58 78 wT momT fmT = true := by decide +kernel
theorem cFZ : chkF 1009 3 9 58 78 wT zetT fzT = true := by decide +kernel
theorem cLen : chkLen 58 78 prT drT fmT fzT = true := by decide +kernel
theorem hW : ∀ v, v < Odd.design.q0 + 1 → (nth wT v : ZMod 1009) = baseFilterWeight Odd.design 1009 v := by
  decide +kernel
theorem hcN : ((2 * 503 + 3) % 1009 == 0 % 1009) = true := by decide +kernel
theorem cBase_0 : chkBase 1009 58 503 baseT prT drT fmT fzT 0 = true := by decide +kernel
theorem cBase_1 : chkBase 1009 58 503 baseT prT drT fmT fzT 1 = true := by decide +kernel
theorem cBase_2 : chkBase 1009 58 503 baseT prT drT fmT fzT 2 = true := by decide +kernel
theorem cBase_3 : chkBase 1009 58 503 baseT prT drT fmT fzT 3 = true := by decide +kernel
theorem cBase_4 : chkBase 1009 58 503 baseT prT drT fmT fzT 4 = true := by decide +kernel
theorem cBase_5 : chkBase 1009 58 503 baseT prT drT fmT fzT 5 = true := by decide +kernel
theorem cBase_6 : chkBase 1009 58 503 baseT prT drT fmT fzT 6 = true := by decide +kernel
theorem cBase_7 : chkBase 1009 58 503 baseT prT drT fmT fzT 7 = true := by decide +kernel
theorem cBase_8 : chkBase 1009 58 503 baseT prT drT fmT fzT 8 = true := by decide +kernel
theorem cBase_9 : chkBase 1009 58 503 baseT prT drT fmT fzT 9 = true := by decide +kernel
theorem cBase_10 : chkBase 1009 58 503 baseT prT drT fmT fzT 10 = true := by decide +kernel
theorem cBase_11 : chkBase 1009 58 503 baseT prT drT fmT fzT 11 = true := by decide +kernel
theorem cBase_12 : chkBase 1009 58 503 baseT prT drT fmT fzT 12 = true := by decide +kernel
theorem cBase_13 : chkBase 1009 58 503 baseT prT drT fmT fzT 13 = true := by decide +kernel
theorem cBase_14 : chkBase 1009 58 503 baseT prT drT fmT fzT 14 = true := by decide +kernel
theorem cBase_15 : chkBase 1009 58 503 baseT prT drT fmT fzT 15 = true := by decide +kernel
theorem cBase_16 : chkBase 1009 58 503 baseT prT drT fmT fzT 16 = true := by decide +kernel
theorem cBase_17 : chkBase 1009 58 503 baseT prT drT fmT fzT 17 = true := by decide +kernel
theorem cBase_18 : chkBase 1009 58 503 baseT prT drT fmT fzT 18 = true := by decide +kernel
theorem cBase_19 : chkBase 1009 58 503 baseT prT drT fmT fzT 19 = true := by decide +kernel
theorem cBase_20 : chkBase 1009 58 503 baseT prT drT fmT fzT 20 = true := by decide +kernel
theorem cBase_21 : chkBase 1009 58 503 baseT prT drT fmT fzT 21 = true := by decide +kernel
theorem cBase_22 : chkBase 1009 58 503 baseT prT drT fmT fzT 22 = true := by decide +kernel
theorem cBase_23 : chkBase 1009 58 503 baseT prT drT fmT fzT 23 = true := by decide +kernel
theorem cBase_24 : chkBase 1009 58 503 baseT prT drT fmT fzT 24 = true := by decide +kernel
theorem cBase_25 : chkBase 1009 58 503 baseT prT drT fmT fzT 25 = true := by decide +kernel
theorem cBase_26 : chkBase 1009 58 503 baseT prT drT fmT fzT 26 = true := by decide +kernel
theorem cBase_27 : chkBase 1009 58 503 baseT prT drT fmT fzT 27 = true := by decide +kernel
theorem cBase_28 : chkBase 1009 58 503 baseT prT drT fmT fzT 28 = true := by decide +kernel
theorem cBase_29 : chkBase 1009 58 503 baseT prT drT fmT fzT 29 = true := by decide +kernel
theorem cBase_30 : chkBase 1009 58 503 baseT prT drT fmT fzT 30 = true := by decide +kernel
theorem cBase_31 : chkBase 1009 58 503 baseT prT drT fmT fzT 31 = true := by decide +kernel
theorem cBase_32 : chkBase 1009 58 503 baseT prT drT fmT fzT 32 = true := by decide +kernel
theorem cBase_33 : chkBase 1009 58 503 baseT prT drT fmT fzT 33 = true := by decide +kernel
theorem cBase_34 : chkBase 1009 58 503 baseT prT drT fmT fzT 34 = true := by decide +kernel
theorem cBase_35 : chkBase 1009 58 503 baseT prT drT fmT fzT 35 = true := by decide +kernel
theorem cBase_36 : chkBase 1009 58 503 baseT prT drT fmT fzT 36 = true := by decide +kernel
theorem cBase_37 : chkBase 1009 58 503 baseT prT drT fmT fzT 37 = true := by decide +kernel
theorem cBase_38 : chkBase 1009 58 503 baseT prT drT fmT fzT 38 = true := by decide +kernel
theorem cBase_39 : chkBase 1009 58 503 baseT prT drT fmT fzT 39 = true := by decide +kernel
theorem cBase_40 : chkBase 1009 58 503 baseT prT drT fmT fzT 40 = true := by decide +kernel
theorem cBase_41 : chkBase 1009 58 503 baseT prT drT fmT fzT 41 = true := by decide +kernel
theorem cBase_42 : chkBase 1009 58 503 baseT prT drT fmT fzT 42 = true := by decide +kernel
theorem cBase_43 : chkBase 1009 58 503 baseT prT drT fmT fzT 43 = true := by decide +kernel
theorem cBase_44 : chkBase 1009 58 503 baseT prT drT fmT fzT 44 = true := by decide +kernel
theorem cBase_45 : chkBase 1009 58 503 baseT prT drT fmT fzT 45 = true := by decide +kernel
theorem cBase_46 : chkBase 1009 58 503 baseT prT drT fmT fzT 46 = true := by decide +kernel
theorem cBase_47 : chkBase 1009 58 503 baseT prT drT fmT fzT 47 = true := by decide +kernel
theorem cBase_48 : chkBase 1009 58 503 baseT prT drT fmT fzT 48 = true := by decide +kernel
theorem cBase_49 : chkBase 1009 58 503 baseT prT drT fmT fzT 49 = true := by decide +kernel
theorem cBase_50 : chkBase 1009 58 503 baseT prT drT fmT fzT 50 = true := by decide +kernel
theorem cBase_51 : chkBase 1009 58 503 baseT prT drT fmT fzT 51 = true := by decide +kernel
theorem cBase_52 : chkBase 1009 58 503 baseT prT drT fmT fzT 52 = true := by decide +kernel
theorem cBase_53 : chkBase 1009 58 503 baseT prT drT fmT fzT 53 = true := by decide +kernel
theorem cBase_54 : chkBase 1009 58 503 baseT prT drT fmT fzT 54 = true := by decide +kernel
theorem cBase_55 : chkBase 1009 58 503 baseT prT drT fmT fzT 55 = true := by decide +kernel
theorem cBase_56 : chkBase 1009 58 503 baseT prT drT fmT fzT 56 = true := by decide +kernel
theorem cBase_57 : chkBase 1009 58 503 baseT prT drT fmT fzT 57 = true := by decide +kernel
theorem cBase_58 : chkBase 1009 58 503 baseT prT drT fmT fzT 58 = true := by decide +kernel
theorem cLenZero : chkInvLen 58 baseT invZeroT = true := by decide +kernel
theorem cRowZero_0 : chkInvRow 1009 58 0 baseT invZeroT 0 = true := by decide +kernel
theorem cRowZero_1 : chkInvRow 1009 58 0 baseT invZeroT 1 = true := by decide +kernel
theorem cRowZero_2 : chkInvRow 1009 58 0 baseT invZeroT 2 = true := by decide +kernel
theorem cRowZero_3 : chkInvRow 1009 58 0 baseT invZeroT 3 = true := by decide +kernel
theorem cRowZero_4 : chkInvRow 1009 58 0 baseT invZeroT 4 = true := by decide +kernel
theorem cRowZero_5 : chkInvRow 1009 58 0 baseT invZeroT 5 = true := by decide +kernel
theorem cRowZero_6 : chkInvRow 1009 58 0 baseT invZeroT 6 = true := by decide +kernel
theorem cRowZero_7 : chkInvRow 1009 58 0 baseT invZeroT 7 = true := by decide +kernel
theorem cRowZero_8 : chkInvRow 1009 58 0 baseT invZeroT 8 = true := by decide +kernel
theorem cRowZero_9 : chkInvRow 1009 58 0 baseT invZeroT 9 = true := by decide +kernel
theorem cRowZero_10 : chkInvRow 1009 58 0 baseT invZeroT 10 = true := by decide +kernel
theorem cRowZero_11 : chkInvRow 1009 58 0 baseT invZeroT 11 = true := by decide +kernel
theorem cRowZero_12 : chkInvRow 1009 58 0 baseT invZeroT 12 = true := by decide +kernel
theorem cRowZero_13 : chkInvRow 1009 58 0 baseT invZeroT 13 = true := by decide +kernel
theorem cRowZero_14 : chkInvRow 1009 58 0 baseT invZeroT 14 = true := by decide +kernel
theorem cRowZero_15 : chkInvRow 1009 58 0 baseT invZeroT 15 = true := by decide +kernel
theorem cRowZero_16 : chkInvRow 1009 58 0 baseT invZeroT 16 = true := by decide +kernel
theorem cRowZero_17 : chkInvRow 1009 58 0 baseT invZeroT 17 = true := by decide +kernel
theorem cRowZero_18 : chkInvRow 1009 58 0 baseT invZeroT 18 = true := by decide +kernel
theorem cRowZero_19 : chkInvRow 1009 58 0 baseT invZeroT 19 = true := by decide +kernel
theorem cRowZero_20 : chkInvRow 1009 58 0 baseT invZeroT 20 = true := by decide +kernel
theorem cRowZero_21 : chkInvRow 1009 58 0 baseT invZeroT 21 = true := by decide +kernel
theorem cRowZero_22 : chkInvRow 1009 58 0 baseT invZeroT 22 = true := by decide +kernel
theorem cRowZero_23 : chkInvRow 1009 58 0 baseT invZeroT 23 = true := by decide +kernel
theorem cRowZero_24 : chkInvRow 1009 58 0 baseT invZeroT 24 = true := by decide +kernel
theorem cRowZero_25 : chkInvRow 1009 58 0 baseT invZeroT 25 = true := by decide +kernel
theorem cRowZero_26 : chkInvRow 1009 58 0 baseT invZeroT 26 = true := by decide +kernel
theorem cRowZero_27 : chkInvRow 1009 58 0 baseT invZeroT 27 = true := by decide +kernel
theorem cRowZero_28 : chkInvRow 1009 58 0 baseT invZeroT 28 = true := by decide +kernel
theorem cRowZero_29 : chkInvRow 1009 58 0 baseT invZeroT 29 = true := by decide +kernel
theorem cRowZero_30 : chkInvRow 1009 58 0 baseT invZeroT 30 = true := by decide +kernel
theorem cRowZero_31 : chkInvRow 1009 58 0 baseT invZeroT 31 = true := by decide +kernel
theorem cRowZero_32 : chkInvRow 1009 58 0 baseT invZeroT 32 = true := by decide +kernel
theorem cRowZero_33 : chkInvRow 1009 58 0 baseT invZeroT 33 = true := by decide +kernel
theorem cRowZero_34 : chkInvRow 1009 58 0 baseT invZeroT 34 = true := by decide +kernel
theorem cRowZero_35 : chkInvRow 1009 58 0 baseT invZeroT 35 = true := by decide +kernel
theorem cRowZero_36 : chkInvRow 1009 58 0 baseT invZeroT 36 = true := by decide +kernel
theorem cRowZero_37 : chkInvRow 1009 58 0 baseT invZeroT 37 = true := by decide +kernel
theorem cRowZero_38 : chkInvRow 1009 58 0 baseT invZeroT 38 = true := by decide +kernel
theorem cRowZero_39 : chkInvRow 1009 58 0 baseT invZeroT 39 = true := by decide +kernel
theorem cRowZero_40 : chkInvRow 1009 58 0 baseT invZeroT 40 = true := by decide +kernel
theorem cRowZero_41 : chkInvRow 1009 58 0 baseT invZeroT 41 = true := by decide +kernel
theorem cRowZero_42 : chkInvRow 1009 58 0 baseT invZeroT 42 = true := by decide +kernel
theorem cRowZero_43 : chkInvRow 1009 58 0 baseT invZeroT 43 = true := by decide +kernel
theorem cRowZero_44 : chkInvRow 1009 58 0 baseT invZeroT 44 = true := by decide +kernel
theorem cRowZero_45 : chkInvRow 1009 58 0 baseT invZeroT 45 = true := by decide +kernel
theorem cRowZero_46 : chkInvRow 1009 58 0 baseT invZeroT 46 = true := by decide +kernel
theorem cRowZero_47 : chkInvRow 1009 58 0 baseT invZeroT 47 = true := by decide +kernel
theorem cRowZero_48 : chkInvRow 1009 58 0 baseT invZeroT 48 = true := by decide +kernel
theorem cRowZero_49 : chkInvRow 1009 58 0 baseT invZeroT 49 = true := by decide +kernel
theorem cRowZero_50 : chkInvRow 1009 58 0 baseT invZeroT 50 = true := by decide +kernel
theorem cRowZero_51 : chkInvRow 1009 58 0 baseT invZeroT 51 = true := by decide +kernel
theorem cRowZero_52 : chkInvRow 1009 58 0 baseT invZeroT 52 = true := by decide +kernel
theorem cRowZero_53 : chkInvRow 1009 58 0 baseT invZeroT 53 = true := by decide +kernel
theorem cRowZero_54 : chkInvRow 1009 58 0 baseT invZeroT 54 = true := by decide +kernel
theorem cRowZero_55 : chkInvRow 1009 58 0 baseT invZeroT 55 = true := by decide +kernel
theorem cRowZero_56 : chkInvRow 1009 58 0 baseT invZeroT 56 = true := by decide +kernel
theorem cRowZero_57 : chkInvRow 1009 58 0 baseT invZeroT 57 = true := by decide +kernel
theorem cLenPlus : chkInvLen 58 baseT invPlusT = true := by decide +kernel
theorem cRowPlus_0 : chkInvRow 1009 58 1 baseT invPlusT 0 = true := by decide +kernel
theorem cRowPlus_1 : chkInvRow 1009 58 1 baseT invPlusT 1 = true := by decide +kernel
theorem cRowPlus_2 : chkInvRow 1009 58 1 baseT invPlusT 2 = true := by decide +kernel
theorem cRowPlus_3 : chkInvRow 1009 58 1 baseT invPlusT 3 = true := by decide +kernel
theorem cRowPlus_4 : chkInvRow 1009 58 1 baseT invPlusT 4 = true := by decide +kernel
theorem cRowPlus_5 : chkInvRow 1009 58 1 baseT invPlusT 5 = true := by decide +kernel
theorem cRowPlus_6 : chkInvRow 1009 58 1 baseT invPlusT 6 = true := by decide +kernel
theorem cRowPlus_7 : chkInvRow 1009 58 1 baseT invPlusT 7 = true := by decide +kernel
theorem cRowPlus_8 : chkInvRow 1009 58 1 baseT invPlusT 8 = true := by decide +kernel
theorem cRowPlus_9 : chkInvRow 1009 58 1 baseT invPlusT 9 = true := by decide +kernel
theorem cRowPlus_10 : chkInvRow 1009 58 1 baseT invPlusT 10 = true := by decide +kernel
theorem cRowPlus_11 : chkInvRow 1009 58 1 baseT invPlusT 11 = true := by decide +kernel
theorem cRowPlus_12 : chkInvRow 1009 58 1 baseT invPlusT 12 = true := by decide +kernel
theorem cRowPlus_13 : chkInvRow 1009 58 1 baseT invPlusT 13 = true := by decide +kernel
theorem cRowPlus_14 : chkInvRow 1009 58 1 baseT invPlusT 14 = true := by decide +kernel
theorem cRowPlus_15 : chkInvRow 1009 58 1 baseT invPlusT 15 = true := by decide +kernel
theorem cRowPlus_16 : chkInvRow 1009 58 1 baseT invPlusT 16 = true := by decide +kernel
theorem cRowPlus_17 : chkInvRow 1009 58 1 baseT invPlusT 17 = true := by decide +kernel
theorem cRowPlus_18 : chkInvRow 1009 58 1 baseT invPlusT 18 = true := by decide +kernel
theorem cRowPlus_19 : chkInvRow 1009 58 1 baseT invPlusT 19 = true := by decide +kernel
theorem cRowPlus_20 : chkInvRow 1009 58 1 baseT invPlusT 20 = true := by decide +kernel
theorem cRowPlus_21 : chkInvRow 1009 58 1 baseT invPlusT 21 = true := by decide +kernel
theorem cRowPlus_22 : chkInvRow 1009 58 1 baseT invPlusT 22 = true := by decide +kernel
theorem cRowPlus_23 : chkInvRow 1009 58 1 baseT invPlusT 23 = true := by decide +kernel
theorem cRowPlus_24 : chkInvRow 1009 58 1 baseT invPlusT 24 = true := by decide +kernel
theorem cRowPlus_25 : chkInvRow 1009 58 1 baseT invPlusT 25 = true := by decide +kernel
theorem cRowPlus_26 : chkInvRow 1009 58 1 baseT invPlusT 26 = true := by decide +kernel
theorem cRowPlus_27 : chkInvRow 1009 58 1 baseT invPlusT 27 = true := by decide +kernel
theorem cRowPlus_28 : chkInvRow 1009 58 1 baseT invPlusT 28 = true := by decide +kernel
theorem cRowPlus_29 : chkInvRow 1009 58 1 baseT invPlusT 29 = true := by decide +kernel
theorem cRowPlus_30 : chkInvRow 1009 58 1 baseT invPlusT 30 = true := by decide +kernel
theorem cRowPlus_31 : chkInvRow 1009 58 1 baseT invPlusT 31 = true := by decide +kernel
theorem cRowPlus_32 : chkInvRow 1009 58 1 baseT invPlusT 32 = true := by decide +kernel
theorem cRowPlus_33 : chkInvRow 1009 58 1 baseT invPlusT 33 = true := by decide +kernel
theorem cRowPlus_34 : chkInvRow 1009 58 1 baseT invPlusT 34 = true := by decide +kernel
theorem cRowPlus_35 : chkInvRow 1009 58 1 baseT invPlusT 35 = true := by decide +kernel
theorem cRowPlus_36 : chkInvRow 1009 58 1 baseT invPlusT 36 = true := by decide +kernel
theorem cRowPlus_37 : chkInvRow 1009 58 1 baseT invPlusT 37 = true := by decide +kernel
theorem cRowPlus_38 : chkInvRow 1009 58 1 baseT invPlusT 38 = true := by decide +kernel
theorem cRowPlus_39 : chkInvRow 1009 58 1 baseT invPlusT 39 = true := by decide +kernel
theorem cRowPlus_40 : chkInvRow 1009 58 1 baseT invPlusT 40 = true := by decide +kernel
theorem cRowPlus_41 : chkInvRow 1009 58 1 baseT invPlusT 41 = true := by decide +kernel
theorem cRowPlus_42 : chkInvRow 1009 58 1 baseT invPlusT 42 = true := by decide +kernel
theorem cRowPlus_43 : chkInvRow 1009 58 1 baseT invPlusT 43 = true := by decide +kernel
theorem cRowPlus_44 : chkInvRow 1009 58 1 baseT invPlusT 44 = true := by decide +kernel
theorem cRowPlus_45 : chkInvRow 1009 58 1 baseT invPlusT 45 = true := by decide +kernel
theorem cRowPlus_46 : chkInvRow 1009 58 1 baseT invPlusT 46 = true := by decide +kernel
theorem cRowPlus_47 : chkInvRow 1009 58 1 baseT invPlusT 47 = true := by decide +kernel
theorem cRowPlus_48 : chkInvRow 1009 58 1 baseT invPlusT 48 = true := by decide +kernel
theorem cRowPlus_49 : chkInvRow 1009 58 1 baseT invPlusT 49 = true := by decide +kernel
theorem cRowPlus_50 : chkInvRow 1009 58 1 baseT invPlusT 50 = true := by decide +kernel
theorem cRowPlus_51 : chkInvRow 1009 58 1 baseT invPlusT 51 = true := by decide +kernel
theorem cRowPlus_52 : chkInvRow 1009 58 1 baseT invPlusT 52 = true := by decide +kernel
theorem cRowPlus_53 : chkInvRow 1009 58 1 baseT invPlusT 53 = true := by decide +kernel
theorem cRowPlus_54 : chkInvRow 1009 58 1 baseT invPlusT 54 = true := by decide +kernel
theorem cRowPlus_55 : chkInvRow 1009 58 1 baseT invPlusT 55 = true := by decide +kernel
theorem cRowPlus_56 : chkInvRow 1009 58 1 baseT invPlusT 56 = true := by decide +kernel
theorem cRowPlus_57 : chkInvRow 1009 58 1 baseT invPlusT 57 = true := by decide +kernel
theorem cLenMinus : chkInvLen 58 baseT invMinusT = true := by decide +kernel
theorem cRowMinus_0 : chkInvRow 1009 58 1008 baseT invMinusT 0 = true := by decide +kernel
theorem cRowMinus_1 : chkInvRow 1009 58 1008 baseT invMinusT 1 = true := by decide +kernel
theorem cRowMinus_2 : chkInvRow 1009 58 1008 baseT invMinusT 2 = true := by decide +kernel
theorem cRowMinus_3 : chkInvRow 1009 58 1008 baseT invMinusT 3 = true := by decide +kernel
theorem cRowMinus_4 : chkInvRow 1009 58 1008 baseT invMinusT 4 = true := by decide +kernel
theorem cRowMinus_5 : chkInvRow 1009 58 1008 baseT invMinusT 5 = true := by decide +kernel
theorem cRowMinus_6 : chkInvRow 1009 58 1008 baseT invMinusT 6 = true := by decide +kernel
theorem cRowMinus_7 : chkInvRow 1009 58 1008 baseT invMinusT 7 = true := by decide +kernel
theorem cRowMinus_8 : chkInvRow 1009 58 1008 baseT invMinusT 8 = true := by decide +kernel
theorem cRowMinus_9 : chkInvRow 1009 58 1008 baseT invMinusT 9 = true := by decide +kernel
theorem cRowMinus_10 : chkInvRow 1009 58 1008 baseT invMinusT 10 = true := by decide +kernel
theorem cRowMinus_11 : chkInvRow 1009 58 1008 baseT invMinusT 11 = true := by decide +kernel
theorem cRowMinus_12 : chkInvRow 1009 58 1008 baseT invMinusT 12 = true := by decide +kernel
theorem cRowMinus_13 : chkInvRow 1009 58 1008 baseT invMinusT 13 = true := by decide +kernel
theorem cRowMinus_14 : chkInvRow 1009 58 1008 baseT invMinusT 14 = true := by decide +kernel
theorem cRowMinus_15 : chkInvRow 1009 58 1008 baseT invMinusT 15 = true := by decide +kernel
theorem cRowMinus_16 : chkInvRow 1009 58 1008 baseT invMinusT 16 = true := by decide +kernel
theorem cRowMinus_17 : chkInvRow 1009 58 1008 baseT invMinusT 17 = true := by decide +kernel
theorem cRowMinus_18 : chkInvRow 1009 58 1008 baseT invMinusT 18 = true := by decide +kernel
theorem cRowMinus_19 : chkInvRow 1009 58 1008 baseT invMinusT 19 = true := by decide +kernel
theorem cRowMinus_20 : chkInvRow 1009 58 1008 baseT invMinusT 20 = true := by decide +kernel
theorem cRowMinus_21 : chkInvRow 1009 58 1008 baseT invMinusT 21 = true := by decide +kernel
theorem cRowMinus_22 : chkInvRow 1009 58 1008 baseT invMinusT 22 = true := by decide +kernel
theorem cRowMinus_23 : chkInvRow 1009 58 1008 baseT invMinusT 23 = true := by decide +kernel
theorem cRowMinus_24 : chkInvRow 1009 58 1008 baseT invMinusT 24 = true := by decide +kernel
theorem cRowMinus_25 : chkInvRow 1009 58 1008 baseT invMinusT 25 = true := by decide +kernel
theorem cRowMinus_26 : chkInvRow 1009 58 1008 baseT invMinusT 26 = true := by decide +kernel
theorem cRowMinus_27 : chkInvRow 1009 58 1008 baseT invMinusT 27 = true := by decide +kernel
theorem cRowMinus_28 : chkInvRow 1009 58 1008 baseT invMinusT 28 = true := by decide +kernel
theorem cRowMinus_29 : chkInvRow 1009 58 1008 baseT invMinusT 29 = true := by decide +kernel
theorem cRowMinus_30 : chkInvRow 1009 58 1008 baseT invMinusT 30 = true := by decide +kernel
theorem cRowMinus_31 : chkInvRow 1009 58 1008 baseT invMinusT 31 = true := by decide +kernel
theorem cRowMinus_32 : chkInvRow 1009 58 1008 baseT invMinusT 32 = true := by decide +kernel
theorem cRowMinus_33 : chkInvRow 1009 58 1008 baseT invMinusT 33 = true := by decide +kernel
theorem cRowMinus_34 : chkInvRow 1009 58 1008 baseT invMinusT 34 = true := by decide +kernel
theorem cRowMinus_35 : chkInvRow 1009 58 1008 baseT invMinusT 35 = true := by decide +kernel
theorem cRowMinus_36 : chkInvRow 1009 58 1008 baseT invMinusT 36 = true := by decide +kernel
theorem cRowMinus_37 : chkInvRow 1009 58 1008 baseT invMinusT 37 = true := by decide +kernel
theorem cRowMinus_38 : chkInvRow 1009 58 1008 baseT invMinusT 38 = true := by decide +kernel
theorem cRowMinus_39 : chkInvRow 1009 58 1008 baseT invMinusT 39 = true := by decide +kernel
theorem cRowMinus_40 : chkInvRow 1009 58 1008 baseT invMinusT 40 = true := by decide +kernel
theorem cRowMinus_41 : chkInvRow 1009 58 1008 baseT invMinusT 41 = true := by decide +kernel
theorem cRowMinus_42 : chkInvRow 1009 58 1008 baseT invMinusT 42 = true := by decide +kernel
theorem cRowMinus_43 : chkInvRow 1009 58 1008 baseT invMinusT 43 = true := by decide +kernel
theorem cRowMinus_44 : chkInvRow 1009 58 1008 baseT invMinusT 44 = true := by decide +kernel
theorem cRowMinus_45 : chkInvRow 1009 58 1008 baseT invMinusT 45 = true := by decide +kernel
theorem cRowMinus_46 : chkInvRow 1009 58 1008 baseT invMinusT 46 = true := by decide +kernel
theorem cRowMinus_47 : chkInvRow 1009 58 1008 baseT invMinusT 47 = true := by decide +kernel
theorem cRowMinus_48 : chkInvRow 1009 58 1008 baseT invMinusT 48 = true := by decide +kernel
theorem cRowMinus_49 : chkInvRow 1009 58 1008 baseT invMinusT 49 = true := by decide +kernel
theorem cRowMinus_50 : chkInvRow 1009 58 1008 baseT invMinusT 50 = true := by decide +kernel
theorem cRowMinus_51 : chkInvRow 1009 58 1008 baseT invMinusT 51 = true := by decide +kernel
theorem cRowMinus_52 : chkInvRow 1009 58 1008 baseT invMinusT 52 = true := by decide +kernel
theorem cRowMinus_53 : chkInvRow 1009 58 1008 baseT invMinusT 53 = true := by decide +kernel
theorem cRowMinus_54 : chkInvRow 1009 58 1008 baseT invMinusT 54 = true := by decide +kernel
theorem cRowMinus_55 : chkInvRow 1009 58 1008 baseT invMinusT 55 = true := by decide +kernel
theorem cRowMinus_56 : chkInvRow 1009 58 1008 baseT invMinusT 56 = true := by decide +kernel
theorem cRowMinus_57 : chkInvRow 1009 58 1008 baseT invMinusT 57 = true := by decide +kernel

theorem cBase_all : ∀ r, r < 58 + 1 → chkBase 1009 58 503 baseT prT drT fmT fzT r = true := by
  intro r hr
  interval_cases r
  · exact cBase_0
  · exact cBase_1
  · exact cBase_2
  · exact cBase_3
  · exact cBase_4
  · exact cBase_5
  · exact cBase_6
  · exact cBase_7
  · exact cBase_8
  · exact cBase_9
  · exact cBase_10
  · exact cBase_11
  · exact cBase_12
  · exact cBase_13
  · exact cBase_14
  · exact cBase_15
  · exact cBase_16
  · exact cBase_17
  · exact cBase_18
  · exact cBase_19
  · exact cBase_20
  · exact cBase_21
  · exact cBase_22
  · exact cBase_23
  · exact cBase_24
  · exact cBase_25
  · exact cBase_26
  · exact cBase_27
  · exact cBase_28
  · exact cBase_29
  · exact cBase_30
  · exact cBase_31
  · exact cBase_32
  · exact cBase_33
  · exact cBase_34
  · exact cBase_35
  · exact cBase_36
  · exact cBase_37
  · exact cBase_38
  · exact cBase_39
  · exact cBase_40
  · exact cBase_41
  · exact cBase_42
  · exact cBase_43
  · exact cBase_44
  · exact cBase_45
  · exact cBase_46
  · exact cBase_47
  · exact cBase_48
  · exact cBase_49
  · exact cBase_50
  · exact cBase_51
  · exact cBase_52
  · exact cBase_53
  · exact cBase_54
  · exact cBase_55
  · exact cBase_56
  · exact cBase_57
  · exact cBase_58

theorem cRowZero_all : ∀ r, r < 58 → chkInvRow 1009 58 0 baseT invZeroT r = true := by
  intro r hr
  interval_cases r
  · exact cRowZero_0
  · exact cRowZero_1
  · exact cRowZero_2
  · exact cRowZero_3
  · exact cRowZero_4
  · exact cRowZero_5
  · exact cRowZero_6
  · exact cRowZero_7
  · exact cRowZero_8
  · exact cRowZero_9
  · exact cRowZero_10
  · exact cRowZero_11
  · exact cRowZero_12
  · exact cRowZero_13
  · exact cRowZero_14
  · exact cRowZero_15
  · exact cRowZero_16
  · exact cRowZero_17
  · exact cRowZero_18
  · exact cRowZero_19
  · exact cRowZero_20
  · exact cRowZero_21
  · exact cRowZero_22
  · exact cRowZero_23
  · exact cRowZero_24
  · exact cRowZero_25
  · exact cRowZero_26
  · exact cRowZero_27
  · exact cRowZero_28
  · exact cRowZero_29
  · exact cRowZero_30
  · exact cRowZero_31
  · exact cRowZero_32
  · exact cRowZero_33
  · exact cRowZero_34
  · exact cRowZero_35
  · exact cRowZero_36
  · exact cRowZero_37
  · exact cRowZero_38
  · exact cRowZero_39
  · exact cRowZero_40
  · exact cRowZero_41
  · exact cRowZero_42
  · exact cRowZero_43
  · exact cRowZero_44
  · exact cRowZero_45
  · exact cRowZero_46
  · exact cRowZero_47
  · exact cRowZero_48
  · exact cRowZero_49
  · exact cRowZero_50
  · exact cRowZero_51
  · exact cRowZero_52
  · exact cRowZero_53
  · exact cRowZero_54
  · exact cRowZero_55
  · exact cRowZero_56
  · exact cRowZero_57

theorem cRowPlus_all : ∀ r, r < 58 → chkInvRow 1009 58 1 baseT invPlusT r = true := by
  intro r hr
  interval_cases r
  · exact cRowPlus_0
  · exact cRowPlus_1
  · exact cRowPlus_2
  · exact cRowPlus_3
  · exact cRowPlus_4
  · exact cRowPlus_5
  · exact cRowPlus_6
  · exact cRowPlus_7
  · exact cRowPlus_8
  · exact cRowPlus_9
  · exact cRowPlus_10
  · exact cRowPlus_11
  · exact cRowPlus_12
  · exact cRowPlus_13
  · exact cRowPlus_14
  · exact cRowPlus_15
  · exact cRowPlus_16
  · exact cRowPlus_17
  · exact cRowPlus_18
  · exact cRowPlus_19
  · exact cRowPlus_20
  · exact cRowPlus_21
  · exact cRowPlus_22
  · exact cRowPlus_23
  · exact cRowPlus_24
  · exact cRowPlus_25
  · exact cRowPlus_26
  · exact cRowPlus_27
  · exact cRowPlus_28
  · exact cRowPlus_29
  · exact cRowPlus_30
  · exact cRowPlus_31
  · exact cRowPlus_32
  · exact cRowPlus_33
  · exact cRowPlus_34
  · exact cRowPlus_35
  · exact cRowPlus_36
  · exact cRowPlus_37
  · exact cRowPlus_38
  · exact cRowPlus_39
  · exact cRowPlus_40
  · exact cRowPlus_41
  · exact cRowPlus_42
  · exact cRowPlus_43
  · exact cRowPlus_44
  · exact cRowPlus_45
  · exact cRowPlus_46
  · exact cRowPlus_47
  · exact cRowPlus_48
  · exact cRowPlus_49
  · exact cRowPlus_50
  · exact cRowPlus_51
  · exact cRowPlus_52
  · exact cRowPlus_53
  · exact cRowPlus_54
  · exact cRowPlus_55
  · exact cRowPlus_56
  · exact cRowPlus_57

theorem cRowMinus_all : ∀ r, r < 58 → chkInvRow 1009 58 1008 baseT invMinusT r = true := by
  intro r hr
  interval_cases r
  · exact cRowMinus_0
  · exact cRowMinus_1
  · exact cRowMinus_2
  · exact cRowMinus_3
  · exact cRowMinus_4
  · exact cRowMinus_5
  · exact cRowMinus_6
  · exact cRowMinus_7
  · exact cRowMinus_8
  · exact cRowMinus_9
  · exact cRowMinus_10
  · exact cRowMinus_11
  · exact cRowMinus_12
  · exact cRowMinus_13
  · exact cRowMinus_14
  · exact cRowMinus_15
  · exact cRowMinus_16
  · exact cRowMinus_17
  · exact cRowMinus_18
  · exact cRowMinus_19
  · exact cRowMinus_20
  · exact cRowMinus_21
  · exact cRowMinus_22
  · exact cRowMinus_23
  · exact cRowMinus_24
  · exact cRowMinus_25
  · exact cRowMinus_26
  · exact cRowMinus_27
  · exact cRowMinus_28
  · exact cRowMinus_29
  · exact cRowMinus_30
  · exact cRowMinus_31
  · exact cRowMinus_32
  · exact cRowMinus_33
  · exact cRowMinus_34
  · exact cRowMinus_35
  · exact cRowMinus_36
  · exact cRowMinus_37
  · exact cRowMinus_38
  · exact cRowMinus_39
  · exact cRowMinus_40
  · exact cRowMinus_41
  · exact cRowMinus_42
  · exact cRowMinus_43
  · exact cRowMinus_44
  · exact cRowMinus_45
  · exact cRowMinus_46
  · exact cRowMinus_47
  · exact cRowMinus_48
  · exact cRowMinus_49
  · exact cRowMinus_50
  · exact cRowMinus_51
  · exact cRowMinus_52
  · exact cRowMinus_53
  · exact cRowMinus_54
  · exact cRowMinus_55
  · exact cRowMinus_56
  · exact cRowMinus_57

theorem hE : ∀ (r k : ℕ) (hk : k < Odd.design.n0), r < Odd.design.n0 + 1 →
    baseFilteredContraction Odd.design 1009 r ⟨k, hk⟩ = CertMod.entry 1009 baseT r k :=
  base_sound Odd.design 1009 (by norm_num) (by decide) (by decide) msT bmT bpT ivT h1T wT momT zetT fmT fzT
    prT drT baseT 503 hW hcN cIV cMS cBM cBP cMT cH1 cZT cPoly cFM cFZ cLen cBase_all

/-- **D58.C3.**  The three residue determinants of the base matrices are nonzero modulo 1009. -/
theorem c3_d58 :
    (baseB0Residue Odd.design 1009).det ≠ 0 ∧
      (baseB0Residue Odd.design 1009 + baseB1Residue Odd.design 1009).det ≠ 0 ∧
      (baseB0Residue Odd.design 1009 - baseB1Residue Odd.design 1009).det ≠ 0 :=
  c3_of_certificate' Odd.design 1009 baseT _ _ _ hE
    (chkInv_sound 0 0 (by simp) cLenZero cRowZero_all)
    (chkInv_sound 1 1 (by simp) cLenPlus cRowPlus_all)
    (chkInv_sound 1008 (-1) (by
      have : ((1008 : ℕ) : ZMod 1009) = -1 := by decide
      exact this) cLenMinus cRowMinus_all)

end C3
end D58
end CatalanMeasure.GenD

#print axioms CatalanMeasure.GenD.D58.C3.c3_d58
