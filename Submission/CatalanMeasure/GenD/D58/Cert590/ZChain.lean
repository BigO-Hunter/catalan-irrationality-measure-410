module

public import Submission.CatalanMeasure.GenD.D58.Cert590.ZDefs
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkPc0
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkPc1
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkPc2
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkPc3
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkVc0
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkVc1
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkVc2
public import Submission.CatalanMeasure.GenD.D58.Cert590.ZChunkVc3

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem uPcN_end : uClenN (((((Pc.reverse).drop 40).drop 40).drop 40).drop 40) uPcN4 = uPcN4 := by decide +kernel
theorem uClenN_Pc : uClenN Pc.reverse ([], []) = uPcN4 :=
  uClenN_chain (Pc.reverse) 40 uPcN_c0 (uClenN_chain ((Pc.reverse).drop 40) 40 uPcN_c1 (uClenN_chain (((Pc.reverse).drop 40).drop 40) 40 uPcN_c2 (uClenN_chain ((((Pc.reverse).drop 40).drop 40).drop 40) 40 uPcN_c3 (uPcN_end))))
theorem uSum_Pc : uSum Pc = shl 2 uPcN4.1 := uSum_of_N Pc uClenN_Pc
theorem uVcN_end : uClenN (((((Vc.reverse).drop 40).drop 40).drop 40).drop 40) uVcN4 = uVcN4 := by decide +kernel
theorem uClenN_Vc : uClenN Vc.reverse ([], []) = uVcN4 :=
  uClenN_chain (Vc.reverse) 40 uVcN_c0 (uClenN_chain ((Vc.reverse).drop 40) 40 uVcN_c1 (uClenN_chain (((Vc.reverse).drop 40).drop 40) 40 uVcN_c2 (uClenN_chain ((((Vc.reverse).drop 40).drop 40).drop 40) 40 uVcN_c3 (uVcN_end))))
theorem uSum_Vc : uSum Vc = shl 2 uVcN4.1 := uSum_of_N Vc uClenN_Vc
end CatalanMeasure.GenD.D58.Cert590
