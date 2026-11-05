module
public import Submission.CatalanMeasure.GenD.D58.FirstCert.FieldsData
@[expose] public section
namespace CatalanMeasure.GenD.D58.FirstCert
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem hAQX : fracSum (shiftedRowFracs R Pc Vc P V)=(AX,QX) := by decide +kernel
theorem hAQY : fracSum (shiftedColumnFracs C Vc V)=(AY,QY) := by decide +kernel
end CatalanMeasure.GenD.D58.FirstCert
