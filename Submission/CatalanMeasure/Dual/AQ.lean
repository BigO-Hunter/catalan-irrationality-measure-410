module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem hAQX : fracSum (rowFracs Pc Vc P V) = (AX, QX) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hAQY : fracSum (colFracs Vc V) = (AY, QY) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hchainX : rowCheck P V AX planX = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hchainY : colCheck V AY planY = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hendX : rowEndOK Pc Vc P V MX = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hIntAX : AX = CatalanMeasure.Cert.lpSmul scaleX (AXZ.map (fun (z : ℤ) => (z : ℚ))) := by decide +kernel
theorem hScaleX : scaleX ≠ 0 := by decide +kernel
set_option maxRecDepth 1000000 in
theorem hIntAY : AY = CatalanMeasure.Cert.lpSmul scaleY (AYZ.map (fun (z : ℤ) => (z : ℚ))) := by decide +kernel
theorem hScaleY : scaleY ≠ 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hIntQX : QX = CatalanMeasure.Cert.lpSmul scaleQX (QXZ.map (fun (z : ℤ) => (z : ℚ))) := by decide +kernel
set_option maxRecDepth 1000000 in
theorem hIntQY : QY = CatalanMeasure.Cert.lpSmul scaleQY (QYZ.map (fun (z : ℤ) => (z : ℚ))) := by decide +kernel

end CatalanMeasure.Dual
