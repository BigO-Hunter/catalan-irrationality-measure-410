module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem hNP : normOK Pc P NP = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hNV : normOK Vc V NV = true := by decide +kernel

end CatalanMeasure.Dual
