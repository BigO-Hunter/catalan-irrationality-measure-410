module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_90 : okY ((9993061 / 10000000 : ℚ), (99951 / 100000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_91 : okY ((99951 / 100000 : ℚ), (1249567 / 1250000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_92 : okY ((1249567 / 1250000 : ℚ), (4998269 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_93 : okY ((4998269 / 5000000 : ℚ), (1 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.Dual
