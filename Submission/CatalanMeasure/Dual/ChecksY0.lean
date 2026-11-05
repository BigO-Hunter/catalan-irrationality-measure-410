module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_0 : okY ((0 : ℚ), (31 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_1 : okY ((31 / 2000 : ℚ), (38777 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_2 : okY ((38777 / 2500000 : ℚ), (15511 / 1000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_3 : okY ((15511 / 1000000 : ℚ), (29 / 1250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_4 : okY ((29 / 1250 : ℚ), (139351 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_5 : okY ((139351 / 5000000 : ℚ), (55741 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_6 : okY ((55741 / 2000000 : ℚ), (31 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_7 : okY ((31 / 1000 : ℚ), (143619 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_8 : okY ((143619 / 2500000 : ℚ), (287239 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_9 : okY ((287239 / 5000000 : ℚ), (31 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_10 : okY ((31 / 500 : ℚ), (86461 / 1000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_11 : okY ((86461 / 1000000 : ℚ), (216153 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_12 : okY ((216153 / 2500000 : ℚ), (1 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_13 : okY ((1 / 8 : ℚ), (670001 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_14 : okY ((670001 / 5000000 : ℚ), (268001 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_15 : okY ((268001 / 2000000 : ℚ), (313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_16 : okY ((313 / 2000 : ℚ), (111477 / 625000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_17 : okY ((111477 / 625000 : ℚ), (891817 / 5000000 : ℚ), true) = true := by decide +kernel

end CatalanMeasure.Dual
