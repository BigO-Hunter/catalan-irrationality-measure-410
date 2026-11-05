module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_18 : okY ((891817 / 5000000 : ℚ), (47 / 250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_19 : okY ((47 / 250 : ℚ), (2370543 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_20 : okY ((2370543 / 10000000 : ℚ), (474109 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_21 : okY ((474109 / 2000000 : ℚ), (1 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_22 : okY ((1 / 4 : ℚ), (181191 / 625000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_23 : okY ((181191 / 625000 : ℚ), (2899059 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_24 : okY ((2899059 / 10000000 : ℚ), (39 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_25 : okY ((39 / 125 : ℚ), (1759763 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_26 : okY ((1759763 / 5000000 : ℚ), (3519529 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_27 : okY ((3519529 / 10000000 : ℚ), (3 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_28 : okY ((3 / 8 : ℚ), (1018193 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_29 : okY ((1018193 / 2500000 : ℚ), (2036387 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_30 : okY ((2036387 / 5000000 : ℚ), (219 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_31 : okY ((219 / 500 : ℚ), (2339637 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_32 : okY ((2339637 / 5000000 : ℚ), (1169819 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_33 : okY ((1169819 / 2500000 : ℚ), (1 / 2 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_34 : okY ((1 / 2 : ℚ), (1044229 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_35 : okY ((1044229 / 2000000 : ℚ), (1305287 / 2500000 : ℚ), true) = true := by decide +kernel

end CatalanMeasure.Dual
