module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_90 : okX ((39 / 125 : ℚ), (1565671 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_91 : okX ((1565671 / 5000000 : ℚ), (626269 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_92 : okX ((626269 / 2000000 : ℚ), (687 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_93 : okX ((687 / 2000 : ℚ), (3612827 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_94 : okX ((3612827 / 10000000 : ℚ), (361283 / 1000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_95 : okX ((361283 / 1000000 : ℚ), (3 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_96 : okX ((3 / 8 : ℚ), (4218749 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_97 : okX ((4218749 / 10000000 : ℚ), (32959 / 78125 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_98 : okX ((32959 / 78125 : ℚ), (219 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_99 : okX ((219 / 500 : ℚ), (1181429 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_100 : okX ((1181429 / 2500000 : ℚ), (2362859 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_101 : okX ((2362859 / 5000000 : ℚ), (1 / 2 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_102 : okX ((1 / 2 : ℚ), (5311151 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_103 : okX ((5311151 / 10000000 : ℚ), (2655577 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_104 : okX ((2655577 / 5000000 : ℚ), (281 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_105 : okX ((281 / 500 : ℚ), (1451311 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_106 : okX ((1451311 / 2500000 : ℚ), (2902623 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_107 : okX ((2902623 / 5000000 : ℚ), (5 / 8 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.Dual
