module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_108 : okX ((5 / 8 : ℚ), (1269159 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_109 : okX ((1269159 / 2000000 : ℚ), (3172899 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_110 : okX ((3172899 / 5000000 : ℚ), (1313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_111 : okX ((1313 / 2000 : ℚ), (679949 / 1000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_112 : okX ((679949 / 1000000 : ℚ), (1699873 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_113 : okX ((1699873 / 2500000 : ℚ), (86 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_114 : okX ((86 / 125 : ℚ), (454877 / 625000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_115 : okX ((454877 / 625000 : ℚ), (3639017 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_116 : okX ((3639017 / 5000000 : ℚ), (3 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_117 : okX ((3 / 4 : ℚ), (7666103 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_118 : okX ((7666103 / 10000000 : ℚ), (1533221 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_119 : okX ((1533221 / 2000000 : ℚ), (781 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_120 : okX ((781 / 1000 : ℚ), (8068027 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_121 : okX ((8068027 / 10000000 : ℚ), (8068029 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_122 : okX ((8068029 / 10000000 : ℚ), (203 / 250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_123 : okX ((203 / 250 : ℚ), (4185313 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_124 : okX ((4185313 / 5000000 : ℚ), (2092657 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_125 : okX ((2092657 / 2500000 : ℚ), (1687 / 2000 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.Dual
