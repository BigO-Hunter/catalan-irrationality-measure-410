module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_0 : okX ((-1 : ℚ), (-2499633 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_1 : okX ((-2499633 / 2500000 : ℚ), (-999853 / 1000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_2 : okX ((-999853 / 1000000 : ℚ), (-49951 / 50000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_3 : okX ((-49951 / 50000 : ℚ), (-2497297 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_4 : okX ((-2497297 / 2500000 : ℚ), (-4994593 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_5 : okX ((-4994593 / 5000000 : ℚ), (-19961 / 20000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_6 : okX ((-19961 / 20000 : ℚ), (-9961 / 10000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_7 : okX ((-9961 / 10000 : ℚ), (-622469 / 625000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_8 : okX ((-622469 / 625000 : ℚ), (-9959501 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_9 : okX ((-9959501 / 10000000 : ℚ), (-4961 / 5000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_10 : okX ((-4961 / 5000 : ℚ), (-4948529 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_11 : okX ((-4948529 / 5000000 : ℚ), (-309283 / 312500 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_12 : okX ((-309283 / 312500 : ℚ), (-1969 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_13 : okX ((-1969 / 2000 : ℚ), (-9793329 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_14 : okX ((-9793329 / 10000000 : ℚ), (-4896663 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_15 : okX ((-4896663 / 5000000 : ℚ), (-969 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_16 : okX ((-969 / 1000 : ℚ), (-1928811 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_17 : okX ((-1928811 / 2000000 : ℚ), (-2411013 / 2500000 : ℚ), true) = true := by decide +kernel

end CatalanMeasure.Dual
