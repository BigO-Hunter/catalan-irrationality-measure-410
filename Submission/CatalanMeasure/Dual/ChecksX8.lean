module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_144 : okX ((969 / 1000 : ℚ), (9728999 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_145 : okX ((9728999 / 10000000 : ℚ), (9729001 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_146 : okX ((9729001 / 10000000 : ℚ), (1969 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_147 : okX ((1969 / 2000 : ℚ), (2461567 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_148 : okX ((2461567 / 2500000 : ℚ), (984627 / 1000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_149 : okX ((984627 / 1000000 : ℚ), (19767 / 20000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_150 : okX ((19767 / 20000 : ℚ), (79137 / 80000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_151 : okX ((79137 / 80000 : ℚ), (309129 / 312500 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_152 : okX ((309129 / 312500 : ℚ), (4961 / 5000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_153 : okX ((4961 / 5000 : ℚ), (1 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.Dual
