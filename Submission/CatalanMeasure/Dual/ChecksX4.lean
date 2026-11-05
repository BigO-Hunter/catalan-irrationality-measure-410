module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_72 : okX ((-1652677 / 10000000 : ℚ), (-313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_73 : okX ((-313 / 2000 : ℚ), (-347107 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_74 : okX ((-347107 / 2500000 : ℚ), (-694213 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_75 : okX ((-694213 / 5000000 : ℚ), (-1 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_76 : okX ((-1 / 8 : ℚ), (0 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_77 : okX ((0 : ℚ), (1 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_78 : okX ((1 / 8 : ℚ), (1359367 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_79 : okX ((1359367 / 10000000 : ℚ), (1359369 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_80 : okX ((1359369 / 10000000 : ℚ), (313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_81 : okX ((313 / 2000 : ℚ), (13021 / 80000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_82 : okX ((13021 / 80000 : ℚ), (1627627 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_83 : okX ((1627627 / 10000000 : ℚ), (47 / 250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_84 : okX ((47 / 250 : ℚ), (1070349 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_85 : okX ((1070349 / 5000000 : ℚ), (2140701 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_86 : okX ((2140701 / 10000000 : ℚ), (1 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_87 : okX ((1 / 4 : ℚ), (317849 / 1250000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_88 : okX ((317849 / 1250000 : ℚ), (1271397 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_89 : okX ((1271397 / 5000000 : ℚ), (39 / 125 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.Dual
