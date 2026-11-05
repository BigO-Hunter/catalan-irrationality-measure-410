module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_72 : okY ((4832523 / 5000000 : ℚ), (969 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_73 : okY ((969 / 1000 : ℚ), (391197 / 400000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_74 : okY ((391197 / 400000 : ℚ), (9779927 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_75 : okY ((9779927 / 10000000 : ℚ), (1969 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_76 : okY ((1969 / 2000 : ℚ), (308567 / 312500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_77 : okY ((308567 / 312500 : ℚ), (4937073 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_78 : okY ((4937073 / 5000000 : ℚ), (4961 / 5000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_79 : okY ((4961 / 5000 : ℚ), (1240819 / 1250000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_80 : okY ((1240819 / 1250000 : ℚ), (4963277 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_81 : okY ((4963277 / 5000000 : ℚ), (9961 / 10000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_82 : okY ((9961 / 10000 : ℚ), (2491299 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_83 : okY ((2491299 / 2500000 : ℚ), (4982599 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_84 : okY ((4982599 / 5000000 : ℚ), (19961 / 20000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_85 : okY ((19961 / 20000 : ℚ), (9981923 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_86 : okY ((9981923 / 10000000 : ℚ), (399277 / 400000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_87 : okY ((399277 / 400000 : ℚ), (49951 / 50000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_88 : okY ((49951 / 50000 : ℚ), (9993059 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_89 : okY ((9993059 / 10000000 : ℚ), (9993061 / 10000000 : ℚ), true) = true := by decide +kernel

end CatalanMeasure.Dual
