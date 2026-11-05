module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_36 : okY ((1305287 / 2500000 : ℚ), (281 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_37 : okY ((281 / 500 : ℚ), (5786963 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_38 : okY ((5786963 / 10000000 : ℚ), (1157393 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_39 : okY ((1157393 / 2000000 : ℚ), (5 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_40 : okY ((5 / 8 : ℚ), (1573537 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_41 : okY ((1573537 / 2500000 : ℚ), (125883 / 200000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_42 : okY ((125883 / 200000 : ℚ), (1313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_43 : okY ((1313 / 2000 : ℚ), (1360301 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_44 : okY ((1360301 / 2000000 : ℚ), (1700377 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_45 : okY ((1700377 / 2500000 : ℚ), (86 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_46 : okY ((86 / 125 : ℚ), (90731 / 125000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_47 : okY ((90731 / 125000 : ℚ), (7258483 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_48 : okY ((7258483 / 10000000 : ℚ), (3 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_49 : okY ((3 / 4 : ℚ), (3847713 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_50 : okY ((3847713 / 5000000 : ℚ), (1923857 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_51 : okY ((1923857 / 2500000 : ℚ), (781 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_52 : okY ((781 / 1000 : ℚ), (8091167 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_53 : okY ((8091167 / 10000000 : ℚ), (8091169 / 10000000 : ℚ), true) = true := by decide +kernel

end CatalanMeasure.Dual
