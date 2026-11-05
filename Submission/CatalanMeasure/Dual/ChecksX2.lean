module

public import Submission.CatalanMeasure.Dual.Data

@[expose] public section

namespace CatalanMeasure.Dual

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_36 : okX ((-7772839 / 10000000 : ℚ), (-3 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_37 : okX ((-3 / 4 : ℚ), (-7322707 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_38 : okX ((-7322707 / 10000000 : ℚ), (-1464541 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_39 : okX ((-1464541 / 2000000 : ℚ), (-86 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_40 : okX ((-86 / 125 : ℚ), (-3419929 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_41 : okX ((-3419929 / 5000000 : ℚ), (-427491 / 625000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_42 : okX ((-427491 / 625000 : ℚ), (-1313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_43 : okX ((-1313 / 2000 : ℚ), (-3169377 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_44 : okX ((-3169377 / 5000000 : ℚ), (-6338751 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_45 : okX ((-6338751 / 10000000 : ℚ), (-5 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_46 : okX ((-5 / 8 : ℚ), (-2901501 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_47 : okX ((-2901501 / 5000000 : ℚ), (-5803 / 10000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_48 : okX ((-5803 / 10000 : ℚ), (-281 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_49 : okX ((-281 / 500 : ℚ), (-659381 / 1250000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_50 : okX ((-659381 / 1250000 : ℚ), (-2637523 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_51 : okX ((-2637523 / 5000000 : ℚ), (-1 / 2 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_52 : okX ((-1 / 2 : ℚ), (-1176213 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_53 : okX ((-1176213 / 2500000 : ℚ), (-94097 / 200000 : ℚ), true) = true := by decide +kernel

end CatalanMeasure.Dual
