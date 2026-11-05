module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkP

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed

def gCpN : List ℤ := raw_ints% [695954170653, 69494745965, -221407844191, -67513598227, 120574730734, 64310144073, -73707940530, -60025634810, 45459152458, 54845446157, -26293235347, -48987819888, 12590564093, 42690878863, -2665077765, -36198856931, -4406014878, 29748519157, 9210086351, -23556702742, -12177507020, 17809790677, 13661148837, -12655750780, -13971703907, 8199149528, 13391656313, -4499303690, -12178636762, 1571485066, 10563753756, 609134019, -8748069932, -2101295994, 6899105179, 2989872037, -5148473140, -3377187612, 3591233618, 3374183020]
def gCp : List ℚ := gCpN.map (fun n : ℤ => (n : ℚ) / 2 ^ 40)
def c0Cp : ℚ := (498365778750 : ℤ) / 2 ^ 40
def PnCp : List ℤ := raw_ints% [-31290375122, 308959680000, 32970151773360, 398319492155896, -190007064817728, -19950904564409184, -28523694165903264, 499365088345185536, 1004818154276947712, -7725940327874373888, -17232133111477730304, 80971973764940772352, 186736816872109490176, -606389088807903490048, -1405636490154550050816, 3360093022462688247808, 7726752852793250381824, -14107898033232675274752, -31978096164376374673408, 45612436614991748268032, 101598304280700737028096, -114720794869765772410880, -250779790962876148088832, 225609945455098631028736, 483850522589269250277376, -347001209157715505446912, -730259543521239790256128, 415310597866565429886976, 858092168904258548137984, -382398419990448162471936, -776216717898678666264576, 265446738859620120395776, 529755463340972226641920, -134289876542062069809152, -263699857867019126833152, 46702419725064737914880, 90304897838109608116224, -9978520487732143194112, -19013924454743580606464, 987150780262768443392, 1854976732367169781760]
theorem monoCp : chebGen c0Cp gCp = PnCp.map (fun n : ℤ => (n : ℚ) / 2 ^ 40) := by decide +kernel
def cutsCpA : List ℤ := raw_ints% [-3, -2, -1]
def cutsCpB : List ℤ := raw_ints% [8, 12, 13, 14, 16, 32, 48, 56]
theorem covCpA : zNonnegCov (zAdd [0 * 2 ^ 40] (zSmul (-1) PnCp)) 2 (-4) cutsCpA (0) = true := by decide +kernel
theorem covCpB : zNonnegCov (zAdd [1 * 2 ^ 40] (zSmul (-1) PnCp)) 6 (0) cutsCpB (64) = true := by decide +kernel
theorem Cp_neg {e : ℝ} (he : e ∈ Set.Ioo (0 : ℝ) (1 / 8)) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) (hy0 : y < 0) :
    evalCert e gCp.length (gcertG e gCp) (c0Cp : ℝ) y ≤ 0 := by
  have h := evalCert_le_of_cov he (M := 0) (S := 2) (A := (-4 : ℤ)) (B := (0 : ℤ)) monoCp covCpA
    (y := y) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0]) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0])
  simpa using h

theorem Cp_pos {e : ℝ} (he : e ∈ Set.Ioo (0 : ℝ) (1 / 8)) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) (hy0 : 0 < y) :
    evalCert e gCp.length (gcertG e gCp) (c0Cp : ℝ) y ≤ 1 := by
  have h := evalCert_le_of_cov he (M := 1) (S := 6) (A := (0 : ℤ)) (B := (64 : ℤ)) monoCp covCpB
    (y := y) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0]) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0])
  simpa using h

def gCmN : List ℤ := raw_ints% [-695954170653, 69494745965, 221407844191, -67513598227, -120574730734, 64310144073, 73707940530, -60025634810, -45459152458, 54845446157, 26293235347, -48987819888, -12590564093, 42690878863, 2665077765, -36198856931, 4406014878, 29748519157, -9210086351, -23556702742, 12177507020, 17809790677, -13661148837, -12655750780, 13971703907, 8199149528, -13391656313, -4499303690, 12178636762, 1571485066, -10563753756, 609134019, 8748069932, -2101295994, -6899105179, 2989872037, 5148473140, -3377187612, -3591233618, 3374183020]
def gCm : List ℚ := gCmN.map (fun n : ℤ => (n : ℚ) / 2 ^ 40)
def c0Cm : ℚ := (498365778750 : ℤ) / 2 ^ 40
def PnCm : List ℤ := raw_ints% [-31290375122, -308959680000, 32970151773360, -398319492155896, -190007064817728, 19950904564409184, -28523694165903264, -499365088345185536, 1004818154276947712, 7725940327874373888, -17232133111477730304, -80971973764940772352, 186736816872109490176, 606389088807903490048, -1405636490154550050816, -3360093022462688247808, 7726752852793250381824, 14107898033232675274752, -31978096164376374673408, -45612436614991748268032, 101598304280700737028096, 114720794869765772410880, -250779790962876148088832, -225609945455098631028736, 483850522589269250277376, 347001209157715505446912, -730259543521239790256128, -415310597866565429886976, 858092168904258548137984, 382398419990448162471936, -776216717898678666264576, -265446738859620120395776, 529755463340972226641920, 134289876542062069809152, -263699857867019126833152, -46702419725064737914880, 90304897838109608116224, 9978520487732143194112, -19013924454743580606464, -987150780262768443392, 1854976732367169781760]
theorem monoCm : chebGen c0Cm gCm = PnCm.map (fun n : ℤ => (n : ℚ) / 2 ^ 40) := by decide +kernel
def cutsCmA : List ℤ := raw_ints% [1, 2, 3]
def cutsCmB : List ℤ := raw_ints% [-56, -48, -32, -16, -14, -13, -12, -8]
theorem covCmA : zNonnegCov (zAdd [0 * 2 ^ 40] (zSmul (-1) PnCm)) 2 (0) cutsCmA (4) = true := by decide +kernel
theorem covCmB : zNonnegCov (zAdd [1 * 2 ^ 40] (zSmul (-1) PnCm)) 6 (-64) cutsCmB (0) = true := by decide +kernel
theorem Cm_pos {e : ℝ} (he : e ∈ Set.Ioo (0 : ℝ) (1 / 8)) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) (hy0 : 0 < y) :
    evalCert e gCm.length (gcertG e gCm) (c0Cm : ℝ) y ≤ 0 := by
  have h := evalCert_le_of_cov he (M := 0) (S := 2) (A := (0 : ℤ)) (B := (4 : ℤ)) monoCm covCmA
    (y := y) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0]) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0])
  simpa using h

theorem Cm_neg {e : ℝ} (he : e ∈ Set.Ioo (0 : ℝ) (1 / 8)) {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) (hy0 : y < 0) :
    evalCert e gCm.length (gcertG e gCm) (c0Cm : ℝ) y ≤ 1 := by
  have h := evalCert_le_of_cov he (M := 1) (S := 6) (A := (-64 : ℤ)) (B := (0 : ℤ)) monoCm covCmB
    (y := y) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0]) (by push_cast; norm_num; linarith [hy.1, hy.2, hy0])
  simpa using h

end CatalanMeasure.Signed.Consts
