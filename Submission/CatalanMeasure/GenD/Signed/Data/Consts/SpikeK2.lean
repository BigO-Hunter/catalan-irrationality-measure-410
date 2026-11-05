module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialB2
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialA2
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeD
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeS2
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeCount

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed OAI.InternalCatalan

theorem tZB2 : tailZB ta2 = true := by decide +kernel
theorem A_2 : absq fa2 + tailMaj ta2 ≤ (1897929 / 1024 : ℚ) := by decide +kernel
theorem A1_2 : absSq fa2 + 7 * tailW ta2 ≤ (983 / 512 : ℚ) := by decide +kernel
theorem B1_2 : absSq bs2 ≤ (1181 / 1024 : ℚ) := by decide +kernel

theorem Lc2_div : (List.range 120).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ 955888052326228459513511038256280353796626534577600)) = true := by decide +kernel

theorem K0chk_2_b1p0 : K0check bs2 (255 / 256 : ℚ) (231 / 16384 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-5697 / 1024 : ℚ) = true := by decide +kernel
theorem K0_2_b1p0 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((231 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((255 / 256 : ℚ) : ℚ) : ℝ) ≤ (((-5697 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b1p0 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b1p0 : List ℤ := raw_ints% []
theorem De2cov2_b1p0 : zNonnegCov (zAdd [1271004294496271630554612781305182883932332235786576885609282089779200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b1p0 (1024) = true := by decide +kernel
theorem De2sig2_b1p0 : (1187173 / 1048576 : ℚ) ≤ Sbq bs2 (-(255 / 256 : ℚ)) := by decide +kernel
theorem De2_2_b1p0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((255 / 256 : ℚ) : ℚ) : ℝ)) ≤ (((173 / 8192 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (255 / 256 : ℚ)) (σ := (1187173 / 1048576 : ℚ))
    (De2 := (173 / 8192 : ℚ)) (1271004294496271630554612781305182883932332235786576885609282089779200) (by norm_num) De2sig2_b1p0 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b1p0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_2_b1p1 : K0check bs2 (509 / 512 : ℚ) (3 / 128 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-1205 / 256 : ℚ) = true := by decide +kernel
theorem K0_2_b1p1 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((3 / 128 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((509 / 512 : ℚ) : ℚ) : ℝ) ≤ (((-1205 / 256 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b1p1 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b1p1 : List ℤ := raw_ints% []
theorem De2cov2_b1p1 : zNonnegCov (zAdd [1271048436917463793906722520717441884410391469183529906388114761318400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b1p1 (1024) = true := by decide +kernel
theorem De2sig2_b1p1 : (1176847 / 1048576 : ℚ) ≤ Sbq bs2 (-(509 / 512 : ℚ)) := by decide +kernel
theorem De2_2_b1p1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((509 / 512 : ℚ) : ℚ) : ℝ)) ≤ (((127 / 4096 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (509 / 512 : ℚ)) (σ := (1176847 / 1048576 : ℚ))
    (De2 := (127 / 4096 : ℚ)) (1271048436917463793906722520717441884410391469183529906388114761318400) (by norm_num) De2sig2_b1p1 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b1p1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_2_b1p2 : K0check bs2 (2033 / 2048 : ℚ) (467 / 16384 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-4597 / 1024 : ℚ) = true := by decide +kernel
theorem K0_2_b1p2 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((467 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((2033 / 2048 : ℚ) : ℚ) : ℝ) ≤ (((-4597 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b1p2 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b1p2 : List ℤ := raw_ints% []
theorem De2cov2_b1p2 : zNonnegCov (zAdd [1270989580355874242770576201501096550439645824654259212016337865932800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b1p2 (1024) = true := by decide +kernel
theorem De2sig2_b1p2 : (1169367 / 1048576 : ℚ) ≤ Sbq bs2 (-(2033 / 2048 : ℚ)) := by decide +kernel
theorem De2_2_b1p2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((2033 / 2048 : ℚ) : ℚ) : ℝ)) ≤ (((39 / 1024 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (2033 / 2048 : ℚ)) (σ := (1169367 / 1048576 : ℚ))
    (De2 := (39 / 1024 : ℚ)) (1270989580355874242770576201501096550439645824654259212016337865932800) (by norm_num) De2sig2_b1p2 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b1p2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_2_b2p0 : K0check bs2 (1021 / 1024 : ℚ) (99 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-2889 / 1024 : ℚ) = true := by decide +kernel
theorem K0_2_b2p0 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((99 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((1021 / 1024 : ℚ) : ℚ) : ℝ) ≤ (((-2889 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b2p0 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b2p0 : List ℤ := raw_ints% []
theorem De2cov2_b2p0 : zNonnegCov (zAdd [1271019008636669018338649361109269217425018646918894559202226313625600] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b2p0 (1024) = true := by decide +kernel
theorem De2sig2_b2p0 : (1192499 / 1048576 : ℚ) ≤ Sbq bs2 (-(1021 / 1024 : ℚ)) := by decide +kernel
theorem De2_2_b2p0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((1021 / 1024 : ℚ) : ℚ) : ℝ)) ≤ (((263 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (1021 / 1024 : ℚ)) (σ := (1192499 / 1048576 : ℚ))
    (De2 := (263 / 16384 : ℚ)) (1271019008636669018338649361109269217425018646918894559202226313625600) (by norm_num) De2sig2_b2p0 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b2p0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_2_b2p1 : K0check bs2 (2037 / 2048 : ℚ) (99 / 8192 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-2347 / 1024 : ℚ) = true := by decide +kernel
theorem K0_2_b2p1 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((99 / 8192 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((2037 / 2048 : ℚ) : ℚ) : ℝ) ≤ (((-2347 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b2p1 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b2p1 : List ℤ := raw_ints% []
theorem De2cov2_b2p1 : zNonnegCov (zAdd [1271030569746981251597535245241051336597843684237144159882396775219200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b2p1 (1024) = true := by decide +kernel
theorem De2sig2_b2p1 : (589695 / 524288 : ℚ) ≤ Sbq bs2 (-(2037 / 2048 : ℚ)) := by decide +kernel
theorem De2_2_b2p1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((2037 / 2048 : ℚ) : ℚ) : ℝ)) ≤ (((117 / 4096 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (2037 / 2048 : ℚ)) (σ := (589695 / 524288 : ℚ))
    (De2 := (117 / 4096 : ℚ)) (1271030569746981251597535245241051336597843684237144159882396775219200) (by norm_num) De2sig2_b2p1 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b2p1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_2_b2p2 : K0check bs2 (1017 / 1024 : ℚ) (261 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-2075 / 1024 : ℚ) = true := by decide +kernel
theorem K0_2_b2p2 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((261 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((1017 / 1024 : ℚ) : ℚ) : ℝ) ≤ (((-2075 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b2p2 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b2p2 : List ℤ := raw_ints% []
theorem De2cov2_b2p2 : zNonnegCov (zAdd [1271028467726924481914101448126181860384602768361098777940547600384000] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b2p2 (1024) = true := by decide +kernel
theorem De2sig2_b2p2 : (292959 / 262144 : ℚ) ≤ Sbq bs2 (-(1017 / 1024 : ℚ)) := by decide +kernel
theorem De2_2_b2p2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((1017 / 1024 : ℚ) : ℚ) : ℝ)) ≤ (((293 / 8192 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (1017 / 1024 : ℚ)) (σ := (292959 / 262144 : ℚ))
    (De2 := (293 / 8192 : ℚ)) (1271028467726924481914101448126181860384602768361098777940547600384000) (by norm_num) De2sig2_b2p2 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b2p2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_2_b2p3 : K0check bs2 (127 / 128 : ℚ) (297 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-983 / 512 : ℚ) = true := by decide +kernel
theorem K0_2_b2p3 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((297 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs2 k) s' m (((127 / 128 : ℚ) : ℚ) : ℝ) ≤ (((-983 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_2_b2p3 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD2_b2p3 : List ℤ := raw_ints% []
theorem De2cov2_b2p3 : zNonnegCov (zAdd [1271042130857293484856421129372833455770668721555393760562567236812800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_b2p3 (1024) = true := by decide +kernel
theorem De2sig2_b2p3 : (1166921 / 1048576 : ℚ) ≤ Sbq bs2 (-(127 / 128 : ℚ)) := by decide +kernel
theorem De2_2_b2p3 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((127 / 128 : ℚ) : ℚ) : ℝ)) ≤ (((663 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (127 / 128 : ℚ)) (σ := (1166921 / 1048576 : ℚ))
    (De2 := (663 / 16384 : ℚ)) (1271042130857293484856421129372833455770668721555393760562567236812800) (by norm_num) De2sig2_b2p3 (S := 10) (A := 1023) (B := 1024)
    De2cov2_b2p3 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

/-- **The spike certificate of trial 2 at every Heine count `x ∈ [s_r, ν]` and every `m ≤ 0.57 N`**, with the pole `rhoSel N x m`
(the same for the two trials of an interval).  This is the `Nonempty (SpikeTrialCert ..)` hypothesis of `hCls_of_cert`. -/
theorem spikeCert2 {D : SignedData} {N : ℕ} {BR Kn Tn : ℝ} (T : RefTrial D N bs2 fa2 ta2 (11 / 10 : ℚ) (983 / 512 : ℚ) (1181 / 1024 : ℚ) BR Kn Tn) :
    ∀ x m : ℕ, D.sp ≤ x → (x : ℝ) ≤ D.ν → 100 * m ≤ 57 * N →
      Nonempty (SpikeTrialCert (D.withCount x) m (rhoSel N x m) Kn Tn) := by
  intro x m hx1 hx2 hm
  obtain ⟨hxq1, hxq2⟩ := count_ranges T hx1 hx2
  have hm57 : (m : ℚ) ≤ 57 / 100 * N := nat_le_q (a := 100) (b := 57) (57 / 100) (by norm_num) (by norm_num) hm
  by_cases hB : 2 * x ≤ 63 * N
  · have hxlo := hxq1
    have hxhi : (x : ℚ) ≤ 63 / 2 * N := nat_le_q (m := x) (a := 2) (b := 63) (63 / 2) (by norm_num) (by norm_num) hB
    by_cases h0 : 32 * m ≤ 9 * N
    · rw [rhoSel_b1p0 hB h0]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (0 : ℚ)) (mhi := (9 / 32 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (255 / 256 : ℚ)) (κ := (231 / 16384 : ℚ)) (K0 := (-5697 / 1024 : ℚ)) (De2 := (173 / 8192 : ℚ)) (Sg := (-19635 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b1p0lo polyS2_b1p0hi K0chk_2_b1p0 (fun y h1 h2 => De2_2_b1p0 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi ((by have := Nat.cast_nonneg (α := ℚ) m; linarith)) (nat_le_q (a := 32) (b := 9) (9 / 32) (by norm_num) (by norm_num) (by omega))
    by_cases h1 : 32 * m ≤ 15 * N
    · rw [rhoSel_b1p1 hB h0 h1]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (9 / 32 : ℚ)) (mhi := (15 / 32 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (509 / 512 : ℚ)) (κ := (3 / 128 : ℚ)) (K0 := (-1205 / 256 : ℚ)) (De2 := (127 / 4096 : ℚ)) (Sg := (-11689 / 8192 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b1p1lo polyS2_b1p1hi K0chk_2_b1p1 (fun y h1 h2 => De2_2_b1p1 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 32) (b := 9) (9 / 32) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 32) (b := 15) (15 / 32) (by norm_num) (by norm_num) (by omega))
    · rw [rhoSel_b1p2 hB h0 h1]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (15 / 32 : ℚ)) (mhi := (57 / 100 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (2033 / 2048 : ℚ)) (κ := (467 / 16384 : ℚ)) (K0 := (-4597 / 1024 : ℚ)) (De2 := (39 / 1024 : ℚ)) (Sg := (-25029 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b1p2lo polyS2_b1p2hi K0chk_2_b1p2 (fun y h1 h2 => De2_2_b1p2 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 32) (b := 15) (15 / 32) (by norm_num) (by norm_num) (by omega)) (hm57)
  · have hxlo : (63 / 2 : ℚ) * N ≤ x := nat_gt_q (m := x) (a := 2) (b := 63) (63 / 2) (by norm_num) (by norm_num) (by omega)
    have hxhi := hxq2
    by_cases h0 : 100 * m ≤ 19 * N
    · rw [rhoSel_b2p0 hB h0]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (0 : ℚ)) (mhi := (19 / 100 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (1021 / 1024 : ℚ)) (κ := (99 / 16384 : ℚ)) (K0 := (-2889 / 1024 : ℚ)) (De2 := (263 / 16384 : ℚ)) (Sg := (-16359 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b2p0lo polyS2_b2p0hi K0chk_2_b2p0 (fun y h1 h2 => De2_2_b2p0 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi ((by have := Nat.cast_nonneg (α := ℚ) m; linarith)) (nat_le_q (a := 100) (b := 19) (19 / 100) (by norm_num) (by norm_num) (by omega))
    by_cases h1 : 50 * m ≤ 19 * N
    · rw [rhoSel_b2p1 hB h0 h1]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (19 / 100 : ℚ)) (mhi := (19 / 50 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (2037 / 2048 : ℚ)) (κ := (99 / 8192 : ℚ)) (K0 := (-2347 / 1024 : ℚ)) (De2 := (117 / 4096 : ℚ)) (Sg := (-11329 / 8192 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b2p1lo polyS2_b2p1hi K0chk_2_b2p1 (fun y h1 h2 => De2_2_b2p1 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 100) (b := 19) (19 / 100) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 50) (b := 19) (19 / 50) (by norm_num) (by norm_num) (by omega))
    by_cases h2 : 2 * m ≤ N
    · rw [rhoSel_b2p2 hB h0 h1 h2]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (19 / 50 : ℚ)) (mhi := (1 / 2 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (1017 / 1024 : ℚ)) (κ := (261 / 16384 : ℚ)) (K0 := (-2075 / 1024 : ℚ)) (De2 := (293 / 8192 : ℚ)) (Sg := (-24547 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b2p2lo polyS2_b2p2hi K0chk_2_b2p2 (fun y h1 h2 => De2_2_b2p2 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 50) (b := 19) (19 / 50) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 2) (b := 1) (1 / 2) (by norm_num) (by norm_num) (by omega))
    · rw [rhoSel_b2p3 hB h0 h1 h2]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (1 / 2 : ℚ)) (mhi := (57 / 100 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (127 / 128 : ℚ)) (κ := (297 / 16384 : ℚ)) (K0 := (-983 / 512 : ℚ)) (De2 := (663 / 16384 : ℚ)) (Sg := (-25457 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1897929 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS2 polyS2_b2p3lo polyS2_b2p3hi K0chk_2_b2p3 (fun y h1 h2 => De2_2_b2p3 h1 h2) A_2 A1_2 B1_2
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 2) (b := 1) (1 / 2) (by norm_num) (by norm_num) (by omega)) (hm57)

end CatalanMeasure.Signed.Consts
