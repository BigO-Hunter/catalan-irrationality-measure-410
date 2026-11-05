module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialB0
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialA0
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeD
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeS0
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeCount

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed OAI.InternalCatalan

theorem tZB0 : tailZB ta0 = true := by decide +kernel
theorem A_0 : absq fa0 + tailMaj ta0 ≤ (6940965 / 1024 : ℚ) := by decide +kernel
theorem A1_0 : absSq fa0 + 7 * tailW ta0 ≤ (469 / 256 : ℚ) := by decide +kernel
theorem B1_0 : absSq bs0 ≤ (1241 / 1024 : ℚ) := by decide +kernel

theorem Lc0_div : (List.range 120).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ 955888052326228459513511038256280353796626534577600)) = true := by decide +kernel

theorem K0chk_0_b1p0 : K0check bs0 (255 / 256 : ℚ) (231 / 16384 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-6415 / 1024 : ℚ) = true := by decide +kernel
theorem K0_0_b1p0 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((231 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((255 / 256 : ℚ) : ℚ) : ℝ) ≤ (((-6415 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b1p0 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b1p0 : List ℤ := raw_ints% []
theorem De2cov0_b1p0 : zNonnegCov (zAdd [1335301935002771092269315829490156032652087510200742413862766536294400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b1p0 (1024) = true := by decide +kernel
theorem De2sig0_b1p0 : (623407 / 524288 : ℚ) ≤ Sbq bs0 (-(255 / 256 : ℚ)) := by decide +kernel
theorem De2_0_b1p0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((255 / 256 : ℚ) : ℚ) : ℝ)) ≤ (((185 / 8192 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (255 / 256 : ℚ)) (σ := (623407 / 524288 : ℚ))
    (De2 := (185 / 8192 : ℚ)) (1335301935002771092269315829490156032652087510200742413862766536294400) (by norm_num) De2sig0_b1p0 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b1p0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_0_b1p1 : K0check bs0 (509 / 512 : ℚ) (3 / 128 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-5499 / 1024 : ℚ) = true := by decide +kernel
theorem K0_0_b1p1 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((3 / 128 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((509 / 512 : ℚ) : ℚ) : ℝ) ≤ (((-5499 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b1p1 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b1p1 : List ℤ := raw_ints% []
theorem De2cov0_b1p1 : zNonnegCov (zAdd [1335285118842316934801845452571200222946160183192379358327973137612800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b1p1 (1024) = true := by decide +kernel
theorem De2sig0_b1p1 : (617895 / 524288 : ℚ) ≤ Sbq bs0 (-(509 / 512 : ℚ)) := by decide +kernel
theorem De2_0_b1p1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((509 / 512 : ℚ) : ℚ) : ℝ)) ≤ (((271 / 8192 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (509 / 512 : ℚ)) (σ := (617895 / 524288 : ℚ))
    (De2 := (271 / 8192 : ℚ)) (1335285118842316934801845452571200222946160183192379358327973137612800) (by norm_num) De2sig0_b1p1 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b1p1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_0_b1p2 : K0check bs0 (2033 / 2048 : ℚ) (467 / 16384 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-2623 / 512 : ℚ) = true := by decide +kernel
theorem K0_0_b1p2 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((467 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((2033 / 2048 : ℚ) : ℚ) : ℝ) ≤ (((-2623 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b1p2 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b1p2 : List ℤ := raw_ints% []
theorem De2cov0_b1p2 : zNonnegCov (zAdd [1335306139042884631636183423719894985078569341952833177746464885964800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b1p2 (1024) = true := by decide +kernel
theorem De2sig0_b1p2 : (613905 / 524288 : ℚ) ≤ Sbq bs0 (-(2033 / 2048 : ℚ)) := by decide +kernel
theorem De2_0_b1p2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((2033 / 2048 : ℚ) : ℚ) : ℝ)) ≤ (((667 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (2033 / 2048 : ℚ)) (σ := (613905 / 524288 : ℚ))
    (De2 := (667 / 16384 : ℚ)) (1335306139042884631636183423719894985078569341952833177746464885964800) (by norm_num) De2sig0_b1p2 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b1p2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_0_b2p0 : K0check bs0 (1021 / 1024 : ℚ) (99 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-3301 / 1024 : ℚ) = true := by decide +kernel
theorem K0_0_b2p0 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((99 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((1021 / 1024 : ℚ) : ℚ) : ℝ) ≤ (((-3301 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b2p0 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b2p0 : List ℤ := raw_ints% []
theorem De2cov0_b2p0 : zNonnegCov (zAdd [1335294577932572398377297539588112865905744304634583577066294424371200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b2p0 (1024) = true := by decide +kernel
theorem De2sig0_b2p0 : (1252503 / 1048576 : ℚ) ≤ Sbq bs0 (-(1021 / 1024 : ℚ)) := by decide +kernel
theorem De2_0_b2p0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((1021 / 1024 : ℚ) : ℚ) : ℝ)) ≤ (((281 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (1021 / 1024 : ℚ)) (σ := (1252503 / 1048576 : ℚ))
    (De2 := (281 / 16384 : ℚ)) (1335294577932572398377297539588112865905744304634583577066294424371200) (by norm_num) De2sig0_b2p0 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b2p0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_0_b2p1 : K0check bs0 (2037 / 2048 : ℚ) (99 / 8192 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-1365 / 512 : ℚ) = true := by decide +kernel
theorem K0_0_b2p1 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((99 / 8192 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((2037 / 2048 : ℚ) : ℚ) : ℝ) ≤ (((-1365 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b2p1 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b2p1 : List ℤ := raw_ints% []
theorem De2cov0_b2p1 : zNonnegCov (zAdd [1335312445103054940686484815064503413718292089580969323572012410470400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b2p1 (1024) = true := by decide +kernel
theorem De2sig0_b2p1 : (154813 / 131072 : ℚ) ≤ Sbq bs0 (-(2037 / 2048 : ℚ)) := by decide +kernel
theorem De2_0_b2p1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((2037 / 2048 : ℚ) : ℚ) : ℝ)) ≤ (((125 / 4096 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (2037 / 2048 : ℚ)) (σ := (154813 / 131072 : ℚ))
    (De2 := (125 / 4096 : ℚ)) (1335312445103054940686484815064503413718292089580969323572012410470400) (by norm_num) De2sig0_b2p1 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b2p1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_0_b2p2 : K0check bs0 (1017 / 1024 : ℚ) (261 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-1221 / 512 : ℚ) = true := by decide +kernel
theorem K0_0_b2p2 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((261 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((1017 / 1024 : ℚ) : ℚ) : ℝ) ≤ (((-1221 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b2p2 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b2p2 : List ℤ := raw_ints% []
theorem De2cov0_b2p2 : zNonnegCov (zAdd [1335316649143168480053352409294242366144773921333060087455710760140800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b2p2 (1024) = true := by decide +kernel
theorem De2sig0_b2p2 : (307611 / 262144 : ℚ) ≤ Sbq bs0 (-(1017 / 1024 : ℚ)) := by decide +kernel
theorem De2_0_b2p2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((1017 / 1024 : ℚ) : ℚ) : ℝ)) ≤ (((313 / 8192 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (1017 / 1024 : ℚ)) (σ := (307611 / 262144 : ℚ))
    (De2 := (313 / 8192 : ℚ)) (1335316649143168480053352409294242366144773921333060087455710760140800) (by norm_num) De2sig0_b2p2 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b2p2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_0_b2p3 : K0check bs0 (127 / 128 : ℚ) (297 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-1161 / 512 : ℚ) = true := by decide +kernel
theorem K0_0_b2p3 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((297 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs0 k) s' m (((127 / 128 : ℚ) : ℚ) : ℝ) ≤ (((-1161 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_0_b2p3 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD0_b2p3 : List ℤ := raw_ints% []
theorem De2cov0_b2p3 : zNonnegCov (zAdd [1335321904193310404261936902081416056677876211023173542310333697228800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_b2p3 (1024) = true := by decide +kernel
theorem De2sig0_b2p3 : (1225201 / 1048576 : ℚ) ≤ Sbq bs0 (-(127 / 128 : ℚ)) := by decide +kernel
theorem De2_0_b2p3 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((127 / 128 : ℚ) : ℚ) : ℝ)) ≤ (((177 / 4096 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (127 / 128 : ℚ)) (σ := (1225201 / 1048576 : ℚ))
    (De2 := (177 / 4096 : ℚ)) (1335321904193310404261936902081416056677876211023173542310333697228800) (by norm_num) De2sig0_b2p3 (S := 10) (A := 1023) (B := 1024)
    De2cov0_b2p3 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

/-- **The spike certificate of trial 0 at every Heine count `x ∈ [s_r, ν]` and every `m ≤ 0.57 N`**, with the pole `rhoSel N x m`
(the same for the two trials of an interval).  This is the `Nonempty (SpikeTrialCert ..)` hypothesis of `hCls_of_cert`. -/
theorem spikeCert0 {D : SignedData} {N : ℕ} {BR Kn Tn : ℝ} (T : RefTrial D N bs0 fa0 ta0 (21 / 20 : ℚ) (469 / 256 : ℚ) (1241 / 1024 : ℚ) BR Kn Tn) :
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
          (ρ := (255 / 256 : ℚ)) (κ := (231 / 16384 : ℚ)) (K0 := (-6415 / 1024 : ℚ)) (De2 := (185 / 8192 : ℚ)) (Sg := (-19635 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b1p0lo polyS0_b1p0hi K0chk_0_b1p0 (fun y h1 h2 => De2_0_b1p0 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi ((by have := Nat.cast_nonneg (α := ℚ) m; linarith)) (nat_le_q (a := 32) (b := 9) (9 / 32) (by norm_num) (by norm_num) (by omega))
    by_cases h1 : 32 * m ≤ 15 * N
    · rw [rhoSel_b1p1 hB h0 h1]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (9 / 32 : ℚ)) (mhi := (15 / 32 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (509 / 512 : ℚ)) (κ := (3 / 128 : ℚ)) (K0 := (-5499 / 1024 : ℚ)) (De2 := (271 / 8192 : ℚ)) (Sg := (-11689 / 8192 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b1p1lo polyS0_b1p1hi K0chk_0_b1p1 (fun y h1 h2 => De2_0_b1p1 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 32) (b := 9) (9 / 32) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 32) (b := 15) (15 / 32) (by norm_num) (by norm_num) (by omega))
    · rw [rhoSel_b1p2 hB h0 h1]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (15 / 32 : ℚ)) (mhi := (57 / 100 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (2033 / 2048 : ℚ)) (κ := (467 / 16384 : ℚ)) (K0 := (-2623 / 512 : ℚ)) (De2 := (667 / 16384 : ℚ)) (Sg := (-25029 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b1p2lo polyS0_b1p2hi K0chk_0_b1p2 (fun y h1 h2 => De2_0_b1p2 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 32) (b := 15) (15 / 32) (by norm_num) (by norm_num) (by omega)) (hm57)
  · have hxlo : (63 / 2 : ℚ) * N ≤ x := nat_gt_q (m := x) (a := 2) (b := 63) (63 / 2) (by norm_num) (by norm_num) (by omega)
    have hxhi := hxq2
    by_cases h0 : 100 * m ≤ 19 * N
    · rw [rhoSel_b2p0 hB h0]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (0 : ℚ)) (mhi := (19 / 100 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (1021 / 1024 : ℚ)) (κ := (99 / 16384 : ℚ)) (K0 := (-3301 / 1024 : ℚ)) (De2 := (281 / 16384 : ℚ)) (Sg := (-16359 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b2p0lo polyS0_b2p0hi K0chk_0_b2p0 (fun y h1 h2 => De2_0_b2p0 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi ((by have := Nat.cast_nonneg (α := ℚ) m; linarith)) (nat_le_q (a := 100) (b := 19) (19 / 100) (by norm_num) (by norm_num) (by omega))
    by_cases h1 : 50 * m ≤ 19 * N
    · rw [rhoSel_b2p1 hB h0 h1]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (19 / 100 : ℚ)) (mhi := (19 / 50 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (2037 / 2048 : ℚ)) (κ := (99 / 8192 : ℚ)) (K0 := (-1365 / 512 : ℚ)) (De2 := (125 / 4096 : ℚ)) (Sg := (-11329 / 8192 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b2p1lo polyS0_b2p1hi K0chk_0_b2p1 (fun y h1 h2 => De2_0_b2p1 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 100) (b := 19) (19 / 100) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 50) (b := 19) (19 / 50) (by norm_num) (by norm_num) (by omega))
    by_cases h2 : 2 * m ≤ N
    · rw [rhoSel_b2p2 hB h0 h1 h2]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (19 / 50 : ℚ)) (mhi := (1 / 2 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (1017 / 1024 : ℚ)) (κ := (261 / 16384 : ℚ)) (K0 := (-1221 / 512 : ℚ)) (De2 := (313 / 8192 : ℚ)) (Sg := (-24547 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b2p2lo polyS0_b2p2hi K0chk_0_b2p2 (fun y h1 h2 => De2_0_b2p2 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 50) (b := 19) (19 / 50) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 2) (b := 1) (1 / 2) (by norm_num) (by norm_num) (by omega))
    · rw [rhoSel_b2p3 hB h0 h1 h2]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (1 / 2 : ℚ)) (mhi := (57 / 100 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (127 / 128 : ℚ)) (κ := (297 / 16384 : ℚ)) (K0 := (-1161 / 512 : ℚ)) (De2 := (177 / 4096 : ℚ)) (Sg := (-25457 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (6940965 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS0 polyS0_b2p3lo polyS0_b2p3hi K0chk_0_b2p3 (fun y h1 h2 => De2_0_b2p3 h1 h2) A_0 A1_0 B1_0
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 2) (b := 1) (1 / 2) (by norm_num) (by norm_num) (by omega)) (hm57)

end CatalanMeasure.Signed.Consts
