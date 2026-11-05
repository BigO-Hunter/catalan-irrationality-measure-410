module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialB1
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialA1
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeD
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeS1
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeCount

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed OAI.InternalCatalan

theorem tZB1 : tailZB ta1 = true := by decide +kernel
theorem A_1 : absq fa1 + tailMaj ta1 ≤ (1574251 / 1024 : ℚ) := by decide +kernel
theorem A1_1 : absSq fa1 + 7 * tailW ta1 ≤ (1861 / 1024 : ℚ) := by decide +kernel
theorem B1_1 : absSq bs1 ≤ (309 / 256 : ℚ) := by decide +kernel

theorem Lc1_div : (List.range 120).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ 955888052326228459513511038256280353796626534577600)) = true := by decide +kernel

theorem K0chk_1_b1p0 : K0check bs1 (255 / 256 : ℚ) (231 / 16384 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-6347 / 1024 : ℚ) = true := by decide +kernel
theorem K0_1_b1p0 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((231 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((255 / 256 : ℚ) : ℚ) : ℝ) ≤ (((-6347 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b1p0 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b1p0 : List ℤ := raw_ints% []
theorem De2cov1_b1p0 : zNonnegCov (zAdd [1330058445971159116943708926448247618722622857405537159919999909888000] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b1p0 (1024) = true := by decide +kernel
theorem De2sig1_b1p0 : (1241953 / 1048576 : ℚ) ≤ Sbq bs1 (-(255 / 256 : ℚ)) := by decide +kernel
theorem De2_1_b1p0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((255 / 256 : ℚ) : ℚ) : ℝ)) ≤ (((23 / 1024 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (255 / 256 : ℚ)) (σ := (1241953 / 1048576 : ℚ))
    (De2 := (23 / 1024 : ℚ)) (1330058445971159116943708926448247618722622857405537159919999909888000) (by norm_num) De2sig1_b1p0 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b1p0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_1_b1p1 : K0check bs1 (509 / 512 : ℚ) (3 / 128 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-5435 / 1024 : ℚ) = true := by decide +kernel
theorem K0_1_b1p1 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((3 / 128 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((509 / 512 : ℚ) : ℚ) : ℝ) ≤ (((-5435 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b1p1 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b1p1 : List ℤ := raw_ints% []
theorem De2cov1_b1p1 : zNonnegCov (zAdd [1330041629810704959476238549529291809016695530397174104385206511206400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b1p1 (1024) = true := by decide +kernel
theorem De2sig1_b1p1 : (1230993 / 1048576 : ℚ) ≤ Sbq bs1 (-(509 / 512 : ℚ)) := by decide +kernel
theorem De2_1_b1p1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((509 / 512 : ℚ) : ℚ) : ℝ)) ≤ (((539 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (509 / 512 : ℚ)) (σ := (1230993 / 1048576 : ℚ))
    (De2 := (539 / 16384 : ℚ)) (1330041629810704959476238549529291809016695530397174104385206511206400) (by norm_num) De2sig1_b1p1 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b1p1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_1_b1p2 : K0check bs1 (2033 / 2048 : ℚ) (467 / 16384 : ℚ) (40 / 63 : ℚ) (1 : ℚ) (-2593 / 512 : ℚ) = true := by decide +kernel
theorem K0_1_b1p2 {l : ℝ} {s' m : ℕ} (hl1 : (((40 / 63 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((1 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((467 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((2033 / 2048 : ℚ) : ℚ) : ℝ) ≤ (((-2593 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b1p2 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b1p2 : List ℤ := raw_ints% []
theorem De2cov1_b1p2 : zNonnegCov (zAdd [1330042680820733344317955448086726547123315988335196795356131098624000] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b1p2 (1024) = true := by decide +kernel
theorem De2sig1_b1p2 : (611529 / 524288 : ℚ) ≤ Sbq bs1 (-(2033 / 2048 : ℚ)) := by decide +kernel
theorem De2_1_b1p2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((2033 / 2048 : ℚ) : ℚ) : ℝ)) ≤ (((663 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (2033 / 2048 : ℚ)) (σ := (611529 / 524288 : ℚ))
    (De2 := (663 / 16384 : ℚ)) (1330042680820733344317955448086726547123315988335196795356131098624000) (by norm_num) De2sig1_b1p2 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b1p2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_1_b2p0 : K0check bs1 (1021 / 1024 : ℚ) (99 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-1631 / 512 : ℚ) = true := by decide +kernel
theorem K0_1_b2p0 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((99 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((1021 / 1024 : ℚ) : ℚ) : ℝ) ≤ (((-1631 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b2p0 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b2p0 : List ℤ := raw_ints% []
theorem De2cov1_b2p0 : zNonnegCov (zAdd [1330015354559995338433316085593423356351184081946606830112091825766400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b2p0 (1024) = true := by decide +kernel
theorem De2sig1_b2p0 : (155951 / 131072 : ℚ) ≤ Sbq bs1 (-(1021 / 1024 : ℚ)) := by decide +kernel
theorem De2_1_b2p0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((1021 / 1024 : ℚ) : ℚ) : ℝ)) ≤ (((279 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (1021 / 1024 : ℚ)) (σ := (155951 / 131072 : ℚ))
    (De2 := (279 / 16384 : ℚ)) (1330015354559995338433316085593423356351184081946606830112091825766400) (by norm_num) De2sig1_b2p0 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b2p0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_1_b2p1 : K0check bs1 (2037 / 2048 : ℚ) (99 / 8192 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-1347 / 512 : ℚ) = true := by decide +kernel
theorem K0_1_b2p1 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((99 / 8192 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((2037 / 2048 : ℚ) : ℚ) : ℝ) ≤ (((-1347 / 512 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b2p1 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b2p1 : List ℤ := raw_ints% []
theorem De2cov1_b2p1 : zNonnegCov (zAdd [1330052139910988807893407535103639190082900109777401014094452385382400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b2p1 (1024) = true := by decide +kernel
theorem De2sig1_b2p1 : (1233691 / 1048576 : ℚ) ≤ Sbq bs1 (-(2037 / 2048 : ℚ)) := by decide +kernel
theorem De2_1_b2p1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((2037 / 2048 : ℚ) : ℚ) : ℝ)) ≤ (((497 / 16384 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (2037 / 2048 : ℚ)) (σ := (1233691 / 1048576 : ℚ))
    (De2 := (497 / 16384 : ℚ)) (1330052139910988807893407535103639190082900109777401014094452385382400) (by norm_num) De2sig1_b2p1 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b2p1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_1_b2p2 : K0check bs1 (1017 / 1024 : ℚ) (261 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-301 / 128 : ℚ) = true := by decide +kernel
theorem K0_1_b2p2 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((261 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((1017 / 1024 : ℚ) : ℚ) : ℝ) ≤ (((-301 / 128 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b2p2 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b2p2 : List ℤ := raw_ints% []
theorem De2cov1_b2p2 : zNonnegCov (zAdd [1330037425770591420109370955299552856590213698645083340501508161536000] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b2p2 (1024) = true := by decide +kernel
theorem De2sig1_b2p2 : (1225677 / 1048576 : ℚ) ≤ Sbq bs1 (-(1017 / 1024 : ℚ)) := by decide +kernel
theorem De2_1_b2p2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((1017 / 1024 : ℚ) : ℚ) : ℝ)) ≤ (((311 / 8192 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (1017 / 1024 : ℚ)) (σ := (1225677 / 1048576 : ℚ))
    (De2 := (311 / 8192 : ℚ)) (1330037425770591420109370955299552856590213698645083340501508161536000) (by norm_num) De2sig1_b2p2 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b2p2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0chk_1_b2p3 : K0check bs1 (127 / 128 : ℚ) (297 / 16384 : ℚ) (10 / 29 : ℚ) (40 / 63 : ℚ) (-2289 / 1024 : ℚ) = true := by decide +kernel
theorem K0_1_b2p3 {l : ℝ} {s' m : ℕ} (hl1 : (((10 / 29 : ℚ) : ℚ) : ℝ) ≤ l) (hl2 : l ≤ (((40 / 63 : ℚ) : ℚ) : ℝ)) (hs : 0 < s')
    (hm : (m : ℝ) ≤ (((297 / 16384 : ℚ) : ℚ) : ℝ) * ((s' : ℝ) + m)) :
    costRem (fun k => l * bSeq bs1 k) s' m (((127 / 128 : ℚ) : ℚ) : ℝ) ≤ (((-2289 / 1024 : ℚ) : ℚ) : ℝ) :=
  costRem_le K0chk_1_b2p3 (by norm_num) (by norm_num) (by norm_num) hl1 hl2 hs hm

def cutsD1_b2p3 : List ℤ := raw_ints% []
theorem De2cov1_b2p3 : zNonnegCov (zAdd [1330073160111556504727745506252333952215309268537854833512944133734400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_b2p3 (1024) = true := by decide +kernel
theorem De2sig1_b2p3 : (1220463 / 1048576 : ℚ) ≤ Sbq bs1 (-(127 / 128 : ℚ)) := by decide +kernel
theorem De2_1_b2p3 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((127 / 128 : ℚ) : ℚ) : ℝ)) ≤ (((11 / 256 : ℚ) : ℚ) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (127 / 128 : ℚ)) (σ := (1220463 / 1048576 : ℚ))
    (De2 := (11 / 256 : ℚ)) (1330073160111556504727745506252333952215309268537854833512944133734400) (by norm_num) De2sig1_b2p3 (S := 10) (A := 1023) (B := 1024)
    De2cov1_b2p3 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

/-- **The spike certificate of trial 1 at every Heine count `x ∈ [s_r, ν]` and every `m ≤ 0.57 N`**, with the pole `rhoSel N x m`
(the same for the two trials of an interval).  This is the `Nonempty (SpikeTrialCert ..)` hypothesis of `hCls_of_cert`. -/
theorem spikeCert1 {D : SignedData} {N : ℕ} {BR Kn Tn : ℝ} (T : RefTrial D N bs1 fa1 ta1 (21 / 20 : ℚ) (1861 / 1024 : ℚ) (309 / 256 : ℚ) BR Kn Tn) :
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
          (ρ := (255 / 256 : ℚ)) (κ := (231 / 16384 : ℚ)) (K0 := (-6347 / 1024 : ℚ)) (De2 := (23 / 1024 : ℚ)) (Sg := (-19635 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b1p0lo polyS1_b1p0hi K0chk_1_b1p0 (fun y h1 h2 => De2_1_b1p0 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi ((by have := Nat.cast_nonneg (α := ℚ) m; linarith)) (nat_le_q (a := 32) (b := 9) (9 / 32) (by norm_num) (by norm_num) (by omega))
    by_cases h1 : 32 * m ≤ 15 * N
    · rw [rhoSel_b1p1 hB h0 h1]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (9 / 32 : ℚ)) (mhi := (15 / 32 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (509 / 512 : ℚ)) (κ := (3 / 128 : ℚ)) (K0 := (-5435 / 1024 : ℚ)) (De2 := (539 / 16384 : ℚ)) (Sg := (-11689 / 8192 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b1p1lo polyS1_b1p1hi K0chk_1_b1p1 (fun y h1 h2 => De2_1_b1p1 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 32) (b := 9) (9 / 32) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 32) (b := 15) (15 / 32) (by norm_num) (by norm_num) (by omega))
    · rw [rhoSel_b1p2 hB h0 h1]
      exact cert_piece T (xa := (20 : ℚ)) (xb := (63 / 2 : ℚ)) (mlo := (15 / 32 : ℚ)) (mhi := (57 / 100 : ℚ)) (l1 := (40 / 63 : ℚ)) (l2 := (1 : ℚ))
          (ρ := (2033 / 2048 : ℚ)) (κ := (467 / 16384 : ℚ)) (K0 := (-2593 / 512 : ℚ)) (De2 := (663 / 16384 : ℚ)) (Sg := (-25029 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b1p2lo polyS1_b1p2hi K0chk_1_b1p2 (fun y h1 h2 => De2_1_b1p2 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 32) (b := 15) (15 / 32) (by norm_num) (by norm_num) (by omega)) (hm57)
  · have hxlo : (63 / 2 : ℚ) * N ≤ x := nat_gt_q (m := x) (a := 2) (b := 63) (63 / 2) (by norm_num) (by norm_num) (by omega)
    have hxhi := hxq2
    by_cases h0 : 100 * m ≤ 19 * N
    · rw [rhoSel_b2p0 hB h0]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (0 : ℚ)) (mhi := (19 / 100 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (1021 / 1024 : ℚ)) (κ := (99 / 16384 : ℚ)) (K0 := (-1631 / 512 : ℚ)) (De2 := (279 / 16384 : ℚ)) (Sg := (-16359 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b2p0lo polyS1_b2p0hi K0chk_1_b2p0 (fun y h1 h2 => De2_1_b2p0 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi ((by have := Nat.cast_nonneg (α := ℚ) m; linarith)) (nat_le_q (a := 100) (b := 19) (19 / 100) (by norm_num) (by norm_num) (by omega))
    by_cases h1 : 50 * m ≤ 19 * N
    · rw [rhoSel_b2p1 hB h0 h1]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (19 / 100 : ℚ)) (mhi := (19 / 50 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (2037 / 2048 : ℚ)) (κ := (99 / 8192 : ℚ)) (K0 := (-1347 / 512 : ℚ)) (De2 := (497 / 16384 : ℚ)) (Sg := (-11329 / 8192 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b2p1lo polyS1_b2p1hi K0chk_1_b2p1 (fun y h1 h2 => De2_1_b2p1 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 100) (b := 19) (19 / 100) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 50) (b := 19) (19 / 50) (by norm_num) (by norm_num) (by omega))
    by_cases h2 : 2 * m ≤ N
    · rw [rhoSel_b2p2 hB h0 h1 h2]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (19 / 50 : ℚ)) (mhi := (1 / 2 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (1017 / 1024 : ℚ)) (κ := (261 / 16384 : ℚ)) (K0 := (-301 / 128 : ℚ)) (De2 := (311 / 8192 : ℚ)) (Sg := (-24547 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b2p2lo polyS1_b2p2hi K0chk_1_b2p2 (fun y h1 h2 => De2_1_b2p2 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 50) (b := 19) (19 / 50) (by norm_num) (by norm_num) (by omega)) (nat_le_q (a := 2) (b := 1) (1 / 2) (by norm_num) (by norm_num) (by omega))
    · rw [rhoSel_b2p3 hB h0 h1 h2]
      exact cert_piece T (xa := (63 / 2 : ℚ)) (xb := (58 : ℚ)) (mlo := (1 / 2 : ℚ)) (mhi := (57 / 100 : ℚ)) (l1 := (10 / 29 : ℚ)) (l2 := (40 / 63 : ℚ))
          (ρ := (127 / 128 : ℚ)) (κ := (297 / 16384 : ℚ)) (K0 := (-2289 / 1024 : ℚ)) (De2 := (11 / 256 : ℚ)) (Sg := (-25457 / 16384 : ℚ)) (Lq := (525569 / 1073741824 : ℚ)) (Aq := (1574251 / 1024 : ℚ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          floorS1 polyS1_b2p3lo polyS1_b2p3hi K0chk_1_b2p3 (fun y h1 h2 => De2_1_b2p3 h1 h2) A_1 A1_1 B1_1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hxlo hxhi (nat_gt_q (a := 2) (b := 1) (1 / 2) (by norm_num) (by norm_num) (by omega)) (hm57)

end CatalanMeasure.Signed.Consts
