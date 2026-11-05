module

public import Submission.CatalanMeasure.CellCert.FieldsS
public import Submission.CatalanMeasure.CellCert.Tower

@[expose] public section

/-!
# Derivative links of the 728 fields with the cell tower

`F' = ptZ Z 0 + Σ_q qt q 0` (`ftZ Z poles 0`), for the row field (with optional peeling of the
`α log|x|` and `β log(1-x)` terms), the column field and the residual field of the scaled trial.

The polynomial part is a parameter: `Z` is an integer list with
`-4 · finUR Pc x - finPR Vc x = ptZ Z 0 x`  (row),  `2 · finUR Vc x = ptZ Z 0 x`  (column),
`-2 · finUR Pc x = ptZ Z 0 x`  (residual), where
`finUR cs x = Σ_k (cs_k / 2^40) U_k(x)` and `finPR cs x = Σ_k (cs_k / 2^40) x^k`.
-/

open OAI.InternalCatalan Polynomial Set

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert
noncomputable section

/-- `Σ_k (cs_k / 2^40) U_k(x)` -/
def finUR (cs : List ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
    (Chebyshev.U ℝ (k : ℤ)).eval x

/-- `Σ_k (cs_k / 2^40) x^k` -/
def finPR (cs : List ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) * x ^ k

/-- pole list of the row field derivative, with the poles of the peeled logs removed -/
def rowPolesP (R : RowWeights) (P V : List TailQ) (f0 f1 : Bool) : List PoleR :=
  (if f0 then [] else [⟨R.alpha, 0, 0, 0⟩]) ++ (if f1 then [] else [⟨R.beta, 0, 1, 0⟩]) ++
    [⟨-2 * R.gamma, 0, 0, 1⟩] ++ P.map poleP ++ V.map poleOfTailS

theorem rowPolesP_false (R : RowWeights) (P V : List TailQ) :
    rowPolesP R P V false false = rowPoles R P V := by
  simp [rowPolesP, rowPoles]

/-- the pole of `2 Re (r z / (1 - 2 x z + z²))` -/
def poleC (t : TailQ) : PoleR :=
  ⟨-(poleOfTail t).rr, -(poleOfTail t).ri, (poleOfTail t).pr, (poleOfTail t).pi⟩

/-- pole list of the column field derivative -/
def colPolesP (C : ColumnWeights) (V : List TailQ) (f0 f1 : Bool) : List PoleR :=
  (if f0 then [] else [⟨C.b, 0, 0, 0⟩]) ++ (if f1 then [] else [⟨C.q, 0, 1, 0⟩]) ++ V.map poleC

def colPoles (C : ColumnWeights) (V : List TailQ) : List PoleR := colPolesP C V false false

/-- pole list of the residual field derivative -/
def resPoles (P : List TailQ) : List PoleR := ⟨-9 / 5, 0, 0, 1⟩ :: P.map poleOfTail

/-! ### tail pole sums -/

theorem sum_qt_poleP (P : List TailQ) (hP : tailsInDisk P = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    ((P.map poleP).map (fun q => qt q 0 x)).sum =
      -4 * ((((P.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum).re) := by
  have hd := tailsInDisk_spec hP
  rw [re_list_sum]
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  have h1 := tailT4_pole t (hd _ (List.mem_map_of_mem ht)) (hPz t ht) x hx
  have h2 := (tailTFrac_spec t (hd _ (List.mem_map_of_mem ht)) hx).2
  rw [← h1, lpEval_smul, mul_div_assoc, ← h2]
  push_cast
  ring

theorem sum_qt_poleOfTailS (V : List TailQ) (hV : tailsInDisk V = true)
    (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    ((V.map poleOfTailS).map (fun q => qt q 0 x)).sum =
      -1 * ((((V.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum).re) := by
  have hd := tailsInDisk_spec hV
  rw [re_list_sum]
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  have h1 := tailS_pole t (hd _ (List.mem_map_of_mem ht)) (hVz t ht) x hx
  have h2 := (tailSFrac_spec t (hd _ (List.mem_map_of_mem ht)) hx).2
  rw [← h1, lpEval_smul, mul_div_assoc, ← h2]
  push_cast
  ring

/-- `qt (poleOfTail t) = -2 Re (r z / quad)` -/
theorem qt_poleOfTail (t : TailQ) (ht : ‖(TailQ.toC t).1‖ < 1) (hz : t.zr ≠ 0 ∨ t.zi ≠ 0)
    {x : ℝ} (hx : |x| ≤ 1) :
    qt (poleOfTail t) 0 x =
      -2 * (((TailQ.toC t).2 * (TailQ.toC t).1 / barrierTailQuadraticDen (TailQ.toC t).1 x).re) := by
  have h1 := tail_pole t ht hz x hx
  have h2 := (tailTFrac_spec t ht hx).2
  rw [← h1, lpEval_smul, mul_div_assoc, ← h2]
  push_cast
  ring

theorem sum_qt_poleOfTail (P : List TailQ) (hP : tailsInDisk P = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    ((P.map poleOfTail).map (fun q => qt q 0 x)).sum =
      -2 * ((((P.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum).re) := by
  have hd := tailsInDisk_spec hP
  rw [re_list_sum]
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  exact qt_poleOfTail t (hd _ (List.mem_map_of_mem ht)) (hPz t ht) hx

theorem sum_qt_poleC (V : List TailQ) (hV : tailsInDisk V = true)
    (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    ((V.map poleC).map (fun q => qt q 0 x)).sum =
      2 * ((((V.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum).re) := by
  have hd := tailsInDisk_spec hV
  rw [re_list_sum]
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  have := qt_poleOfTail t (hd _ (List.mem_map_of_mem ht)) (hVz t ht) hx
  have e : qt (poleC t) 0 x = -(qt (poleOfTail t) 0 x) := by
    have := qt_scale (-1) (poleOfTail t) 0 x
    unfold poleC
    simpa using this
  rw [e, this]
  ring

/-! ### pieces of the derivative -/

theorem hasDerivAt_peel0 (α : ℝ) (f0 : Bool) {x : ℝ} (h0 : f0 = true ∨ x ≠ 0) :
    HasDerivAt (fun y : ℝ => if f0 then (0 : ℝ) else α * Real.log |y|)
      (if f0 then 0 else α / x) x := by
  cases f0
  · have hx : x ≠ 0 := h0.resolve_left (by simp)
    have := (by simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log hx :
      HasDerivAt (fun y : ℝ => Real.log |y|) (x⁻¹) x)
    simpa [div_eq_mul_inv] using this.const_mul α
  · simpa using hasDerivAt_const x (0 : ℝ)

theorem hasDerivAt_peel1 (β : ℝ) (f1 : Bool) {x : ℝ} (h1 : f1 = true ∨ x ≠ 1) :
    HasDerivAt (fun y : ℝ => if f1 then (0 : ℝ) else β * Real.log (1 - y))
      (if f1 then 0 else β / (x - 1)) x := by
  cases f1
  · have hx : 1 - x ≠ 0 := fun h => (h1.resolve_left (by simp)) (by linarith)
    have := ((hasDerivAt_id x).const_sub (1 : ℝ)).log hx
    have e : β / (x - 1) = β * (-1 / (1 - x)) := by
      have : x - 1 ≠ 0 := fun h => hx (by linarith)
      field_simp
      ring
    simpa [e] using this.const_mul β
  · simpa using hasDerivAt_const x (0 : ℝ)

theorem hasDerivAt_log_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) (2 * x / (1 + x ^ 2)) x := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
  exact hp.log hd

/-! ### the row field -/

theorem rowFieldSP_hasDerivAt (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (Z : List ℤ) (hZ : ∀ x : ℝ, -4 * finUR Pc x - finPR Vc x = ptZ Z 0 x)
    (f0 f1 : Bool) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (h0 : f0 = true ∨ x ≠ 0) :
    HasDerivAt (rowFieldSP R Pc Vc P V f0 f1) (ftZ Z (rowPolesP R P V f0 f1) 0 x) x := by
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have h1 : f1 = true ∨ x ≠ 1 := Or.inr hx.2.ne
  obtain ⟨sP1, sP2⟩ := trialSeqS_summable (cs := Pc) hP
  obtain ⟨sV1, -⟩ := trialSeqS_summable (cs := Vc) hV
  have hT := barrierTrialT_hasDerivAt_series (trialSeqS Pc P) sP1 sP2 hx
  rw [(trialSeqS_U_hasSum Pc hP hxa).tsum_eq] at hT
  have hS := barrierTrialS_hasDerivAt_series (trialSeqS Vc V) sV1 hx
  rw [(trialSeqS_power_hasSum Vc hV hxa).tsum_eq] at hS
  have hg := (hasDerivAt_log_one_add_sq x).const_mul (-(R.gamma : ℝ))
  have hall := (((hasDerivAt_peel0 (R.alpha : ℝ) f0 h0).add
    (hasDerivAt_peel1 (R.beta : ℝ) f1 h1)).add
    ((hg.sub (hT.const_mul 4)).sub hS))
  unfold rowFieldSP rowFieldGP rowRegG
  refine hall.congr_deriv ?_
  unfold ftZ
  rw [← hZ x]
  simp only [rowPolesP, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, sum_qt_poleP P hP hPz hxa, sum_qt_poleOfTailS V hV hVz hxa]
  have q2 : qt ⟨-2 * R.gamma, 0, 0, 1⟩ 0 x = (-2 * (R.gamma : ℝ)) * x / (x ^ 2 + 1) := by
    rw [qt_i]; push_cast; ring
  rw [q2]
  unfold finUR finPR
  have hd : (1 + x ^ 2) ≠ 0 := by positivity
  have hd' : (x ^ 2 + 1) ≠ 0 := by positivity
  cases f0 <;> cases f1 <;>
  · simp only [Bool.false_eq_true, if_false, if_true, List.map_nil, List.sum_nil,
      List.map_cons, List.sum_cons, List.nil_append, qt_real, Rat.cast_zero, Rat.cast_one,
      sub_zero]
    field_simp
    ring

/-! ### the column field -/

theorem hasDerivAt_peel0c (b : ℝ) (f0 : Bool) {x : ℝ} (h0 : f0 = true ∨ x ≠ 0) :
    HasDerivAt (fun y : ℝ => if f0 then (0 : ℝ) else b * Real.log y)
      (if f0 then 0 else b / x) x := by
  cases f0
  · have hx : x ≠ 0 := h0.resolve_left (by simp)
    have := Real.hasDerivAt_log hx
    simpa [div_eq_mul_inv] using this.const_mul b
  · simpa using hasDerivAt_const x (0 : ℝ)

theorem colFieldSP_hasDerivAt (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (Z : List ℤ) (hZ : ∀ x : ℝ, 2 * finUR Vc x = ptZ Z 0 x)
    (f0 f1 : Bool) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (h0 : f0 = true ∨ x ≠ 0) :
    HasDerivAt (colFieldSP C Vc V f0 f1) (ftZ Z (colPolesP C V f0 f1) 0 x) x := by
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have h1 : f1 = true ∨ x ≠ 1 := Or.inr hx.2.ne
  obtain ⟨sV1, sV2⟩ := trialSeqS_summable (cs := Vc) hV
  have hT := barrierTrialT_hasDerivAt_series (trialSeqS Vc V) sV1 sV2 hx
  rw [(trialSeqS_U_hasSum Vc hV hxa).tsum_eq] at hT
  have hall := ((hasDerivAt_peel0c (C.b : ℝ) f0 h0).add
    (hasDerivAt_peel1 (C.q : ℝ) f1 h1)).add (hT.const_mul 2)
  unfold colFieldSP colFieldGP colRegG
  refine hall.congr_deriv ?_
  unfold ftZ
  rw [← hZ x]
  simp only [colPolesP, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, sum_qt_poleC V hV hVz hxa]
  unfold finUR
  cases f0 <;> cases f1 <;>
  · simp only [Bool.false_eq_true, if_false, if_true, List.map_nil, List.sum_nil,
      List.map_cons, List.sum_cons, List.nil_append, qt_real, Rat.cast_zero, Rat.cast_one,
      sub_zero]
    ring

/-! ### the residual field -/

theorem resFieldS_hasDerivAt {Pc : List ℤ} {P : List TailQ}
    (hP : tailsInDisk P = true) (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (Z : List ℤ) (hZ : ∀ x : ℝ, -2 * finUR Pc x = ptZ Z 0 x)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (resFieldS Pc P) (ftZ Z (resPoles P) 0 x) x := by
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  obtain ⟨sP1, sP2⟩ := trialSeqS_summable (cs := Pc) hP
  have hT := barrierTrialT_hasDerivAt_series (trialSeqS Pc P) sP1 sP2 hx
  rw [(trialSeqS_U_hasSum Pc hP hxa).tsum_eq] at hT
  have hg := (hasDerivAt_log_one_add_sq x).const_mul (-(9 / 10 : ℝ))
  have hall := hg.sub (hT.const_mul 2)
  unfold resFieldS resFieldG
  refine hall.congr_deriv ?_
  unfold ftZ
  rw [← hZ x]
  simp only [resPoles, List.map_cons, List.sum_cons, sum_qt_poleOfTail P hP hPz hxa]
  rw [qt_i]
  unfold finUR
  have hd : (x ^ 2 + 1) ≠ 0 := by positivity
  have hd' : (1 + x ^ 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end
end CatalanMeasure.CellCert
