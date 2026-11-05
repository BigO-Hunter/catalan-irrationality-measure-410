module

public import Submission.CatalanMeasure.CellCert.FieldsS
public import Submission.CatalanMeasure.CellCert.IntEval

@[expose] public section

/-!
# Centre enclosures of the (peeled) 728 fields

`rowApproxS R Pc Vc P V f0 f1 c = some (v, e)` gives `|rowFieldSP R Pc Vc P V f0 f1 c - v| ≤ e`
for a rational `c` with `|c| ≤ 1`.  The ~115 logarithm terms of the tails go through
`Cert.sumLogs`; the finite Chebyshev / power sums are evaluated with big-integer arithmetic
(`IntEval`) and rounded to a dyadic enclosure of width `2^-128`.
-/

open OAI.InternalCatalan Polynomial

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert

/-! ### logarithm terms -/

def rowTermsS (R : RowWeights) (P V : List TailQ) (f0 f1 : Bool) (x : ℚ) : List LogTerm :=
  (if f0 then [] else [⟨R.alpha, 0, x, 0⟩]) ++ (if f1 then [] else [⟨R.beta, 0, 1 - x, 0⟩]) ++
    [⟨-R.gamma, 0, 1 + x * x, 0⟩] ++
    P.map (fun t => ⟨2 * t.rr, 2 * t.ri, (quadArg x t).1, (quadArg x t).2⟩) ++
    V.map (fun t => ⟨t.rr, t.ri, (linArg x t).1, (linArg x t).2⟩)

def colTermsS (C : ColumnWeights) (V : List TailQ) (f0 f1 : Bool) (s : ℚ) : List LogTerm :=
  (if f0 then [] else [⟨C.b, 0, s, 0⟩]) ++ (if f1 then [] else [⟨C.q, 0, 1 - s, 0⟩]) ++
    V.map (fun t => ⟨-t.rr, -t.ri, (quadArg s t).1, (quadArg s t).2⟩)

def resTermsS (P : List TailQ) (x : ℚ) : List LogTerm :=
  [⟨-9 / 10, 0, 1 + x * x, 0⟩] ++
    P.map (fun t => ⟨t.rr, t.ri, (quadArg x t).1, (quadArg x t).2⟩)

/-! ### sums of the tail log terms -/

theorem tailLog_T2 (P : List TailQ) (x : ℚ) :
    ((P.map (fun t => (⟨2 * t.rr, 2 * t.ri, (quadArg x t).1, (quadArg x t).2⟩ : LogTerm))).map
        LogTerm.val).sum =
      2 * (((P.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * ((x : ℝ) : ℂ) * zr.1 + zr.1 ^ 2))).sum).re := by
  rw [re_list_sum]
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [← tailTerm_T]
  simp [Complex.mul_re]

theorem tailLog_T1 (P : List TailQ) (x : ℚ) :
    ((P.map (fun t => (⟨t.rr, t.ri, (quadArg x t).1, (quadArg x t).2⟩ : LogTerm))).map
        LogTerm.val).sum =
      (((P.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * ((x : ℝ) : ℂ) * zr.1 + zr.1 ^ 2))).sum).re := by
  rw [re_list_sum]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, LogTerm.val]
  rw [quadArg_spec]
  rfl

theorem tailLog_Tneg (V : List TailQ) (x : ℚ) :
    ((V.map (fun t => (⟨-t.rr, -t.ri, (quadArg x t).1, (quadArg x t).2⟩ : LogTerm))).map
        LogTerm.val).sum =
      -(((V.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * ((x : ℝ) : ℂ) * zr.1 + zr.1 ^ 2))).sum).re := by
  rw [re_list_sum, neg_eq_neg_one_mul]
  simp only [List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [← tailTerm_colT]
  ring

theorem tailLog_S (V : List TailQ) (x : ℚ) :
    ((V.map (fun t => (⟨t.rr, t.ri, (linArg x t).1, (linArg x t).2⟩ : LogTerm))).map
        LogTerm.val).sum =
      (((V.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - ((x : ℝ) : ℂ) * zr.1))).sum).re := by
  rw [re_list_sum]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  exact (tailTerm_S t x).symm

theorem abs_one_sub_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : |1 - x| = 1 - x :=
  abs_of_nonneg (by linarith [(abs_le.mp hx).2])

theorem log_term_sq {c : ℚ} (x : ℚ) :
    LogTerm.val ⟨c, 0, 1 + x * x, 0⟩ = (c : ℝ) * Real.log (1 + (x : ℝ) ^ 2) := by
  have hxx : (0 : ℝ) < 1 + (x : ℝ) * x := by nlinarith [mul_self_nonneg (x : ℝ)]
  have h2 : (((1 + x * x : ℚ)) : ℝ) ≠ 0 := by push_cast; exact hxx.ne'
  rw [realLogTerm _ _ h2]
  push_cast
  rw [abs_of_pos hxx, pow_two]

theorem realLogTerm' (c a : ℚ) : LogTerm.val ⟨c, 0, a, 0⟩ = (c : ℝ) * Real.log |(a : ℝ)| := by
  simp only [LogTerm.val, barrierComplex, Complex.mul_re, Complex.log_re]
  have : ‖(⟨(a : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ)‖ = |(a : ℝ)| := by
    rw [show (⟨(a : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = ((a : ℝ) : ℂ) by apply Complex.ext <;> simp]
    exact Complex.norm_real _
  rw [this]
  simp

/-! ### the fields as logarithm sums plus a finite sum -/

/-- the finite Chebyshev sum -/
noncomputable def finTR (cs : List ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
    (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)

/-- the finite power sum -/
noncomputable def finSR (cs : List ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) * x ^ (k + 1) /
    ((k + 1 : ℕ) : ℝ)

theorem log_abs_sq (x : ℚ) :
    Real.log |(((1 + x * x : ℚ)) : ℝ)| = Real.log (1 + (x : ℝ) ^ 2) := by
  have hxx : (0 : ℝ) < 1 + (x : ℝ) * x := by nlinarith [mul_self_nonneg (x : ℝ)]
  push_cast
  rw [abs_of_pos hxx, pow_two]

theorem rowFieldSP_eq (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (f0 f1 : Bool) {x : ℚ}
    (hx : |(x : ℝ)| ≤ 1) :
    rowFieldSP R Pc Vc P V f0 f1 x =
      ((rowTermsS R P V f0 f1 x).map LogTerm.val).sum +
        (-4 * finTR Pc x - finSR Vc x) := by
  unfold rowFieldSP rowFieldGP rowRegG finTR finSR
  rw [trialSeqS_T_eq_finite_log Pc hP hx, trialSeqS_S_eq_finite_log Vc hV hx]
  have h1 := abs_one_sub_of_abs_le hx
  cases f0 <;> cases f1 <;>
  · simp only [rowTermsS, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, tailLog_T2, tailLog_S, realLogTerm',
      Bool.false_eq_true, if_false, if_true, List.nil_append, List.append_nil, Rat.cast_neg,
      Rat.cast_sub, Rat.cast_one, log_abs_sq]
    try rw [h1]
    ring

theorem colFieldSP_eq (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (f0 f1 : Bool) {s : ℚ} (hs : |(s : ℝ)| ≤ 1) :
    colFieldSP C Vc V f0 f1 s =
      ((colTermsS C V f0 f1 s).map LogTerm.val).sum + 2 * finTR Vc s := by
  unfold colFieldSP colFieldGP colRegG finTR
  rw [trialSeqS_T_eq_finite_log Vc hV hs]
  have h1 := abs_one_sub_of_abs_le hs
  have h0 : Real.log |(s : ℝ)| = Real.log (s : ℝ) := Real.log_abs _
  cases f0 <;> cases f1 <;>
  · simp only [colTermsS, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, tailLog_Tneg, realLogTerm',
      Bool.false_eq_true, if_false, if_true, List.nil_append, List.append_nil, Rat.cast_neg,
      Rat.cast_sub, Rat.cast_one]
    try rw [h1]
    try rw [h0]
    ring

theorem resFieldS_eq {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) {x : ℚ}
    (hx : |(x : ℝ)| ≤ 1) :
    resFieldS Pc P x = ((resTermsS P x).map LogTerm.val).sum + (-2 * finTR Pc x) := by
  unfold resFieldS resFieldG finTR
  rw [trialSeqS_T_eq_finite_log Pc hP hx]
  simp only [resTermsS, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, tailLog_T1, log_term_sq]
  push_cast
  ring

/-! ### logarithm sums with dyadic rounding

`sumLogs` adds the exact rational logarithm enclosures, whose common denominator grows to
~10^200000 over the ~60 terms of a field.  `sumLogsR` rounds each term to the `2^-128` grid
(`encDiv`) before adding, at an extra error of `2^-128` per term. -/

def sumLogsR : List LogTerm → Option (ℚ × ℚ)
  | [] => some (0, 0)
  | t :: l =>
    match cLog t.c t.d t.a t.b, sumLogsR l with
    | some q, some (v, e) => some ((encDiv q.num q.den).1 + v,
        (wPieces t.c t.d : ℚ) / 1000000000000 + (encDiv q.num q.den).2 + e)
    | _, _ => none

theorem sumLogsR_spec {l : List LogTerm} {v e : ℚ} (h : sumLogsR l = some (v, e)) :
    |(l.map LogTerm.val).sum - (v : ℝ)| ≤ (e : ℝ) := by
  induction l generalizing v e with
  | nil =>
    simp only [sumLogsR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons t l ih =>
    simp only [sumLogsR] at h
    split at h
    · rename_i q v' e' hq hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 := cLog_spec hq
      have h2 := ih hl
      have h3 := encDiv_spec q.num q.den_pos
      have hq' : ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) := by
        rw [Rat.cast_def]
      rw [hq'] at h3
      simp only [List.map_cons, List.sum_cons]
      have hv : t.val = (barrierComplex t.c t.d * Complex.log ⟨(t.a : ℝ), (t.b : ℝ)⟩).re := rfl
      rw [hv]
      push_cast
      rw [abs_le] at h1 h2 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    · simp at h

/-! ### enclosures -/

def rowApproxS (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (f0 f1 : Bool) (c : ℚ) :
    Option (ℚ × ℚ) :=
  (sumLogsR (rowTermsS R P V f0 f1 c)).map (fun ve =>
    (ve.1 - 4 * (finTEnc Pc c).1 - (finSEnc Vc c).1,
     ve.2 + 4 * (finTEnc Pc c).2 + (finSEnc Vc c).2))

def colApproxS (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (f0 f1 : Bool) (c : ℚ) :
    Option (ℚ × ℚ) :=
  (sumLogsR (colTermsS C V f0 f1 c)).map (fun ve =>
    (ve.1 + 2 * (finTEnc Vc c).1, ve.2 + 2 * (finTEnc Vc c).2))

def resApproxS (Pc : List ℤ) (P : List TailQ) (c : ℚ) : Option (ℚ × ℚ) :=
  (sumLogsR (resTermsS P c)).map (fun ve =>
    (ve.1 - 2 * (finTEnc Pc c).1, ve.2 + 2 * (finTEnc Pc c).2))

theorem rowApproxS_spec (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : rowApproxS R Pc Vc P V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    |rowFieldSP R Pc Vc P V f0 f1 c - (v : ℝ)| ≤ (e : ℝ) := by
  unfold rowApproxS at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have hs := sumLogsR_spec h1
  have ht := finTEnc_spec Pc c
  have hv := finSEnc_spec Vc c
  rw [rowFieldSP_eq R hP hV f0 f1 hc]
  unfold finTR finSR
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
  rw [abs_le] at hs ht hv ⊢
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, hv.1, hv.2]

theorem colApproxS_spec (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : colApproxS C Vc V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    |colFieldSP C Vc V f0 f1 c - (v : ℝ)| ≤ (e : ℝ) := by
  unfold colApproxS at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have hs := sumLogsR_spec h1
  have ht := finTEnc_spec Vc c
  rw [colFieldSP_eq C hV f0 f1 hc]
  unfold finTR
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
  rw [abs_le] at hs ht ⊢
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

theorem resApproxS_spec {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) {c v e : ℚ}
    (h : resApproxS Pc P c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    |resFieldS Pc P c - (v : ℝ)| ≤ (e : ℝ) := by
  unfold resApproxS at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have hs := sumLogsR_spec h1
  have ht := finTEnc_spec Pc c
  rw [resFieldS_eq hP hc]
  unfold finTR
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
  rw [abs_le] at hs ht ⊢
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

/-- upper-bound forms used by the cell covers -/
theorem rowApproxS_le (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : rowApproxS R Pc Vc P V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    rowFieldSP R Pc Vc P V f0 f1 c ≤ (v : ℝ) + (e : ℝ) := by
  have := (abs_le.mp (rowApproxS_spec R hP hV f0 f1 h hc)).2
  linarith

theorem colApproxS_le (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : colApproxS C Vc V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    colFieldSP C Vc V f0 f1 c ≤ (v : ℝ) + (e : ℝ) := by
  have := (abs_le.mp (colApproxS_spec C hV f0 f1 h hc)).2
  linarith

theorem resApproxS_le {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) {c v e : ℚ}
    (h : resApproxS Pc P c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    resFieldS Pc P c ≤ (v : ℝ) + (e : ℝ) := by
  have := (abs_le.mp (resApproxS_spec hP h hc)).2
  linarith

end CatalanMeasure.CellCert
