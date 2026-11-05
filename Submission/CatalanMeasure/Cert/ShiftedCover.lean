module
public import Submission.CatalanMeasure.Cert.ShiftedCoverColumn
public import Submission.CatalanMeasure.Cert.FlexibleCover
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set Filter
open scoped Topology
noncomputable section

def shiftedRowBracketOK (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ)
    (A Q : List ℚ) (M : ℚ) (p : Piece) : Bool :=
  rowBracketIn p && bracketOK A Q (shiftedRowApprox R Pc Vc P V) M p

def shiftedColumnBracketOK (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ)
    (A Q : List ℚ) (M : ℚ) (p : Piece) : Bool :=
  colBracketIn p && bracketOK A Q (shiftedColumnApprox C Vc V) M p

def shiftedRowEndOK (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (M : ℚ) : Bool :=
  match shiftedRowApprox R Pc Vc P V (-1) with
  | some ve =>decide (ve.1+ve.2 ≤ M)
  | none =>false

theorem shiftedRowCheck_spec {R : RowWeights} (hAlpha : 0<R.alpha) (hBeta : 0<R.beta) {Pc Vc : List ℤ} {P V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (shiftedRowFracs R Pc Vc P V) = (A, Q))
    (h : rowCheck P V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (shiftedRowBracketOK R Pc Vc P V A Q M) = true) (hm1 : shiftedRowEndOK R Pc Vc P V M = true) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField R Pc Vc P V x ≤ M := by
  unfold rowCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hP, hV⟩, hcov⟩ := h
  unfold shiftedRowEndOK at hm1
  have hall' := List.all_eq_true.mp hall
  set F := shiftedRowField R Pc Vc P V
  have hder : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 → lpEval Q x ≠ 0 ∧
      HasDerivAt F (lpEval A x / lpEval Q x) x := by
    intro x hx hx0
    have := shiftedRowField_hasDerivAt (R := R) (Pc := Pc) (Vc := Vc) hP hV hx hx0
    rw [hAQ] at this
    exact this
  refine shiftedRowField_sup_of_cover hP hV hAlpha hBeta (S := {x | ∃ p ∈ ps, p.2.2 = true ∧ x ∈ Icc (p.1 : ℝ) p.2.1})
    ?_ ?_ ?_
  · split at hm1
    · rename_i ve hve
      simp only [decide_eq_true_eq] at hm1
      have := shiftedRowApprox_spec hP hV (v := ve.1) (e := ve.2) (by rw [hve]) (by norm_num)
        (by norm_num) (by norm_num)
      push_cast at this
      have hm : ((ve.1 + ve.2 : ℚ) : ℝ) ≤ M := by exact_mod_cast hm1
      push_cast at hm
      linarith
    · simp at hm1
  · intro x hx hd
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := by
      rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2]⟩
      · exact ⟨by linarith [hx.1], hx.2⟩
    have hx0 : x ≠ 0 := by rcases hx with hx | hx <;> [exact hx.2.ne; exact hx.1.ne']
    obtain ⟨hQ, hD⟩ := hder x hx' hx0
    rw [hD.deriv] at hd
    have hA : lpEval A x = 0 := by
      rcases div_eq_zero_iff.mp hd with h | h
      · exact h
      · exact absurd h hQ
    rcases coverFrom_spec_of_noRoot hcov hgaps (by push_cast; exact hx') hA with ⟨e, he, rfl⟩ | hp
    · simp at he; subst he; simp at hx0
    · exact hp
  · rintro x ⟨p, hp, hk, hx⟩
    have hpa := hall' p hp
    unfold shiftedRowBracketOK at hpa
    simp only [Bool.and_eq_true] at hpa
    obtain ⟨hin, hok⟩ := hpa
    unfold rowBracketIn at hin
    simp only [hk, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hin
    obtain ⟨hlt, hin⟩ := hin
    have hlt' : (p.1 : ℝ) < p.2.1 := by exact_mod_cast hlt
    have hdom : Icc (p.1 : ℝ) p.2.1 ⊆ Ioo (-1 : ℝ) 1 ∧ ∀ y ∈ Icc (p.1 : ℝ) p.2.1, y ≠ 0 := by
      rcases hin with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1' : (-1 : ℝ) < p.1 := by exact_mod_cast h1
        have h2' : (p.2.1 : ℝ) < 0 := by exact_mod_cast h2
        exact ⟨fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩,
          fun y hy => by linarith [hy.2]⟩
      · have h1' : (0 : ℝ) < p.1 := by exact_mod_cast h1
        have h2' : (p.2.1 : ℝ) < 1 := by exact_mod_cast h2
        exact ⟨fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩,
          fun y hy => by linarith [hy.1]⟩
    refine bracketOK_spec hok hk hlt (F := F) ?_ ?_ x hx
    · intro v e hve
      have hl : (p.1 : ℝ) ∈ Icc (p.1 : ℝ) p.2.1 := ⟨le_rfl, hlt'.le⟩
      have h1 := hdom.1 hl
      exact shiftedRowApprox_spec hP hV hve (abs_le.mpr ⟨h1.1.le, h1.2.le⟩) (hdom.2 _ hl) h1.2.ne
    · intro y hy _
      exact (hder y (hdom.1 hy) (hdom.2 y hy)).2

theorem shiftedColumnCheck_spec {C : ColumnWeights} (hb : 0<C.b) (hq : 0<C.q) {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (shiftedColumnFracs C Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (shiftedColumnBracketOK C Vc V A Q M) = true) :
    ∀ x ∈ Ioo (0 : ℝ) 1, shiftedColumnField C Vc V x ≤ M := by
  unfold colCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hV, hcov⟩ := h
  have hall' := List.all_eq_true.mp hall
  set F := shiftedColumnField C Vc V
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, lpEval Q x ≠ 0 ∧
      HasDerivAt F (lpEval A x / lpEval Q x) x := by
    intro x hx
    have := shiftedColumnField_hasDerivAt (C := C) (Vc := Vc) hV hx
    rw [hAQ] at this
    exact this
  refine shiftedColumnField_sup_of_cover hV hb hq (S := {x | ∃ p ∈ ps, p.2.2 = true ∧ x ∈ Icc (p.1 : ℝ) p.2.1})
    ?_ ?_
  · intro x hx hd
    obtain ⟨hQ, hD⟩ := hder x hx
    rw [hD.deriv] at hd
    have hA : lpEval A x = 0 := by
      rcases div_eq_zero_iff.mp hd with h | h
      · exact h
      · exact absurd h hQ
    rcases coverFrom_spec_of_noRoot hcov hgaps (by push_cast; exact hx) hA with ⟨e, he, rfl⟩ | hp
    · simp at he
    · exact hp
  · rintro x ⟨p, hp, hk, hx⟩
    have hpa := hall' p hp
    unfold shiftedColumnBracketOK at hpa
    simp only [Bool.and_eq_true] at hpa
    obtain ⟨hin, hok⟩ := hpa
    unfold colBracketIn at hin
    simp only [hk, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hin
    obtain ⟨⟨hlt, h1⟩, h2⟩ := hin
    have hlt' : (p.1 : ℝ) < p.2.1 := by exact_mod_cast hlt
    have h1' : (0 : ℝ) < p.1 := by exact_mod_cast h1
    have h2' : (p.2.1 : ℝ) < 1 := by exact_mod_cast h2
    have hdom : Icc (p.1 : ℝ) p.2.1 ⊆ Ioo (0 : ℝ) 1 :=
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    refine bracketOK_spec hok hk hlt (F := F) ?_ ?_ x hx
    · intro v e hve
      exact shiftedColumnApprox_spec hV hve (hdom ⟨le_rfl, hlt'.le⟩)
    · intro y hy _
      exact (hder y (hdom hy)).2


end
end CatalanMeasure.Cert
