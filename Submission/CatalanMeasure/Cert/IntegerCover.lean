module
public import Submission.CatalanMeasure.Cert.IntegerRatio
@[expose] public section
open OAI.InternalCatalan Set Filter
open scoped Topology
namespace CatalanMeasure.Cert

def integerBracketOK (AZ QZ : List ℤ) (cA cQ : ℚ)
    (ev : ℚ → Option (ℚ × ℚ)) (M : ℚ) (p : Piece) : Bool :=
  !p.2.2 ||
    match ev p.1, ipRatioBound AZ QZ cA cQ p.1 (p.2.1 - p.1) with
    | some ve, some B => decide (ve.1 + ve.2 + (p.2.1 - p.1) * B ≤ M)
    | _, _ => false
theorem integerBracketOK_spec {A Q : List ℚ} {AZ QZ : List ℤ} {cA cQ : ℚ} {ev : ℚ → Option (ℚ × ℚ)} {M : ℚ} {p : Piece}
    (hAint : A = lpSmul cA (AZ.map (fun (z : ℤ) => (z : ℚ))))
    (hQint : Q = lpSmul cQ (QZ.map (fun (z : ℤ) => (z : ℚ))))
    (h : integerBracketOK AZ QZ cA cQ ev M p = true) (hk : p.2.2 = true) (hlt : p.1 < p.2.1)
    {F : ℝ → ℝ}
    (hev : ∀ v e, ev p.1 = some (v, e) → F p.1 ≤ v + e)
    (hder : ∀ y ∈ Icc (p.1 : ℝ) p.2.1, lpEval Q y ≠ 0 →
      HasDerivAt F (lpEval A y / lpEval Q y) y) :
    ∀ x ∈ Icc (p.1 : ℝ) p.2.1, F x ≤ M := by
  unfold integerBracketOK at h
  rw [hk] at h
  simp only [Bool.not_true, Bool.false_or] at h
  split at h
  · rename_i ve B hve hB
    simp only [decide_eq_true_eq] at h
    have hw : 0 < p.2.1 - p.1 := sub_pos.mpr hlt
    have hpw : ((p.1 + (p.2.1 - p.1) : ℚ) : ℝ) = p.2.1 := by push_cast; ring
    intro x hx
    have hbd : ∀ y ∈ Icc (p.1 : ℝ) p.2.1, lpEval Q y ≠ 0 ∧ |lpEval A y / lpEval Q y| ≤ B := by
      intro y hy
      refine ipRatioBound_spec hAint hQint hw hB ⟨hy.1, ?_⟩
      push_cast; linarith [hy.2]
    have hF0 := hev ve.1 ve.2 hve
    have hmvt := Case1Height.abs_sub_le_on_Icc (f := F) (a := p.1) (b := p.2.1) (C := B)
      (fun y hy => (hder y hy (hbd y hy).1).differentiableAt)
      (fun y hy => by rw [(hder y hy (hbd y hy).1).deriv]; exact (hbd y hy).2) hx
    have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hbd p.1 ⟨le_rfl, by exact_mod_cast hlt.le⟩).2
    have hxl : |x - p.1| ≤ ((p.2.1 - p.1 : ℚ) : ℝ) := by
      rw [abs_of_nonneg (by linarith [hx.1])]; push_cast; linarith [hx.2]
    have hM : ((ve.1 + ve.2 + (p.2.1 - p.1) * B : ℚ) : ℝ) ≤ M := by exact_mod_cast h
    push_cast at hM
    have := (abs_le.mp hmvt).2
    have h2 : (B : ℝ) * |x - p.1| ≤ B * ((p.2.1 - p.1 : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hxl hB0
    push_cast at h2
    linarith
  · simp at h

/-! ### Continuity and limits of the fields -/


def integerRowBracketOK (Pc Vc : List ℤ) (P V : List TailQ)
    (AZ QZ : List ℤ) (cA cQ M : ℚ) (p : Piece) : Bool :=
  rowBracketIn p && integerBracketOK AZ QZ cA cQ (rowApprox Pc Vc P V) M p
def integerColBracketOK (Vc : List ℤ) (V : List TailQ)
    (AZ QZ : List ℤ) (cA cQ M : ℚ) (p : Piece) : Bool :=
  colBracketIn p && integerBracketOK AZ QZ cA cQ (colApprox Vc V) M p
def integerModColBracketOK (Vc : List ℤ) (V : List TailQ)
    (AZ QZ : List ℤ) (cA cQ M : ℚ) (p : Piece) : Bool :=
  colBracketIn p && integerBracketOK AZ QZ cA cQ (modColApprox Vc V) M p

theorem rowCheck_spec_integer {Pc Vc : List ℤ} {P V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {AZ QZ : List ℤ} {cA cQ : ℚ} {ps : List Piece}
    (hAint : A = lpSmul cA (AZ.map (fun (z : ℤ) => (z : ℚ))))
    (hQint : Q = lpSmul cQ (QZ.map (fun (z : ℤ) => (z : ℚ)))) (hAQ : fracSum (rowFracs Pc Vc P V) = (A, Q))
    (h : rowCheck P V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (integerRowBracketOK Pc Vc P V AZ QZ cA cQ M) = true) (hm1 : rowEndOK Pc Vc P V M = true) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x ≤ M := by
  unfold rowCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hP, hV⟩, hcov⟩ := h
  unfold rowEndOK at hm1
  have hall' := List.all_eq_true.mp hall
  set F := realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V)
  have hder : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 → lpEval Q x ≠ 0 ∧
      HasDerivAt F (lpEval A x / lpEval Q x) x := by
    intro x hx hx0
    have := rowField_hasDerivAt (Pc := Pc) (Vc := Vc) hP hV hx hx0
    rw [hAQ] at this
    exact this
  refine rowField_sup_of_cover hP hV (S := {x | ∃ p ∈ ps, p.2.2 = true ∧ x ∈ Icc (p.1 : ℝ) p.2.1})
    ?_ ?_ ?_
  · split at hm1
    · rename_i ve hve
      simp only [decide_eq_true_eq] at hm1
      have := rowApprox_spec hP hV (v := ve.1) (e := ve.2) (by rw [hve]) (by norm_num)
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
    unfold integerRowBracketOK at hpa
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
    refine integerBracketOK_spec hAint hQint hok hk hlt (F := F) ?_ ?_ x hx
    · intro v e hve
      have hl : (p.1 : ℝ) ∈ Icc (p.1 : ℝ) p.2.1 := ⟨le_rfl, hlt'.le⟩
      have h1 := hdom.1 hl
      exact rowApprox_spec hP hV hve (abs_le.mpr ⟨h1.1.le, h1.2.le⟩) (hdom.2 _ hl) h1.2.ne
    · intro y hy _
      exact (hder y (hdom.1 hy) (hdom.2 y hy)).2

theorem colCheck_spec_integer {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {AZ QZ : List ℤ} {cA cQ : ℚ} {ps : List Piece}
    (hAint : A = lpSmul cA (AZ.map (fun (z : ℤ) => (z : ℚ))))
    (hQint : Q = lpSmul cQ (QZ.map (fun (z : ℤ) => (z : ℚ)))) (hAQ : fracSum (colFracs Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (integerColBracketOK Vc V AZ QZ cA cQ M) = true) :
    ∀ x ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField (trialSeq Vc V) x ≤ M := by
  unfold colCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hV, hcov⟩ := h
  have hall' := List.all_eq_true.mp hall
  set F := realEnergyColumnTrialField (trialSeq Vc V)
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, lpEval Q x ≠ 0 ∧
      HasDerivAt F (lpEval A x / lpEval Q x) x := by
    intro x hx
    have := colField_hasDerivAt (Vc := Vc) hV hx
    rw [hAQ] at this
    exact this
  refine colField_sup_of_cover hV (S := {x | ∃ p ∈ ps, p.2.2 = true ∧ x ∈ Icc (p.1 : ℝ) p.2.1})
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
    unfold integerColBracketOK at hpa
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
    refine integerBracketOK_spec hAint hQint hok hk hlt (F := F) ?_ ?_ x hx
    · intro v e hve
      exact colApprox_spec hV hve (hdom ⟨le_rfl, hlt'.le⟩)
    · intro y hy _
      exact (hder y (hdom hy)).2

theorem modColCheck_spec_integer {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {AZ QZ : List ℤ} {cA cQ : ℚ} {ps : List Piece}
    (hAint : A = lpSmul cA (AZ.map (fun (z : ℤ) => (z : ℚ))))
    (hQint : Q = lpSmul cQ (QZ.map (fun (z : ℤ) => (z : ℚ)))) (hAQ : fracSum (modColFracs Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (integerModColBracketOK Vc V AZ QZ cA cQ M) = true) :
    ∀ x ∈ Ioo (0 : ℝ) 1, modColField (trialSeq Vc V) x ≤ M := by
  unfold colCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hV, hcov⟩ := h
  have hall' := List.all_eq_true.mp hall
  set F := modColField (trialSeq Vc V)
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, lpEval Q x ≠ 0 ∧
      HasDerivAt F (lpEval A x / lpEval Q x) x := by
    intro x hx
    have := modColField_hasDerivAt (Vc := Vc) hV hx
    rw [hAQ] at this
    exact this
  refine modColField_sup_of_cover hV (S := {x | ∃ p ∈ ps, p.2.2 = true ∧ x ∈ Icc (p.1 : ℝ) p.2.1})
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
    unfold integerModColBracketOK at hpa
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
    refine integerBracketOK_spec hAint hQint hok hk hlt (F := F) ?_ ?_ x hx
    · intro v e hve
      exact modColApprox_spec hV hve (hdom ⟨le_rfl, hlt'.le⟩)
    · intro y hy _
      exact (hder y (hdom hy)).2


end CatalanMeasure.Cert
