module
public import Submission.CatalanMeasure.Cert.ModColumn
public import Submission.CatalanMeasure.Cert.IntegerPoly
@[expose] public section
open OAI.InternalCatalan Set Filter
open scoped Topology
namespace CatalanMeasure.Cert
def NoRootGaps (A : List ℚ) (ps : List Piece) : Prop :=
  ∀ p ∈ ps, p.2.2 = false → ∀ x ∈ Ioo (p.1 : ℝ) p.2.1, lpEval A x ≠ 0

theorem coverFrom_spec_of_noRoot {A E : List ℚ} {ps : List Piece} {cur b : ℚ}
    (h : coverFrom A E cur ps b = true) (hgaps : NoRootGaps A ps)
    {x : ℝ} (hx : x ∈ Ioo (cur : ℝ) b)
    (hA : lpEval A x = 0) :
    (∃ e ∈ E, x = e) ∨ ∃ p ∈ ps, p.2.2 = true ∧ x ∈ Icc (p.1 : ℝ) p.2.1 := by
  induction ps generalizing cur with
  | nil =>
    simp only [coverFrom, decide_eq_true_eq] at h
    subst h
    exact absurd hx.2 (not_lt.mpr hx.1.le)
  | cons p rest ih =>
    simp only [coverFrom, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hlo, hlt⟩, hbrk⟩, hrest⟩ := h
    have hgap := hgaps p List.mem_cons_self
    have hgaps' : NoRootGaps A rest := by
      intro q hq
      exact hgaps q (List.mem_cons_of_mem _ hq)
    subst hlo
    rcases lt_trichotomy x p.2.1 with hlt' | heq | hgt
    · -- inside the piece
      cases hk : p.2.2 with
      | true => exact Or.inr ⟨p, List.mem_cons_self, hk, hx.1.le, hlt'.le⟩
      | false => exact absurd hA (hgap hk x ⟨hx.1, hlt'⟩)
    · -- at the right end of the piece
      rcases hbrk with ((((hb | hk) | hn) | he) | hne)
      · exfalso; rw [heq, hb] at hx; exact lt_irrefl _ hx.2
      · exact Or.inr ⟨p, List.mem_cons_self, hk, hx.1.le, heq.le⟩
      · cases rest with
        | nil => simp [nextIsBracket] at hn
        | cons q rest' =>
          simp only [coverFrom, Bool.and_eq_true, decide_eq_true_eq] at hrest
          have hq : q.1 = p.2.1 := hrest.1.1.1
          refine Or.inr ⟨q, List.mem_cons_of_mem _ List.mem_cons_self, hn, ?_, ?_⟩
          · rw [hq, heq]
          · have : (q.1 : ℝ) < q.2.1 := by exact_mod_cast hrest.1.1.2
            rw [heq, ← hq]; exact this.le
      · exact Or.inl ⟨p.2.1, List.elem_iff.mp he, heq⟩
      · exfalso; apply hne
        have := hA; rw [heq, ← lpEvalQ_cast] at this; exact_mod_cast this
    · -- beyond the piece
      rcases ih hrest hgaps' ⟨hgt, hx.2⟩ with h1 | ⟨q, hq, hq'⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

/-- Every bracket satisfies `v + e + (hi - lo) B ≤ M`, where `v + e` bounds the field at `lo`
and `B` bounds `|A / Q|` on the bracket. -/
theorem rowCheck_spec_of_noRoot {Pc Vc : List ℤ} {P V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (rowFracs Pc Vc P V) = (A, Q))
    (h : rowCheck P V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (rowBracketOK Pc Vc P V A Q M) = true) (hm1 : rowEndOK Pc Vc P V M = true) :
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
    unfold rowBracketOK at hpa
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
      exact rowApprox_spec hP hV hve (abs_le.mpr ⟨h1.1.le, h1.2.le⟩) (hdom.2 _ hl) h1.2.ne
    · intro y hy _
      exact (hder y (hdom.1 hy) (hdom.2 y hy)).2

theorem colCheck_spec_of_noRoot {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (colFracs Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (colBracketOK Vc V A Q M) = true) :
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
    unfold colBracketOK at hpa
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
      exact colApprox_spec hV hve (hdom ⟨le_rfl, hlt'.le⟩)
    · intro y hy _
      exact (hder y (hdom hy)).2

theorem modColCheck_spec_of_noRoot {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (modColFracs Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : NoRootGaps A ps)
    (hall : ps.all (modColBracketOK Vc V A Q M) = true) :
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
    unfold modColBracketOK at hpa
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
      exact modColApprox_spec hV hve (hdom ⟨le_rfl, hlt'.le⟩)
    · intro y hy _
      exact (hder y (hdom hy)).2


end CatalanMeasure.Cert
