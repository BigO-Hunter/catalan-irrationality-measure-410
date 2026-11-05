module

public import Submission.CatalanMeasure.Cert.Cover

@[expose] public section

open OAI.InternalCatalan Set Filter
open scoped Topology

namespace CatalanMeasure.Cert

noncomputable def modColField (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  realEnergyColumnTrialField v s + Real.log (1 + s)

def modColTerms (V : List TailQ) (s : ℚ) : List LogTerm :=
  colTerms V s ++ [⟨1, 0, 1 + s, 0⟩]

def modColApprox (Vc : List ℤ) (V : List TailQ) (s : ℚ) : Option (ℚ × ℚ) :=
  (sumLogs (modColTerms V s)).map (fun ve => (ve.1 + colRat Vc s, ve.2))

theorem modColField_eq (Vc : List ℤ) (V : List TailQ) (hV : tailsInDisk V = true)
    {s : ℚ} (hs : (s : ℝ) ∈ Ioo (0 : ℝ) 1) :
    modColField (trialSeq Vc V) s =
      ((modColTerms V s).map LogTerm.val).sum + (colRat Vc s : ℝ) := by
  have hp : (0 : ℝ) < ((1 + s : ℚ) : ℝ) := by push_cast; linarith [hs.1]
  unfold modColField modColTerms
  rw [colField_eq Vc V hV hs]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [realLogTerm 1 (1 + s) hp.ne', abs_of_pos hp]
  push_cast
  ring

theorem modColApprox_spec {Vc : List ℤ} {V : List TailQ} (hV : tailsInDisk V = true)
    {s v e : ℚ} (h : modColApprox Vc V s = some (v, e))
    (hs : (s : ℝ) ∈ Ioo (0 : ℝ) 1) : modColField (trialSeq Vc V) s ≤ v + e := by
  unfold modColApprox at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have := sumLogs_spec h1
  rw [modColField_eq Vc V hV hs]
  push_cast
  linarith [(abs_le.mp this).2]

def modColFracs (Vc : List ℤ) (V : List TailQ) : List (List ℚ × List ℚ) :=
  [fracSum (colFracs Vc V), ([1], [1, 1])]

theorem modColField_hasDerivAt {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    lpEval (fracSum (modColFracs Vc V)).2 x ≠ 0 ∧
      HasDerivAt (modColField (trialSeq Vc V))
        (lpEval (fracSum (modColFracs Vc V)).1 x /
          lpEval (fracSum (modColFracs Vc V)).2 x) x := by
  obtain ⟨hQ, hd⟩ := colField_hasDerivAt (Vc := Vc) hV hx
  have hplus : 1 + x ≠ 0 := by linarith [hx.1]
  have hden : ∀ f ∈ modColFracs Vc V, lpEval f.2 x ≠ 0 := by
    intro f hf
    simp only [modColFracs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact hQ
    · simpa [lpEval] using hplus
  obtain ⟨hq, ha⟩ := fracSum_spec (modColFracs Vc V) x hden
  refine ⟨hq, ?_⟩
  have hl : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + x)) x := by
    simpa using ((hasDerivAt_id x).const_add 1).log hplus
  unfold modColField
  convert hd.add hl using 1
  rw [ha]
  simp [modColFracs, lpEval]

theorem modColField_continuousOn {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) : ContinuousOn (modColField (trialSeq Vc V)) (Ioo 0 1) := by
  apply (colField_continuousOn hV).add
  intro x hx
  exact ((continuousAt_const.add continuousAt_id).log (by linarith [hx.1] : 1 + x ≠ 0)).continuousWithinAt

theorem modColField_sup_of_cover {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) {M : ℝ} {S : Set ℝ}
    (hcover : ∀ x ∈ Ioo (0 : ℝ) 1, deriv (modColField (trialSeq Vc V)) x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, modColField (trialSeq Vc V) x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, modColField (trialSeq Vc V) x ≤ M := by
  have hT := barrierTrialT_continuousOn (trialSeq Vc V) (trialSeq_summable (cs := Vc) hV).1
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover (S := S) (modColField_continuousOn hV)
  · have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 7 / 48)
      Real.tendsto_log_nhdsGT_zero
    have hr : ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
        2 * barrierTrialT (trialSeq Vc V) x + Real.log (1 + x)) 0 := by
      have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
        (continuousAt_const.sub continuousAt_id).log (by norm_num)
      have hlogp : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
        (continuousAt_const.add continuousAt_id).log (by norm_num)
      exact ((hlog.const_mul (1 / 12 : ℝ)).add ((continuousOn_continuousAt_zero hT).const_mul 2)).add hlogp
    have hh := atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
    convert hh using 1
    funext x
    unfold modColField realEnergyColumnTrialField realEnergyColumnField
    ring
  · have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12) log_one_sub_tendsto
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
    have hlogp := ((continuousAt_const.add continuousAt_id).log
      (by norm_num : (1 : ℝ) + 1 ≠ 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
    have hr := ((hlog.const_mul (7 / 48 : ℝ)).add
      ((continuousOn_tendsto_one_left hT).const_mul 2)).add hlogp
    have hh := atBot_add_finite hl hr
    convert hh using 1
    funext x
    unfold modColField realEnergyColumnTrialField realEnergyColumnField
    simp only [Pi.add_apply, id_eq]
    ring
  · exact hcover
  · exact hvalues

def modColBracketOK (Vc : List ℤ) (V : List TailQ) (A Q : List ℚ) (M : ℚ) (p : Piece) : Bool :=
  colBracketIn p && bracketOK A Q (modColApprox Vc V) M p

theorem modColCheck_spec {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (modColFracs Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : ps.all (gapOK A) = true)
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
    rcases coverFrom_spec hcov hgaps (by push_cast; exact hx) hA with ⟨e, he, rfl⟩ | hp
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
