module

public import Submission.OAI.NumberTheory.Catalan.Energy.BarrierGlobalMaxReduction
public import Submission.OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneBracketHeight
public import Submission.CatalanMeasure.Cert.FieldDeriv

@[expose] public section

/-!
# Upper bounds for the trial fields from a kernel-checked plan

A plan is a list of pieces `(lo, hi, isBracket)` covering an interval.  On a gap the
derivative numerator `A` has no root (`lpNoRootCheck`); a bracket is a short interval on which
the field is bounded by its certified value at the left end plus the length times a bound for
`|A / Q|`.  Since the fields tend to `-∞` at their singular points, their maxima are
stationary points, hence lie in brackets.
-/

open OAI.InternalCatalan Set Filter
open scoped Topology

namespace CatalanMeasure.Cert

/-- Rational Horner evaluation. -/
def lpEvalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: p, x => c + x * lpEvalQ p x

theorem lpEvalQ_cast (p : List ℚ) (x : ℚ) : ((lpEvalQ p x : ℚ) : ℝ) = lpEval p x := by
  induction p with
  | nil => simp [lpEvalQ]
  | cons c p ih => simp [lpEvalQ, ih]

/-- A piece of a plan: `(lo, hi, isBracket)`. -/
abbrev Piece := ℚ × ℚ × Bool

def nextIsBracket : List Piece → Bool
  | [] => false
  | p :: _ => p.2.2

/-- A gap piece contains no root of `A`. -/
def gapOK (A : List ℚ) (p : Piece) : Bool := p.2.2 || lpNoRootCheck A p.1 p.2.1

/-- The pieces start at `cur`, are contiguous, end at `b`, and a breakpoint between two gaps is
either in `E` or not a root of `A`. -/
def coverFrom (A : List ℚ) (E : List ℚ) : ℚ → List Piece → ℚ → Bool
  | cur, [], b => decide (cur = b)
  | cur, p :: rest, b =>
    decide (p.1 = cur) && decide (p.1 < p.2.1) &&
      (decide (p.2.1 = b) || p.2.2 || nextIsBracket rest || E.contains p.2.1 ||
        decide (lpEvalQ A p.2.1 ≠ 0)) &&
      coverFrom A E p.2.1 rest b

theorem coverFrom_spec {A E : List ℚ} {ps : List Piece} {cur b : ℚ}
    (h : coverFrom A E cur ps b = true) (hgaps : ps.all (gapOK A) = true)
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
    simp only [List.all_cons, Bool.and_eq_true] at hgaps
    obtain ⟨hgap, hgaps'⟩ := hgaps
    unfold gapOK at hgap
    simp only [Bool.or_eq_true] at hgap
    subst hlo
    rcases lt_trichotomy x p.2.1 with hlt' | heq | hgt
    · -- inside the piece
      rcases hgap with hk | hg
      · exact Or.inr ⟨p, List.mem_cons_self, hk, hx.1.le, hlt'.le⟩
      · exact absurd hA (lpEval_ne_zero_of_noRootCheck hg ⟨hx.1, hlt'⟩)
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
def bracketOK (A Q : List ℚ) (ev : ℚ → Option (ℚ × ℚ)) (M : ℚ) (p : Piece) : Bool :=
  !p.2.2 ||
    match ev p.1, lpRatioBound A Q p.1 (p.2.1 - p.1) with
    | some ve, some B => decide (ve.1 + ve.2 + (p.2.1 - p.1) * B ≤ M)
    | _, _ => false

theorem bracketOK_spec {A Q : List ℚ} {ev : ℚ → Option (ℚ × ℚ)} {M : ℚ} {p : Piece}
    (h : bracketOK A Q ev M p = true) (hk : p.2.2 = true) (hlt : p.1 < p.2.1)
    {F : ℝ → ℝ}
    (hev : ∀ v e, ev p.1 = some (v, e) → F p.1 ≤ v + e)
    (hder : ∀ y ∈ Icc (p.1 : ℝ) p.2.1, lpEval Q y ≠ 0 →
      HasDerivAt F (lpEval A y / lpEval Q y) y) :
    ∀ x ∈ Icc (p.1 : ℝ) p.2.1, F x ≤ M := by
  unfold bracketOK at h
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
      refine lpRatioBound_spec hw hB ⟨hy.1, ?_⟩
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

theorem atBot_add_finite {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  have hb : ∀ᶠ x in l, g x ≤ c + 1 :=
    ((tendsto_order.mp hg).2 (c + 1) (by linarith)).mono (fun _ hx => hx.le)
  exact tendsto_atBot_add_right_of_ge' l (c + 1) hf hb

theorem log_one_sub_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 - x)) (𝓝[<] 1) atBot := by
  have hc : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have ht : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x < 1 at hx
      change 0 < 1 - x
      exact sub_pos.mpr hx
  exact Real.tendsto_log_nhdsGT_zero.comp ht

theorem continuousOn_tendsto_one_left {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := by
  have ht : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝[Icc (-1) 1] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, ?_⟩
    have ha : ∀ᶠ x : ℝ in 𝓝[<] 1, -1 < x :=
      (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [ha, self_mem_nhdsWithin] with x hx hx1
    exact ⟨hx.le, le_of_lt hx1⟩
  exact (hf 1 (by norm_num)).tendsto.comp ht

theorem continuousOn_continuousAt_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) : ContinuousAt f 0 :=
  (hf 0 (by norm_num)).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

section Row

variable (Pc Vc : List ℤ) (P V : List TailQ)

noncomputable def rowRegular (x : ℝ) : ℝ :=
  -(2 / 2 + 17 / 48 : ℝ) * Real.log (1 + x ^ 2) + 0 * realEnergyCaseField x -
    2 * 2 * barrierTrialT (trialSeq Pc P) x - barrierTrialS (trialSeq Vc V) x

theorem rowField_split (x : ℝ) :
    realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x =
      (19 / 48 : ℝ) * Real.log |x| + (1 / 12 : ℝ) * Real.log (1 - x) + rowRegular Pc Vc P V x := by
  unfold realEnergyRowTrialField realEnergyField rowRegular
  ring

variable {Pc Vc P V}

theorem rowRegular_continuousOn (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) :
    ContinuousOn (rowRegular Pc Vc P V) (Icc (-1 : ℝ) 1) := by
  have hl : Continuous (fun x : ℝ => Real.log (1 + x ^ 2)) := by
    apply Continuous.log (continuous_const.add (continuous_id.pow 2))
    intro x
    exact ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hc : Continuous (fun x : ℝ => 0 * realEnergyCaseField x) := by
    simp only [zero_mul]; exact continuous_const
  have ht := barrierTrialT_continuousOn (trialSeq Pc P) (trialSeq_summable (cs := Pc) hP).1
  have hs := barrierTrialS_continuousOn (trialSeq Vc V) (trialSeq_summable (cs := Vc) hV).1
  exact (((hl.continuousOn.const_mul _).add hc.continuousOn).sub (ht.const_mul _)).sub hs

theorem rowField_continuousWithinAt (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ContinuousWithinAt (realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V))
      (Icc (-1 : ℝ) 1) x := by
  have hlog : ContinuousAt (fun y : ℝ => Real.log |y|) x := by
    simpa only [Real.log_abs] using Real.continuousAt_log h0
  have hlog1 : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (continuousAt_const.sub continuousAt_id).log (sub_ne_zero.mpr (Ne.symm h1))
  have hh := ((hlog.continuousWithinAt.const_mul (19 / 48 : ℝ)).add
    (hlog1.continuousWithinAt.const_mul (1 / 12 : ℝ))).add
    (rowRegular_continuousOn (Pc := Pc) (Vc := Vc) hP hV x hx)
  convert hh using 1
  funext y
  exact rowField_split Pc Vc P V y

theorem rowField_zero_remainder (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) :
    ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) + rowRegular Pc Vc P V x) 0 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  exact (hl.const_mul (1 / 12 : ℝ)).add
    (continuousOn_continuousAt_zero (rowRegular_continuousOn (Pc := Pc) (Vc := Vc) hP hV))

theorem rowField_sup_of_cover (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    {M : ℝ} {S : Set ℝ}
    (hm1 : realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) (-1) ≤ M)
    (hcover : ∀ x ∈ Ioo (-1 : ℝ) 0 ∪ Ioo 0 1,
      deriv (realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V)) x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x ≤ M := by
  set F := realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) with hF
  have hsplit : F = fun x => (19 / 48 : ℝ) * Real.log |x| +
      ((1 / 12 : ℝ) * Real.log (1 - x) + rowRegular Pc Vc P V x) := by
    funext x; rw [hF, rowField_split]; ring
  apply GlobalMaxReduction.le_on_two_components_of_stationary_cover (S := S)
  · intro x hx
    apply (rowField_continuousWithinAt hP hV ⟨hx.1, by linarith [hx.2]⟩ (ne_of_lt hx.2)
      (by linarith [hx.2])).mono
    intro y hy; exact ⟨hy.1, by linarith [hy.2]⟩
  · intro x hx
    apply (rowField_continuousWithinAt hP hV ⟨by linarith [hx.1], hx.2.le⟩ (ne_of_gt hx.1)
      (ne_of_lt hx.2)).mono
    intro y hy; exact ⟨by linarith [hy.1], hy.2.le⟩
  · exact hm1
  · rw [hsplit]
    have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|) (𝓝[<] 0) atBot := by
      simpa only [Real.log_abs] using
        (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48) Real.tendsto_log_nhdsLT_zero)
    exact atBot_add_finite hl ((rowField_zero_remainder (Pc := Pc) (Vc := Vc) hP hV).tendsto.mono_left nhdsWithin_le_nhds)
  · rw [hsplit]
    have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|) (𝓝[>] 0) atBot := by
      simpa only [Real.log_abs] using
        (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48) Real.tendsto_log_nhdsGT_zero)
    exact atBot_add_finite hl ((rowField_zero_remainder (Pc := Pc) (Vc := Vc) hP hV).tendsto.mono_left nhdsWithin_le_nhds)
  · have hsplit' : F = fun x => (1 / 12 : ℝ) * Real.log (1 - x) +
        ((19 / 48 : ℝ) * Real.log |x| + rowRegular Pc Vc P V x) := by
      funext x; rw [hF, rowField_split]; ring
    rw [hsplit']
    have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12) log_one_sub_tendsto
    have hc : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
      simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
    have hr := ((hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul (19 / 48 : ℝ)).add
      (continuousOn_tendsto_one_left (rowRegular_continuousOn (Pc := Pc) (Vc := Vc) hP hV))
    exact atBot_add_finite hl hr
  · exact hcover
  · exact hvalues

end Row

section Col

variable {Vc : List ℤ} {V : List TailQ}

theorem colField_continuousOn (hV : tailsInDisk V = true) :
    ContinuousOn (realEnergyColumnTrialField (trialSeq Vc V)) (Ioo (0 : ℝ) 1) := by
  intro x hx
  have hlog : ContinuousWithinAt Real.log (Ioo (0 : ℝ) 1) x :=
    (Real.continuousAt_log (ne_of_gt hx.1)).continuousWithinAt
  have hlog1 : ContinuousWithinAt (fun y : ℝ => Real.log (1 - y)) (Ioo 0 1) x :=
    ((continuousAt_const.sub continuousAt_id).log
      (sub_ne_zero.mpr (Ne.symm (ne_of_lt hx.2)))).continuousWithinAt
  have ht : ContinuousWithinAt (barrierTrialT (trialSeq Vc V)) (Ioo (0 : ℝ) 1) x := by
    apply (barrierTrialT_continuousOn _ (trialSeq_summable (cs := Vc) hV).1 x
      ⟨by linarith [hx.1], hx.2.le⟩).mono
    intro y hy
    exact ⟨by linarith [hy.1], hy.2.le⟩
  exact ((hlog.const_mul (7 / 48 : ℝ)).add (hlog1.const_mul (1 / 12 : ℝ))).add (ht.const_mul 2)

theorem colField_sup_of_cover (hV : tailsInDisk V = true) {M : ℝ} {S : Set ℝ}
    (hcover : ∀ x ∈ Ioo (0 : ℝ) 1,
      deriv (realEnergyColumnTrialField (trialSeq Vc V)) x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, realEnergyColumnTrialField (trialSeq Vc V) x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField (trialSeq Vc V) x ≤ M := by
  have hT := barrierTrialT_continuousOn (trialSeq Vc V) (trialSeq_summable (cs := Vc) hV).1
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover (S := S) (colField_continuousOn hV)
  · have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 7 / 48)
      Real.tendsto_log_nhdsGT_zero
    have hr : ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
        2 * barrierTrialT (trialSeq Vc V) x) 0 := by
      have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
        (continuousAt_const.sub continuousAt_id).log (by norm_num)
      exact (hlog.const_mul (1 / 12 : ℝ)).add ((continuousOn_continuousAt_zero hT).const_mul 2)
    have hh := atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
    convert hh using 1
    funext x
    unfold realEnergyColumnTrialField realEnergyColumnField
    ring
  · have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12) log_one_sub_tendsto
    have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
    have hr := (hlog.const_mul (7 / 48 : ℝ)).add
      ((continuousOn_tendsto_one_left hT).const_mul 2)
    have hh := atBot_add_finite hl hr
    convert hh using 1
    funext x
    unfold realEnergyColumnTrialField realEnergyColumnField
    ring
  · exact hcover
  · exact hvalues

end Col

/-! ### The certificates -/

/-- Brackets of the row field lie in `(-1, 0) ∪ (0, 1)`. -/
def rowBracketIn (p : Piece) : Bool :=
  !p.2.2 || (decide (p.1 < p.2.1) &&
    ((decide (-1 < p.1) && decide (p.2.1 < 0)) || (decide (0 < p.1) && decide (p.2.1 < 1))))

def colBracketIn (p : Piece) : Bool :=
  !p.2.2 || (decide (p.1 < p.2.1) && decide (0 < p.1) && decide (p.2.1 < 1))

/-- The full check for `sup X ≤ M`, given the derivative quotient `(A, Q)`. -/
def rowBracketOK (Pc Vc : List ℤ) (P V : List TailQ) (A Q : List ℚ) (M : ℚ) (p : Piece) :
    Bool :=
  rowBracketIn p && bracketOK A Q (rowApprox Pc Vc P V) M p

def colBracketOK (Vc : List ℤ) (V : List TailQ) (A Q : List ℚ) (M : ℚ) (p : Piece) : Bool :=
  colBracketIn p && bracketOK A Q (colApprox Vc V) M p

def rowEndOK (Pc Vc : List ℤ) (P V : List TailQ) (M : ℚ) : Bool :=
  match rowApprox Pc Vc P V (-1) with
  | some ve => decide (ve.1 + ve.2 ≤ M)
  | none => false

/-- The cheap part of the check for `sup X ≤ M`; the gaps and brackets are checked piece by
piece (`gapOK`, `rowBracketOK`). -/
def rowCheck (P V : List TailQ) (A : List ℚ) (ps : List Piece) : Bool :=
  tailsInDisk P && tailsInDisk V && coverFrom A [0] (-1) ps 1

def colCheck (V : List TailQ) (A : List ℚ) (ps : List Piece) : Bool :=
  tailsInDisk V && coverFrom A [] 0 ps 1

theorem rowCheck_spec {Pc Vc : List ℤ} {P V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (rowFracs Pc Vc P V) = (A, Q))
    (h : rowCheck P V A ps = true) (hgaps : ps.all (gapOK A) = true)
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
    rcases coverFrom_spec hcov hgaps (by push_cast; exact hx') hA with ⟨e, he, rfl⟩ | hp
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

theorem colCheck_spec {Vc : List ℤ} {V : List TailQ} {A Q : List ℚ} {M : ℚ}
    {ps : List Piece} (hAQ : fracSum (colFracs Vc V) = (A, Q))
    (h : colCheck V A ps = true) (hgaps : ps.all (gapOK A) = true)
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
    rcases coverFrom_spec hcov hgaps (by push_cast; exact hx) hA with ⟨e, he, rfl⟩ | hp
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

end CatalanMeasure.Cert

namespace CatalanMeasure.Cert

theorem all_and_left {l : List Piece} {f g : Piece → Bool}
    (h : l.all (fun p => f p && g p) = true) : l.all f = true := by
  simp only [List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun p hp => (h p hp).1

theorem all_and_right {l : List Piece} {f g : Piece → Bool}
    (h : l.all (fun p => f p && g p) = true) : l.all g = true := by
  simp only [List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun p hp => (h p hp).2

end CatalanMeasure.Cert
