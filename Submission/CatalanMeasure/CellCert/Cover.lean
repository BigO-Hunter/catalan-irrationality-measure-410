module
public import Submission.CatalanMeasure.CellCert.Cell
public import Submission.CatalanMeasure.Cert.FieldEval
@[expose] public section
/-! # Peeled cells and cover theorems

* A *peeled* cell handles a cell that touches a logarithmic singularity `w log |x - p|` of the field:
  `F = Freg + w log|x-p|` where `Freg` has the pole `p` removed from its pole list.  The cell check is
  `cellVal` for `Freg` with the cap lowered by `u ≥ sup_cell w log|x-p|` (from `Cert.sumLogs`).
* A *typed cell* `(cc, hh, t)` selects a `Spec` (enclosure `ev`, pole list, optional peel) by its type `t`.
* `coverFrom` checks that a list of typed cells covers `[L/2^40, ghi]`; `field_le_of_cells` is the
  pointwise sup theorem. -/
namespace CatalanMeasure.CellCert
open Set Nat CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000

/-! ### peel bound -/

/-- an upper bound for `w * log |x - p|` on `x ∈ [lo, hi]` (`x ≠ p`), via `sumLogs` -/
def peelBound (w p lo hi : ℚ) : Option ℚ :=
  let h := qmax (qabs' (lo - p)) (qabs' (hi - p))
  if 0 < h then
    (match sumLogs [⟨w, 0, h, 0⟩] with
    | some (v, e) => some (v + e)
    | none => none)
  else none

theorem logTerm_real_val (w h : ℚ) (hh : 0 < h) :
    LogTerm.val ⟨w, 0, h, 0⟩ = (w : ℝ) * Real.log (h : ℝ) := by
  unfold LogTerm.val
  have h1 : barrierComplex h 0 = (((h : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [barrierComplex]
  have h2 : barrierComplex w 0 = (((w : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp [barrierComplex]
  have hpos : (0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh.le
  rw [h1, h2, ← Complex.ofReal_log hpos, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem peelBound_spec {w p lo hi u : ℚ} (hw : 0 ≤ w) (h : peelBound w p lo hi = some u)
    (x : ℝ) (hx1 : (lo : ℝ) ≤ x) (hx2 : x ≤ (hi : ℝ)) (hxp : x ≠ (p : ℝ)) :
    (w : ℝ) * Real.log |x - p| ≤ (u : ℝ) := by
  unfold peelBound at h
  simp only at h
  split_ifs at h with hpos
  · split at h
    · rename_i v e hs
      simp only [Option.some.injEq] at h
      subst h
      have hspec := sumLogs_spec hs
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hspec
      rw [logTerm_real_val w _ hpos] at hspec
      have hh : (0 : ℝ) < ((qmax (qabs' (lo - p)) (qabs' (hi - p)) : ℚ) : ℝ) := by exact_mod_cast hpos
      have hxh : |x - p| ≤ ((qmax (qabs' (lo - p)) (qabs' (hi - p)) : ℚ) : ℝ) := by
        apply abs_le.mpr
        have ha : ((qabs' (lo - p) : ℚ) : ℝ) ≤ ((qmax (qabs' (lo - p)) (qabs' (hi - p)) : ℚ) : ℝ) := by
          unfold qmax; split_ifs with hc
          · exact_mod_cast hc
          · exact le_rfl
        have hb : ((qabs' (hi - p) : ℚ) : ℝ) ≤ ((qmax (qabs' (lo - p)) (qabs' (hi - p)) : ℚ) : ℝ) := by
          unfold qmax; split_ifs with hc
          · exact le_rfl
          · exact_mod_cast (not_le.mp hc).le
        rw [qabs'_cast] at ha hb
        push_cast at ha hb
        have a1 := le_abs_self ((hi : ℝ) - p)
        have a2 := neg_abs_le ((lo : ℝ) - p)
        constructor <;> linarith
      have habs : 0 < |x - p| := abs_pos.mpr (sub_ne_zero.mpr hxp)
      have hlog : Real.log |x - p| ≤ Real.log ((qmax (qabs' (lo - p)) (qabs' (hi - p)) : ℚ) : ℝ) :=
        Real.log_le_log habs hxh
      have hm := mul_le_mul_of_nonneg_left hlog (by exact_mod_cast hw : (0 : ℝ) ≤ w)
      have := (abs_le.mp hspec).2
      push_cast
      linarith
    · simp at h

/-! ### derivative of the peeled field -/

theorem ftZ_peel (Z : List ℤ) (pre post : List PoleR) (q : PoleR) (j : ℕ) (x : ℝ) :
    ftZ Z (pre ++ q :: post) j x = ftZ Z (pre ++ post) j x + qt q j x := by
  simp only [ftZ, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

theorem hasDerivAt_peel (Z : List ℤ) (pre post : List PoleR) (w p : ℚ) (F Freg : ℝ → ℝ) (y : ℝ)
    (hy : y ≠ (p : ℝ))
    (hsplit : ∀ z : ℝ, z ≠ (p : ℝ) → F z = Freg z + (w : ℝ) * Real.log |z - p|)
    (hF : HasDerivAt F (ftZ Z (pre ++ (⟨w, 0, p, 0⟩ : PoleR) :: post) 0 y) y) :
    HasDerivAt Freg (ftZ Z (pre ++ post) 0 y) y := by
  have hne : y - (p : ℝ) ≠ 0 := sub_ne_zero.mpr hy
  have hl : HasDerivAt (fun z : ℝ => Real.log (z - p)) (1 / (y - p)) y :=
    ((hasDerivAt_id y).sub_const (p : ℝ)).log hne
  have hl2 : HasDerivAt (fun z : ℝ => (w : ℝ) * Real.log |z - p|) ((w : ℝ) / (y - p)) y := by
    have := hl.const_mul (w : ℝ)
    simp only [Real.log_abs] at *
    simpa [div_eq_mul_inv] using this
  have h3 := hF.sub hl2
  have heq : (fun z => F z - (w : ℝ) * Real.log |z - p|) =ᶠ[nhds y] Freg := by
    filter_upwards [isOpen_ne.mem_nhds hy] with z hz
    rw [hsplit z hz]; ring
  refine (h3.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [ftZ_peel, qt_real]
  ring

/-! ### peeled cells -/

/-- `cellVal` for a field with an optional peeled logarithm `(w, p)` -/
def cellValP (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (poles : List PoleR) (m L : ℕ) (MGL : ℤ)
    (peel : Option (ℚ × ℚ)) (cap : ℚ) (cell : ℤ × ℤ) : Bool :=
  match peel with
  | none => cellVal ev D poles m L MGL none cap cell
  | some (w, p) =>
    match peelBound w p (((cell.1 - cell.2 : ℤ) : ℚ) / (TT : ℚ)) (((cell.1 + cell.2 : ℤ) : ℚ) / (TT : ℚ)) with
    | none => false
    | some u => cellVal ev D poles m L MGL (some p) (cap - u) cell

/-- what a cell type needs: the centre enclosure `ev` (for the regular part), the pole list of the
regular part, and the optional peeled logarithm -/
structure Spec where
  ev : ℚ → Option (ℚ × ℚ)
  poles : List PoleR
  peel : Option (ℚ × ℚ)

noncomputable def peelTerm : Option (ℚ × ℚ) → ℝ → ℝ
  | none, _ => 0
  | some (w, p), y => (w : ℝ) * Real.log |y - p|

/-- soundness hypotheses of a spec for the field `F`: a regular part `Freg` with an enclosure, continuity,
the derivative tower base `ftZ`, and `F = Freg + peeled log` -/
def Spec.Sound (S : Spec) (D : PolyData) (F : ℝ → ℝ) : Prop :=
  ∃ Freg : ℝ → ℝ,
    (∀ q v e, S.ev q = some (v, e) → |(q : ℝ)| ≤ 1 → (∀ p ∈ S.poles, ((q : ℝ) : ℂ) ≠ p.pc) →
      Freg q ≤ (v : ℝ) + e) ∧
    ContinuousOn Freg {y : ℝ | |y| ≤ 1 ∧ ∀ q ∈ S.poles, (y : ℂ) ≠ q.pc} ∧
    (∀ y ∈ Ioo (-1 : ℝ) 1, (∀ p : ℚ, S.peel.map Prod.snd = some p → y ≠ (p : ℝ)) →
      (∀ q ∈ S.poles, (y : ℂ) ≠ q.pc) → HasDerivAt Freg (ftZ D.Z S.poles 0 y) y) ∧
    (∀ y : ℝ, (∀ pr, S.peel = some pr → y ≠ (pr.2 : ℝ)) → F y = Freg y + peelTerm S.peel y) ∧
    (∀ pr, S.peel = some pr → 0 ≤ pr.1)

theorem cellValP_sound (F : ℝ → ℝ) (S : Spec) (D : PolyData) (hD : D.Ok) (m L : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ))
    (hS : S.Sound D F) (cap : ℚ) (cc hh : ℤ)
    (h : cellValP S.ev D S.poles m L MGL S.peel cap (cc, hh) = true) :
    ∀ x : ℝ, |x - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → (∀ pr, S.peel = some pr → x ≠ (pr.2 : ℝ)) →
      F x ≤ (cap : ℝ) := by
  intro x hx hxp
  obtain ⟨Freg, hev, hFc, hFd, hsplit, hw⟩ := hS
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  unfold cellValP at h
  rcases hpe : S.peel with _ | ⟨w, p⟩
  · rw [hpe] at h hFd hsplit
    simp only at h
    have := cellVal_sound Freg S.ev D hD S.poles m L MGL hMGL none cap hev hFc
      (by simpa using hFd) cc hh h x hx
    rw [hsplit x (by simp)]
    simpa [peelTerm] using this
  · rw [hpe] at h hFd hsplit hw hxp
    simp only at h
    generalize hpb : peelBound w p (((cc - hh : ℤ) : ℚ) / (TT : ℚ))
      (((cc + hh : ℤ) : ℚ) / (TT : ℚ)) = pb at h
    cases pb with
    | none => simp at h
    | some u =>
      have h1 := cellVal_sound Freg S.ev D hD S.poles m L MGL hMGL (some p) (cap - u) hev hFc
        (by simpa using hFd) cc hh h x hx
      have hw' : 0 ≤ w := hw (w, p) rfl
      have hxp' : x ≠ (p : ℝ) := hxp (w, p) rfl
      have e1 : ((((cc - hh : ℤ) : ℚ) / (TT : ℚ) : ℚ) : ℝ) = (cc : ℝ) / TT - (hh : ℝ) / TT := by
        push_cast; ring
      have e2 : ((((cc + hh : ℤ) : ℚ) / (TT : ℚ) : ℚ) : ℝ) = (cc : ℝ) / TT + (hh : ℝ) / TT := by
        push_cast; ring
      have hxa := abs_le.mp hx
      have hb := peelBound_spec hw' hpb x (by rw [e1]; linarith [hxa.1])
        (by rw [e2]; linarith [hxa.2]) hxp'
      rw [hsplit x hxp]
      simp only [peelTerm]
      push_cast at h1
      linarith

/-! ### typed cells and covers -/

/-- `(centre, half width, type)`, centre and half width in units of `2^-40` -/
abbrev TCell := ℤ × ℤ × ℕ

/-- the cells, in order, cover `[L/2^40, ghi]`: each starts at or before the covered frontier, and some
cell ends at or after `ghi` -/
def coverFrom (ghi : ℚ) : ℤ → List TCell → Bool
  | _, [] => false
  | L, c :: t => decide (c.1 - c.2.1 ≤ L) &&
      (decide (ghi * (TT : ℚ) ≤ ((c.1 + c.2.1 : ℤ) : ℚ)) || coverFrom ghi (c.1 + c.2.1) t)

theorem cover_spec (ghi : ℚ) : ∀ (cells : List TCell) (L : ℤ), coverFrom ghi L cells = true →
    ∀ x : ℝ, (L : ℝ) / TT ≤ x → x ≤ (ghi : ℝ) →
      ∃ c ∈ cells, |x - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT := by
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  intro cells
  induction cells with
  | nil => intro L h; simp [coverFrom] at h
  | cons c t ih =>
    intro L h x hLx hxg
    simp only [coverFrom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (c.1 : ℝ) - c.2.1 ≤ (L : ℝ) := by exact_mod_cast h1
    have hLx' : (L : ℝ) ≤ x * TT := by rwa [div_le_iff₀ hT] at hLx
    by_cases hc : x * TT ≤ (c.1 : ℝ) + c.2.1
    · refine ⟨c, List.mem_cons_self, ?_⟩
      have e : x - (c.1 : ℝ) / TT = (x * TT - c.1) / TT := by field_simp
      rw [e, abs_div, abs_of_pos hT, div_le_div_iff_of_pos_right hT, abs_le]
      constructor <;> linarith
    · push_neg at hc
      rcases h2 with h2 | h2
      · have h2' : (ghi : ℝ) * TT ≤ (c.1 : ℝ) + c.2.1 := by exact_mod_cast h2
        nlinarith
      · obtain ⟨d, hd, hd'⟩ := ih (c.1 + c.2.1) h2 x
          (by rw [div_le_iff₀ hT]; push_cast; linarith) hxg
        exact ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

theorem floor_le_of_ge (glo : ℚ) (x : ℝ) (hx : (glo : ℝ) ≤ x) :
    ((qfloor (glo * (TT : ℚ)) : ℤ) : ℝ) / TT ≤ x := by
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have h' : ((qfloor (glo * (TT : ℚ)) : ℤ) : ℝ) ≤ (glo : ℝ) * TT := by
    exact_mod_cast qfloor_le (glo * (TT : ℚ))
  rw [div_le_iff₀ hT]
  nlinarith

/-- the check of one typed cell -/
def cellT (S : ℕ → Spec) (D : PolyData) (m L : ℕ) (MGL : ℤ) (cap : ℚ) (c : TCell) : Bool :=
  cellValP (S c.2.2).ev D (S c.2.2).poles m L MGL (S c.2.2).peel cap (c.1, c.2.1)

/-- **Pointwise sup from a cover**: if every cell of a covering list passes `cellT`, then `F ≤ cap` at every
point of `[L/2^40, ghi]` that avoids the peeled singularities. -/
theorem field_le_of_cells (F : ℝ → ℝ) (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m L : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ)) (cap : ℚ)
    (cells : List TCell) (hsound : ∀ c ∈ cells, (S c.2.2).Sound D F)
    (L0 : ℤ) (ghi : ℚ) (hcov : coverFrom ghi L0 cells = true)
    (hcells : ∀ c ∈ cells, cellT S D m L MGL cap c = true)
    (x : ℝ) (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c ∈ cells, ∀ pr, (S c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    F x ≤ (cap : ℝ) := by
  obtain ⟨c, hc, hcx⟩ := cover_spec ghi cells L0 hcov x hL hx
  exact cellValP_sound F (S c.2.2) D hD m L MGL hMGL (hsound c hc) cap c.1 c.2.1 (hcells c hc) x hcx
    (hxp c hc)

end CatalanMeasure.CellCert
