module

public import Submission.CatalanMeasure.GenD.Cert.CellLoc
public import Submission.CatalanMeasure.GenD.Cert.PolyShift
public import Submission.CatalanMeasure.CellCert.CellSound

@[expose] public section


namespace CatalanMeasure.CellCert
open Set Nat CatalanMeasure.Cert
set_option maxRecDepth 100000

/-- `cellValP_sound` with a bound `MGL` that is only known on the cell (block-local bound). -/
theorem cellValP_soundL (F : ℝ → ℝ) (S : Spec) (D : PolyData) (hD : D.Ok) (m L : ℕ) (MGL : ℤ)
    (hS : S.Sound D F) (cap : ℚ) (cc hh : ℤ)
    (hMGL : ∀ y : ℝ, |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ))
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
    have := cellVal_soundL Freg S.ev D hD S.poles m L MGL none cap hev hFc
      (by simpa using hFd) cc hh hMGL h x hx
    rw [hsplit x (by simp)]
    simpa [peelTerm] using this
  · rw [hpe] at h hFd hsplit hw hxp
    simp only at h
    generalize hpb : peelBound w p (((cc - hh : ℤ) : ℚ) / (TT : ℚ))
      (((cc + hh : ℤ) : ℚ) / (TT : ℚ)) = pb at h
    cases pb with
    | none => simp at h
    | some u =>
      have h1 := cellVal_soundL Freg S.ev D hD S.poles m L MGL (some p) (cap - u) hev hFc
        (by simpa using hFd) cc hh hMGL h x hx
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

/-- a block of typed cells sharing one Taylor tower: centre `cB`, half width `HB`, cell order `L`
(`m + L` is the tower base), tower bound `BB` at level `m + LT` -/
structure Block where
  cB : ℤ
  HB : ℤ
  L : ℕ
  BB : ℤ
  cells : List TCell

/-- the Boolean check of a block: the block tower `PbV ≤ BB` (one `decide`), the guards, and `cellT` of every
cell with `MGL := BB` -/
def blockOK (S : ℕ → Spec) (D : PolyData) (m LT : ℕ) (MGL : ℤ) (cap : ℚ) (b : Block) : Bool :=
  decide (b.L ≤ LT) && decide (m + LT ≤ D.LV.length) && decide (0 ≤ b.HB) &&
    decide (-TT ≤ b.cB - b.HB) && decide (b.cB + b.HB ≤ TT) &&
    decide (PbV D.N b.cB b.HB (polyValsD D b.cB (m + LT)) (m + b.L) (LT - b.L) MGL ≤ b.BB) &&
    b.cells.all (fun c => decide (|c.1 - b.cB| + c.2.1 ≤ b.HB) && cellT S D m b.L b.BB cap c)

/-- the cells of a list of blocks, in order -/
def blocksCells (bs : List Block) : List TCell := bs.flatMap Block.cells

theorem blockOK_cell (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ) (MGL : ℤ) (cap : ℚ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ))
    (b : Block) (hb : blockOK S D m LT MGL cap b = true) (c : TCell) (hc : c ∈ b.cells) :
    cellT S D m b.L b.BB cap c = true ∧
    ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      (SC : ℝ) * |ptZ D.Z (m + b.L) y| ≤ (b.BB : ℝ) := by
  unfold blockOK at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨hL, hlv⟩, hH0⟩, hlow⟩, hhigh⟩, hPb⟩, hall⟩ := hb
  obtain ⟨hcell, hct⟩ := hall c hc
  refine ⟨hct, ?_⟩
  have hLT : m + b.L + (LT - b.L) = m + LT := by omega
  have hM : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + b.L + (LT - b.L)) y| ≤ (MGL : ℝ) := by
    rw [hLT]; exact hMGL
  have hPb' : PbV D.N b.cB b.HB (polyValsD D b.cB (m + b.L + (LT - b.L))) (m + b.L) (LT - b.L) MGL ≤ b.BB := by
    rw [hLT]; exact hPb
  have := block_sup D hD b.cB b.HB c.1 c.2.1 (m + b.L) (LT - b.L) MGL b.BB hM (by omega) hH0 hlow hhigh hcell hPb'
  exact this

/-- **Pointwise sup from a covering list of blocks** (the block analogue of `field_le_of_cells`). -/
theorem field_le_of_blocks (F : ℝ → ℝ) (S : ℕ → Spec) (D : PolyData) (hD : D.Ok) (m LT : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m + LT) y| ≤ (MGL : ℝ)) (cap : ℚ)
    (bs : List Block) (hsound : ∀ c ∈ blocksCells bs, (S c.2.2).Sound D F)
    (L0 : ℤ) (ghi : ℚ) (hcov : coverFrom ghi L0 (blocksCells bs) = true)
    (hbs : ∀ b ∈ bs, blockOK S D m LT MGL cap b = true)
    (x : ℝ) (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c ∈ blocksCells bs, ∀ pr, (S c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    F x ≤ (cap : ℝ) := by
  obtain ⟨c, hc, hcx⟩ := cover_spec ghi (blocksCells bs) L0 hcov x hL hx
  obtain ⟨b, hbmem, hcb⟩ := List.mem_flatMap.mp hc
  obtain ⟨hct, hloc⟩ := blockOK_cell S D hD m LT MGL cap hMGL b (hbs b hbmem) c hcb
  exact cellValP_soundL F (S c.2.2) D hD m b.L b.BB (hsound c hc) cap c.1 c.2.1 (hloc) hct x hcx (hxp c hc)

end CatalanMeasure.CellCert

#print axioms CatalanMeasure.CellCert.cellValP_soundL
#print axioms CatalanMeasure.CellCert.blockOK_cell
#print axioms CatalanMeasure.CellCert.field_le_of_blocks


namespace CatalanMeasure.CellCert
open Set Nat CatalanMeasure.Cert
set_option maxRecDepth 100000

/-! ### glue for the normalised tables (`PolyDataS`) and for peeled cells with a kernel-computed `peelBound` -/

theorem cellT_none_of_piecesS (S : ℕ → Spec) (D : PolyDataS) (m L : ℕ) (MGL : ℤ) (cap : ℚ)
    (cc hh : ℤ) (t : ℕ) (U : ℚ) (FH AA : List ℤ) (Mp : ℤ)
    (hpeel : (S t).peel = none)
    (hev : evLe (S t).ev ((cc : ℚ) / (TT : ℚ)) U = true)
    (hfh : fhL D.N (S t).poles cc (polyValsS D cc (m + L)) m = FH)
    (hA : AL D.N (polyValsS D cc (m + L)) m L = AA)
    (hMp : MpoleV (S t).poles m (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ)) = Mp)
    (hfin : cellFin D.toD (S t).poles m L MGL none cap (cc, hh) U FH AA Mp = true) :
    cellT S D.toD m L MGL cap (cc, hh, t) = true := by
  rw [← polyValsD_toD] at hfh hA
  exact cellT_none_of_pieces S D.toD m L MGL cap cc hh t U FH AA Mp hpeel hev hfh hA hMp hfin

theorem cellT_some_of_piecesS (S : ℕ → Spec) (D : PolyDataS) (m L : ℕ) (MGL : ℤ) (cap : ℚ)
    (cc hh : ℤ) (t : ℕ) (w p : ℚ) (U : ℚ) (FH AA : List ℤ) (Mp : ℤ)
    (hpeel : (S t).peel = some (w, p))
    (hso : (peelBound w p (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ))).isSome = true)
    (hev : evLe (S t).ev ((cc : ℚ) / (TT : ℚ)) U = true)
    (hfh : fhL D.N (S t).poles cc (polyValsS D cc (m + L)) m = FH)
    (hA : AL D.N (polyValsS D cc (m + L)) m L = AA)
    (hMp : MpoleV (S t).poles m (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ)) = Mp)
    (hfin : cellFin D.toD (S t).poles m L MGL (some p)
      (cap - ((peelBound w p (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ))).getD 0))
      (cc, hh) U FH AA Mp = true) :
    cellT S D.toD m L MGL cap (cc, hh, t) = true := by
  rw [← polyValsD_toD] at hfh hA
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hso
  have e : (peelBound w p (((cc - hh : ℤ) : ℚ) / (TT : ℚ)) (((cc + hh : ℤ) : ℚ) / (TT : ℚ))).getD 0 = u := by
    rw [hu]; rfl
  rw [e] at hfin
  exact cellT_some_of_pieces S D.toD m L MGL cap cc hh t w p u U FH AA Mp hpeel hu hev hfh hA hMp hfin

/-- assembling `blockOK` from the block theorem (stated with `polyValsS`), the guards and the cells -/
theorem blockOK_ofS (S : ℕ → Spec) (D : PolyDataS) (m LT : ℕ) (MGL : ℤ) (cap : ℚ) (b : Block)
    (hL : b.L ≤ LT) (hlv : m + LT ≤ D.LV.length) (hH : 0 ≤ b.HB) (hlow : -TT ≤ b.cB - b.HB)
    (hhigh : b.cB + b.HB ≤ TT)
    (hPb : decide (PbV D.N b.cB b.HB (polyValsS D b.cB (m + LT)) (m + b.L) (LT - b.L) MGL ≤ b.BB) = true)
    (hcells : ∀ c ∈ b.cells, |c.1 - b.cB| + c.2.1 ≤ b.HB ∧ cellT S D.toD m b.L b.BB cap c = true) :
    blockOK S D.toD m LT MGL cap b = true := by
  unfold blockOK
  rw [polyValsD_toD]
  simp only [PolyDataS.toD_len, PolyDataS.toD_N] 
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hL, hlv⟩, hH⟩, hlow⟩, hhigh⟩, decide_eq_true_eq.mpr (of_decide_eq_true hPb)⟩, ?_⟩
  intro c hc
  exact hcells c hc
  
end CatalanMeasure.CellCert

#print axioms CatalanMeasure.CellCert.cellT_none_of_piecesS
#print axioms CatalanMeasure.CellCert.cellT_some_of_piecesS
#print axioms CatalanMeasure.CellCert.blockOK_ofS
