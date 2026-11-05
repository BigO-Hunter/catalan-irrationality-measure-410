module

public import Submission.CatalanMeasure.GenD.Cert.WLog
public import Submission.CatalanMeasure.GenD.Cert.ResW
public import Submission.CatalanMeasure.CellCert.CellSound

@[expose] public section

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert OAI.InternalCatalan Polynomial Set
noncomputable section

/-! # Weight-scaled log evaluator wired into the cell specs
`rowApproxW`, `colApproxW`, `resApproxW` are `*ApproxS` with `sumLogsR` replaced by `WLog.sumLogsW`;
`*SpecW` / `*SpecW_sound` are the copies of `*SpecS` / `*SpecS_sound` over them. -/

/-! ### enclosures -/

def rowApproxW (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (f0 f1 : Bool) (c : ℚ) :
    Option (ℚ × ℚ) :=
  (CatalanMeasure.WLog.sumLogsWI (rowTermsS R P V f0 f1 c)).map (fun ve =>
    (ve.1 - 4 * (finTEnc Pc c).1 - (finSEnc Vc c).1,
     ve.2 + 4 * (finTEnc Pc c).2 + (finSEnc Vc c).2))

def colApproxW (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (f0 f1 : Bool) (c : ℚ) :
    Option (ℚ × ℚ) :=
  (CatalanMeasure.WLog.sumLogsWI (colTermsS C V f0 f1 c)).map (fun ve =>
    (ve.1 + 2 * (finTEnc Vc c).1, ve.2 + 2 * (finTEnc Vc c).2))

def resApproxW (ρ : ℚ) (Pc : List ℤ) (P : List TailQ) (c : ℚ) : Option (ℚ × ℚ) :=
  (CatalanMeasure.WLog.sumLogsWI (resTermsW ρ P c)).map (fun ve =>
    (ve.1 - 2 * (finTEnc Pc c).1, ve.2 + 2 * (finTEnc Pc c).2))

theorem rowApproxW_spec (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : rowApproxW R Pc Vc P V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    |rowFieldSP R Pc Vc P V f0 f1 c - (v : ℝ)| ≤ (e : ℝ) := by
  unfold rowApproxW at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have hs := CatalanMeasure.WLog.sumLogsWI_spec h1
  have ht := finTEnc_spec Pc c
  have hv := finSEnc_spec Vc c
  rw [rowFieldSP_eq R hP hV f0 f1 hc]
  unfold finTR finSR
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
  rw [abs_le] at hs ht hv ⊢
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, hv.1, hv.2]

theorem colApproxW_spec (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : colApproxW C Vc V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    |colFieldSP C Vc V f0 f1 c - (v : ℝ)| ≤ (e : ℝ) := by
  unfold colApproxW at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have hs := CatalanMeasure.WLog.sumLogsWI_spec h1
  have ht := finTEnc_spec Vc c
  rw [colFieldSP_eq C hV f0 f1 hc]
  unfold finTR
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
  rw [abs_le] at hs ht ⊢
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

theorem resApproxW_spec (ρ : ℚ) {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) {c v e : ℚ}
    (h : resApproxW ρ Pc P c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    |resFieldW (ρ : ℝ) (trialSeqS Pc P) c - (v : ℝ)| ≤ (e : ℝ) := by
  unfold resApproxW at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v', e'⟩, h1, rfl, rfl⟩ := h
  have hs := CatalanMeasure.WLog.sumLogsWI_spec h1
  have ht := finTEnc_spec Pc c
  rw [resFieldW_eq ρ hP hc]
  unfold finTR
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
  rw [abs_le] at hs ht ⊢
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

/-- upper-bound forms used by the cell covers -/
theorem rowApproxW_le (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : rowApproxW R Pc Vc P V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    rowFieldSP R Pc Vc P V f0 f1 c ≤ (v : ℝ) + (e : ℝ) := by
  have := (abs_le.mp (rowApproxW_spec R hP hV f0 f1 h hc)).2
  linarith

theorem colApproxW_le (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (f0 f1 : Bool) {c v e : ℚ}
    (h : colApproxW C Vc V f0 f1 c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    colFieldSP C Vc V f0 f1 c ≤ (v : ℝ) + (e : ℝ) := by
  have := (abs_le.mp (colApproxW_spec C hV f0 f1 h hc)).2
  linarith

theorem resApproxW_le (ρ : ℚ) {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) {c v e : ℚ}
    (h : resApproxW ρ Pc P c = some (v, e)) (hc : |(c : ℝ)| ≤ 1) :
    resFieldW (ρ : ℝ) (trialSeqS Pc P) c ≤ (v : ℝ) + (e : ℝ) := by
  have := (abs_le.mp (resApproxW_spec ρ hP h hc)).2
  linarith


def rowSpecW (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (t : ℕ) : Spec where
  ev := rowApproxW R Pc Vc P V (flag0 t) (flag1 t)
  poles := rowPolesP R P V (flag0 t) (flag1 t)
  peel := rowPeel R t

theorem rowSpecW_sound (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (D : PolyData) (hZ : ∀ x : ℝ, -4 * finUR Pc x - finPR Vc x = ptZ D.Z 0 x)
    (hα : 0 ≤ R.alpha) (hβ : 0 ≤ R.beta) (t : ℕ) :
    (rowSpecW R Pc Vc P V t).Sound D (rowFieldS R Pc Vc P V) := by
  refine ⟨rowFieldSP R Pc Vc P V (flag0 t) (flag1 t), ?_, ?_, ?_, ?_, ?_⟩
  · intro q v e hq hq1 _
    exact rowApproxW_le R hP hV (flag0 t) (flag1 t) hq hq1
  · apply rowFieldSP_continuousOn R hP hV (flag0 t) (flag1 t)
    · intro y hy; exact abs_le.mp hy.1
    · by_cases hf : flag0 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨R.alpha, 0, 0, 0⟩ (by simp [rowSpecW, rowPolesP, hf])
        exact this (pc_zero R.alpha)
    · by_cases hf : flag1 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨R.beta, 0, 1, 0⟩ (by simp [rowSpecW, rowPolesP, hf])
        exact this (pc_one R.beta)
  · intro y hy _ hpoles
    apply rowFieldSP_hasDerivAt R hP hV hPz hVz D.Z hZ (flag0 t) (flag1 t) hy
    by_cases hf : flag0 t = true
    · exact Or.inl hf
    · right
      intro h0
      have := hpoles ⟨R.alpha, 0, 0, 0⟩ (by simp [rowSpecW, rowPolesP, hf])
      exact this (by rw [h0]; exact pc_zero R.alpha)
  · intro y hy
    unfold rowFieldS rowFieldSP rowFieldG rowFieldGP
    have hlog1 : Real.log |y - 1| = Real.log (1 - y) := by
      rw [abs_sub_comm, Real.log_abs]
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      have hy0 : y ≠ 0 := by
        have := hy _ rfl
        simpa [rowSpecW, rowPeel] using this
      simp [flag0, flag1, rowSpecW, rowPeel, peelTerm]
      ring
    · subst h
      simp [flag0, flag1, rowSpecW, rowPeel, peelTerm, hlog1]
      ring
    · obtain ⟨hf0, hf1⟩ := flag_other h.1 h.2
      simp [rowSpecW, rowPeel_other R h.1 h.2, hf0, hf1, peelTerm]
  · intro pr hpr
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      simp [rowSpecW, rowPeel] at hpr
      subst hpr
      exact hα
    · subst h
      simp [rowSpecW, rowPeel] at hpr
      subst hpr
      exact hβ
    · simp [rowSpecW, rowPeel_other R h.1 h.2] at hpr

def colSpecW (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (t : ℕ) : Spec where
  ev := colApproxW C Vc V (flag0 t) (flag1 t)
  poles := colPolesP C V (flag0 t) (flag1 t)
  peel := colPeel C t

theorem colSpecW_sound (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (D : PolyData) (hZ : ∀ x : ℝ, 2 * finUR Vc x = ptZ D.Z 0 x)
    (hb : 0 ≤ C.b) (hq : 0 ≤ C.q) (t : ℕ) :
    (colSpecW C Vc V t).Sound D (colFieldS C Vc V) := by
  refine ⟨colFieldSP C Vc V (flag0 t) (flag1 t), ?_, ?_, ?_, ?_, ?_⟩
  · intro q v e hq' hq1 _
    exact colApproxW_le C hV (flag0 t) (flag1 t) hq' hq1
  · apply colFieldSP_continuousOn C hV (flag0 t) (flag1 t)
    · intro y hy; exact abs_le.mp hy.1
    · by_cases hf : flag0 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨C.b, 0, 0, 0⟩ (by simp [colSpecW, colPolesP, hf])
        exact this (pc_zero C.b)
    · by_cases hf : flag1 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨C.q, 0, 1, 0⟩ (by simp [colSpecW, colPolesP, hf])
        exact this (pc_one C.q)
  · intro y hy _ hpoles
    apply colFieldSP_hasDerivAt C hV hVz D.Z hZ (flag0 t) (flag1 t) hy
    by_cases hf : flag0 t = true
    · exact Or.inl hf
    · right
      intro h0
      have := hpoles ⟨C.b, 0, 0, 0⟩ (by simp [colSpecW, colPolesP, hf])
      exact this (by rw [h0]; exact pc_zero C.b)
  · intro y hy
    unfold colFieldS colFieldSP colFieldG colFieldGP
    have hlog1 : Real.log |y - 1| = Real.log (1 - y) := by
      rw [abs_sub_comm, Real.log_abs]
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      simp [flag0, flag1, colSpecW, colPeel, peelTerm, Real.log_abs]
      ring
    · subst h
      simp [flag0, flag1, colSpecW, colPeel, peelTerm, hlog1]
      ring
    · obtain ⟨hf0, hf1⟩ := flag_other h.1 h.2
      simp [colSpecW, colPeel_other C h.1 h.2, hf0, hf1, peelTerm]
  · intro pr hpr
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      simp [colSpecW, colPeel] at hpr
      subst hpr
      exact hb
    · subst h
      simp [colSpecW, colPeel] at hpr
      subst hpr
      exact hq
    · simp [colSpecW, colPeel_other C h.1 h.2] at hpr

def resSpecW (ρ : ℚ) (Pc : List ℤ) (P : List TailQ) (_t : ℕ) : Spec where
  ev := resApproxW ρ Pc P
  poles := resPolesW ρ P
  peel := none

theorem resSpecW_sound (ρ : ℚ) {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) (D : PolyData)
    (hZ : ∀ x : ℝ, -2 * finUR Pc x = ptZ D.Z 0 x) (t : ℕ) :
    (resSpecW ρ Pc P t).Sound D (resFieldW (ρ : ℝ) (trialSeqS Pc P)) := by
  refine ⟨resFieldW (ρ : ℝ) (trialSeqS Pc P), ?_, ?_, ?_, ?_, ?_⟩
  · intro q v e hq hq1 _
    exact resApproxW_le ρ hP hq hq1
  · exact (resFieldW_continuousOn (ρ : ℝ) (trialSeqS_summable hP).1).mono (fun y hy => abs_le.mp hy.1)
  · intro y hy _ _
    exact resFieldW_hasDerivAt ρ hP hPz D.Z hZ hy
  · intro y _
    simp [resSpecW, peelTerm]
  · intro pr hpr
    simp [resSpecW] at hpr


end
end CatalanMeasure.CellCert
