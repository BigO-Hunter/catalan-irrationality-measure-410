module

public import Submission.CatalanMeasure.CellCert.Cover
public import Submission.CatalanMeasure.CellCert.EvalS
public import Submission.CatalanMeasure.CellCert.FieldsSLink

@[expose] public section

/-!
# Cell specs of the 728 fields and their soundness (`Spec.Sound`)

`rowSpecS`, `colSpecS`, `resSpecS` are the cell-type tables (type `0`: no peel, type `1`: the
`α log|x|` / `b log s` term peeled, type `2`: the `β log(1-x)` / `q log(1-s)` term peeled) in the
form expected by `Cover.field_le_of_cells`.  `*_sound` prove `Spec.Sound` for the fields
`rowFieldS`, `colFieldS`, `resFieldS`; the only hypotheses are the tail conditions (`tailsInDisk`,
tails not at the origin), nonnegative log weights, and the polynomial identity for `D.Z`.
-/

open OAI.InternalCatalan Polynomial Set

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert
noncomputable section

def flag0 (t : ℕ) : Bool := decide (t = 1)
def flag1 (t : ℕ) : Bool := decide (t = 2)

theorem pc_zero (a : ℚ) : (((0 : ℝ)) : ℂ) = PoleR.pc ⟨a, 0, 0, 0⟩ := by
  apply Complex.ext <;> simp [PoleR.pc]

theorem pc_one (a : ℚ) : (((1 : ℝ)) : ℂ) = PoleR.pc ⟨a, 0, 1, 0⟩ := by
  apply Complex.ext <;> simp [PoleR.pc]

/-! ### row -/

def rowPeel (R : RowWeights) : ℕ → Option (ℚ × ℚ)
  | 1 => some (R.alpha, 0)
  | 2 => some (R.beta, 1)
  | _ => none

theorem rowPeel_other (R : RowWeights) {t : ℕ} (h1 : t ≠ 1) (h2 : t ≠ 2) : rowPeel R t = none := by
  unfold rowPeel
  split <;> simp_all

theorem flag_other {t : ℕ} (h1 : t ≠ 1) (h2 : t ≠ 2) : flag0 t = false ∧ flag1 t = false := by
  simp [flag0, flag1, h1, h2]

def rowSpecS (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (t : ℕ) : Spec where
  ev := rowApproxS R Pc Vc P V (flag0 t) (flag1 t)
  poles := rowPolesP R P V (flag0 t) (flag1 t)
  peel := rowPeel R t

theorem rowSpecS_sound (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (D : PolyData) (hZ : ∀ x : ℝ, -4 * finUR Pc x - finPR Vc x = ptZ D.Z 0 x)
    (hα : 0 ≤ R.alpha) (hβ : 0 ≤ R.beta) (t : ℕ) :
    (rowSpecS R Pc Vc P V t).Sound D (rowFieldS R Pc Vc P V) := by
  refine ⟨rowFieldSP R Pc Vc P V (flag0 t) (flag1 t), ?_, ?_, ?_, ?_, ?_⟩
  · intro q v e hq hq1 _
    exact rowApproxS_le R hP hV (flag0 t) (flag1 t) hq hq1
  · apply rowFieldSP_continuousOn R hP hV (flag0 t) (flag1 t)
    · intro y hy; exact abs_le.mp hy.1
    · by_cases hf : flag0 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨R.alpha, 0, 0, 0⟩ (by simp [rowSpecS, rowPolesP, hf])
        exact this (pc_zero R.alpha)
    · by_cases hf : flag1 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨R.beta, 0, 1, 0⟩ (by simp [rowSpecS, rowPolesP, hf])
        exact this (pc_one R.beta)
  · intro y hy _ hpoles
    apply rowFieldSP_hasDerivAt R hP hV hPz hVz D.Z hZ (flag0 t) (flag1 t) hy
    by_cases hf : flag0 t = true
    · exact Or.inl hf
    · right
      intro h0
      have := hpoles ⟨R.alpha, 0, 0, 0⟩ (by simp [rowSpecS, rowPolesP, hf])
      exact this (by rw [h0]; exact pc_zero R.alpha)
  · intro y hy
    unfold rowFieldS rowFieldSP rowFieldG rowFieldGP
    have hlog1 : Real.log |y - 1| = Real.log (1 - y) := by
      rw [abs_sub_comm, Real.log_abs]
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      have hy0 : y ≠ 0 := by
        have := hy _ rfl
        simpa [rowSpecS, rowPeel] using this
      simp [flag0, flag1, rowSpecS, rowPeel, peelTerm]
      ring
    · subst h
      simp [flag0, flag1, rowSpecS, rowPeel, peelTerm, hlog1]
      ring
    · obtain ⟨hf0, hf1⟩ := flag_other h.1 h.2
      simp [rowSpecS, rowPeel_other R h.1 h.2, hf0, hf1, peelTerm]
  · intro pr hpr
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      simp [rowSpecS, rowPeel] at hpr
      subst hpr
      exact hα
    · subst h
      simp [rowSpecS, rowPeel] at hpr
      subst hpr
      exact hβ
    · simp [rowSpecS, rowPeel_other R h.1 h.2] at hpr

/-! ### column -/

def colPeel (C : ColumnWeights) : ℕ → Option (ℚ × ℚ)
  | 1 => some (C.b, 0)
  | 2 => some (C.q, 1)
  | _ => none

theorem colPeel_other (C : ColumnWeights) {t : ℕ} (h1 : t ≠ 1) (h2 : t ≠ 2) :
    colPeel C t = none := by
  unfold colPeel
  split <;> simp_all

def colSpecS (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (t : ℕ) : Spec where
  ev := colApproxS C Vc V (flag0 t) (flag1 t)
  poles := colPolesP C V (flag0 t) (flag1 t)
  peel := colPeel C t

theorem colSpecS_sound (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (hVz : ∀ t ∈ V, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (D : PolyData) (hZ : ∀ x : ℝ, 2 * finUR Vc x = ptZ D.Z 0 x)
    (hb : 0 ≤ C.b) (hq : 0 ≤ C.q) (t : ℕ) :
    (colSpecS C Vc V t).Sound D (colFieldS C Vc V) := by
  refine ⟨colFieldSP C Vc V (flag0 t) (flag1 t), ?_, ?_, ?_, ?_, ?_⟩
  · intro q v e hq' hq1 _
    exact colApproxS_le C hV (flag0 t) (flag1 t) hq' hq1
  · apply colFieldSP_continuousOn C hV (flag0 t) (flag1 t)
    · intro y hy; exact abs_le.mp hy.1
    · by_cases hf : flag0 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨C.b, 0, 0, 0⟩ (by simp [colSpecS, colPolesP, hf])
        exact this (pc_zero C.b)
    · by_cases hf : flag1 t = true
      · exact Or.inl hf
      · right
        intro hmem
        have := hmem.2 ⟨C.q, 0, 1, 0⟩ (by simp [colSpecS, colPolesP, hf])
        exact this (pc_one C.q)
  · intro y hy _ hpoles
    apply colFieldSP_hasDerivAt C hV hVz D.Z hZ (flag0 t) (flag1 t) hy
    by_cases hf : flag0 t = true
    · exact Or.inl hf
    · right
      intro h0
      have := hpoles ⟨C.b, 0, 0, 0⟩ (by simp [colSpecS, colPolesP, hf])
      exact this (by rw [h0]; exact pc_zero C.b)
  · intro y hy
    unfold colFieldS colFieldSP colFieldG colFieldGP
    have hlog1 : Real.log |y - 1| = Real.log (1 - y) := by
      rw [abs_sub_comm, Real.log_abs]
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      simp [flag0, flag1, colSpecS, colPeel, peelTerm, Real.log_abs]
      ring
    · subst h
      simp [flag0, flag1, colSpecS, colPeel, peelTerm, hlog1]
      ring
    · obtain ⟨hf0, hf1⟩ := flag_other h.1 h.2
      simp [colSpecS, colPeel_other C h.1 h.2, hf0, hf1, peelTerm]
  · intro pr hpr
    rcases (by omega : t = 1 ∨ t = 2 ∨ (t ≠ 1 ∧ t ≠ 2)) with h | h | h
    · subst h
      simp [colSpecS, colPeel] at hpr
      subst hpr
      exact hb
    · subst h
      simp [colSpecS, colPeel] at hpr
      subst hpr
      exact hq
    · simp [colSpecS, colPeel_other C h.1 h.2] at hpr

/-! ### residual -/

def resSpecS (Pc : List ℤ) (P : List TailQ) (_t : ℕ) : Spec where
  ev := resApproxS Pc P
  poles := resPoles P
  peel := none

theorem resSpecS_sound {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true)
    (hPz : ∀ t ∈ P, t.zr ≠ 0 ∨ t.zi ≠ 0) (D : PolyData)
    (hZ : ∀ x : ℝ, -2 * finUR Pc x = ptZ D.Z 0 x) (t : ℕ) :
    (resSpecS Pc P t).Sound D (resFieldS Pc P) := by
  refine ⟨resFieldS Pc P, ?_, ?_, ?_, ?_, ?_⟩
  · intro q v e hq hq1 _
    exact resApproxS_le hP hq hq1
  · exact (resFieldS_continuousOn hP).mono (fun y hy => abs_le.mp hy.1)
  · intro y hy _ _
    exact resFieldS_hasDerivAt hP hPz D.Z hZ hy
  · intro y _
    simp [resSpecS, peelTerm]
  · intro pr hpr
    simp [resSpecS] at hpr

end
end CatalanMeasure.CellCert
