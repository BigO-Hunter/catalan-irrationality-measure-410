module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger10.CWin

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger9 + Theorem C` (lane G6e)

`cWins` are the Theorem C windows: cell 1 (`S = 22`) on `(58/17, 59/17]` and cell 2 (`S = 21`) on
`(29/8, 11/3]`.  They sit between `wWins` (ending at `x = 16/5`) and `wins9` (starting at `x = 4.06`).
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger10
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535.Ledger6 CatalanMeasure.GenD.Uniform.Bank535.Ledger7
  CatalanMeasure.GenD.Uniform.Bank535.Ledger8 CatalanMeasure.GenD.Uniform.Bank535.Ledger9
open CatalanMeasure.GenD.Uniform.W.TheoremC
noncomputable section

def cWins : List KapWindow :=
  [cw (58 / 17 : ℝ) (24 / 7 : ℝ) (-58 : ℝ) (17 : ℝ),
   cw (24 / 7 : ℝ) (69 / 20 : ℝ) (-10 : ℝ) (3 : ℝ),
   cw (69 / 20 : ℝ) (59 / 17 : ℝ) (59 : ℝ) (-17 : ℝ),
   cw (29 / 8 : ℝ) (69 / 19 : ℝ) (-58 : ℝ) (16 : ℝ),
   cw (69 / 19 : ℝ) (11 / 3 : ℝ) (11 : ℝ) (-3 : ℝ)]

theorem cWins_cert : ∀ w ∈ cWins, WinCert (cLB design adm) w := by
  intro w hw
  simp only [cWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  have le1 : ∀ N p, (cCellLB cell1 design adm).kap N p ≤ (cLB design adm).kap N p :=
    fun N p => le_max_left _ _
  have le2 : ∀ N p, (cCellLB cell2 design adm).kap N p ≤ (cLB design adm).kap N p :=
    fun N p => le_max_right _ _
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact (wincert_cw (cCellLB cell1 design adm) (na := 58) (da := 17) (nb := 24) (db := 7)
      (A := -58) (B := 17) (d := 1) (N0 := cell1.modulus) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => c1a_cell hp h1 h2 hN).mono le1
  · exact (wincert_cw (cCellLB cell1 design adm) (na := 24) (da := 7) (nb := 69) (db := 20)
      (A := -10) (B := 3) (d := 1) (N0 := cell1.modulus) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => c1b_cell hp h1 h2 hN).mono le1
  · exact (wincert_cw (cCellLB cell1 design adm) (na := 69) (da := 20) (nb := 59) (db := 17)
      (A := 59) (B := -17) (d := 1) (N0 := cell1.modulus) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => c1c_cell hp h1 h2 hN).mono le1
  · exact (wincert_cw (cCellLB cell2 design adm) (na := 29) (da := 8) (nb := 69) (db := 19)
      (A := -58) (B := 16) (d := 1) (N0 := cell2.modulus) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => c2a_cell hp h1 h2 hN).mono le2
  · exact (wincert_cw (cCellLB cell2 design adm) (na := 69) (da := 19) (nb := 11) (db := 3)
      (A := 11) (B := -3) (d := 1) (N0 := cell2.modulus) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => c2b_cell hp h1 h2 hN).mono le2

def fams12 : List (NullityLB design) := fams11 ++ [cLB design adm]

def wins12 : List KapWindow := lWins ++ wWins ++ cWins ++ wins9

def cGain : ℝ := (cWins.map (KapWindow.area 58)).sum

def gain12 : ℝ := gain11 + cGain

theorem cWins_pos : ∀ w ∈ cWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [cWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem wins12_pos : ∀ w ∈ wins12, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [wins12, List.mem_append] at hw
  rcases hw with ((h | h) | h) | h
  · exact wins11_pos w (by simp [wins11, h])
  · exact wins11_pos w (by simp [wins11, h])
  · exact cWins_pos w h
  · exact wins9_pos w h

theorem wins12_rec : ∀ w ∈ wins12, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  simp only [wins12, List.mem_append] at hw
  rcases hw with ((h | h) | h) | h
  · exact wins11_rec w (by simp [wins11, h])
  · exact wins11_rec w (by simp [wins11, h])
  · right
    simp only [cWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins9_rec w h

theorem cWins_ord : cWins.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [cWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem wins12_ord : wins12.Pairwise (fun s t => s.b ≤ t.a) := by
  unfold wins12
  rw [List.pairwise_append]
  refine ⟨?_, wins9_ord, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨?_, cWins_ord, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨lWins_ord, wWins_ord, ?_⟩
      intro s hs t ht
      simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases hs with rfl | rfl | rfl | rfl <;>
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
    · intro s hs t ht
      simp only [cWins, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases List.mem_append.mp hs with h | h
      · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;>
          rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
      · simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · intro s hs t ht
    have h4 := wins9_a_ge t ht
    rcases List.mem_append.mp hs with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] at h4 ⊢ <;> linarith
      · simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [cw] at h4 ⊢ <;> linarith
    · simp only [cWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [cw] at h4 ⊢ <;> linarith

theorem wins12_area : (wins12.map (KapWindow.area 58)).sum = gain12 := by
  unfold wins12 gain12 cGain
  have h11 : (wins11.map (KapWindow.area 58)).sum = gain11 := wins11_area
  unfold wins11 at h11
  simp only [List.map_append, List.sum_append] at h11 ⊢
  linarith

theorem wins12_cert : ∀ w ∈ wins12, ∃ lb ∈ fams12, WinCert lb w := by
  intro w hw
  simp only [wins12, List.mem_append] at hw
  rcases hw with ((h | h) | h) | h
  · obtain ⟨lb, hl, hc⟩ := wins11_cert w (by simp [wins11, h])
    exact ⟨lb, List.mem_append_left _ hl, hc⟩
  · obtain ⟨lb, hl, hc⟩ := wins11_cert w (by simp [wins11, h])
    exact ⟨lb, List.mem_append_left _ hl, hc⟩
  · exact ⟨cLB design adm, by simp [fams12], cWins_cert w h⟩
  · obtain ⟨lb, hl, hc⟩ := wins11_cert w (by simp [wins11, h])
    exact ⟨lb, List.mem_append_left _ hl, hc⟩

/-- **Denominator growth for `fams12` on `wins12`.** -/
theorem partial_growth12 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams12) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain12 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams12 wins12 gain12 wins12_area wins12_pos wins12_ord wins12_rec
    wins12_cert hε

theorem gain11_ge_sharp : (21871 / 1000 : ℝ) ≤ gain11 := by
  unfold gain11 wGain gain10 lGain gain9 gain8 gain7 gain6 gain5
  simp only [lWins, wWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area]
  norm_num

theorem gain12_ge : (218855 / 10000 : ℝ) ≤ gain12 := by
  have h := gain11_ge_sharp
  unfold gain12 cGain
  simp only [cWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area]
  norm_num
  linarith

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger10
