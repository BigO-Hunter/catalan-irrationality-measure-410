module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger10.Merge12
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger10.CWinP

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger10 + Theorem C'` (lane G6e)

`cpWins` are the Theorem C' windows on `(16/7, 5/2]` (cells `S = 33, 32, 31`).  They sit before `lWins`
(starting at `59/21`).  The extended ledger `wins13` has `gain13 >= 21.894`.
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

def cpWins : List KapWindow :=
  [cw (16 / 7 : ℝ) (23 / 10 : ℝ) (-16 : ℝ) (7 : ℝ),
   cw (23 / 10 : ℝ) (53 / 23 : ℝ) (53 : ℝ) (-23 : ℝ),
   cw (64 / 27 : ℝ) (69 / 29 : ℝ) (-64 : ℝ) (27 : ℝ),
   cw (69 / 29 : ℝ) (12 / 5 : ℝ) (5 : ℝ) (-2 : ℝ),
   cw (12 / 5 : ℝ) (53 / 22 : ℝ) (53 : ℝ) (-22 : ℝ),
   cw (32 / 13 : ℝ) (69 / 28 : ℝ) (-64 : ℝ) (26 : ℝ),
   cw (69 / 28 : ℝ) (5 / 2 : ℝ) (5 : ℝ) (-2 : ℝ)]

theorem cpWins_cert : ∀ w ∈ cpWins, WinCert (cPrimeLB design adm) w := by
  intro w hw
  simp only [cpWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  have le1 : ∀ N p, (cCellLBP cellp1 design adm).kap N p ≤ (cPrimeLB design adm).kap N p :=
    fun N p => le_max_left _ _
  have le2 : ∀ N p, (cCellLBP cellp2 design adm).kap N p ≤ (cPrimeLB design adm).kap N p :=
    fun N p => (le_max_left _ _).trans (le_max_right _ _)
  have le3 : ∀ N p, (cCellLBP cellp3 design adm).kap N p ≤ (cPrimeLB design adm).kap N p :=
    fun N p => (le_max_right _ _).trans (le_max_right _ _)
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (wincert_cw (cCellLBP cellp3 design adm) (na := 16) (da := 7) (nb := 23) (db := 10)
      (A := -16) (B := 7) (d := 1) (N0 := cellp3.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p3a_cell hp h1 h2 hN).mono le3
  · exact (wincert_cw (cCellLBP cellp3 design adm) (na := 23) (da := 10) (nb := 53) (db := 23)
      (A := 53) (B := -23) (d := 1) (N0 := cellp3.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p3b_cell hp h1 h2 hN).mono le3
  · exact (wincert_cw (cCellLBP cellp2 design adm) (na := 64) (da := 27) (nb := 69) (db := 29)
      (A := -64) (B := 27) (d := 1) (N0 := cellp2.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p2a_cell hp h1 h2 hN).mono le2
  · exact (wincert_cw (cCellLBP cellp2 design adm) (na := 69) (da := 29) (nb := 12) (db := 5)
      (A := 5) (B := -2) (d := 1) (N0 := cellp2.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p2b_cell hp h1 h2 hN).mono le2
  · exact (wincert_cw (cCellLBP cellp2 design adm) (na := 12) (da := 5) (nb := 53) (db := 22)
      (A := 53) (B := -22) (d := 1) (N0 := cellp2.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p2c_cell hp h1 h2 hN).mono le2
  · exact (wincert_cw (cCellLBP cellp1 design adm) (na := 32) (da := 13) (nb := 69) (db := 28)
      (A := -64) (B := 26) (d := 1) (N0 := cellp1.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p1a_cell hp h1 h2 hN).mono le1
  · exact (wincert_cw (cCellLBP cellp1 design adm) (na := 69) (da := 28) (nb := 5) (db := 2)
      (A := 5) (B := -2) (d := 1) (N0 := cellp1.modulus + 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => p1b_cell hp h1 h2 hN).mono le1

def fams13 : List (NullityLB design) := fams12 ++ [cPrimeLB design adm]

def wins13 : List KapWindow := cpWins ++ wins12

def cpGain : ℝ := (cpWins.map (KapWindow.area 58)).sum

def gain13 : ℝ := gain12 + cpGain

theorem cpWins_pos : ∀ w ∈ cpWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [cpWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem cpWins_ord : cpWins.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [cpWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem wins12_a_ge : ∀ t ∈ wins12, (5 / 2 : ℝ) ≤ t.a := by
  intro t ht
  simp only [wins12, List.mem_append] at ht
  rcases ht with ((h | h) | h) | h
  · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · simp only [cWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · have := wins9_a_ge t h
    linarith

theorem wins13_pos : ∀ w ∈ wins13, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact cpWins_pos w h
  · exact wins12_pos w h

theorem wins13_rec : ∀ w ∈ wins13, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · right
    simp only [cpWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins12_rec w h

theorem wins13_ord : wins13.Pairwise (fun s t => s.b ≤ t.a) := by
  unfold wins13
  rw [List.pairwise_append]
  refine ⟨cpWins_ord, wins12_ord, ?_⟩
  intro s hs t ht
  have h4 := wins12_a_ge t ht
  simp only [cpWins, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] at h4 ⊢ <;> linarith

theorem wins13_area : (wins13.map (KapWindow.area 58)).sum = gain13 := by
  unfold wins13 gain13 cpGain
  simp only [List.map_append, List.sum_append]
  have := wins12_area
  linarith

theorem wins13_cert : ∀ w ∈ wins13, ∃ lb ∈ fams13, WinCert lb w := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact ⟨cPrimeLB design adm, by simp [fams13], cpWins_cert w h⟩
  · obtain ⟨lb, hl, hc⟩ := wins12_cert w h
    exact ⟨lb, List.mem_append_left _ hl, hc⟩

/-- **Denominator growth for `fams13` on `wins13`.** -/
theorem partial_growth13 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams13) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain13 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams13 wins13 gain13 wins13_area wins13_pos wins13_ord wins13_rec
    wins13_cert hε

theorem gain13_ge : (21894 / 1000 : ℝ) ≤ gain13 := by
  have h := gain12_ge
  unfold gain13 cpGain
  simp only [cpWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area]
  norm_num
  linarith

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger10
