module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger8.Merge10
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger9.WCells

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger8 + L*(h < p)` (lane G6d)

`wWins` are the Theorem L* windows for `h < p` on `x in (3, 16/5]` (window relations
`lstar2Kap`).  They sit between `lWins` (ending at `x = 3`) and `wins9` (starting at `x = 4.06`).
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger9
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535.Ledger6 CatalanMeasure.GenD.Uniform.Bank535.Ledger7
  CatalanMeasure.GenD.Uniform.Bank535.Ledger8
open CatalanMeasure.GenD.Uniform.W.LStar2
noncomputable section

def wWins : List KapWindow :=
  [cw (3 : ℝ) (73 / 24 : ℝ) (67 : ℝ) (-22 : ℝ),
   cw (73 / 24 : ℝ) (70 / 23 : ℝ) (-6 : ℝ) (2 : ℝ),
   cw (70 / 23 : ℝ) (64 / 21 : ℝ) (64 : ℝ) (-21 : ℝ),
   cw (53 / 17 : ℝ) (78 / 25 : ℝ) (-53 : ℝ) (17 : ℝ),
   cw (78 / 25 : ℝ) (25 / 8 : ℝ) (25 : ℝ) (-8 : ℝ),
   cw (25 / 8 : ℝ) (69 / 22 : ℝ) (-75 : ℝ) (24 : ℝ),
   cw (69 / 22 : ℝ) (22 / 7 : ℝ) (-6 : ℝ) (2 : ℝ),
   cw (22 / 7 : ℝ) (16 / 5 : ℝ) (16 : ℝ) (-5 : ℝ)]

theorem wWins_cert : ∀ w ∈ wWins, WinCert (lstar2LB design adm) w := by
  intro w hw
  simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wincert_cw (lstar2LB design adm) (na := 3) (da := 1) (nb := 73) (db := 24)
      (A := 67) (B := -22) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w1_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 73) (da := 24) (nb := 70) (db := 23)
      (A := -6) (B := 2) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w2_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 70) (da := 23) (nb := 64) (db := 21)
      (A := 64) (B := -21) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w3_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 53) (da := 17) (nb := 78) (db := 25)
      (A := -53) (B := 17) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w4_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 78) (da := 25) (nb := 25) (db := 8)
      (A := 25) (B := -8) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w5_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 25) (da := 8) (nb := 69) (db := 22)
      (A := -75) (B := 24) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w6_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 69) (da := 22) (nb := 22) (db := 7)
      (A := -6) (B := 2) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w7_cell hp h1 h2 hN
  · exact wincert_cw (lstar2LB design adm) (na := 22) (da := 7) (nb := 16) (db := 5)
      (A := 16) (B := -5) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => w8_cell hp h1 h2 hN

def fams11 : List (NullityLB design) := fams10 ++ [lstar2LB design adm]

def wins11 : List KapWindow := lWins ++ wWins ++ wins9

def wGain : ℝ := (wWins.map (KapWindow.area 58)).sum

def gain11 : ℝ := gain10 + wGain

theorem wins11_pos : ∀ w ∈ wins11, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · rcases List.mem_append.mp h with h | h
    · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
    · simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins9_pos w h

theorem wins11_rec : ∀ w ∈ wins11, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · right
    rcases List.mem_append.mp h with h | h
    · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
    · simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins9_rec w h

theorem wWins_ord : wWins.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [wWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem lWins_ord : lWins.Pairwise (fun s t => s.b ≤ t.a) := by
  simp only [lWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  norm_num

theorem wins11_ord : wins11.Pairwise (fun s t => s.b ≤ t.a) := by
  unfold wins11
  rw [List.pairwise_append]
  refine ⟨?_, wins9_ord, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨lWins_ord, wWins_ord, ?_⟩
    intro s hs t ht
    simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at hs
    simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases hs with rfl | rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · intro s hs t ht
    have h4 := wins9_a_ge t ht
    rcases List.mem_append.mp hs with h | h
    · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] at h4 ⊢ <;> linarith
    · simp only [wWins, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [cw] at h4 ⊢ <;> linarith

theorem wins11_area : (wins11.map (KapWindow.area 58)).sum = gain11 := by
  unfold wins11 gain11 wGain
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append, wins9_area]
  have : (wins10.map (KapWindow.area 58)).sum = gain10 := wins10_area
  unfold wins10 at this
  rw [List.map_append, List.sum_append, wins9_area] at this
  linarith

theorem wins11_cert : ∀ w ∈ wins11, ∃ lb ∈ fams11, WinCert lb w := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · rcases List.mem_append.mp h with h | h
    · exact ⟨W.LStar.lstarLB design adm, by simp [fams11, fams10], lWins_cert w h⟩
    · exact ⟨lstar2LB design adm, by simp [fams11], wWins_cert w h⟩
  · obtain ⟨lb, hl, hc⟩ := wins9_cert w h
    exact ⟨lb, by
      unfold fams11
      exact List.mem_append_left _ (List.mem_append_left _ hl), hc⟩

/-- **Denominator growth for `fams11` on `wins11`.** -/
theorem partial_growth11 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams11) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain11 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams11 wins11 gain11 wins11_area wins11_pos wins11_ord wins11_rec
    wins11_cert hε

theorem gain11_ge : (21870 / 1000 : ℝ) ≤ gain11 := by
  unfold gain11 wGain gain10 lGain gain9 gain8 gain7 gain6 gain5
  simp only [lWins, wWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area]
  norm_num

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger9
