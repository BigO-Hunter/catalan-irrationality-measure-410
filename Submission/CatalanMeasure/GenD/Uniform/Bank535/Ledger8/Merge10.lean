module

public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger7.Merge9
public import Submission.CatalanMeasure.GenD.Uniform.Bank535.Ledger8.LCells

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger7 + L*` (lane G6c)

`lWins` are the Theorem L* windows on `x in (59/21, 3]` (`h >= p`):
`K = 21x - 59` on `(59/21, 2.8235]`, `K = 4x - 11` on `(48/17, 23/8]`, `K = 58 - 20x` on
`(23/8, 29/10]`, `K = 20x - 59` on `(59/20, 3]`.  They sit below every window of `wins9`
(`wins9` starts at `x = 4.06`), so `wins10 = lWins ++ wins9`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank535.Ledger8
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Uniform.Bank540.Ledger5
open CatalanMeasure.GenD.Uniform.Bank535.Ledger6 CatalanMeasure.GenD.Uniform.Bank535.Ledger7
open CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section

def lWins : List KapWindow :=
  [cw (59 / 21 : ℝ) (28235 / 10000 : ℝ) (-59 : ℝ) (21 : ℝ),
   cw (48 / 17 : ℝ) (23 / 8 : ℝ) (-11 : ℝ) (4 : ℝ),
   cw (23 / 8 : ℝ) (29 / 10 : ℝ) (58 : ℝ) (-20 : ℝ),
   cw (59 / 20 : ℝ) (3 : ℝ) (-59 : ℝ) (20 : ℝ)]

theorem lWins_cert : ∀ w ∈ lWins, WinCert (lstarLB design adm) w := by
  intro w hw
  simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact wincert_cw (lstarLB design adm) (na := 59) (da := 21) (nb := 28235) (db := 10000)
      (A := -59) (B := 21) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => lW3_cell hp h1 h2 hN
  · exact wincert_cw (lstarLB design adm) (na := 48) (da := 17) (nb := 23) (db := 8)
      (A := -11) (B := 4) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => lW4_cell hp h1 h2 hN
  · exact wincert_cw (lstarLB design adm) (na := 23) (da := 8) (nb := 29) (db := 10)
      (A := 58) (B := -20) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => lW5_cell hp h1 h2 hN
  · exact wincert_cw (lstarLB design adm) (na := 59) (da := 20) (nb := 3) (db := 1)
      (A := -59) (B := 20) (d := 1) (N0 := 2000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => lW6_cell hp h1 (by omega) hN

def fams10 : List (NullityLB design) := fams9 ++ [lstarLB design adm]

def wins10 : List KapWindow := lWins ++ wins9

def lGain : ℝ := (lWins.map (KapWindow.area 58)).sum

def gain10 : ℝ := gain9 + lGain

theorem wins9_head : ∃ tl, wins9 = gw18 :: tl := ⟨_, rfl⟩

theorem wins9_a_ge : ∀ t ∈ wins9, (4 : ℝ) ≤ t.a := by
  intro t ht
  obtain ⟨tl, htl⟩ := wins9_head
  have hord := wins9_ord
  rw [htl, List.pairwise_cons] at hord
  rw [htl, List.mem_cons] at ht
  rcases ht with rfl | ht
  · simp only [gw18, cw]; norm_num
  · have := hord.1 t ht
    simp only [gw18, cw] at this
    linarith

theorem wins10_pos : ∀ w ∈ wins10, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins9_pos w h

theorem wins10_rec : ∀ w ∈ wins10, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · right
    simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · exact wins9_rec w h

theorem wins10_ord : wins10.Pairwise (fun s t => s.b ≤ t.a) := by
  unfold wins10
  rw [List.pairwise_append]
  refine ⟨?_, wins9_ord, ?_⟩
  · simp only [lWins, cw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    norm_num
  · intro s hs t ht
    have h4 := wins9_a_ge t ht
    simp only [lWins, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp only [cw] at h4 ⊢ <;> linarith

theorem wins10_area : (wins10.map (KapWindow.area 58)).sum = gain10 := by
  unfold wins10 gain10 lGain
  rw [List.map_append, List.sum_append, wins9_area]
  ring

theorem wins10_cert : ∀ w ∈ wins10, ∃ lb ∈ fams10, WinCert lb w := by
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact ⟨lstarLB design adm, by simp [fams10], lWins_cert w h⟩
  · obtain ⟨lb, hl, hc⟩ := wins9_cert w h
    exact ⟨lb, List.mem_append_left _ hl, hc⟩

/-- **Denominator growth for `fams10` on `wins10`.** -/
theorem partial_growth10 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams10) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain10 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams10 wins10 gain10 wins10_area wins10_pos wins10_ord wins10_rec
    wins10_cert hε

theorem gain10_ge : (21836 / 1000 : ℝ) ≤ gain10 := by
  unfold gain10 lGain gain9 gain8 gain7 gain6 gain5
  simp only [lWins, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cw_area]
  norm_num

end
end CatalanMeasure.GenD.Uniform.Bank535.Ledger8
