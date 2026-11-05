module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Gate3
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.ZWins
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.MWins2
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.GlueWins

@[expose] public section
set_option Elab.async false

/-!
# The ledger `Ledger2 + MT (1) + MT (b) + M + Z_H` (lane G5g)

`wins4` merges the windows of `Ledger3` with the glue windows (`s = 17, 18`), the family M windows and the
Theorem Z (Law_H (4)) windows:

* `mtWins[0], mtWins[1]` (`4.2943 .. 4.3333`) are replaced by `gw17a, gw17b` and the tail `(4.33, 4.3333]` of `mtWins[1]`;
  `gw18` is new (`x in (4.06, 4.1]`);
* `wins2[2]` (`6.9001 .. 6.9999`) is replaced by the two M windows (`6.9 .. 7.06`);
* `wins2[16]` (`16 .. 118/7`) is shortened to start at `16.19`; `zWins` (`15.1435 .. 16.18`) is new.

`gain4 = 4184623903687 / 196350000000 = 21.31206...`; the residual for the remaining family Z_L is
`gate_of_remaining4`: `extra >= 0.2963`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger2
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.MTGlue
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section

/-- The tail of `mtWins[1]`. -/
def mt1tail : KapWindow := cw (433 / 100 : ℝ) (10833 / 2500 : ℝ) (-140 : ℝ) (65 / 2 : ℝ)

/-- `wins2[16]` shortened. -/
def mod16 : KapWindow := cw (1619 / 100 : ℝ) (118 / 7 : ℝ) (-16 : ℝ) (1 : ℝ)

/-- The glue / MT (1) part below `x = 5.1`. -/
def glueMt : List KapWindow := gw18 :: gw17a :: gw17b :: mt1tail :: mtWins.drop 2

/-- The merged list. -/
def wins4 : List KapWindow :=
  glueMt ++ wins2.take 2 ++ mWins ++ (wins2.drop 3).take 13 ++ zWins ++ [mod16] ++ wins2.drop 17

/-- Families of the ledger so far. -/
def fams4 : List (NullityLB design) :=
  [ledgerLB, mtLB3 design adm, mtGlueLB' design adm, mLB' design adm, zHLB design adm]

def gain4 : ℝ := 4184623903687 / 196350000000

theorem mt1tail_mem : cw (43227 / 10000 : ℝ) (10833 / 2500 : ℝ) (-140 : ℝ) (65 / 2 : ℝ) ∈ mtWins := by
  simp [mtWins]

theorem mod16_mem : cw (16 : ℝ) (118 / 7 : ℝ) (-16 : ℝ) (1 : ℝ) ∈ wins2 := by
  simp [wins2]

/-- Chain condition (consecutive windows). -/
def Ch : List KapWindow → Prop
  | [] => True
  | [_] => True
  | s :: t :: r => s.b ≤ t.a ∧ Ch (t :: r)

theorem ch_lb : ∀ (l : List KapWindow) (h : KapWindow), (∀ w ∈ l, w.a ≤ w.b) → Ch (h :: l) →
    ∀ t ∈ l, h.b ≤ t.a := by
  intro l
  induction l with
  | nil => intro h _ _ t ht; simp at ht
  | cons x xs ih =>
    intro h hab hc t ht
    simp only [Ch] at hc
    have hx : x.a ≤ x.b := hab x (List.mem_cons_self)
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact hc.1
    · have := ih x (fun w hw => hab w (List.mem_cons_of_mem _ hw)) hc.2 t ht'
      exact le_trans hc.1 (le_trans hx this)

theorem pw_of_ch : ∀ l : List KapWindow, (∀ w ∈ l, w.a ≤ w.b) → Ch l →
    l.Pairwise (fun s t => s.b ≤ t.a) := by
  intro l
  induction l with
  | nil => intros; exact List.Pairwise.nil
  | cons h t ih =>
    intro hab hc
    refine List.Pairwise.cons ?_ (ih (fun w hw => hab w (List.mem_cons_of_mem _ hw)) ?_)
    · exact ch_lb t h (fun w hw => hab w (List.mem_cons_of_mem _ hw)) hc
    · cases t with
      | nil => trivial
      | cons x xs => exact hc.2

theorem wins4_mem {w : KapWindow} (h : w ∈ wins4) :
    w = gw18 ∨ w = gw17a ∨ w = gw17b ∨ w = mt1tail ∨ w ∈ mtWins ∨ w ∈ wins2 ∨ w ∈ mWins ∨
      w ∈ zWins ∨ w = mod16 := by
  simp only [wins4, glueMt, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with (((((( rfl | rfl | rfl | rfl | h1) | h2) | h3) | h4) | h5) | rfl) | h7
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h2))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (List.mem_of_mem_drop (List.mem_of_mem_take h4)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h7))))))

theorem mWins_pos : ∀ w ∈ mWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [mWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> simp only [cw] <;> norm_num

theorem zWins_pos : ∀ w ∈ zWins, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  simp only [zWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> simp only [cw] <;> norm_num

theorem wins4_pos : ∀ w ∈ wins4, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78 := by
  intro w hw
  rcases wins4_mem hw with rfl | rfl | rfl | rfl | h | h | h | h | rfl
  · simp only [gw18, cw]; norm_num
  · simp only [gw17a, cw]; norm_num
  · simp only [gw17b, cw]; norm_num
  · simp only [mt1tail, cw]; norm_num
  · exact mtWins_pos w h
  · exact wins2_pos w h
  · exact mWins_pos w h
  · exact zWins_pos w h
  · simp only [mod16, cw]; norm_num

theorem wins4_rec : ∀ w ∈ wins4, w.b ≤ 1 ∨ 2 ≤ w.a := by
  intro w hw
  rcases wins4_mem hw with rfl | rfl | rfl | rfl | h | h | h | h | rfl
  · right; simp only [gw18, cw]; norm_num
  · right; simp only [gw17a, cw]; norm_num
  · right; simp only [gw17b, cw]; norm_num
  · right; simp only [mt1tail, cw]; norm_num
  · exact mtWins_rec w h
  · exact wins2_rec w h
  · right
    simp only [mWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [cw] <;> norm_num
  · right
    simp only [zWins, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only [cw] <;> norm_num
  · right; simp only [mod16, cw]; norm_num

theorem wins4_cert : ∀ w ∈ wins4, ∃ lb ∈ fams4, WinCert lb w := by
  intro w hw
  rcases wins4_mem hw with rfl | rfl | rfl | rfl | h | h | h | h | rfl
  · exact ⟨mtGlueLB' design adm, by simp [fams4], gw18_cert⟩
  · exact ⟨mtGlueLB' design adm, by simp [fams4], gw17a_cert⟩
  · exact ⟨mtGlueLB' design adm, by simp [fams4], gw17b_cert⟩
  · exact ⟨mtLB3 design adm, by simp [fams4],
      WinCert.shrink (mtWins_cert _ mt1tail_mem) (by norm_num) (le_refl _)⟩
  · exact ⟨mtLB3 design adm, by simp [fams4], mtWins_cert w h⟩
  · exact ⟨ledgerLB, by simp [fams4], wins2_cert w h⟩
  · exact ⟨mLB' design adm, by simp [fams4], mWins_cert w h⟩
  · exact ⟨zHLB design adm, by simp [fams4], zWins_cert w h⟩
  · exact ⟨ledgerLB, by simp [fams4], WinCert.shrink (wins2_cert _ mod16_mem : WinCert ledgerLB _) (by norm_num) (le_refl _)⟩

theorem wins4_ord : wins4.Pairwise (fun s t => s.b ≤ t.a) := by
  refine pw_of_ch _ (fun w hw => (wins4_pos w hw).2.1.le) ?_
  simp only [wins4, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mWins, zWins, mtWins, wins2, cw, Ch,
    List.cons_append, List.nil_append, List.drop, List.take, List.append_assoc]
  norm_num

theorem wins4_area : (wins4.map (KapWindow.area 58)).sum = gain4 := by
  simp only [wins4, glueMt, gw18, gw17a, gw17b, mt1tail, mod16, mWins, zWins, mtWins, wins2, List.drop,
    List.take, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    List.cons_append, List.nil_append, cw_area, gain4]
  norm_num

/-- **Denominator growth for the families `[ledgerLB, mtLB3, mtGlueLB', mLB', zHLB]` on `wins4`.** -/
theorem partial_growth4 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams4) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain4 + ε) * (N : ℝ) ^ 2 :=
  growth_of_families fams4 wins4 gain4 wins4_area wins4_pos wins4_ord wins4_rec wins4_cert hε

theorem gain4_ge : (213120 / 10000 : ℝ) ≤ gain4 := by
  unfold gain4; norm_num

/-- **The gate for `wins4` plus anything the remaining family (Theorem Z, Law_L (4)) adds:
`extra >= 0.2963` suffices.** -/
theorem gate_of_remaining4 (extra : ℝ) (h : 2963 / 10000 ≤ extra) :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg (gain4 + extra) := by
  refine gate (gain4 + extra) ?_
  have := gain4_ge
  linarith

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
