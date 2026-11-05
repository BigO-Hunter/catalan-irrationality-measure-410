module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger2.Gate2
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.MTCell

@[expose] public section
set_option Elab.async false

/-!
# Generic window machinery: windows certified against any family (lane G5f)

`WinCert lb w` says that the window `w` is certified against the nullity lower bound `lb` (the shape
`wins2_cert` has for `ledgerLB`).  A window certified against one member of a list `fams` is
certified against `famLB fams` (`WinCert.lift`), so Theorem M (`W/HYPlus`), Theorem Z (`W/ZoneZ`),
or any other `NullityLB` family drop in by supplying windows `w` with `WinCert lb w`; the growth
theorem `growth_of_families` and the gate theorem `gate_of_families` then hold for the combined
list, with no other change.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

/-- The window `w` is certified (for large `N`) against the nullity bound `lb`. -/
def WinCert (lb : NullityLB design) (w : KapWindow) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → w.a * N < p → (p : ℝ) ≤ w.b * N →
    (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ (lb.kap N p : ℝ) ∧
    (N : ℝ) * w.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ)

/-- The pointwise maximum of a list of families. -/
def famLB (fams : List (NullityLB design)) : NullityLB design := NullityLB.supList design fams

theorem WinCert.mono {lb lb' : NullityLB design} {w : KapWindow}
    (h : ∀ N p, lb.kap N p ≤ lb'.kap N p) (hw : WinCert lb w) : WinCert lb' w := by
  filter_upwards [hw] with N hN p hp h1 h2
  obtain ⟨k, g⟩ := hN p hp h1 h2
  exact ⟨k.trans (by exact_mod_cast h N p), g⟩

theorem WinCert.lift {fams : List (NullityLB design)} {lb : NullityLB design} {w : KapWindow}
    (hlb : lb ∈ fams) (hw : WinCert lb w) : WinCert (famLB fams) w :=
  hw.mono fun N p => NullityLB.le_supList_kap hlb N p

/-- A family together with windows certified against it: the data a new family supplies. -/
structure FamWindows (lb : NullityLB design) where
  ws : List KapWindow
  cert : ∀ w ∈ ws, WinCert lb w

/-- **Denominator growth for windows certified against any list of families.** -/
theorem growth_of_families (fams : List (NullityLB design)) (ws : List KapWindow) (gain : ℝ)
    (hsum : (ws.map (KapWindow.area 58)).sum = gain)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78)
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (hcert : ∀ w ∈ ws, ∃ lb ∈ fams, WinCert lb w) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain + ε) * (N : ℝ) ^ 2 :=
  ledger_growth (famLB fams) ws gain hsum hpos hord hrec
    (fun w hw => by
      obtain ⟨lb, hlb, h⟩ := hcert w hw
      exact (WinCert.lift hlb h)) hε

/-- **Gate for windows certified against any list of families**: if the total area is at least
`21.6083`, the payment hypotheses hold and `eta = 29.596 < tDelta - gDg gain`. -/
theorem gate_of_families (gain : ℝ) (hgain : 216083 / 10000 ≤ gain) :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg gain :=
  gate gain hgain

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger3
