module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Instance3

@[expose] public section
set_option Elab.async false

/-!
# The B = 540 gate for Ledger2 + MT (1), and the drop-in interface for M and Z (lane G5f)

* `gain3 = mtGain + gain2 = 20.2223...` (`mtGain = 35863749/400000000 = 0.08966`, the certified MT (1) area).
* `gate_of_remaining3`: the remaining families (Theorem M, Theorem Z, ...) must add area `>= 1.3860`.
* `gate_of_families_windows`: the general final statement.  A new family is any `lb : NullityLB design`
  (for instance the `NullityLB` of `W/HYPlus` or `W/ZoneZ`, taken as a parameter); it enters by supplying
  windows `w` with `WinCert lb w`.  Given an ordered window list whose members are each certified against
  one family of the list and whose total area is `>= 21.6083`, the payment hypotheses hold, the decay rate
  `eta = 29.596` is admissible, and the denominator growth bound follows.
* `wins3_cert_ext`: the windows `wins3` stay certified when further families are added to the list.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger2
noncomputable section

theorem gain3_ge : (202223 / 10000 : ℝ) ≤ gain3 := by
  have h2 := Ledger2.gain2_ge
  unfold gain3 mtGain Ledger2.gain2 at *
  norm_num at *

theorem gate_of_remaining3 (extra : ℝ) (h : 13860 / 10000 ≤ extra) :
    PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg (gain3 + extra) := by
  refine gate (gain3 + extra) ?_
  have := gain3_ge
  linarith

/-- The windows of `wins3` remain certified when more families are appended. -/
theorem wins3_cert_ext (ex : List (NullityLB design)) :
    ∀ w ∈ wins3, ∃ lb ∈ fams3 ++ ex, WinCert lb w := by
  intro w hw
  obtain ⟨lb, hlb, h⟩ := wins3_cert w hw
  exact ⟨lb, List.mem_append_left _ hlb, h⟩

/-- **Final statement for any list of families.**  `fams` may contain `ledgerLB`, `mtLB3` and the
`NullityLB`s of Theorems M and Z; `ws` is the merged window list. -/
theorem gate_of_families_windows (fams : List (NullityLB design)) (ws : List KapWindow) (gain : ℝ)
    (hsum : (ws.map (KapWindow.area 58)).sum = gain)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78)
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (hcert : ∀ w ∈ ws, ∃ lb ∈ fams, WinCert lb w) (hgain : 216083 / 10000 ≤ gain) :
    (PayW (3 / 4) D58.d0 Bank540.rho etaG Bank540.kappa D58.delta Bank540.B ∧
      etaG < Bank540.tDelta - gDg gain) ∧
    ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible (famLB fams) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (24733 / 4 + 2673 / 8 * Real.log 2 - gain + ε) * (N : ℝ) ^ 2 :=
  ⟨gate_of_families gain hgain,
    fun hε => growth_of_families fams ws gain hsum hpos hord hrec hcert hε⟩

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger3
