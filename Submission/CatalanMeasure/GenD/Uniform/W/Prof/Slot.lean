module
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.OfWindow
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Fam
@[expose] public section
set_option Elab.async false

/-!
# Plugging a packet family into the Ledger3 window machinery

`packet_winCert` : the `WinCert` obligation for `NullityLB.ofPacketWindow` reduces to the affine
inequality `N K(p/N) - 2 ≤ c d - Σ_j w_j r_j` (together with the window predicate and the pool
bound), for large `N` and all primes of the window.  `eventually_gt_D` supplies `p > |D|` from
`p > a N`.  Then `gate_of_families_windows`-style assembly (Bank540/Ledger3/Gate3) applies
unchanged.
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger
  CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

/-- `p > a N` forces `p > |D|` for large `N`. -/
theorem eventually_gt_D (D : ℤ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, a * N < p → D.natAbs < p := by
  filter_upwards [eventually_ge_atTop ⌈(D.natAbs : ℝ) / a⌉₊] with N hN p hp
  have h1 : (D.natAbs : ℝ) / a ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h2 : (D.natAbs : ℝ) ≤ a * N := by
    rw [div_le_iff₀ ha] at h1; linarith
  exact_mod_cast lt_of_le_of_lt h2 hp

/-- The window certificate of a packet family (against `design`). -/
theorem packet_winCert (hP : Admissible design) (pk : Packet) (hS : pk.Sound)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysWindow design pk Win c w) (kw : KapWindow)
    (hcert : ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → kw.a * N < p → (p : ℝ) ≤ kw.b * N →
      PacketApp design pk Win N p ∧
      (N : ℝ) * kw.K.eval ((p : ℝ) / N) - 2 ≤ (packetVal pk c w N p : ℝ) ∧
      (N : ℝ) * kw.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ)) :
    WinCert (NullityLB.ofPacketWindow hP pk hS Win c w phys) kw := by
  filter_upwards [hcert] with N hN p hp h1 h2
  obtain ⟨hA, hK, hG⟩ := hN p hp h1 h2
  refine ⟨?_, hG⟩
  rw [ofPacketWindow_kap hP pk hS Win c w phys hA]
  exact hK

end
end CatalanMeasure.GenD.Uniform.W.Prof
