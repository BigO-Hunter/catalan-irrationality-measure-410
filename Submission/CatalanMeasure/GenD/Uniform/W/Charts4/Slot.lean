module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.Host
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Slot
@[expose] public section
set_option Elab.async false

/-!
# `packet_winCert_host`: the `WinCert` obligation for `NullityLB.ofPacketHost` (any `q`)
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger
  CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
  CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section

theorem packet_winCert_host (hP : Admissible design) (pk : Packet) (hS : pk.Sound)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysHost design pk Win c w) (kw : KapWindow)
    (hcert : ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → kw.a * N < p → (p : ℝ) ≤ kw.b * N →
      HostApp pk Win N p ∧
      (N : ℝ) * kw.K.eval ((p : ℝ) / N) - 2 ≤ (packetVal pk c w N p : ℝ) ∧
      (N : ℝ) * kw.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss design N p : ℝ)) :
    WinCert (NullityLB.ofPacketHost hP pk hS Win c w phys) kw := by
  filter_upwards [hcert] with N hN p hp h1 h2
  obtain ⟨hA, hK, hG⟩ := hN p hp h1 h2
  refine ⟨?_, hG⟩
  rw [ofPacketHost_kap hP pk hS Win c w phys hA]
  exact hK

end
end CatalanMeasure.GenD.Uniform.W.Charts4
