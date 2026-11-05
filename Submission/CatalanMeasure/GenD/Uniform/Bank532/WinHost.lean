module

public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Slot
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win

@[expose] public section
set_option Elab.async false

/-!
# Window certificate of a host packet, affine window (lane G10)

`winCert_host_cw`: the affine window `cw a b c0 c1` is certified against `NullityLB.ofPacketHost`
as soon as the cleared inequality `A N + B p <= d (packetVal + 2)` holds for the primes of the window
(`N >= N0`) and the window implies the packet window predicate `Win`.  The physical host
`phys : PhysHost ...` stays an explicit hypothesis (G8d supplies it).  The exception integer
`pk.D` is absorbed by enlarging `N0`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank532
open Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.Bank540.Ledger3 CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.W.Prof
  CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section

theorem winCert_host_cw (hP : Admissible design) (pk : Packet) (hS : pk.Sound) (hD : pk.D ≠ 0)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysHost design pk Win c w)
    {a b c0 c1 : ℝ} {na da nb db : ℕ} {A B : ℤ} {d N0 : ℕ}
    (hd : 0 < d) (hda : 0 < da) (hdb : 0 < db) (ha : a * da = na) (hb : b * db = nb)
    (hna : 1 ≤ na) (hc0 : c0 * d = A) (hc1 : c1 * d = B) (hb59 : 2 * nb ≤ 59 * db)
    (hWin : ∀ N p : ℕ, N0 ≤ N → p.Prime → na * N < da * p → db * p ≤ nb * N → Win N p)
    (hcell : ∀ N p : ℕ, N0 ≤ N → p.Prime → na * N < da * p → db * p ≤ nb * N →
      A * (N : ℤ) + B * (p : ℤ) ≤ (d : ℤ) * (((packetVal pk c w N p : ℕ) : ℤ) + 2)) :
    WinCert (NullityLB.ofPacketHost hP pk hS Win c w phys) (cw a b c0 c1) := by
  refine wincert_cw (NullityLB.ofPacketHost hP pk hS Win c w phys) (na := na) (da := da)
    (nb := nb) (db := db) (A := A) (B := B) (d := d) (N0 := N0 + pk.D.natAbs * da)
    hd hda hdb ha hb hc0 hc1 hb59 ?_
  intro N p hN hp h1 h2
  have hN0 : N0 ≤ N := by omega
  have hW := hWin N p hN0 hp h1 h2
  have hpD : pk.D.natAbs < p := by
    by_contra hcon
    push_neg at hcon
    have h3 : N ≤ na * N := Nat.le_mul_of_pos_left N hna
    have h4 : da * p ≤ da * pk.D.natAbs := Nat.mul_le_mul_left da hcon
    have h5 : pk.D.natAbs * da = da * pk.D.natAbs := Nat.mul_comm _ _
    omega
  rw [ofPacketHost_kap hP pk hS Win c w phys (hostApp_of_large pk hD hW hpD)]
  exact hcell N p hN0 hp h1 h2

end
end CatalanMeasure.GenD.Uniform.Bank532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.winCert_host_cw
