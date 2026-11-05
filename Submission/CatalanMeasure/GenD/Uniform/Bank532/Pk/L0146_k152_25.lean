module

public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Check146O
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Arith146O
public import Submission.CatalanMeasure.GenD.Uniform.Bank532.WinHost

@[expose] public section
set_option Elab.async false

/-!
# L0146 (k152_25): window `(6, 152/25]`, `K = 73 - 12 x`, reusing G8d's `packetO` (label rows) and `Win`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank532.Pk.L0146_k152_25
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Bank532 CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

theorem pk_D_ne : packetO.D ≠ 0 := by decide +kernel

def Phys : Prop := PhysHost design packetO Win cNat wNatO

theorem cell0 : ∀ N p : ℕ, 20 ≤ N → p.Prime → 6 * N < 1 * p → 25 * p ≤ 152 * N →
    (146 : ℤ) * (N : ℤ) + (-24 : ℤ) * (p : ℤ) ≤ ((2 : ℕ) : ℤ) * (((packetVal packetO cNat wNatO N p : ℕ) : ℤ) + 2) := by
  intro N p hN hp h1 h2
  have hW : Win N p := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · omega
    · exact ⟨hN, by omega, h2, hodd⟩
  rw [packetValO_eq hW]
  have : 12 * p ≤ 73 * N := by omega
  push_cast [Nat.cast_sub this]
  omega

theorem win0 (hP : Admissible design) (phys : Phys) :
    WinCert (NullityLB.ofPacketHost hP packetO packetO_sound Win cNat wNatO phys)
      (cw (6 : ℝ) (152 / 25 : ℝ) (73 : ℝ) (-12 : ℝ)) :=
  winCert_host_cw hP packetO packetO_sound pk_D_ne Win cNat wNatO phys (d := 2) (A := 146) (B := -24) (N0 := 20)
    (na := 6) (da := 1) (nb := 152) (db := 25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun N p hN hp h1 h2 => by
      rcases hp.eq_two_or_odd with rfl | hodd
      · omega
      · exact ⟨hN, by omega, h2, hodd⟩) cell0

end
end CatalanMeasure.GenD.Uniform.Bank532.Pk.L0146_k152_25
#print axioms CatalanMeasure.GenD.Uniform.Bank532.Pk.L0146_k152_25.win0
