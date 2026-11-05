module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Slot
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Pilot.Check146
@[expose] public section
set_option Elab.async false

/-!
# L0146 pilot arithmetic: exact weights and `packetVal = 73 N - 12 p`

Weights from `complete29/production/D58-L0146/compression.json` (affine in `N`, `hp = (p-1)/2`),
central coefficient `p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
noncomputable section

/-- Exact weights as integers. -/
def wInt (N p : ℕ) : List ℤ :=
  let N : ℤ := N
  let hp : ℤ := ((p : ℤ) - 1) / 2
  [hp, 69*N - 11 - 22*hp, 9*N - 1 - 2*hp, 3*N, -6*N + 1 + 2*hp, 6*N - 1 - hp,
   -78*N + 13 + 26*hp, 75*N - 12 - 24*hp, 1, -5*N + 2*hp, 9 - 48*N + 16*hp]

def wNat (g : Fin packet.charts.length) (N p : ℕ) : ℕ := ((wInt N p).getD g.val 0).toNat

def cNat (_N p : ℕ) : ℕ := p

/-- The window of the leaf piece (6, 152/25]. -/
def Win (N p : ℕ) : Prop := 20 ≤ N ∧ 6 * N < p ∧ 25 * p ≤ 152 * N ∧ p % 2 = 1

def ranks : List ℕ := [1,1,0,2,2,1,3,2,2,2,1]

theorem packet_len : packet.charts.length = 11 := by decide +kernel

theorem packet_d : packet.d = 4 := by decide +kernel

theorem packet_ranks (g : Fin packet.charts.length) :
    (packet.chart g).r = ranks.getD g.val 0 := by
  obtain ⟨i, hi⟩ := g
  rw [packet_len] at hi
  interval_cases i <;> rfl

theorem packetVal_eq {N p : ℕ} (h : Win N p) :
    packetVal packet cNat wNat N p = 73 * N - 12 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold packetVal cNat
  have hs : ∑ g : Fin packet.charts.length, wNat g N p * (packet.chart g).r =
      ∑ i ∈ Finset.range 11, ((wInt N p).getD i 0).toNat * ranks.getD i 0 := by
    have e : ∑ g : Fin packet.charts.length, wNat g N p * (packet.chart g).r =
        ∑ g : Fin packet.charts.length, ((wInt N p).getD g.val 0).toNat * ranks.getD g.val 0 :=
      Finset.sum_congr rfl (fun g _ => by rw [packet_ranks g]; rfl)
    rw [e, Fin.sum_univ_eq_sum_range
      (fun i => ((wInt N p).getD i 0).toNat * ranks.getD i 0) packet.charts.length, packet_len]
  rw [hs, packet_d]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, wInt, ranks]
  simp
  omega

/-- The affine inequality of the pilot window, in the form consumed by `packet_winCert_host`. -/
theorem pilot_ineq {N p : ℕ} (h : Win N p) :
    (N : ℝ) * (73 - 12 * ((p : ℝ) / N)) - 2 ≤ (packetVal packet cNat wNat N p : ℝ) := by
  have hN : (0 : ℝ) < N := by have := h.1; exact_mod_cast (by omega : 0 < N)
  rw [packetVal_eq h]
  have : 12 * p ≤ 73 * N := by have := h.2.2.1; omega
  rw [Nat.cast_sub this]
  push_cast
  have : (N : ℝ) * (73 - 12 * ((p : ℝ) / N)) = 73 * N - 12 * p := by field_simp
  linarith

end
end CatalanMeasure.GenD.Uniform.W.Charts4
