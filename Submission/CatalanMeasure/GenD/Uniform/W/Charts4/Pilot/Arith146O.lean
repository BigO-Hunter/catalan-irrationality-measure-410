module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146Arith
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Data146O
@[expose] public section
set_option Elab.async false

/-!
# L0146 pilot arithmetic for `packetO` (label rows): `packetVal = 73 N - 12 p`
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4
noncomputable section

theorem packetO_len : packetO.charts.length = 11 := by decide +kernel
theorem packetO_d : packetO.d = 4 := by decide +kernel
theorem packetO_n : packetO.n = 44 := by decide +kernel

def wNatO (g : Fin packetO.charts.length) (N p : ℕ) : ℕ := ((wInt N p).getD g.val 0).toNat

theorem packetO_ranks (g : Fin packetO.charts.length) :
    (packetO.chart g).r = ranks.getD g.val 0 := by
  obtain ⟨i, hi⟩ := g
  rw [packetO_len] at hi
  interval_cases i <;> rfl

theorem packetValO_eq {N p : ℕ} (h : Win N p) :
    packetVal packetO cNat wNatO N p = 73 * N - 12 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold packetVal cNat
  have hs : ∑ g : Fin packetO.charts.length, wNatO g N p * (packetO.chart g).r =
      ∑ i ∈ Finset.range 11, ((wInt N p).getD i 0).toNat * ranks.getD i 0 := by
    have e : ∑ g : Fin packetO.charts.length, wNatO g N p * (packetO.chart g).r =
        ∑ g : Fin packetO.charts.length, ((wInt N p).getD g.val 0).toNat * ranks.getD g.val 0 :=
      Finset.sum_congr rfl (fun g _ => by rw [packetO_ranks g]; rfl)
    rw [e, Fin.sum_univ_eq_sum_range
      (fun i => ((wInt N p).getD i 0).toNat * ranks.getD i 0) packetO.charts.length, packetO_len]
  rw [hs, packetO_d]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, wInt, ranks]
  simp
  omega

theorem pilotO_ineq {N p : ℕ} (h : Win N p) :
    (N : ℝ) * (73 - 12 * ((p : ℝ) / N)) - 2 ≤ (packetVal packetO cNat wNatO N p : ℝ) := by
  have hN : (0 : ℝ) < N := by have := h.1; exact_mod_cast (by omega : 0 < N)
  rw [packetValO_eq h]
  have : 12 * p ≤ 73 * N := by have := h.2.2.1; omega
  rw [Nat.cast_sub this]
  push_cast
  have : (N : ℝ) * (73 - 12 * ((p : ℝ) / N)) = 73 * N - 12 * p := by field_simp
  linarith

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
