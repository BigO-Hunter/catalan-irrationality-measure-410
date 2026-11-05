module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.Win
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLBcap

@[expose] public section
set_option Elab.async false

/-!
# Certified windows for Theorem Z, Law_H (4) (lane G5g)

`zHLB` (`W/ZoneZ`) has two regimes: `zHvalCap` (`5p + 1 <= H`, `L <= 5p`) and `zHval` (`H <= 5p`).
`zk_cap` / `zk_nc` verify the window predicate for large `N`: arithmetic by `omega`, and
`p` does not divide the fixed integer `ZcH6 > 0` because `p > N >= ZcH6`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

theorem foldl_lcm_ne_zero (l : List ℕ) (a : ℕ) (ha : a ≠ 0) (hl : ∀ x ∈ l, x ≠ 0) :
    l.foldl Nat.lcm a ≠ 0 := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x t ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.lcm_ne_zero ha (hl x (List.mem_cons_self))) (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem Zmom_ne : Zmom ≠ 0 := by
  unfold Zmom
  refine foldl_lcm_ne_zero _ _ one_ne_zero ?_
  intro x hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, -, J, -, rfl | rfl⟩ := hx
  · exact Rat.den_nz _
  · exact Rat.den_nz _

theorem ZcH_ne : ZcH ≠ 0 := by
  unfold ZcH
  refine foldl_lcm_ne_zero _ _ Zmom_ne ?_
  intro x hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with ⟨k, -, rfl | rfl | rfl | rfl⟩ | rfl | rfl | rfl <;> exact Rat.den_nz _

theorem ZcH6_ne : ZcH6 ≠ 0 := by
  unfold ZcH6 ZcH'
  refine Nat.lcm_ne_zero (Nat.lcm_ne_zero ZcH_ne (Nat.lcm_ne_zero ?_ ?_)) (by norm_num)
  · simpa using DqU_num_ne
  · simpa using DqY_num_ne

theorem not_dvd_ZcH6 {N p : ℕ} (hN : ZcH6 ≤ N) (hp : N < p) : ¬ p ∣ ZcH6 := fun h =>
  absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero ZcH6_ne) h) (by omega)

theorem not_dvd_ZcH' {N p : ℕ} (hN : ZcH6 ≤ N) (hp : N < p) : ¬ p ∣ ZcH' := fun h =>
  not_dvd_ZcH6 hN hp (h.trans (Nat.dvd_lcm_left _ _))

theorem zk_cap {N p : ℕ} (hN : ZcH6 + 1000 ≤ N) (hp : p.Prime) (h1 : 14 * N ≤ p) (h2 : 5 * p + 1 ≤ 78 * N) :
    zHvalCap design N p ≤ (zHLB design adm).kap N p := by
  have hA : zHAppCap design N p := by
    have hZ : ZcH6 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
    have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
    have hNp : N < p := by clear hN hZ; omega
    clear hN
    refine ⟨not_dvd_ZcH6 hZ hNp, ?_⟩
    clear hZ
    des_unfold; omega
  have : (zHLBcap design adm).kap N p = zHvalCap design N p := by
    simp [zHLBcap, NullityLB.ofWindow, hA]
  rw [← this]
  exact le_max_right _ _

theorem zk_nc {N p : ℕ} (hN : ZcH6 + 1000 ≤ N) (hp : p.Prime) (h1 : 15 * N ≤ p) (h2 : 78 * N ≤ 5 * p)
    (h3 : 5 * p ≤ 83 * N) :
    zHval design N p ≤ (zHLB design adm).kap N p := by
  have hA : zHApp design N p := by
    have hZ : ZcH6 ≤ N := Nat.le_trans (Nat.le_add_right _ _) hN
    have h1000 : 1000 ≤ N := Nat.le_trans (Nat.le_add_left _ _) hN
    have hNp : N < p := by clear hN hZ; omega
    clear hN
    refine ⟨not_dvd_ZcH' hZ hNp, ?_⟩
    clear hZ
    des_unfold; omega
  have : (zHLBnc design adm).kap N p = zHval design N p := by
    simp [zHLBnc, NullityLB.ofWindow, hA]
  rw [← this]
  exact le_max_left _ _

/-- Cleared value of the cap formula and of the no-cap formula, as one statement. -/
theorem zcell_lo {N p : ℕ} (hN : ZcH6 + 1000 ≤ N) (hp : p.Prime) (h1 : 151435 * N < 10000 * p)
    (h2 : 5 * p ≤ 78 * N) :
    (-106 : ℤ) * N + 7 * p ≤ 2 * (((zHLB design adm).kap N p : ℕ) + 2 : ℤ) := by
  rcases le_or_gt (5 * p + 1) (78 * N) with h | h
  · have hk := zk_cap hN hp (by omega) h
    dsimp only [zHvalCap] at hk
    des_unfold at hk
    omega
  · exfalso
    have h5 : 5 * p = 78 * N := by omega
    have h2d : 2 ∣ p := by omega
    rcases hp.eq_one_or_self_of_dvd 2 h2d with h | h <;> omega

theorem zcell_mid {N p : ℕ} (hN : ZcH6 + 1000 ≤ N) (hp : p.Prime) (h1 : 78 * N < 5 * p)
    (h2 : p ≤ 16 * N) :
    (50 : ℤ) * N + (-3) * p ≤ 2 * (((zHLB design adm).kap N p : ℕ) + 2 : ℤ) := by
  have hk := zk_nc hN hp (by omega) (by omega) (by omega)
  dsimp only [zHval] at hk
  des_unfold at hk
  omega

theorem zcell_hi {N p : ℕ} (hN : ZcH6 + 1000 ≤ N) (hp : p.Prime) (h1 : 16 * N < p)
    (h2 : 50 * p ≤ 809 * N) :
    (146 : ℤ) * N + (-9) * p ≤ 2 * (((zHLB design adm).kap N p : ℕ) + 2 : ℤ) := by
  have hk := zk_nc hN hp (by omega) (by omega) (by omega)
  dsimp only [zHval] at hk
  des_unfold at hk
  omega

/-- The three Z windows (tent of Law_H (4)): `K = 3.5 x - 53`, `25 - 1.5 x`, `73 - 4.5 x`. -/
def zWins : List KapWindow :=
  [cw (151435 / 10000 : ℝ) (78 / 5 : ℝ) (-53 : ℝ) (7 / 2 : ℝ),
   cw (78 / 5 : ℝ) (16 : ℝ) (25 : ℝ) (-3 / 2 : ℝ),
   cw (16 : ℝ) (809 / 50 : ℝ) (73 : ℝ) (-9 / 2 : ℝ)]

theorem zWins_cert : ∀ w ∈ zWins, WinCert (zHLB design adm) w := by
  intro w hw
  simp only [zWins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact wincert_cw (zHLB design adm) (na := 151435) (da := 10000) (nb := 78) (db := 5) (A := -106) (B := 7)
      (d := 2) (N0 := ZcH6 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => zcell_lo hN hp h1 (by omega)
  · exact wincert_cw (zHLB design adm) (na := 78) (da := 5) (nb := 16) (db := 1) (A := 50) (B := -3)
      (d := 2) (N0 := ZcH6 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => zcell_mid hN hp h1 (by omega)
  · exact wincert_cw (zHLB design adm) (na := 16) (da := 1) (nb := 809) (db := 50) (A := 146) (B := -9)
      (d := 2) (N0 := ZcH6 + 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      fun N p hN hp h1 h2 => zcell_hi hN hp (by omega) h2

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
