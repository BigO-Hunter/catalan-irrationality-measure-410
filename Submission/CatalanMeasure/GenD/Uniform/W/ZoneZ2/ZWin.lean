module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZLLB5
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Fam
@[expose] public section
set_option Elab.async false

/-!
# Law_L(4): piecewise-linear (closed) form and window certificates (G2h)

`zLval5_closed`: on the window `zLApp5` the bound is the *affine* function
`2 zLval ≥ 11 p - 2 (n + b + q + g) - 1` (no truncation occurs).  `zLLB_kap_ge` is the bound for the
family `zLLB`, `zL_winCert` the `WinCert` certificate for any affine window `cw a b c0 c1` below
`(11/2) x - (n0+b0+q0+g0)` at the design `D58`, ready for `Ledger3.growth_of_families`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- **Closed (piecewise-linear) form of Law_L(4).**  With `T = H - 5p = t + 1` (a linear function of
`N, p`):
`2 zLval ≥ 11 p - 2 (n + b + q + g) - 1 + 2 (min 0 (L - 5p) + min 0 (T - b) + min 0 (h + hp - T))`;
the three `min` terms vanish in the interior regime `5p ≤ L`, `b ≤ T ≤ h + (p-1)/2`
(there `2 zLval ≥ 11 p - 2 (n + b + q + g) - 1`, i.e. `N_L = (11/2) p - (n+b+q+g) - 1/2`). -/
theorem zLval5_closed {P : Parameters} {N p : ℕ} (hodd : p % 2 = 1) (hA : zLApp5 P N p) :
    (11 * p : ℤ) + 2 * (min 0 ((P.L N : ℤ) - 5 * p) + min 0 ((P.H N : ℤ) - 5 * p - P.b N) +
        min 0 ((P.h N : ℤ) + ((p - 1) / 2 : ℕ) - ((P.H N : ℤ) - 5 * p))) ≤
      2 * (zLval5 P N p : ℤ) + 2 * ((P.n N : ℤ) + P.b N + P.q N + P.g N) + 1 := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hA
  have hHL : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
  have hL : P.L N = P.n N + P.b N + P.q N := rfl
  unfold zLval5
  simp only [Nat.sub_zero]
  have hp2 : 2 * ((p - 1) / 2) + 1 = p := by omega
  generalize (p - 1) / 2 = hp at *
  omega

/-- The family value: `zLLB.kap = zLval5` on the window. -/
theorem zLLB_kap_eq {P : Parameters} (hP : Admissible P) {N p : ℕ} (hA : zLApp5 P N p) :
    (zLLB P hP).kap N p = zLval5 P N p := by
  unfold zLLB
  simp only [CatalanMeasure.GenD.NullityLB.ofWindow]
  simp [hA]

theorem zLLB_kap_ge {P : Parameters} (hP : Admissible P) {N p : ℕ} (hodd : p % 2 = 1)
    (hA : zLApp5 P N p) :
    (11 * p : ℤ) + 2 * (min 0 ((P.L N : ℤ) - 5 * p) + min 0 ((P.H N : ℤ) - 5 * p - P.b N) +
        min 0 ((P.h N : ℤ) + ((p - 1) / 2 : ℕ) - ((P.H N : ℤ) - 5 * p))) ≤
      2 * ((zLLB P hP).kap N p : ℤ) + 2 * ((P.n N : ℤ) + P.b N + P.q N + P.g N) + 1 := by
  rw [zLLB_kap_eq hP hA]
  exact zLval5_closed hodd hA

theorem ZcL6_pos : 0 < ZcL6 := by
  unfold ZcL6 ZcL'
  exact Nat.lcm_pos (Nat.lcm_pos (by unfold ZcL; decide +kernel)
    (Nat.lcm_pos (by exact Nat.pos_of_ne_zero (by simpa using DqUL_num_ne))
      (by exact Nat.pos_of_ne_zero (by simpa using DqYL_num_ne)))) (by norm_num)

theorem not_dvd_ZcL6 {p : ℕ} (hp : ZcL6 < p) : ¬ p ∣ ZcL6 := fun h =>
  absurd (Nat.le_of_dvd ZcL6_pos h) (by omega)

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
