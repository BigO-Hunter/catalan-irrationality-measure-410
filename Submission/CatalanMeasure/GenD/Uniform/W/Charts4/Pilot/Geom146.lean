module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Hdom
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146Arith
public import Submission.CatalanMeasure.GenD.D58.OddProfile
@[expose] public section
set_option Elab.async false

/-!
# Block geometry of D58 on the L0146 window (6, 152/25]

`k0 = -1`, `k1 = 8`, `b = 10` blocks, `ja = p - 5N`, `rho = 53N - 1 - 8p`, `a_h = 0`, `r_h = 3N`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.D58.Odd
noncomputable section

theorem design_n (N : ℕ) : design.n N = 58 * N := rfl
theorem design_g (N : ℕ) : design.g N = 5 * N := rfl
theorem design_h (N : ℕ) : design.h N = 3 * N := rfl

theorem geom_k0 {N p : ℕ} (h : Win N p) : gk0 (design.g N) p = -1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : (0 : ℤ) < p := by omega
  unfold gk0
  rw [design_g]
  exact ((Int.ediv_emod_unique (r := (p : ℤ) - 5 * N) hp).mpr ⟨by push_cast; ring, by omega, by omega⟩).1

theorem geom_k1 {N p : ℕ} (h : Win N p) : gk1 (design.n N) (design.g N) p = 8 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : (0 : ℤ) < p := by omega
  unfold gk1
  rw [design_n, design_g]
  exact ((Int.ediv_emod_unique (r := 53 * (N : ℤ) - 1 - 8 * p) hp).mpr ⟨by push_cast; ring, by omega, by omega⟩).1

theorem geom_b {N p : ℕ} (h : Win N p) : gb (design.n N) (design.g N) p = 10 := by
  have := geom_k0 h; have := geom_k1 h
  unfold gb; rw [‹gk1 _ _ _ = 8›, ‹gk0 _ _ = -1›]; rfl

theorem geom_ja {N p : ℕ} (h : Win N p) : gja (design.g N) p = p - 5 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold gja; rw [geom_k0 ⟨h1, h2, h3, h4⟩, design_g]; omega

theorem geom_rho {N p : ℕ} (h : Win N p) : grho (design.n N) (design.g N) p = 53 * N - 1 - 8 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold grho; rw [geom_k1 ⟨h1, h2, h3, h4⟩, design_n, design_g]; omega

theorem geom_hmod {N p : ℕ} (h : Win N p) : design.h N % p = 3 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [design_h]; exact Nat.mod_eq_of_lt (by omega)

theorem geom_hdiv {N p : ℕ} (h : Win N p) : design.h N / p = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [design_h]; exact Nat.div_eq_of_lt (by omega)

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
