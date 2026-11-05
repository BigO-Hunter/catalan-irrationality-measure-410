module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Extract
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open CatalanMeasure.GenD.Uniform.W.Charts4
noncomputable section
variable {N p : ℕ}

theorem wd0 (h : Win N p) : wd N p 0 = (p - 1) / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd1 (h : Win N p) : wd N p 1 = 69 * N - 11 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd2 (h : Win N p) : wd N p 2 = 9 * N - p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd3 (h : Win N p) : wd N p 3 = 3 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd4 (h : Win N p) : wd N p 4 = p - 6 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd5 (h : Win N p) : wd N p 5 = 6 * N - 1 - (p - 1) / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd6 (h : Win N p) : wd N p 6 = 13 * p - 78 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd7 (h : Win N p) : wd N p 7 = 75 * N - 12 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd8 (h : Win N p) : wd N p 8 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]
theorem wd9 (h : Win N p) : wd N p 9 = p - 1 - 5 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega
theorem wd10 (h : Win N p) : wd N p 10 = 8 * p + 1 - 48 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, wInt]; omega

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
