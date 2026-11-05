module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCount
@[expose] public section
set_option Elab.async false

/-!
# Valuation maps
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime]

/-- `τ ↦ Σ τ_d T_d` as a linear map. -/
def tpolyL (p D : ℕ) [Fact p.Prime] : (Fin D → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ d : Fin D, (LinearMap.proj d : (Fin D → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (Chebyshev.T (ZMod p) ((d : ℕ) : ℤ))

theorem tpolyL_apply {D : ℕ} (τ : Fin D → ZMod p) : tpolyL p D τ = tpoly τ := by
  simp [tpolyL, tpoly, LinearMap.sum_apply, smul_eq_C_mul]

theorem monic_Xm1 (e : ℕ) : (((X - 1) ^ e : (ZMod p)[X])).Monic := by
  have : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
  rw [this]; exact (monic_X_sub_C 1).pow e

/-- Valuation map: `τ ↦ tpoly τ mod (X-1)^e`, valued in `degreeLT e`. -/
def valL (p D e : ℕ) [Fact p.Prime] : (Fin D → ZMod p) →ₗ[ZMod p] (degreeLT (ZMod p) e) :=
  LinearMap.codRestrict (degreeLT (ZMod p) e)
    ((modByMonicHom ((X - 1) ^ e : (ZMod p)[X])).comp (tpolyL p D))
    (fun τ => by
      rw [mem_degreeLT]
      have h := degree_modByMonic_lt (tpoly τ) (monic_Xm1 (p := p) e)
      have hd : (((X - 1) ^ e : (ZMod p)[X])).degree = (e : WithBot ℕ) := by
        have : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
        rw [this, degree_pow, degree_X_sub_C]; simp
      simpa [modByMonicHom, tpolyL_apply, hd] using h)

theorem valL_eq_zero_iff {D : ℕ} (e : ℕ) (τ : Fin D → ZMod p) :
    valL p D e τ = 0 ↔ ((X - 1) ^ e : (ZMod p)[X]) ∣ tpoly τ := by
  rw [← Subtype.coe_inj]
  have h := modByMonic_eq_zero_iff_dvd (monic_Xm1 (p := p) e) (p := tpoly τ)
  simpa [valL, modByMonicHom, tpolyL_apply] using h

theorem finrank_degreeLT (e : ℕ) : finrank (ZMod p) (degreeLT (ZMod p) e) = e := by
  rw [(degreeLTEquiv (ZMod p) e).finrank_eq]; simp

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
