module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLin
@[expose] public section
set_option Elab.async false

/-!
# The condition maps and their ranks

* `vtopL`, `v0L`: the virtual-row functionals of the top block (`δ > rt`) and block `0` (`δ > g`);
* `valL e`: `τ ↦ tpoly τ mod (X-1)^e`, with values in `degreeLT e` (rank `≤ e`);
* `mainL`, `wL`, `d0L`, `dsL`: coefficient functionals of the flatness conditions.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime]

/-- `finrank (ker f) ≥ finrank M - m` for `f : M → F^m`. -/
theorem finrank_ker_ge_pi {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [FiniteDimensional (ZMod p) M]
    {m : ℕ} (f : M →ₗ[ZMod p] (Fin m → ZMod p)) :
    finrank (ZMod p) M - m ≤ finrank (ZMod p) (LinearMap.ker f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank (ZMod p) (LinearMap.range f) ≤ m := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  omega

/-- A coordinate functional of the parameter space: `τ1_δ`, `τ2_δ`, `A1_δ = Aext σ1 δ`, `A2_δ`. -/
def coT1 (p hp : ℕ) [Fact p.Prime] (δ : Fin (hp + 1)) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj δ : (Fin (hp + 1) → ZMod p) →ₗ[ZMod p] ZMod p).comp (LinearMap.fst _ _ _)

def coT2 (p hp : ℕ) [Fact p.Prime] (δ : Fin (hp + 1)) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj δ : (Fin (hp + 1) → ZMod p) →ₗ[ZMod p] ZMod p).comp
    ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))

def coA1 (p hp : ℕ) [Fact p.Prime] (δ : Fin (hp + 1)) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj δ : (Fin (hp + 1) → ZMod p) →ₗ[ZMod p] ZMod p).comp ((AextL p hp).comp
    ((LinearMap.fst _ _ _).comp ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))))

def coA2 (p hp : ℕ) [Fact p.Prime] (δ : Fin (hp + 1)) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj δ : (Fin (hp + 1) → ZMod p) →ₗ[ZMod p] ZMod p).comp ((AextL p hp).comp
    ((LinearMap.snd _ _ _).comp ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))))

theorem coT1_apply (δ : Fin (hp + 1)) (a : ZPar p hp) : coT1 p hp δ a = a.1 δ := rfl
theorem coT2_apply (δ : Fin (hp + 1)) (a : ZPar p hp) : coT2 p hp δ a = a.2.1 δ := rfl
theorem coA1_apply (δ : Fin (hp + 1)) (a : ZPar p hp) : coA1 p hp δ a = Aext a.2.2.1 δ := by
  simp [coA1, AextL_apply]
theorem coA2_apply (δ : Fin (hp + 1)) (a : ZPar p hp) : coA2 p hp δ a = Aext a.2.2.2 δ := by
  simp [coA2, AextL_apply]

/-- The block functional `s_δ + sgn · a_δ` of the block `k`. -/
def blkL {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (k : Fin K) (sgn : ZMod p) (δ : Fin (hp + 1)) :
    ZPar p hp →ₗ[ZMod p] ZMod p :=
  u k • coT1 p hp δ + u2 k • coT2 p hp δ + (sgn * y1 k) • coA1 p hp δ + (sgn * y2 k) • coA2 p hp δ

theorem blkL_apply {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (k : Fin K) (sgn : ZMod p)
    (δ : Fin (hp + 1)) (a : ZPar p hp) :
    blkL u u2 y1 y2 k sgn δ a = (u k * a.1 δ + u2 k * a.2.1 δ) +
      sgn * (y1 k * Aext a.2.2.1 δ + y2 k * Aext a.2.2.2 δ) := by
  simp [blkL, coT1_apply, coT2_apply, coA1_apply, coA2_apply]; ring

/-- Index `j < m` ↦ `δ = off + j` in `Fin (hp+1)`, for `off + m ≤ hp + 1`. -/
def idxFin (hp off m : ℕ) (h : off + m ≤ hp + 1) (j : Fin m) : Fin (hp + 1) :=
  ⟨off + j, by have := j.isLt; omega⟩

/-- The virtual-row functionals: top block (`sgn = 1`, `δ = rt+1+j`) and block `0`
(`sgn = -1`, `δ = g+1+j`). -/
def virtL {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (ktop k0 : Fin K) (rt g : ℕ)
    (ht : rt + 1 + (hp - rt) ≤ hp + 1) (hg : g + 1 + (hp - g) ≤ hp + 1) :
    ZPar p hp →ₗ[ZMod p] (Fin (hp - rt) → ZMod p) × (Fin (hp - g) → ZMod p) :=
  LinearMap.prod
    (LinearMap.pi fun j => blkL u u2 y1 y2 ktop 1 (idxFin hp (rt + 1) (hp - rt) ht j))
    (LinearMap.pi fun j => blkL u u2 y1 y2 k0 (-1) (idxFin hp (g + 1) (hp - g) hg j))

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
