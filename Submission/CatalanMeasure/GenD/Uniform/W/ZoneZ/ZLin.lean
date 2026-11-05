module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat6
@[expose] public section
set_option Elab.async false

/-!
# Linear functionals on the parameter space

`ZPar p hp = F^{hp+1} × F^{hp+1} × F^{hp} × F^{hp}` (parameters `τ1 τ2 σ1 σ2`) and the linear maps
`seqL c r` (coefficient sequences), `dotL`, and the atom data map `atomData`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The parameter space. -/
abbrev ZPar (p hp : ℕ) : Type :=
  (Fin (hp + 1) → ZMod p) × (Fin (hp + 1) → ZMod p) × (Fin hp → ZMod p) × (Fin hp → ZMod p)

/-- `τ ↦ π[e]` as a linear map. -/
def piLin (P : Parameters) (N p : ℕ) [Fact p.Prime] {D : ℕ} (e : ℕ) :
    (Fin D → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ d : Fin D, (zpLam P N p d).coeff e • (LinearMap.proj d : (Fin D → ZMod p) →ₗ[ZMod p] ZMod p)

def laLin (P : Parameters) (N p : ℕ) [Fact p.Prime] {D : ℕ} (e : ℕ) :
    (Fin D → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ d : Fin D, (zaLam P N p d).coeff e • (LinearMap.proj d : (Fin D → ZMod p) →ₗ[ZMod p] ZMod p)

theorem piLin_apply {D : ℕ} (e : ℕ) (τ : Fin D → ZMod p) :
    piLin P N p e τ = piSeq P N p τ e := by
  simp [piLin, piSeq, LinearMap.sum_apply]

theorem laLin_apply {D : ℕ} (e : ℕ) (σ : Fin D → ZMod p) :
    laLin P N p e σ = laSeq P N p σ e := by
  simp [laLin, laSeq, LinearMap.sum_apply]

/-- `σ ↦ Aext σ` as a linear map. -/
def AextL (p hp : ℕ) [Fact p.Prime] : (Fin hp → ZMod p) →ₗ[ZMod p] (Fin (hp + 1) → ZMod p) :=
  LinearMap.pi fun δ => Fin.cases (0 : (Fin hp → ZMod p) →ₗ[ZMod p] ZMod p)
    (fun j => (LinearMap.proj j : (Fin hp → ZMod p) →ₗ[ZMod p] ZMod p)) δ

theorem AextL_apply {hp : ℕ} (σ : Fin hp → ZMod p) : AextL p hp σ = Aext σ := by
  funext δ
  refine Fin.cases ?_ (fun j => ?_) δ <;> simp [AextL, Aext]

variable {hp : ℕ}

/-- The four coefficient sequences as linear maps on `ZPar`. -/
def seqL (P : Parameters) (N p hp : ℕ) [Fact p.Prime] (c : ℕ) (r : ℕ) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  match c with
  | 0 => (piLin P N p (r + p)).comp (LinearMap.fst _ _ _)
  | 1 => (piLin P N p (r + p)).comp ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
  | 2 => (laLin P N p r).comp ((AextL p hp).comp ((LinearMap.fst _ _ _).comp
      ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))))
  | 3 => (laLin P N p r).comp ((AextL p hp).comp ((LinearMap.snd _ _ _).comp
      ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))))
  | _ => 0

/-- `Σ_c v_c seq_c[r]` as a linear map. -/
def dotL (P : Parameters) (N p hp : ℕ) [Fact p.Prime] (v : ℕ → ZMod p) (r : ℕ) :
    ZPar p hp →ₗ[ZMod p] ZMod p :=
  ∑ c ∈ Finset.range 4, v c • seqL P N p hp c r

theorem dotL_apply (v : ℕ → ZMod p) (r : ℕ) (a : ZPar p hp) :
    dotL P N p hp v r a = dotc v (piSeq P N p a.1) (piSeq P N p a.2.1)
      (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) p r := by
  simp only [dotL, dotc, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  have : c < 4 := Finset.mem_range.mp hc
  interval_cases c <;> simp [seqL, seqc, piLin_apply, laLin_apply, AextL_apply]

/-- The fold `π1[r] + π1[r+p]` as a linear map. -/
def foldL (P : Parameters) (N p hp : ℕ) [Fact p.Prime] (r : ℕ) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  (piLin P N p r).comp (LinearMap.fst _ _ _) + (piLin P N p (r + p)).comp (LinearMap.fst _ _ _)

theorem foldL_apply (r : ℕ) (a : ZPar p hp) :
    foldL P N p hp r a = piSeq P N p a.1 r + piSeq P N p a.1 (r + p) := by
  simp [foldL, piLin_apply]

/-- `π1[r]` as a linear map. -/
def pi1L (P : Parameters) (N p hp : ℕ) [Fact p.Prime] (r : ℕ) : ZPar p hp →ₗ[ZMod p] ZMod p :=
  (piLin P N p r).comp (LinearMap.fst _ _ _)

theorem pi1L_apply (r : ℕ) (a : ZPar p hp) : pi1L P N p hp r a = piSeq P N p a.1 r := by
  simp [pi1L, piLin_apply]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
