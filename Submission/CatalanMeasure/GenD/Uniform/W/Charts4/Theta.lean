module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Slots
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.TilingUT
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.Mono
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.FrobeniusSplit
@[expose] public section
set_option Elab.async false

/-!
# The forward map `Θ` : physical rows -> monomial atoms (four-point frame)

For physical rows `c`, the tiling coordinates `t(c)` (extension by zero, inverse tiling), the slot
polynomials `Λ_τ = (X-1)^{r_h} Q_τ` (`τ` = A_k, C_k, centre) and their Frobenius splits
`Λ = F + (Y-1) E` give the monomial atoms `Θ c e idx = coeff_e` of the corresponding `F`/`E`.
The profile maps `Ty, Gy` carry the Chebyshev block coefficients and `(Y-1)^{a_h}`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Number of blocks, first block, for the design at `(N, p)`. -/
abbrev bN (P : Parameters) (N p : ℕ) : ℕ := gb (P.n N) (P.g N) p
abbrev k0N (P : Parameters) (N p : ℕ) : ℤ := gk0 (P.g N) p

/-- Coordinates of the tiling of the physical rows. -/
def tL (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) :
    (Fin (P.n N) → Fp) →ₗ[Fp] TilingCoordinates (K := Fp) (bN P N p) ((p - 1) / 2) :=
  (physicalTilingEquiv (bN P N p) ((p - 1) / 2) p (native_half_identity hp2)
    (native_two_ne_zero hp2)).symm.toLinearMap.comp (rowsExt (P.n N) (P.g N) p (Fact.out : p.Prime).pos hn)

/-- `QA` as a linear map of the tiling coordinates. -/
def qaL {b : ℕ} (k : Fin b) : TilingCoordinates (K := Fp) b ((p - 1) / 2) →ₗ[Fp] Fp[X] :=
  ((LinearMap.proj k.succ : (Fin (b + 1) → Fp) →ₗ[Fp] Fp).comp (LinearMap.snd Fp _ _)).smulRight
      (nativeCenter (p := p)) +
    ∑ j : Fin ((p - 1) / 2),
      ((LinearMap.proj (finProdFinEquiv (k, j)) : (Fin (b * ((p - 1) / 2)) → Fp) →ₗ[Fp] Fp).comp
        ((LinearMap.fst Fp _ _).comp (LinearMap.fst Fp _ _))).smulRight
        (nativePlus (p := p) ((j : ℤ) + 1))

def qcL {b : ℕ} (k : Fin b) : TilingCoordinates (K := Fp) b ((p - 1) / 2) →ₗ[Fp] Fp[X] :=
  ∑ j : Fin ((p - 1) / 2),
    ((LinearMap.proj (finProdFinEquiv (k, j)) : (Fin (b * ((p - 1) / 2)) → Fp) →ₗ[Fp] Fp).comp
      ((LinearMap.snd Fp _ _).comp (LinearMap.fst Fp _ _))).smulRight
      (nativeMinus (p := p) ((j : ℤ) + 1))

def zL {b : ℕ} : TilingCoordinates (K := Fp) b ((p - 1) / 2) →ₗ[Fp] Fp[X] :=
  ((LinearMap.proj 0 : (Fin (b + 1) → Fp) →ₗ[Fp] Fp).comp (LinearMap.snd Fp _ _)).smulRight
    (nativeCenter (p := p))

theorem qaL_apply {b : ℕ} (k : Fin b) (t : TilingCoordinates (K := Fp) b ((p - 1) / 2)) :
    qaL k t = QA t k := by
  simp [qaL, QA, LinearMap.sum_apply]

theorem qcL_apply {b : ℕ} (k : Fin b) (t : TilingCoordinates (K := Fp) b ((p - 1) / 2)) :
    qcL k t = QC t k := by
  simp [qcL, QC, LinearMap.sum_apply]

theorem zL_apply {b : ℕ} (t : TilingCoordinates (K := Fp) b ((p - 1) / 2)) :
    zL t = t.2 0 • nativeCenter (p := p) := by
  simp [zL]

/-- `Frobenius-normalised` remainder power `(X-1)^{h % p}`. -/
def rem (P : Parameters) (N p : ℕ) : (Fp)[X] := (X - 1) ^ (P.h N % p)

def lamA (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (k : Fin (bN P N p)) : (Fin (P.n N) → Fp) →ₗ[Fp] Fp[X] :=
  (LinearMap.mulLeft Fp (rem P N p)).comp ((qaL k).comp (tL hp2 hn))
def lamC (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (k : Fin (bN P N p)) : (Fin (P.n N) → Fp) →ₗ[Fp] Fp[X] :=
  (LinearMap.mulLeft Fp (rem P N p)).comp ((qcL k).comp (tL hp2 hn))
def lamZ (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) : (Fin (P.n N) → Fp) →ₗ[Fp] Fp[X] :=
  (LinearMap.mulLeft Fp (rem P N p)).comp (zL.comp (tL hp2 hn))

/-- The polynomial attached to a coordinate kind. -/
def kindPoly (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex : ℕ} :
    CK (bN P N p) ex → ((Fin (P.n N) → Fp) →ₗ[Fp] Fp[X])
  | .inl (k, u) =>
    match u.val with
    | 0 => (fpart p).comp (lamA hp2 hn k)
    | 1 => (epart p).comp (lamA hp2 hn k)
    | 2 => (fpart p).comp (lamC hp2 hn k)
    | _ => (epart p).comp (lamC hp2 hn k)
  | .inr (.inl z) => if z.val = 0 then (fpart p).comp (lamZ hp2 hn) else (epart p).comp (lamZ hp2 hn)
  | .inr (.inr _) => 0

end
end CatalanMeasure.GenD.Uniform.W.Charts4
