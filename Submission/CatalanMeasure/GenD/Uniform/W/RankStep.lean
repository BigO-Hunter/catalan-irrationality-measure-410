module
public import Submission.CatalanMeasure.GenD.Uniform.W.Jets
public import Submission.CatalanCore.Uniform.Content.RankCertificate
public import Submission.OAI.NumberTheory.Catalan.FiniteMatrices.FixedDeterminantGoodPrimes
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Data.ZMod.Basic
@[expose] public section
set_option Elab.async false

/-!
# Rank steps for Theorem W

Lower bounds on ranks are needed only where a rank enters with a positive sign (Theorem U's
`ρ`, Theorem M's `det = -1291/96`).  They come from one explicit nonzero minor of a fixed
matrix:

* `int_minor_rank` : an integer matrix whose `r × r` minor is nonzero in `K` has rank `≥ r`
  over `K`;
* `int_minor_unit` : the minor is nonzero mod `p` when `p ∤ det`;
* `rat_minor_rank` : a rational matrix, reduced by `palindromicRatResidue`, has rank `≥ r`
  whenever the minor's entries are `p`-integral and `p` does not divide the numerator of its
  determinant.

Upper bounds (the jet costs) are plain counts (`rank_le_width`, `rank_jetMap_le`).

`mixed_proj_finrank` is the projection count of Theorem U:
`dim proj_X {(x,y) : α x = 0, β x + Γ y = 0} ≥ dim X - n_C - (n_mix - rank Γ)`,
and `exists_section` gives a subspace on which the projection is injective with the full
projected dimension.
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module Matrix CatalanCore.Uniform.Content OAI.InternalCatalan
noncomputable section

section Minor
variable {K : Type*} [Field K]

/-- An `r × r` minor nonzero in `K` forces rank `≥ r`. -/
theorem int_minor_rank {m s r : ℕ} (A : Matrix (Fin m) (Fin s) ℤ) (e : Fin r → Fin m)
    (f : Fin r → Fin s) (hdet : ((A.submatrix e f).det : K) ≠ 0) :
    r ≤ (castMatrix K A).rank := by
  have hc : (castMatrix K A).submatrix e f = (Int.castRingHom K).mapMatrix (A.submatrix e f) := by
    ext i j
    rfl
  have hd : ((castMatrix K A).submatrix e f).det ≠ 0 := by
    rw [hc, ← RingHom.map_det]
    exact hdet
  have h1 := Matrix.rank_of_det_ne_zero hd
  have h2 := Matrix.rank_submatrix_le (castMatrix K A) e f
  rw [h1, Fintype.card_fin] at h2
  exact h2

/-- A fixed integer minor survives every prime not dividing it. -/
theorem int_minor_unit {p : ℕ} [Fact p.Prime] (d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    ((d : ℤ) : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

end Minor

/-- The residue matrix of a rational matrix. -/
def residueMat (p : ℕ) [Fact p.Prime] {m s : ℕ} (Q : Matrix (Fin m) (Fin s) ℚ) :
    Matrix (Fin m) (Fin s) (ZMod p) :=
  fun i j => palindromicRatResidue p (Q i j)

/-- **Fixed rational minor.**  If the `r × r` minor of `Q` on rows `e`, columns `f` has
`p`-integral entries and `p` does not divide the numerator of its determinant, then the residue
matrix has rank `≥ r`.  (The exceptional primes are the divisors of one explicit minor and its
entry denominators.) -/
theorem rat_minor_rank {p : ℕ} [Fact p.Prime] {m s r : ℕ} (Q : Matrix (Fin m) (Fin s) ℚ)
    (e : Fin r → Fin m) (f : Fin r → Fin s)
    (hentry : ∀ i j, ((Q (e i) (f j)).den : ZMod p) ≠ 0)
    (hnum : ¬ (p : ℤ) ∣ (Q.submatrix e f).det.num) :
    r ≤ (residueMat p Q).rank := by
  have hdet := palindromicRatResidue_det (p := p) (Q.submatrix e f) (fun i j => hentry i j)
  have hne : palindromicRatResidue p (Q.submatrix e f).det ≠ 0 := by
    unfold palindromicRatResidue
    exact div_ne_zero (int_minor_unit _ hnum) hdet.1
  rw [hdet.2] at hne
  have h1 := Matrix.rank_of_det_ne_zero hne
  have h2 := Matrix.rank_submatrix_le (residueMat p Q) e f
  have hs : (residueMat p Q).submatrix e f =
      (fun i j => palindromicRatResidue p ((Q.submatrix e f) i j)) := by
    ext i j
    rfl
  rw [hs, h1, Fintype.card_fin] at h2
  exact h2

section Proj
variable {K : Type*} [Field K]
variable {X Y : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

/-- The mixed condition map `(x,y) ↦ (α x, β x + Γ y)` of Theorem U. -/
def mixedMap {nC nM : ℕ} (α : X →ₗ[K] (Fin nC → K)) (β : X →ₗ[K] (Fin nM → K))
    (Γ : Y →ₗ[K] (Fin nM → K)) : (X × Y) →ₗ[K] (Fin nC → K) × (Fin nM → K) :=
  (α.comp (LinearMap.fst K X Y)).prod
    (β.comp (LinearMap.fst K X Y) + Γ.comp (LinearMap.snd K X Y))

/-- **Projection count.**  The projection of the mixed kernel to `X` has dimension at least
`dim X - n_C - (n_mix - rank Γ)`. -/
theorem mixed_proj_finrank {nC nM : ℕ} (α : X →ₗ[K] (Fin nC → K)) (β : X →ₗ[K] (Fin nM → K))
    (Γ : Y →ₗ[K] (Fin nM → K)) :
    finrank K X - nC - (nM - finrank K (LinearMap.range Γ)) ≤
      finrank K (Submodule.map (LinearMap.fst K X Y) (LinearMap.ker (mixedMap α β Γ))) := by
  let φ : X →ₗ[K] (Fin nC → K) × ((Fin nM → K) ⧸ LinearMap.range Γ) :=
    α.prod ((LinearMap.range Γ).mkQ.comp β)
  have hle : LinearMap.ker φ ≤
      Submodule.map (LinearMap.fst K X Y) (LinearMap.ker (mixedMap α β Γ)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : α x = 0 := congrArg Prod.fst hx
    have h2 : (LinearMap.range Γ).mkQ (β x) = 0 := congrArg Prod.snd hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    obtain ⟨y, hy⟩ := h2
    refine ⟨(x, -y), ?_, rfl⟩
    show (x, -y) ∈ LinearMap.ker (mixedMap α β Γ)
    rw [LinearMap.mem_ker]
    simp [mixedMap, h1, hy]
  have hk := φ.finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range φ)
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range Γ)
  rw [Module.finrank_prod, Module.finrank_fin_fun] at hr
  rw [Module.finrank_fin_fun] at hq
  have hm := Submodule.finrank_mono hle
  omega

/-- A linear map from a finite-dimensional space restricts injectively to a subspace with the
full image dimension. -/
theorem exists_section {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (f : U →ₗ[K] X) :
    ∃ V : Submodule K U, finrank K V = finrank K (LinearMap.range f) ∧
      Function.Injective (f.comp V.subtype) := by
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  have hgi : Function.Injective g := by
    intro a b hab
    have := congrArg f.rangeRestrict hab
    rwa [← LinearMap.comp_apply, hg, ← LinearMap.comp_apply, hg] at this
  refine ⟨LinearMap.range g, LinearMap.finrank_range_of_inj hgi, ?_⟩
  intro u v huv
  obtain ⟨a, ha⟩ := u.2
  obtain ⟨b, hb⟩ := v.2
  apply Subtype.ext
  have hf : f (g a) = f (g b) := by rw [ha, hb]; exact huv
  have h : f.rangeRestrict (g a) = f.rangeRestrict (g b) := Subtype.ext hf
  have e1 := LinearMap.congr_fun hg a
  have e2 := LinearMap.congr_fun hg b
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at e1 e2
  have hab : a = b := by rw [← e1, ← e2, h]
  rw [← ha, ← hb, hab]

end Proj

end
end CatalanMeasure.GenD.Uniform.W
