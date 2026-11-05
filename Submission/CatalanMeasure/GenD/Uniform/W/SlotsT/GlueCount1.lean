module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueResp3
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax5
@[expose] public section
set_option Elab.async false

/-!
# The overflow-below family: conditions, kernel, injectivity

Free space `Fr = (Fin m → Fin D1 → F_p) × (Fin m → Fin (D1+1) → F_p)` of slot-coefficient vectors
`(σ_i, τ_i)`.  `Fr.cond` are the jet / glue conditions on the polynomial pairs
`(lamPoly σ_i, pPoly τ_i)` (`η - p + 1 + elo` per profile) and the missing-row conditions.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Coordinate `σ_{i,d}`. -/
def cS (p D1 m : ℕ) [Fact p.Prime] (i : Fin m) (d : Fin D1) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj d : (Fin D1 → ZMod p) →ₗ[ZMod p] ZMod p).comp
    ((LinearMap.proj i : (Fin m → Fin D1 → ZMod p) →ₗ[ZMod p] (Fin D1 → ZMod p)).comp
      (LinearMap.fst _ _ _))

/-- Coordinate `τ_{i,d}`. -/
def cT (p D1 m : ℕ) [Fact p.Prime] (i : Fin m) (d : Fin (D1 + 1)) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj d : (Fin (D1 + 1) → ZMod p) →ₗ[ZMod p] ZMod p).comp
    ((LinearMap.proj i : (Fin m → Fin (D1 + 1) → ZMod p) →ₗ[ZMod p] (Fin (D1 + 1) → ZMod p)).comp
      (LinearMap.snd _ _ _))

/-- `a ↦ (lamPoly σ_i).coeff e`. -/
def lamL (P : Parameters) (N p D1 m : ℕ) [Fact p.Prime] (i : Fin m) (e : ℕ) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p] ZMod p :=
  ∑ d : Fin D1, (Thin.lam P N p (d : ℕ)).coeff e • cS p D1 m i d

/-- `a ↦ (pPoly τ_i).coeff e`. -/
def pL (P : Parameters) (N p D1 m : ℕ) [Fact p.Prime] (i : Fin m) (e : ℕ) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p] ZMod p :=
  ∑ d : Fin (D1 + 1), (tpLam P N p (d : ℕ)).coeff e • cT p D1 m i d

theorem lamL_apply {D1 m : ℕ} (i : Fin m) (e : ℕ)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) :
    lamL P N p D1 m i e a = (lamPoly P N p (a.1 i)).coeff e := by
  rw [lamPoly_coeff]
  simp [lamL, cS, LinearMap.sum_apply, mul_comm]

theorem pL_apply {D1 m : ℕ} (i : Fin m) (e : ℕ)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) :
    pL P N p D1 m i e a = (pPoly P N p (a.2 i)).coeff e := by
  rw [pPoly_coeff]
  simp [pL, cT, LinearMap.sum_apply, mul_comm]

/-- Index set of the polynomial conditions: glue `(e, true)`, `e ≤ η - p`, and `(e, false)`, `e < elo`. -/
def glueIdx (η p elo : ℕ) : Finset (ℕ × Bool) :=
  (Finset.range (η - p + 1) ×ˢ {true}) ∪ (Finset.range elo ×ˢ {false})

theorem glueIdx_card (η p elo : ℕ) : (glueIdx η p elo).card = (η - p + 1) + elo := by
  unfold glueIdx
  rw [Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_product, Finset.mem_singleton] at hx hy
    rw [hx.2] at hy; simp at hy

/-- Polynomial (jet and glue) conditions. -/
def glueCond (P : Parameters) (N p D1 m η elo : ℕ) [Fact p.Prime] :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p]
      (Fin m → (glueIdx η p elo → ZMod p)) :=
  LinearMap.pi fun i : Fin m => LinearMap.pi fun c : glueIdx η p elo =>
    if c.1.2 then lamL P N p D1 m i c.1.1 - pL P N p D1 m i c.1.1 else pL P N p D1 m i c.1.1

/-- Missing-row conditions of the relaxed domain. -/
def virtCond (P : Parameters) (N p K D1 m : ℕ) (k0 : ℤ) [Fact p.Prime] (y u : Fin m → Fin K → ZMod p) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p]
      ((mmP P N p K D1 k0 → ZMod p) × ((mmM P N p K D1 k0 → ZMod p) × (mm0 P N p K k0 → ZMod p))) :=
  LinearMap.prod
    (LinearMap.pi fun c : mmP P N p K D1 k0 =>
      ∑ i : Fin m, (y i c.1.2 • cS p D1 m i c.1.1 + u i c.1.2 • cT p D1 m i c.1.1.succ))
    (LinearMap.prod
      (LinearMap.pi fun c : mmM P N p K D1 k0 =>
        ∑ i : Fin m, (u i c.1.2 • cT p D1 m i c.1.1.succ - y i c.1.2 • cS p D1 m i c.1.1))
      (LinearMap.pi fun c : mm0 P N p K k0 => ∑ i : Fin m, u i c.1 • cT p D1 m i 0))

/-- All conditions. -/
def totalCond (P : Parameters) (N p K D1 m η elo : ℕ) (k0 : ℤ) [Fact p.Prime]
    (y u : Fin m → Fin K → ZMod p) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p]
      ((Fin m → (glueIdx η p elo → ZMod p)) ×
        ((mmP P N p K D1 k0 → ZMod p) × ((mmM P N p K D1 k0 → ZMod p) × (mm0 P N p K k0 → ZMod p)))) :=
  LinearMap.prod (glueCond P N p D1 m η elo) (virtCond P N p K D1 m k0 y u)

/-- The kernel has the expected dimension. -/
theorem finrank_ker_totalCond (K D1 m η elo : ℕ) (k0 : ℤ) (y u : Fin m → Fin K → ZMod p) :
    m * D1 + m * (D1 + 1) ≤
      finrank (ZMod p) (LinearMap.ker (totalCond P N p K D1 m η elo k0 y u)) +
        (m * ((η - p + 1) + elo) + mixMiss P N p K D1 k0) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (totalCond P N p K D1 m η elo k0 y u)
  have h2 := Submodule.finrank_le (LinearMap.range (totalCond P N p K D1 m η elo k0 y u))
  have h3 : finrank (ZMod p) ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) =
      m * D1 + m * (D1 + 1) := by
    rw [Module.finrank_prod]; simp [Module.finrank_pi_fintype]
  have h4 : finrank (ZMod p) ((Fin m → (glueIdx η p elo → ZMod p)) ×
        ((mmP P N p K D1 k0 → ZMod p) × ((mmM P N p K D1 k0 → ZMod p) × (mm0 P N p K k0 → ZMod p)))) =
      m * ((η - p + 1) + elo) + mixMiss P N p K D1 k0 := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, glueIdx_card, mixMiss, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Module.finrank_self]
    ring
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
