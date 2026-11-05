module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZJPoly
@[expose] public section
set_option Elab.async false

/-!
# The atom map as a linear map, and the virtual-row subspace
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime]

theorem Aext_add (σ σ' : Fin hp → ZMod p) : Aext (σ + σ') = Aext σ + Aext σ' := by
  funext δ; refine Fin.cases ?_ (fun j => ?_) δ <;> simp [Aext]

theorem Aext_smul (c : ZMod p) (σ : Fin hp → ZMod p) : Aext (c • σ) = c • Aext σ := by
  funext δ; refine Fin.cases ?_ (fun j => ?_) δ <;> simp [Aext]

theorem mergeData_add {K D : ℕ} (S A S' A' : Fin D → Fin K → ZMod p) :
    mergeData (S + S') (A + A') = mergeData S A + mergeData S' A' := by
  funext d k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
    refine Fin.addCases (fun a' => ?_) (fun b' => ?_) k
  · simp only [merge_cc, Pi.add_apply]
  · simp only [merge_cn, Pi.add_apply]; ring
  · simp only [merge_nc, Pi.add_apply]; ring
  · simp only [merge_nn, Pi.add_apply]

theorem mergeData_smul {K D : ℕ} (c : ZMod p) (S A : Fin D → Fin K → ZMod p) :
    mergeData (c • S) (c • A) = c • mergeData S A := by
  funext d k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
    refine Fin.addCases (fun a' => ?_) (fun b' => ?_) k
  · simp only [merge_cc, Pi.smul_apply]
  · simp only [merge_cn, Pi.smul_apply]; ring
  · simp only [merge_nc, Pi.smul_apply]; ring
  · simp only [merge_nn, Pi.smul_apply]

theorem Sdata_add {K : ℕ} (u u2 : Fin K → ZMod p) (τ1 τ2 τ1' τ2' : Fin (hp + 1) → ZMod p) :
    Sdata u u2 (τ1 + τ1') (τ2 + τ2') = Sdata u u2 τ1 τ2 + Sdata u u2 τ1' τ2' := by
  funext d k; simp only [Sdata, Pi.add_apply]; ring

theorem Sdata_smul {K : ℕ} (c : ZMod p) (u u2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p) :
    Sdata u u2 (c • τ1) (c • τ2) = c • Sdata u u2 τ1 τ2 := by
  funext d k; simp only [Sdata, Pi.smul_apply, smul_eq_mul]; ring

theorem Adata_add {K : ℕ} (y1 y2 : Fin K → ZMod p) (σ1 σ2 σ1' σ2' : Fin hp → ZMod p) :
    Adata y1 y2 (σ1 + σ1') (σ2 + σ2') = Adata y1 y2 σ1 σ2 + Adata y1 y2 σ1' σ2' := by
  funext d k; simp only [Adata, Aext_add, Pi.add_apply]; ring

theorem Adata_smul {K : ℕ} (c : ZMod p) (y1 y2 : Fin K → ZMod p) (σ1 σ2 : Fin hp → ZMod p) :
    Adata y1 y2 (c • σ1) (c • σ2) = c • Adata y1 y2 σ1 σ2 := by
  funext d k; simp only [Adata, Aext_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- The atom data as a linear map of the parameters. -/
def atomLin {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin ((hp + 1) + (hp + 1)) → Fin (K + K) → ZMod p) where
  toFun a := mergeData (Sdata u u2 a.1 a.2.1) (Adata y1 y2 a.2.2.1 a.2.2.2)
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add]
    rw [Sdata_add, Adata_add, mergeData_add]
  map_smul' c a := by
    show mergeData (Sdata u u2 (c • a.1) (c • a.2.1)) (Adata y1 y2 (c • a.2.2.1) (c • a.2.2.2)) =
      c • mergeData (Sdata u u2 a.1 a.2.1) (Adata y1 y2 a.2.2.1 a.2.2.2)
    rw [Sdata_smul, Adata_smul, mergeData_smul]

theorem atomLin_apply {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) :
    atomLin u u2 y1 y2 a = mergeData (Sdata u u2 a.1 a.2.1) (Adata y1 y2 a.2.2.1 a.2.2.2) := rfl

/-- Injectivity of the parameters-to-data map from the independence of the cell pairs. -/
theorem atomLin_injective {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p)
    (hind1 : ∀ (c1 c2 : ZMod p), (∀ k, c1 * u k + c2 * u2 k = 0) → c1 = 0 ∧ c2 = 0)
    (hind2 : ∀ (c1 c2 : ZMod p), (∀ k, c1 * y1 k + c2 * y2 k = 0) → c1 = 0 ∧ c2 = 0) :
    Function.Injective (atomLin (hp := hp) u u2 y1 y2) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  have h11 : Sdata u u2 a.1 a.2.1 = 0 := by
    have := congrArg (blk11 (hp + 1) (hp + 1) K K) ha
    rw [atomLin_apply, blk11_merge] at this; simpa using this
  have h22 : Adata y1 y2 a.2.2.1 a.2.2.2 = 0 := by
    have := congrArg (blk22 (hp + 1) (hp + 1) K K) ha
    rw [atomLin_apply, blk22_merge] at this; simpa using this
  have hS : ∀ d, a.1 d = 0 ∧ a.2.1 d = 0 := fun d => by
    refine hind1 (a.1 d) (a.2.1 d) fun k => ?_
    have := congrFun (congrFun h11 d) k
    simp only [Sdata, Pi.zero_apply] at this; linear_combination this
  have hA : ∀ d, Aext a.2.2.1 d = 0 ∧ Aext a.2.2.2 d = 0 := fun d => by
    refine hind2 (Aext a.2.2.1 d) (Aext a.2.2.2 d) fun k => ?_
    have := congrFun (congrFun h22 d) k
    simp only [Adata, Pi.zero_apply] at this; linear_combination this
  refine Prod.ext (funext fun d => (hS d).1) (Prod.ext (funext fun d => (hS d).2)
    (Prod.ext (funext fun j => ?_) (funext fun j => ?_)))
  · have := (hA j.succ).1; simpa [Aext] using this
  · have := (hA j.succ).2; simpa [Aext] using this

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
