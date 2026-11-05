module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax6
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTFam
@[expose] public section
set_option Elab.async false

/-!
# Overflow-below (glue) family of Theorem MT: the response

Data: `m` profile pairs `(y_i, u_i)` (T- and T+ profiles) and slot-coefficient vectors
`(σ_i, τ_i)`.  The datum `famData y u (σ,τ)` has T- slot `d` equal to `Σ_i σ_{i,d} y_i` and T+ slot `d`
equal to `Σ_i τ_{i,d} u_i`; the slot polynomials of the pair are
`lamPoly σ_i = Σ_d σ_{i,d} lam_d` and `pPoly τ_i = Σ_d τ_{i,d} P_d`.

`resp_fam` : if the profiles satisfy the J1/J2 equations (`Φ-(J,s;y)=A`, `Φ+'(J,s;u)=B` on the digits
J1 that see the main window, `Φ-(J,s+1;y)+Φ+'(J,s+1;u)=A+B` on the digits J2 that see the overflow
window), and the polynomials satisfy the jet and glue conditions, then the slot response of a column
`J p + ℓ` is `f[η-ℓ] + f[η-p-ℓ]` with `f = Σ_i A_i lam_i + B_i P_i` (the fold of `f` mod `X^p - 1`).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Data of the profile family with slot coefficients `(σ, τ)`. -/
def famData {K D1 m : ℕ} (y u : Fin m → Fin K → ZMod p) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p]
      (Fin (D1 + (D1 + 1)) → Fin (K + K) → ZMod p) where
  toFun στ := Fin.append (fun d : Fin D1 => emb1 K K (∑ i, στ.1 i d • y i))
    (fun d : Fin (D1 + 1) => emb2 K K (∑ i, στ.2 i d • u i))
  map_add' a b := by
    funext d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
      simp [Fin.append_left, Fin.append_right, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
      simp [Fin.append_left, Fin.append_right, smul_smul, Finset.smul_sum, mul_comm]

theorem famData_left {K D1 m : ℕ} (y u : Fin m → Fin K → ZMod p)
    (στ : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) (d : Fin D1) :
    famData y u στ (Fin.castAdd (D1 + 1) d) = emb1 K K (∑ i, στ.1 i d • y i) := by
  simp [famData, Fin.append_left]

theorem famData_right {K D1 m : ℕ} (y u : Fin m → Fin K → ZMod p)
    (στ : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) (d : Fin (D1 + 1)) :
    famData y u στ (Fin.natAdd D1 d) = emb2 K K (∑ i, στ.2 i d • u i) := by
  simp [famData, Fin.append_right]

/-- The T- slot polynomial `Σ_d σ_d lam_d`. -/
def lamPoly (P : Parameters) (N p : ℕ) {D1 : ℕ} (σ : Fin D1 → ZMod p) : (ZMod p)[X] :=
  ∑ d, C (σ d) * Thin.lam P N p (d : ℕ)

/-- The T+ slot polynomial `Σ_d τ_d P_d`. -/
def pPoly (P : Parameters) (N p : ℕ) {D1 : ℕ} (τ : Fin (D1 + 1) → ZMod p) : (ZMod p)[X] :=
  ∑ d, C (τ d) * tpLam P N p (d : ℕ)

theorem lamPoly_coeff {D1 : ℕ} (σ : Fin D1 → ZMod p) (e : ℕ) :
    (lamPoly P N p σ).coeff e = ∑ d, σ d * (Thin.lam P N p (d : ℕ)).coeff e := by
  simp [lamPoly, finset_sum_coeff, coeff_C_mul]

theorem pPoly_coeff {D1 : ℕ} (τ : Fin (D1 + 1) → ZMod p) (e : ℕ) :
    (pPoly P N p τ).coeff e = ∑ d, τ d * (tpLam P N p (d : ℕ)).coeff e := by
  simp [pPoly, finset_sum_coeff, coeff_C_mul]

theorem lamPoly_natDegree_le (hp2 : p ≠ 2) {D1 : ℕ} (σ : Fin D1 → ZMod p) :
    (lamPoly P N p σ).natDegree ≤ P.h N + D1 - 1 := by
  unfold lamPoly
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  have h1 := lam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
  have h2 : (d : ℕ) < D1 := d.isLt
  omega

theorem pPoly_natDegree_le (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) {D1 : ℕ} (σ : Fin (D1 + 1) → ZMod p) :
    (pPoly P N p σ).natDegree ≤ P.h N + D1 - 1 := by
  have hpo := p_odd_half hp2
  unfold pPoly
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  have h1 := tpLam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
  have h2 : (d : ℕ) < D1 + 1 := d.isLt
  omega

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
