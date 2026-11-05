module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueCount2
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT, overflow-below variant (b) with explicit profile data

`mt_glue_le_nullity`: given `m` profile pairs `(y_i, u_i)` with `y`, `u` each linearly independent
(this is the hypothesis `(I_T)` of proof4, now an explicit input) and scalars `(A_i, B_i)` such that

* `Φ-(J,s;y_i) = A_i`, `Φ+'(J,s;u_i) = B_i` for every digit `J` in `J1` (digits seeing the main window),
* `Φ-(J,s+1;y_i) + Φ+'(J,s+1;u_i) = A_i + B_i` for every digit `J` in `J2` (digits seeing the overflow),

the nullity is at least `m (2 D1 + 1 - (η - p + 1) - elo) - V - r` (written without subtraction).
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `a ↦ f.coeff e`. -/
def fcoefL (P : Parameters) (N p D1 m : ℕ) [Fact p.Prime] (A B : Fin m → ZMod p) (e : ℕ) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p] ZMod p :=
  ∑ i : Fin m, (A i • lamL P N p D1 m i e + B i • pL P N p D1 m i e)

theorem fcoefL_apply {D1 m : ℕ} (A B : Fin m → ZMod p) (e : ℕ)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) :
    fcoefL P N p D1 m A B e a = fcoef (P := P) (N := N) A B a e := by
  simp [fcoefL, fcoef, LinearMap.sum_apply, lamL_apply, pL_apply]

/-- The fold of `f` as a linear function of the residue. -/
def omegaL (P : Parameters) (N p D1 m η : ℕ) [Fact p.Prime] (A B : Fin m → ZMod p) (ℓ : ZMod p) :
    ((Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) →ₗ[ZMod p] ZMod p :=
  open Classical in
  if ℓ.val ≤ η then
    fcoefL P N p D1 m A B (η - ℓ.val) +
      (if p + ℓ.val ≤ η then fcoefL P N p D1 m A B (η - p - ℓ.val) else 0)
  else 0

theorem omegaL_apply {D1 m : ℕ} (A B : Fin m → ZMod p) (η : ℕ) (ℓ : ZMod p)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) :
    omegaL P N p D1 m η A B ℓ a =
      (if ℓ.val ≤ η then fcoef (P := P) (N := N) A B a (η - ℓ.val) +
        (if p + ℓ.val ≤ η then fcoef (P := P) (N := N) A B a (η - p - ℓ.val) else 0) else 0) := by
  classical
  unfold omegaL
  by_cases h1 : ℓ.val ≤ η
  · by_cases h2 : p + ℓ.val ≤ η
    · simp [h1, h2, fcoefL_apply]
    · simp [h1, h2, fcoefL_apply]
  · simp [h1]

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
