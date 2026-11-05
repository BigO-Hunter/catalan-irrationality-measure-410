module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HRows
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalPairs
@[expose] public section
set_option Elab.async false

/-!
# H+ pairs as a slot system

Slot polynomial of index `t` (pair `e_{c+h-t} + e_{c+h+1+t}`, `h = (p-1)/2`):

    lam t = (X-1)^h · (U_{h-t-1} + U_{h+t})  =  (X-1)^h · f_{h-t},

`f_j = U_{p-1} T_j + (1 - T_p) U_{j-1}` (the physical pair identity), of degree `h + t`, divisible
by `(X-1)^h`.  Profile maps: `Ty y = Σ y_k (U_{k0+k} + U_{k0+k-1})`,
`Gy y = (1+X) Σ y_k (U_{k0+k} - U_{k0+k-1})` (polynomials in `Y = X^p`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `Ty y = Σ_k y_k (U_{k0+k} + U_{k0+k-1})`. -/
def hTy (p K : ℕ) (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))

/-- `Gy y = (1+X) Σ_k y_k (U_{k0+k} - U_{k0+k-1})`. -/
def hGy (p K : ℕ) (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    ((1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) - Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))

theorem hTy_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    hTy p K k0 y = ∑ k : Fin K, C (y k) *
      (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)) := by
  simp [hTy, LinearMap.sum_apply, Polynomial.smul_eq_C_mul, mul_add]

theorem hGy_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    hGy p K k0 y = ∑ k : Fin K, C (y k) *
      ((1 + X) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) - Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))) := by
  simp [hGy, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

/-- The slot polynomial `(X-1)^h f_{h-t}`. -/
def hLam (P : Parameters) (N p : ℕ) [Fact p.Prime] (t : ℕ) : (ZMod p)[X] :=
  (X - 1) ^ P.h N * (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t))

theorem p_eq_hh (hp2 : p ≠ 2) : (p : ℤ) = 2 * hh p + 1 := by
  have := p_odd_half hp2
  unfold hh
  omega

/-- `U` pair identity: the sum over the H+ pair of block `κ`. -/
theorem hU_pair (hp2 : p ≠ 2) (κ t : ℤ) :
    Chebyshev.U (ZMod p) (κ * p + hh p - t - 1) +
        Chebyshev.U (ZMod p) (κ * p + hh p + 1 + t - 1) =
      ((Chebyshev.U (ZMod p) κ).comp (X ^ p) + (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) := by
  have hpe := p_eq_hh hp2
  have h1 := physical_pair_U_plus (ZMod p) κ p (hh p - t)
  have h2 := chebyshev_U_reflect (ZMod p) (p : ℤ) (hh p - t)
  have e0 : κ * (p : ℤ) + (hh p - t) = κ * p + hh p - t := by ring
  rw [chebyshev_T_prime hp2] at h1 h2
  have e1 : (κ + 1) * (p : ℤ) - (hh p - t) - 1 = κ * p + hh p + 1 + t - 1 := by
    rw [hpe]; ring
  have e2 : (p : ℤ) - (hh p - t) - 1 = hh p + t := by rw [hpe]; ring
  rw [e1, e0] at h1
  rw [e2] at h2
  rw [h1]
  have h3 : Chebyshev.U (ZMod p) ((hh p - t) - 1) + Chebyshev.U (ZMod p) (hh p + t) =
      Chebyshev.U (ZMod p) ((p : ℤ) - 1) * Chebyshev.T (ZMod p) (hh p - t) +
        (1 - (X : (ZMod p)[X]) ^ p) * Chebyshev.U (ZMod p) (hh p - t - 1) := by
    rw [h2]; ring
  rw [← h3]

/-- `T` pair identity. -/
theorem hT_pair (hp2 : p ≠ 2) (κ t : ℤ) :
    (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (κ * p + hh p - t) +
          Chebyshev.T (ZMod p) (κ * p + hh p + 1 + t)) =
      (1 + X ^ p) * ((Chebyshev.U (ZMod p) κ).comp (X ^ p) -
          (Chebyshev.U (ZMod p) (κ - 1)).comp (X ^ p)) *
        (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) := by
  have hpe := p_eq_hh hp2
  have h1 := physical_pair_T_plus (ZMod p) κ p (hh p - t)
  have h2 := chebyshev_U_reflect (ZMod p) (p : ℤ) (hh p - t)
  have e0 : κ * (p : ℤ) + (hh p - t) = κ * p + hh p - t := by ring
  rw [chebyshev_T_prime hp2] at h1 h2
  have e1 : (κ + 1) * (p : ℤ) - (hh p - t) = κ * p + hh p + 1 + t := by
    rw [hpe]; ring
  have e2 : (p : ℤ) - (hh p - t) - 1 = hh p + t := by rw [hpe]; ring
  rw [e1, e0, chebyshev_U_prime hp2] at h1
  rw [chebyshev_U_prime hp2] at h2
  rw [e2] at h2
  rw [h1]
  have h3 : Chebyshev.U (ZMod p) ((hh p - t) - 1) + Chebyshev.U (ZMod p) (hh p + t) =
      (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (hh p - t) +
        (1 - (X : (ZMod p)[X]) ^ p) * Chebyshev.U (ZMod p) (hh p - t - 1) := by
    rw [h2]; ring
  rw [← h3]

end
end CatalanMeasure.GenD.Uniform.W.Slots
