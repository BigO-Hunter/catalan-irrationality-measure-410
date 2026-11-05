module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HInst
@[expose] public section
set_option Elab.async false

/-!
# Profile maps of the H- (antisymmetric half-centred) pairs, and the HY+ cell predicate

H- pair of block `k`, index `t`: `e_{lo} - e_{hi}` with `lo = c_k + hh - t`, `hi = c_k + hh + 1 + t`.
Its slot polynomial is `(X-1)^h (U_{hh-t-1} - U_{hh+t})` and its profile maps are (polynomials in `Y`)

    `hmTy y = Σ_k y_k (U_{k0+k} - U_{k0+k-1})`,   `hmGy y = (Y - 1) Σ_k y_k (U_{k0+k} + U_{k0+k-1})`.

`HYCell` is the interface between the cell lane (exact rational certificates, Lemma B) and the
HY+ count: three profiles `u, v` (H+ profile maps) and `y` (H- profile maps) with the
constancy / shift identities used by the response computation.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `Ty y = Σ_k y_k (U_{k0+k} - U_{k0+k-1})`. -/
def hmTy (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) - Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))

/-- `Gy y = (X - 1) Σ_k y_k (U_{k0+k} + U_{k0+k-1})`  (`X` stands for `Y`). -/
def hmGy (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  ∑ k : Fin K, (LinearMap.proj k : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    ((X - 1) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)))

theorem hmTy_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    hmTy p K k0 y = ∑ k : Fin K, C (y k) *
      (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) - Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)) := by
  simp [hmTy, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

theorem hmGy_apply (K : ℕ) (k0 : ℤ) (y : Fin K → ZMod p) :
    hmGy p K k0 y = ∑ k : Fin K, C (y k) *
      ((X - 1) * (Chebyshev.U (ZMod p) (k0 + (k : ℕ)) + Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1))) := by
  simp [hmGy, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

/-- The H+ profile maps as a `Prof`. -/
def profHp (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : Prof p K := ⟨hTy p K k0, hGy p K k0⟩

/-- The H- profile maps as a `Prof`. -/
def profHm (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : Prof p K := ⟨hmTy p K k0, hmGy p K k0⟩

/-- **The HY+ cell predicate** (window `s`, total digit count `H`).  `u, v` are H+ profiles
(`u*` = single `H+(s;1..s-1)`, `v` = raw `Pd(s;2..s-1)`), `y` an H- profile (`y*`).

* `ψ+(J,s) u` is constant on `J = 1..s-1`, `ψ-(J,s) y` likewise;
* `ψ+(J,s) v = ψ+(J,s+1) v` for `J = 2..s-1`;
* shift identities: `J (ψ(J,s+1) z - γ_z) = Ψ_z` for `J = 2..s` (`z = u, y`),
  `(J+1)(γ_z - ψ(J,s-1) z) = Ψ'_z` for `J = 0..s-2`,
  `(J+1)(ψ+(J,s-1) v - ψ+(J,s) v) = κ` for `J = 1..s-2`;
* `u, v` linearly independent, `y ≠ 0`. -/
def HYCell (p K s : ℕ) [Fact p.Prime] (k0 : ℤ) (H : ℕ) (u v y : Fin K → ZMod p) : Prop :=
  ∃ γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p,
    (∀ J, 1 ≤ J → J ≤ s - 1 → (profHp p K k0).psi H J (s : ℤ) u = γu) ∧
    (∀ J, 1 ≤ J → J ≤ s - 1 → (profHm p K k0).psi H J (s : ℤ) y = γy) ∧
    (∀ J, 2 ≤ J → J ≤ s - 1 →
      (profHp p K k0).psi H J (s : ℤ) v = (profHp p K k0).psi H J ((s : ℤ) + 1) v) ∧
    (∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHp p K k0).psi H J ((s : ℤ) + 1) u - γu) = Ψu) ∧
    (∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHm p K k0).psi H J ((s : ℤ) + 1) y - γy) = Ψy) ∧
    (∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γu - (profHp p K k0).psi H J ((s : ℤ) - 1) u) = Ψu') ∧
    (∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γy - (profHm p K k0).psi H J ((s : ℤ) - 1) y) = Ψy') ∧
    (∀ J, 1 ≤ J → J + 2 ≤ s →
      ((J : ZMod p) + 1) * ((profHp p K k0).psi H J ((s : ℤ) - 1) v -
        (profHp p K k0).psi H J (s : ℤ) v) = κ) ∧
    LinearIndependent (ZMod p) ![u, v] ∧ y ≠ 0

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
