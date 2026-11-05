module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyCond
@[expose] public section
set_option Elab.async false

/-!
# The HY+ condition map
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

section
variable (hp2 : p ≠ 2) {K Dn nQ : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
  (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)

/-- The folded-coefficient functional `ρ(ℓ)`. -/
def rhoL (P : Parameters) (N p Dn nQ : ℕ) [Fact p.Prime] (γu γy : ZMod p) (η ℓ : ℕ) :
    HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  γu • (acoL P N p Dn nQ (η - ℓ) + (if p ≤ η - ℓ then acoL P N p Dn nQ (η - ℓ - p) else 0) +
      acoL P N p Dn nQ (η - ℓ + p)) +
    γy • (ccoL P N p Dn nQ (η - ℓ) + (if p ≤ η - ℓ then ccoL P N p Dn nQ (η - ℓ - p) else 0) +
      ccoL P N p Dn nQ (η - ℓ + p))

theorem rhoL_apply (γu γy : ZMod p) (η ℓ : ℕ) (a : HyA p Dn nQ) :
    rhoL P N p Dn nQ γu γy η ℓ a =
      γu * foldco p η ℓ (aco P N p a.1) + γy * foldco p η ℓ (cco P N p a.2.2) := by
  simp only [rhoL, foldco, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  by_cases h : p ≤ η - ℓ
  · simp [h, acoL_apply, ccoL_apply]
  · simp [h, acoL_apply, ccoL_apply]

/-- All conditions. -/
def hyCond (P : Parameters) (N : ℕ) (hp2 : p ≠ 2) (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) :
    HyA p Dn nQ →ₗ[ZMod p]
      ((((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)) → ZMod p) ×
        ((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)) → ZMod p)) ×
       ((Fin ((η + 1) - p) → ZMod p) × (Fin ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) → ZMod p)) ×
       (Fin f → ZMod p) × (edgeSet P N p a0 nQ s η Dn → ZMod p)) :=
  LinearMap.prod
    (LinearMap.prod
      (LinearMap.pi fun tk => (datL (K + K) (Dn + Dn) (Fin.natAdd Dn tk.1.1) (Fin.natAdd K tk.1.2) +
        datL (K + K) (Dn + Dn) (Fin.castAdd Dn tk.1.1) (Fin.castAdd K tk.1.2)).comp (xi u v y sc))
      (LinearMap.pi fun tk => ((datL (K + K) (Dn + Dn) (Fin.castAdd Dn tk.1.1) (Fin.castAdd K tk.1.2) -
        datL (K + K) (Dn + Dn) (Fin.natAdd Dn tk.1.1) (Fin.natAdd K tk.1.2) :
          (Fin (Dn + Dn) → Fin (K + K) → ZMod p) →ₗ[ZMod p] ZMod p)).comp (xi u v y sc)))
    (LinearMap.prod
      (LinearMap.prod
        (LinearMap.pi fun e : Fin ((η + 1) - p) =>
          Ψu • acoL P N p Dn nQ e + Ψy • ccoL P N p Dn nQ e)
        (LinearMap.pi fun j : Fin ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) =>
          Ψu' • acoL P N p Dn nQ (η + 1 + j) - κ • qcoL p Dn nQ a0 (η + 1 + j - p) +
            Ψy' • ccoL P N p Dn nQ (η + 1 + j)))
      (LinearMap.prod
        (LinearMap.pi fun i : Fin f => jetL p Dn nQ i)
        (LinearMap.pi fun c : edgeSet P N p a0 nQ s η Dn =>
          (respL (hySys P N p hp2 K Dn k0 hD) c.1.2 c.1.1).comp (xi u v y sc) -
            rhoL P N p Dn nQ γu γy η c.1.1)))

end

theorem finrank_hyCond_cod (P : Parameters) (N : ℕ) (K Dn nQ : ℕ) (k0 : ℤ) (a0 s η f : ℕ) :
    finrank (ZMod p)
      ((((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)) → ZMod p) ×
        ((Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)) → ZMod p)) ×
       ((Fin ((η + 1) - p) → ZMod p) × (Fin ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) → ZMod p)) ×
       (Fin f → ZMod p) × (edgeSet P N p a0 nQ s η Dn → ZMod p)) =
    hyMiss P N p K Dn k0 + ((η + 1) - p) + ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) + f +
      (edgeSet P N p a0 nQ s η Dn).card := by
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, Fintype.card_fin, hyMiss, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Module.finrank_self, mul_one]
  ring

theorem finrank_ker_hyCond (hp2 : p ≠ 2) {K Dn nQ : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) :
    Dn + nQ + Dn ≤ finrank (ZMod p)
        (LinearMap.ker (hyCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f)) +
      (hyMiss P N p K Dn k0 + ((η + 1) - p) + ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) + f +
        (edgeSet P N p a0 nQ s η Dn).card) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (hyCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f)
  have h2 := Submodule.finrank_le (LinearMap.range
    (hyCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f))
  have h3 : finrank (ZMod p) (HyA p Dn nQ) = Dn + nQ + Dn := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype]; ring
  rw [finrank_hyCond_cod] at h2
  omega

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
