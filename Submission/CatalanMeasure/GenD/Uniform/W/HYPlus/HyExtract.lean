module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyMap
@[expose] public section
set_option Elab.async false

/-!
# Reading off the conditions from the kernel of `hyCond`
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
  (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p) (η s f : ℕ) (a : HyA p Dn nQ)
  (ha : hyCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a = 0)
include ha

theorem ker_lo (t : Fin Dn) (k : Fin K) (h : ¬ InRange P N (hlo p K k0 k t)) :
    xi u v y sc a (Fin.natAdd Dn t) (Fin.natAdd K k) +
      xi u v y sc a (Fin.castAdd Dn t) (Fin.castAdd K k) = 0 := by
  have := congrFun (congrArg (fun z => z.1.1) ha) ⟨(t, k), by simp [h]⟩
  simpa [hyCond, datL] using this

theorem ker_hi (t : Fin Dn) (k : Fin K) (h : ¬ InRange P N (hhi p K k0 k t)) :
    xi u v y sc a (Fin.castAdd Dn t) (Fin.castAdd K k) -
      xi u v y sc a (Fin.natAdd Dn t) (Fin.natAdd K k) = 0 := by
  have := congrFun (congrArg (fun z => z.1.2) ha) ⟨(t, k), by simp [h]⟩
  simpa [hyCond, datL] using this

theorem ker_sp (e : ℕ) (he : e + p ≤ η) :
    Ψu * aco P N p a.1 e + Ψy * cco P N p a.2.2 e = 0 := by
  have := congrFun (congrArg (fun z => z.2.1.1) ha) ⟨e, by omega⟩
  simpa [hyCond, acoL_apply, ccoL_apply] using this

theorem ker_sm (e : ℕ) (he1 : η < e) (he2 : e < P.h N + (p - 1) / 2 + Dn) :
    Ψu' * aco P N p a.1 e - κ * (Qpoly p a0 nQ a.2.1).coeff (e - p) +
      Ψy' * cco P N p a.2.2 e = 0 := by
  have := congrFun (congrArg (fun z => z.2.1.2) ha) ⟨e - (η + 1), by omega⟩
  have h2 : η + 1 + (e - (η + 1)) = e := by omega
  simpa [hyCond, acoL_apply, ccoL_apply, qcoL_apply, h2] using this

theorem ker_jet (i : ℕ) (hi : i < f) :
    (taylor 1 (∑ t : Fin Dn, C (a.2.2 t) * hmF p (t : ℕ))).coeff i = 0 := by
  have := congrFun (congrArg (fun z => z.2.2.1) ha) ⟨i, hi⟩
  simpa [hyCond, jetL_apply] using this

theorem ker_edge (c : ℕ × ℕ) (hc : c ∈ edgeSet P N p a0 nQ s η Dn) :
    (hySys P N p hp2 K Dn k0 hD).resp c.2 c.1 (xi u v y sc a) =
      γu * foldco p η c.1 (aco P N p a.1) + γy * foldco p η c.1 (cco P N p a.2.2) := by
  have := congrFun (congrArg (fun z => z.2.2.2) ha) ⟨c, hc⟩
  have h2 : (respL (hySys P N p hp2 K Dn k0 hD) c.2 c.1) (xi u v y sc a) -
      rhoL P N p Dn nQ γu γy η c.1 a = 0 := by
    exact this
  exact ((respL_apply _ _ _ _).symm.trans (sub_eq_zero.mp h2)).trans (rhoL_apply _ _ _ _ _)

end

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
