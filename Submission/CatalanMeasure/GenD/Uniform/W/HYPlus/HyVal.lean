module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyMain
@[expose] public section
set_option Elab.async false

/-!
# The HY+ integer bound `hyVal` and its proof from an `HYCell`
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem exists_sc (hp2 : p ≠ 2) {Dn nQ a0 : ℕ} (hD : Dn ≤ (p - 1) / 2)
    (hle : P.h N + (p - 1) / 2 ≤ p + a0)
    (hnQ : p + a0 - (P.h N + (p - 1) / 2) + nQ ≤ Dn) :
    ∃ sc : Fin nQ → Fin Dn → ZMod p, ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
      X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)) := by
  set b0 := p + a0 - (P.h N + (p - 1) / 2) with hb0
  have hex : ∀ i : Fin nQ, ∃ s : Fin Dn → ZMod p,
      (X - 1 : (ZMod p)[X]) ^ b0 * X ^ (i : ℕ) = ∑ t : Fin Dn, C (s t) * gBasis p t := by
    intro i
    have hi := i.isLt
    refine exists_combination hp2 Dn hD _ ?_
    have h1 : ((X - 1 : (ZMod p)[X]) ^ b0 * X ^ (i : ℕ)).natDegree ≤ b0 + i := by
      refine natDegree_mul_le.trans ?_
      have h2 : ((X - 1 : (ZMod p)[X]) ^ b0).natDegree ≤ b0 := by
        refine natDegree_pow_le.trans ?_
        have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
        nlinarith
      have h3 : ((X : (ZMod p)[X]) ^ (i : ℕ)).natDegree ≤ i := by simp
      omega
    exact lt_of_le_of_lt (degree_le_of_natDegree_le h1) (by exact_mod_cast (by omega : b0 + i < Dn))
  choose sc hsc using hex
  refine ⟨sc, fun i => ?_⟩
  have e1 : ∑ t : Fin Dn, C (sc i t) * hLam P N p (t : ℕ) =
      (X - 1) ^ (P.h N + (p - 1) / 2) * ∑ t : Fin Dn, C (sc i t) * gBasis p t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold hLam
    rw [f_eq_gBasis hp2]; ring
  rw [e1, ← hsc i, ← mul_assoc, ← pow_add]
  have e2 : P.h N + (p - 1) / 2 + b0 = p + a0 := by omega
  rw [e2, pow_add, sub_one_pow_prime]
  ring

/-- `η = H - 1 - s p`. -/
def hyEta (P : Parameters) (N p s : ℕ) : ℕ := P.H N - 1 - s * p
/-- `emax = h + (p-1)/2 + Dn` (number of coefficient positions). -/
def hyEmax (P : Parameters) (N p Dn : ℕ) : ℕ := P.h N + (p - 1) / 2 + Dn
/-- `a0 = (h + (p-1)/2 - p)_+`. -/
def hyA0 (P : Parameters) (N p : ℕ) : ℕ := P.h N + (p - 1) / 2 - p
/-- Number of free period parameters. -/
def hyNQ (P : Parameters) (N p Dn : ℕ) : ℕ := hyEmax P N p Dn - p - hyA0 P N p
/-- Filter cost `(p - q - h)_+`. -/
def hyF (P : Parameters) (N p : ℕ) : ℕ := p - P.q N - P.h N

/-- Total number of conditions. -/
def hyConds (P : Parameters) (N p s K Dn : ℕ) [Fact p.Prime] (k0 : ℤ) : ℕ :=
  hyMiss P N p K Dn k0 + ((hyEta P N p s + 1) - p) +
    (hyEmax P N p Dn - (hyEta P N p s + 1)) + hyF P N p +
    (edgeSet P N p (hyA0 P N p) (hyNQ P N p Dn) s (hyEta P N p s) Dn).card

/-- **The HY+ integer bound** (design-generic): `2 Dn + nQ - #conditions`. -/
def hyVal (P : Parameters) (N p s K Dn : ℕ) [Fact p.Prime] (k0 : ℤ) : ℕ :=
  (2 * Dn + hyNQ P N p Dn) - hyConds P N p s K Dn k0

/-- Numerical hypotheses of Theorem HY+. -/
def HYNum (P : Parameters) (N p s Dn : ℕ) : Prop :=
  Dn ≤ (p - 1) / 2 ∧ p ≤ P.q N + (P.h N + (p - 1) / 2) ∧ s * p + 1 ≤ P.H N ∧ s < p ∧
    p ≤ hyEta P N p s ∧ hyEta P N p s < 2 * p ∧ hyEmax P N p Dn ≤ hyEta P N p s + p ∧
    p + hyA0 P N p < hyEmax P N p Dn

theorem hyVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {s K Dn : ℕ} {k0 : ℤ} (hnum : HYNum P N p s Dn)
    (hcell : ∃ u v y : Fin K → ZMod p, HYCell p K s k0 (P.H N) u v y) :
    hyVal P N p s K Dn k0 ≤ nullity P N p := by
  obtain ⟨hD, hph, hs, hsp, hpη, hη2, hem, hQ0⟩ := hnum
  obtain ⟨u, v, y, γu, γy, Ψu, Ψy, Ψu', Ψy', κ, h1, h2, h3, h4, h5, h6, h7, h8, hind, hy0⟩ := hcell
  unfold hyEta hyEmax hyA0 at *
  obtain ⟨sc, hsc⟩ := exists_sc (P := P) (N := N) hp2 (Dn := Dn)
    (nQ := P.h N + (p - 1) / 2 + Dn - p - (P.h N + (p - 1) / 2 - p))
    (a0 := P.h N + (p - 1) / 2 - p) hD (by omega) (by omega)
  have key := hy_le_nullity hP hN hp2 hH (K := K) (Dn := Dn)
    (nQ := P.h N + (p - 1) / 2 + Dn - p - (P.h N + (p - 1) / 2 - p)) (s := s)
    (a0 := P.h N + (p - 1) / 2 - p) (η := P.H N - 1 - s * p) k0 hD hph (by omega) hsp hpη hη2 hem
    (by omega) u v y sc hsc hind hy0 γu γy Ψu Ψy Ψu' Ψy' κ h1 h2 h3 h4 h5 h6 h7 h8
  simp only [hyVal, hyConds, hyEta, hyEmax, hyA0, hyNQ, hyF]
  omega

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
