module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.LowFilterPrefix
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def residuePolynomialMap (eta : ZMod p) : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] where
  toFun := residuePolynomial eta
  map_add' B C := by simp only [residuePolynomial,eval_add,map_add,Finset.sum_add_distrib]
  map_smul' a B := by simp only [residuePolynomial,eval_smul,Finset.smul_sum,smul_monomial,RingHom.id_apply]

theorem residuePolynomial_injective (eta : ZMod p) (r : ℕ) (hr : r ≤ p)
    (B C : (ZMod p)[X]) (hB : B.degree < r) (hC : C.degree < r)
    (heq : residuePolynomial eta B = residuePolynomial eta C) : B = C := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (univ : Finset (Fin r))
    (v := fun e : Fin r => eta-(e.val:ZMod p))
  · intro e _ f _ he
    have hc : (e.val:ZMod p) = (f.val:ZMod p) := by linear_combination -he
    apply Fin.ext
    have hv := congrArg ZMod.val hc
    simpa only [ZMod.val_cast_of_lt (e.isLt.trans_le hr),ZMod.val_cast_of_lt (f.isLt.trans_le hr)] using hv
  · simpa using hB
  · simpa using hC
  · intro e _
    have hcoef := congrArg (fun P : (ZMod p)[X] => P.coeff e.val) heq
    simpa only [coeff_residuePolynomial,if_pos (e.isLt.trans_le hr)] using hcoef

noncomputable def residueQuotientMap (eta : ZMod p) (r : ℕ) :
    (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] :=
  (divByMonicHom ((X-1 : (ZMod p)[X])^(p-r))).comp (residuePolynomialMap eta)

theorem residueQuotient_spec (eta : ZMod p) (r : ℕ) (hr : r ≤ p)
    (B : (ZMod p)[X]) (hB : B.degree < r) :
    (residueQuotientMap eta r B).degree < r ∧
      residuePolynomial eta B = (X-1)^(p-r)*residueQuotientMap eta r B := by
  obtain ⟨Q,hdeg,heq⟩ := residuePolynomial_prefix_lift eta r hr B hB
  have hquot : residueQuotientMap eta r B = Q := by
    change residuePolynomial eta B /ₘ (X-1)^(p-r) = Q
    rw [heq]
    simpa only [map_one] using mul_divByMonic_cancel_left Q ((monic_X_sub_C (1:ZMod p)).pow (p-r))
  rw [hquot]
  exact ⟨hdeg,heq⟩

noncomputable def residuePrefixEnd (eta : ZMod p) (r : ℕ) (hr : r ≤ p) :
    degreeLT (ZMod p) r →ₗ[ZMod p] degreeLT (ZMod p) r :=
  ((residueQuotientMap eta r).comp (degreeLT (ZMod p) r).subtype).codRestrict _
    (fun B => Polynomial.mem_degreeLT.mpr (residueQuotient_spec eta r hr B.val
      (Polynomial.mem_degreeLT.mp B.property)).1)

@[simp] theorem residuePrefixEnd_val (eta : ZMod p) (r : ℕ) (hr : r ≤ p)
    (B : degreeLT (ZMod p) r) :
    (residuePrefixEnd eta r hr B).val = residueQuotientMap eta r B.val := rfl

theorem residuePrefixEnd_injective (eta : ZMod p) (r : ℕ) (hr : r ≤ p) :
    Function.Injective (residuePrefixEnd eta r hr) := by
  intro B C heq
  have hc := congrArg Subtype.val heq
  change residueQuotientMap eta r B.val = residueQuotientMap eta r C.val at hc
  apply Subtype.ext
  apply residuePolynomial_injective eta r hr B.val C.val
    (Polynomial.mem_degreeLT.mp B.property) (Polynomial.mem_degreeLT.mp C.property)
  rw [(residueQuotient_spec eta r hr B.val (Polynomial.mem_degreeLT.mp B.property)).2,
    (residueQuotient_spec eta r hr C.val (Polynomial.mem_degreeLT.mp C.property)).2,hc]

/-- The low-degree response polynomial and the actual (X-1) prefix quotient are
linearly equivalent. Finite-dimensional surjectivity is proved from an explicit
injective endomorphism; it is not a rank or dimension premise. -/
noncomputable def residuePrefixEquiv (eta : ZMod p) (r : ℕ) (hr : r ≤ p) :
    degreeLT (ZMod p) r ≃ₗ[ZMod p] degreeLT (ZMod p) r := by
  letI : FiniteDimensional (ZMod p) (degreeLT (ZMod p) r) :=
    FiniteDimensional.of_injective (degreeLTEquiv (ZMod p) r).toLinearMap
      (degreeLTEquiv (ZMod p) r).injective
  exact LinearEquiv.ofBijective (residuePrefixEnd eta r hr)
    ⟨residuePrefixEnd_injective eta r hr,
      LinearMap.injective_iff_surjective.mp (residuePrefixEnd_injective eta r hr)⟩

/-- Every actual prefix vector has a unique degree-r response polynomial. -/
theorem existsUnique_residuePrefix (eta : ZMod p) (r : ℕ) (hr : r ≤ p)
    (Q : (ZMod p)[X]) (hQ : Q.degree < r) :
    ∃! B : (ZMod p)[X],B.degree < r ∧ residuePolynomial eta B = (X-1)^(p-r)*Q := by
  let q : degreeLT (ZMod p) r := ⟨Q,Polynomial.mem_degreeLT.mpr hQ⟩
  let b := (residuePrefixEquiv eta r hr).symm q
  have hb : b.val.degree < r := Polynomial.mem_degreeLT.mp b.property
  have hquot : residueQuotientMap eta r b.val = Q := by
    have he := congrArg Subtype.val ((residuePrefixEquiv eta r hr).apply_symm_apply q)
    exact he
  have heq : residuePolynomial eta b.val = (X-1)^(p-r)*Q := by
    rw [(residueQuotient_spec eta r hr b.val hb).2,hquot]
  refine ⟨b.val,⟨hb,heq⟩,?_⟩
  intro B hB
  apply residuePolynomial_injective eta r hr B b.val hB.1 hb
  rw [hB.2,heq]

/-- Exact equality of the two source descriptions, with both degree windows. -/
theorem residuePolynomial_iff_prefix (eta : ZMod p) (r : ℕ) (hr : r ≤ p) (G : (ZMod p)[X]) :
    (∃ B : (ZMod p)[X],B.degree < r ∧ G = residuePolynomial eta B) ↔
      ∃ Q : (ZMod p)[X],Q.degree < r ∧ G = (X-1)^(p-r)*Q := by
  constructor
  · rintro ⟨B,hB,rfl⟩
    exact residuePolynomial_prefix_lift eta r hr B hB
  · rintro ⟨Q,hQ,rfl⟩
    obtain ⟨B,⟨hB,heq⟩,_⟩ := existsUnique_residuePrefix eta r hr Q hQ
    exact ⟨B,hB,heq.symm⟩

#print axioms existsUnique_residuePrefix
#print axioms residuePolynomial_iff_prefix
end CatalanMeasure.GenD.Uniform.Prefix

