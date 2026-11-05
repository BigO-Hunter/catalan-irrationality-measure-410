module
public import Submission.CatalanMeasure.Parametric.SparseRowDelta
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem intPolynomial_mod_eq_of_ratW_eval {p : ℕ} [Fact p.Prime] (F G : ℤ[X])
    (h : F.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatW p)=
      G.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatW p)) :
    F.map (Int.castRingHom (ZMod p))=G.map (Int.castRingHom (ZMod p)) := by
  apply (transcendental_iff_injective.mp palindromicRatW_transcendental)
  change (F.map (Int.castRingHom (ZMod p))).eval₂
    (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatW p) =
    (G.map (Int.castRingHom (ZMod p))).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatW p)
  simpa only [palindromicRat_int_map_eval₂] using h

theorem power_cut_product {K : Type*} [Field K] (x : K) (C s : ℕ) (hs : s<C) :
    x^s*x^(C-s-1)=x^(C-1) := by
  rw [← pow_add]
  congr 1
  omega

theorem power_cut_inv_product {K : Type*} [Field K] (x : K) (hx : x≠0)
    (C s : ℕ) (hs : s<C) : x^(C-1)*(x⁻¹)^s=x^(C-s-1) := by
  rw [inv_pow,← div_eq_mul_inv]
  apply (div_eq_iff (pow_ne_zero _ hx)).mpr
  rw [← pow_add]
  congr 1
  omega

theorem sparseRowDDelta_zero_mod {P : Parameters} {p N d : ℕ} [hp : Fact p.Prime]
    (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N) :
    (sparseRowDDelta P N p 0 d).map (Int.castRingHom (ZMod p)) =
      (X^p*sparseRowCore P N p d).map (Int.castRingHom (ZMod p)) := by
  apply intPolynomial_mod_eq_of_ratW_eval
  let x : RatFunc (ZMod p) :=palindromicRatW p
  have hx : x≠0 :=palindromicRatW_ne_zero
  have hp0 : 0<p :=hp.out.pos
  have hcut0 : 0*p+d<P.C N :=by omega
  have hcutp : p+d ≤ P.C N :=by omega
  change (sparseRowDDelta P N p 0 d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x =
    (X^p*sparseRowCore P N p d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x
  rw [sparseRowDDelta_eval₂ _ P N p 0 d hdg hcut0 hx]
  simp only [zero_mul,Nat.cast_zero]
  rw [chebyshev_U_difference ℤ (0:ℤ) d]
  simp only [Chebyshev.T_zero,eval₂_mul,eval₂_ofNat,eval₂_one,mul_one]
  rw [eval₂_X_pow,sparseRowCore_eval₂ _ P N p d hd hcutp hx]
  have he :=power_cut_product x (P.C N) p (by omega)
  linear_combination (norm :=ring_nf)
    -2*(1-x)^(P.h N)*(Chebyshev.U ℤ ((d:ℤ)-1)).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*he

theorem sparseRowDDelta_one_mod {P : Parameters} {p N d : ℕ} [hp : Fact p.Prime]
    (hp2 : p≠2) (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N) :
    (sparseRowDDelta P N p 1 d).map (Int.castRingHom (ZMod p)) =
      (sparseRowCore P N p d).map (Int.castRingHom (ZMod p)) := by
  apply intPolynomial_mod_eq_of_ratW_eval
  let x : RatFunc (ZMod p) :=palindromicRatW p
  have hx : x≠0 :=palindromicRatW_ne_zero
  have hp0 : 0<p :=hp.out.pos
  have hcut1 : 1*p+d<P.C N :=by omega
  have hcutp : p+d ≤ P.C N :=by omega
  change (sparseRowDDelta P N p 1 d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x =
    (sparseRowCore P N p d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x
  rw [sparseRowDDelta_eval₂ _ P N p 1 d hdg hcut1 hx]
  simp only [one_mul]
  rw [chebyshev_U_difference ℤ (p:ℤ) d]
  simp only [eval₂_mul,eval₂_ofNat]
  rw [chebyshev_T_prime_eval hp2,sparseRowCore_eval₂ _ P N p d hd hcutp hx]
  have he :=power_cut_inv_product x hx (P.C N) p (by omega)
  linear_combination (norm :=ring_nf)
    2*(1-x)^(P.h N)*(Chebyshev.U ℤ ((d:ℤ)-1)).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*he

end
end CatalanMeasure.Parametric
