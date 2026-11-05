module
public import Submission.CatalanMeasure.Parametric.SparseRowDIdentities
public import Submission.CatalanMeasure.Parametric.SparsePrimeGeometry
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem chebyshev_T_double (R : Type*) [CommRing R] (m : ℤ) :
    Chebyshev.T R (2*m)=2*(Chebyshev.T R m)^2-1 := by
  have h :=Chebyshev.T_mul_T R m m
  simp only [sub_self,Chebyshev.T_zero] at h
  rw [show m+m=2*m by ring] at h
  linear_combination (norm :=ring_nf) -h

theorem chebyshev_U_double (R : Type*) [CommRing R] (m : ℕ) :
    Chebyshev.U R (2*(m:ℤ)-1)=2*Chebyshev.T R (m:ℤ)*Chebyshev.U R ((m:ℤ)-1) := by
  have h :=chebyshev_U_difference R (m:ℤ) m
  simpa only [show (m:ℤ)+(m:ℤ)-1=2*(m:ℤ)-1 by ring,sub_self,
    zero_sub,Chebyshev.U_neg_one,sub_zero] using h

theorem sparseRowDDelta_two_mod {P : Parameters} {p N d : ℕ} [hp : Fact p.Prime]
    (hp2 : p≠2) (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N) :
    (sparseRowDDelta P N p 2 d).map (Int.castRingHom (ZMod p)) =
      (2*sparseRowCore P N (2*p) d-X^p*sparseRowCore P N p d).map
        (Int.castRingHom (ZMod p)) := by
  apply intPolynomial_mod_eq_of_ratW_eval
  let x : RatFunc (ZMod p) :=palindromicRatW p
  have hx : x≠0 :=palindromicRatW_ne_zero
  have hp0 : 0<p :=hp.out.pos
  have hcut2 : 2*p+d<P.C N :=by omega
  have hcutp : p+d ≤ P.C N :=by omega
  have hcutpp : 2*p+d ≤ P.C N :=by omega
  change (sparseRowDDelta P N p 2 d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x =
    (2*sparseRowCore P N (2*p) d-X^p*sparseRowCore P N p d).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x
  rw [sparseRowDDelta_eval₂ _ P N p 2 d hdg hcut2 hx]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  rw [chebyshev_U_difference ℤ (2*(p:ℤ)) d,chebyshev_T_double]
  simp only [eval₂_mul,eval₂_sub,eval₂_pow,eval₂_ofNat,eval₂_one]
  rw [chebyshev_T_prime_eval hp2]
  rw [sparseRowCore_eval₂ _ P N (2*p) d hd hcutpp hx,
    eval₂_X,sparseRowCore_eval₂ _ P N p d hd hcutp hx]
  have he1 :=power_cut_inv_product x hx (P.C N) (2*p) (by omega)
  have he2 :=power_cut_product x (P.C N) p (by omega)
  simp only [pow_mul] at he1
  linear_combination (norm :=ring_nf)
    4*(1-x)^(P.h N)*(Chebyshev.U ℤ ((d:ℤ)-1)).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*he1 +
    2*(1-x)^(P.h N)*(Chebyshev.U ℤ ((d:ℤ)-1)).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*he2

theorem sparseRowPDelta_one_weighted_mod {P : Parameters} {p N d : ℕ}
    [hp : Fact p.Prime] (hp2 : p≠2) (hd : 0<d) (hdg : d ≤ P.g N)
    (hcut : 3*p+d ≤ P.C N) :
    X*oddPrimeWeight p*(sparseRowPDelta P N p 1 d).map (Int.castRingHom (ZMod p)) =
      (1-X^(2*p))*(sparseRowCore P N p d).map (Int.castRingHom (ZMod p)) := by
  apply (transcendental_iff_injective.mp palindromicRatW_transcendental)
  let x : RatFunc (ZMod p) :=palindromicRatW p
  have hx : x≠0 :=palindromicRatW_ne_zero
  have hp0 : 0<p :=hp.out.pos
  have hcut1 : 1*p+d<P.C N :=by omega
  have hcutp : p+d ≤ P.C N :=by omega
  change (X*oddPrimeWeight p*(sparseRowPDelta P N p 1 d).map (Int.castRingHom (ZMod p))).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) x =
    ((1-X^(2*p))*(sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).eval₂
      (algebraMap (ZMod p) (RatFunc (ZMod p))) x
  simp only [oddPrimeWeight,eval₂_mul,eval₂_pow,eval₂_sub,eval₂_one,eval₂_X,
    palindromicRat_int_map_eval₂]
  rw [sparseRowPDelta_eval₂ _ P N p 1 d hdg hcut1 hx]
  simp only [one_mul]
  rw [chebyshev_T_difference ℤ (p:ℤ) d]
  simp only [eval₂_mul,eval₂_pow,eval₂_sub,eval₂_X,eval₂_one,eval₂_ofNat]
  rw [chebyshev_U_prime_eval hp2,sparseRowCore_eval₂ _ P N p d hd hcutp hx]
  have hg :=sparse_prime_inverse_geometry hp2 x hx
  have he :=power_cut_inv_product x hx (P.C N) p (by omega)
  rw [pow_succ'] at hg
  linear_combination (norm :=ring_nf)
    2*(1-x)^(P.h N)*x^(P.C N-1)*(Chebyshev.U ℤ ((d:ℤ)-1)).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*hg +
    2*(1-x)^(P.h N)*(1-x^(2*p))*(Chebyshev.U ℤ ((d:ℤ)-1)).eval₂
      (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*he

theorem sparseRowPDelta_two_shift_mod {P : Parameters} {p N d : ℕ}
    [hp : Fact p.Prime] (hp2 : p≠2) (hdg : d ≤ P.g N)
    (hcut : 3*p+d ≤ P.C N) :
    (X^p*sparseRowPDelta P N p 2 d).map (Int.castRingHom (ZMod p)) =
      (2*sparseRowPDelta P N p 1 d).map (Int.castRingHom (ZMod p)) := by
  apply intPolynomial_mod_eq_of_ratW_eval
  let x : RatFunc (ZMod p) :=palindromicRatW p
  have hx : x≠0 :=palindromicRatW_ne_zero
  have hp0 : 0<p :=hp.out.pos
  have hcut1 : 1*p+d<P.C N :=by omega
  have hcut2 : 2*p+d<P.C N :=by omega
  change (X^p*sparseRowPDelta P N p 2 d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x =
    (2*sparseRowPDelta P N p 1 d).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x
  rw [eval₂_mul,eval₂_X_pow,eval₂_mul,eval₂_ofNat,
    sparseRowPDelta_eval₂ _ P N p 2 d hdg hcut2 hx,
    sparseRowPDelta_eval₂ _ P N p 1 d hdg hcut1 hx]
  simp only [Nat.cast_mul,Nat.cast_ofNat,one_mul]
  rw [chebyshev_T_difference ℤ (2*(p:ℤ)) d,chebyshev_T_difference ℤ (p:ℤ) d,
    chebyshev_U_double ℤ p]
  simp only [eval₂_mul,eval₂_pow,eval₂_sub,eval₂_X,eval₂_one,eval₂_ofNat]
  rw [chebyshev_T_prime_eval hp2]
  have he : x^p*(x⁻¹)^p=1 := by rw [← mul_pow,mul_inv_cancel₀ hx,one_pow]
  linear_combination (norm :=ring_nf)
    4*(1-x)^(P.h N)*x^(P.C N-1)*((x⁻¹)^2-1)*
      (Chebyshev.U ℤ ((p:ℤ)-1)).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*
      (Chebyshev.U ℤ ((d:ℤ)-1)).eval₂ (Int.castRingHom (RatFunc (ZMod p))) x⁻¹*he

theorem sparseRowPDelta_two_weighted_mod {P : Parameters} {p N d : ℕ}
    [hp : Fact p.Prime] (hp2 : p≠2) (hd : 0<d) (hdg : d ≤ P.g N)
    (hcut : 3*p+d ≤ P.C N) :
    X*oddPrimeWeight p*(sparseRowPDelta P N p 2 d).map (Int.castRingHom (ZMod p)) =
      2*(1-X^(2*p))*(sparseRowCore P N (2*p) d).map (Int.castRingHom (ZMod p)) := by
  have hh :=sparseRowPDelta_two_shift_mod hp2 hdg hcut
  have h1 :=sparseRowPDelta_one_weighted_mod hp2 hd hdg hcut
  have hQ :=sparseRowCore_shift P N p d hd (by omega)
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
    Polynomial.map_ofNat] at hh
  have hQmod :=congrArg (fun F : ℤ[X] => F.map (Int.castRingHom (ZMod p))) hQ
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X] at hQmod
  apply mul_left_cancel₀ (pow_ne_zero p (X_ne_zero : (X : (ZMod p)[X])≠0))
  rw [hQmod] at h1
  linear_combination (norm :=ring_nf) X*oddPrimeWeight p*hh + 2*h1

end
end CatalanMeasure.Parametric
