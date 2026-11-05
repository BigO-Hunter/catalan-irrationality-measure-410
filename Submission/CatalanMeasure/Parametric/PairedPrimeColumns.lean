module
public import Submission.CatalanMeasure.Parametric.RawDigitFunctional
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.OddPrimePairedColumnIntegrality
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan Finset
open scoped BigOperators
noncomputable section

theorem weighted_prime_coeff_zero_high {p H : ℕ} (hp : 0<p)
    (F : (ZMod p)[X]) (hF : ∀ i,H ≤ i → F.coeff i=0)
    {i : ℕ} (hi : H+p ≤ i) : (X*oddPrimeWeight p*F).coeff i=0 :=by
  cases i with
  | zero =>simp only [mul_assoc,coeff_X_mul_zero]
  | succ i =>
    rw [mul_assoc,coeff_X_mul,coeff_mul]
    apply sum_eq_zero
    intro u hu
    have hsum :=mem_antidiagonal.mp hu
    by_cases hFH : H ≤ u.2
    · rw [hF _ hFH,mul_zero]
    · have hw : p ≤ u.1 :=by omega
      rw [oddPrimeWeight_coeff_eq_zero_of_ge hp hw,zero_mul]

private theorem pair_moment_values {p : ℕ} [Fact p.Prime] (v : ℕ) (hv : v<3) :
    palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) 0)+
      palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) 1)=if v=0 then 2 else 0 :=by
  have hc : v=0 ∨ v=1 ∨ v=2 :=by omega
  rcases hc with rfl | rfl | rfl <;>
    norm_num [palindromicRatResidue,momentRatSigned,momentRatNegOne,momentRat,
      boundaryPlus,boundaryMinus,momentScalar,centralCoeff,Finset.sum_range_succ]

private theorem pair_zeta_values {p : ℕ} [Fact p.Prime] (v : ℕ) (hv : v<2) :
    palindromicRatResidue p (zetaRat v 0)+palindromicRatResidue p (zetaRat v 1)=
      if v=0 then 1 else 0 :=by
  have hc : v=0 ∨ v=1 :=by omega
  rcases hc with rfl | rfl <;>
    norm_num [palindromicRatResidue,zetaRat,harmonicRat,Finset.sum_range_succ]

/-- The paired leading digit identity is independent of the determinant parameters. -/
theorem primeDigitPair_columns {H p ell : ℕ} [hp : Fact p.Prime]
    (hH : 0<H) (hell : ell<p) (hwidth : H ≤ ell+2*p)
    (F G : (ZMod p)[X]) (hF : ∀ i,H ≤ i → F.coeff i=0)
    (hG : ∀ i,H ≤ i → G.coeff i=0) :
    primeDigitPair H p ell F G+primeDigitPair H p (p+ell) F G=
      2*(X*oddPrimeWeight p*F).coeff ell-(3/2:ZMod p)*G.coeff ell :=by
  have hdiv : (p+ell)/p=1 :=by simp [Nat.add_div_left,hp.out.pos,Nat.div_eq_of_lt hell]
  have hmod : (p+ell)%p=ell :=by simp [Nat.add_mod,Nat.mod_eq_of_lt hell]
  unfold primeDigitPair primeDigitSample
  rw [Nat.mod_eq_of_lt hell,Nat.div_eq_of_lt hell,hdiv,hmod]
  have hM : (∑ v ∈ range (H+1),(X*oddPrimeWeight p*F).coeff (v*p+ell)*
        palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) 0))+
      (∑ v ∈ range (H+1),(X*oddPrimeWeight p*F).coeff (v*p+ell)*
        palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) 1))=
        2*(X*oddPrimeWeight p*F).coeff ell :=by
    rw [← sum_add_distrib]
    calc
      _ = ∑ v ∈ range (H+1),if v=0 then (2:ZMod p)*(X*oddPrimeWeight p*F).coeff ell else 0 :=by
        apply sum_congr rfl
        intro v hv
        rw [← mul_add]
        by_cases hv3 : v<3
        · rw [pair_moment_values v hv3]
          split_ifs with hv0
          · subst v;simp;ring
          · simp
        · have hi : H+p ≤ v*p+ell :=by nlinarith only [hwidth,hp.out.pos,show 3 ≤ v by omega]
          rw [weighted_prime_coeff_zero_high hp.out.pos F hF hi]
          simp only [zero_mul,if_neg (by omega : v≠0)]
      _ = _ :=by simp [hH.ne']
  have hZ : (∑ v ∈ range H,G.coeff (v*p+ell)*palindromicRatResidue p (zetaRat v 0))+
      (∑ v ∈ range H,G.coeff (v*p+ell)*palindromicRatResidue p (zetaRat v 1))=G.coeff ell :=by
    rw [← sum_add_distrib]
    calc
      _ = ∑ v ∈ range H,if v=0 then G.coeff ell else 0 :=by
        apply sum_congr rfl
        intro v hv
        rw [← mul_add]
        by_cases hv2 : v<2
        · rw [pair_zeta_values v hv2]
          split_ifs with hv0
          · subst v;simp
          · simp
        · have hi : H ≤ v*p+ell :=by nlinarith only [hwidth,hp.out.pos,show 2 ≤ v by omega]
          rw [hG _ hi]
          simp only [zero_mul,if_neg (by omega : v≠0)]
      _ = _ :=by simp [hH.ne']
  linear_combination hM-(3/2:ZMod p)*hZ

theorem weighted_prime_coeff_zero_low {p A ell : ℕ}
    (F : (ZMod p)[X]) (hF : ∀ i,i<A → F.coeff i=0) (hell : ell ≤ A) :
    (X*oddPrimeWeight p*F).coeff ell=0 :=by
  cases ell with
  | zero =>simp only [mul_assoc,coeff_X_mul_zero]
  | succ ell =>
    rw [mul_assoc,coeff_X_mul,coeff_mul]
    apply sum_eq_zero
    intro u hu
    have hh :=mem_antidiagonal.mp hu
    rw [hF u.2 (by omega),mul_zero]

/-- Actual raw paired columns gain one prime power in the starting support range. -/
theorem rawEntry_pair_prime_integral {P : Parameters} (hAdm : Admissible P)
    {p N r ell : ℕ} [hp : Fact p.Prime] (hp2 : p≠2) (hN : 0<N) (hr : r<P.n N)
    (hell : ell<p) (hwidth : P.H N ≤ ell+2*p) (hhigh : p+ell<P.H N)
    (hA : ell ≤ P.A N) (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0) :
    (((p:ℚ)*(rawEntryRat P z N r ell+rawEntryRat P z N r (p+ell))).den : ZMod p)≠0 :=by
  have hp3 : 3 ≤ p :=by have hh :=hp.out.two_le;omega
  have hH : P.H N<p^2 :=by nlinarith only [hwidth,hell,hp3]
  have hellH : ell<P.H N :=by omega
  let F : (ZMod p)[X] :=(rowP P N r).map (Int.castRingHom (ZMod p))
  let G : (ZMod p)[X] :=(rowD P N r).map (Int.castRingHom (ZMod p))
  have hF : ∀ i,P.H N ≤ i → F.coeff i=0 :=by
    intro i hi
    simp only [F,coeff_map,rowP_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hG : ∀ i,P.H N ≤ i → G.coeff i=0 :=by
    intro i hi
    simp only [G,coeff_map,rowD_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hFlo : ∀ i,i<P.A N → F.coeff i=0 :=by
    intro i hi
    simp only [F,coeff_map,rowP_coeff_eq_zero_of_lt hAdm hN hr hi,map_zero]
  have hGell : G.coeff ell=0 :=by
    simp only [G,coeff_map,rowD_coeff_eq_zero_of_lt hAdm hN hr (show ell<P.A N+1 by omega),map_zero]
  have hHpos : 0<P.H N :=by have hh :=C_pos hAdm hN;unfold Parameters.H;omega
  have hdlo :=(scaledRawEntry_transfer (r :=r) hp2 hH hellH z hz).1
  have hdhi :=(scaledRawEntry_transfer (r :=r) hp2 hH hhigh z hz).1
  have he : (p:ℚ)^2*(rawEntryRat P z N r ell+rawEntryRat P z N r (p+ell))=
      (p:ℚ)^2*rawEntryRat P z N r ell+(p:ℚ)^2*rawEntryRat P z N r (p+ell) :=by ring
  have hden : (((p:ℚ)^2*(rawEntryRat P z N r ell+rawEntryRat P z N r (p+ell))).den : ZMod p)≠0 :=by
    rw [he]
    exact (rational_residue_add hdlo hdhi).1
  have hres : palindromicRatResidue p ((p:ℚ)^2*(rawEntryRat P z N r ell+
      rawEntryRat P z N r (p+ell)))=0 :=by
    rw [he,palindromicRatResidue_add hdlo hdhi,
      rawEntry_primeDigitPair hAdm hN hp2 hH hellH z hz,
      rawEntry_primeDigitPair hAdm hN hp2 hH hhigh z hz]
    rw [primeDigitPair_columns hHpos hell hwidth F G hF hG,
      weighted_prime_coeff_zero_low F hFlo hA,hGell]
    ring
  exact rational_prime_scaled_den_ne_zero_of_prime_sq_residue_zero hden hres

end
end CatalanMeasure.Parametric
