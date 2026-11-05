module
public import Submission.CatalanMeasure.Parametric.CentralPrimeColumns
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan Finset
open scoped BigOperators
noncomputable section

def paramLeadingU (P : Parameters) (p N r ell : ℕ) [Fact p.Prime] : ZMod p :=
  2*(X*((rowP P N r).map (Int.castRingHom (ZMod p)))*oddPrimeWeight p).coeff ell-
    (3/2:ZMod p)*((rowD P N r).map (Int.castRingHom (ZMod p))).coeff ell

theorem paramRawEntry_pair_leading {P : Parameters} (hAdm : Admissible P)
    {p N r ell : ℕ} [hp : Fact p.Prime] (hp2 : p≠2) (hN : 0<N)
    (hell : ell<p) (hwidth : P.H N ≤ ell+2*p) (hhigh : p+ell<P.H N)
    (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0) :
    (((p:ℚ)^2*(rawEntryRat P z N r ell+rawEntryRat P z N r (p+ell))).den : ZMod p)≠0 ∧
      palindromicRatResidue p ((p:ℚ)^2*(rawEntryRat P z N r ell+
        rawEntryRat P z N r (p+ell)))=paramLeadingU P p N r ell :=by
  have hp3 : 3 ≤ p :=by have hh :=hp.out.two_le;omega
  have hH : P.H N<p^2 :=by nlinarith only [hwidth,hell,hp3]
  have hellH : ell<P.H N :=by omega
  let F : (ZMod p)[X] :=(rowP P N r).map (Int.castRingHom (ZMod p))
  let G : (ZMod p)[X] :=(rowD P N r).map (Int.castRingHom (ZMod p))
  have hF : ∀ i,P.H N ≤ i → F.coeff i=0 :=by
    intro i hi;simp only [F,coeff_map,rowP_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hG : ∀ i,P.H N ≤ i → G.coeff i=0 :=by
    intro i hi;simp only [G,coeff_map,rowD_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hdlo :=(scaledRawEntry_transfer (r :=r) hp2 hH hellH z hz).1
  have hdhi :=(scaledRawEntry_transfer (r :=r) hp2 hH hhigh z hz).1
  have he : (p:ℚ)^2*(rawEntryRat P z N r ell+rawEntryRat P z N r (p+ell))=
      (p:ℚ)^2*rawEntryRat P z N r ell+(p:ℚ)^2*rawEntryRat P z N r (p+ell) :=by ring
  refine ⟨?_,?_⟩
  · rw [he];exact (rational_residue_add hdlo hdhi).1
  · rw [he,palindromicRatResidue_add hdlo hdhi,
      rawEntry_primeDigitPair hAdm hN hp2 hH hellH z hz,
      rawEntry_primeDigitPair hAdm hN hp2 hH hhigh z hz]
    rw [primeDigitPair_columns (by omega) hell hwidth F G hF hG]
    unfold paramLeadingU
    have hcomm : X*oddPrimeWeight p*F=X*F*oddPrimeWeight p :=by ring
    rw [hcomm]

theorem paramRawEntry_low_leading {P : Parameters} (hAdm : Admissible P)
    {p N r ell : ℕ} [hp : Fact p.Prime] (hp2 : p≠2) (hN : 0<N)
    (hell : ell<p) (hwidth : P.H N ≤ ell+2*p) (hhigh : p+ell<P.H N)
    (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0) :
    (((p:ℚ)^2*rawEntryRat P z N r ell).den : ZMod p)≠0 ∧
      palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N r ell)=paramLeadingV P p N r ell :=by
  have hp3 : 3 ≤ p :=by have hh :=hp.out.two_le;omega
  have hH : P.H N<p^2 :=by nlinarith only [hwidth,hell,hp3]
  have hellH : ell<P.H N :=by omega
  let F : (ZMod p)[X] :=(rowP P N r).map (Int.castRingHom (ZMod p))
  let G : (ZMod p)[X] :=(rowD P N r).map (Int.castRingHom (ZMod p))
  let Q : (ZMod p)[X] :=X*oddPrimeWeight p*F
  have hF : ∀ i,P.H N ≤ i → F.coeff i=0 :=by
    intro i hi;simp only [F,coeff_map,rowP_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hG : ∀ i,P.H N ≤ i → G.coeff i=0 :=by
    intro i hi;simp only [G,coeff_map,rowD_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  refine ⟨(scaledRawEntry_transfer hp2 hH hellH z hz).1,?_⟩
  rw [rawEntry_primeDigitPair hAdm hN hp2 hH hellH z hz]
  unfold primeDigitPair primeDigitSample
  rw [Nat.mod_eq_of_lt hell,Nat.div_eq_of_lt hell]
  have hM : (∑ v ∈ range (P.H N+1),Q.coeff (v*p+ell)*
      palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) 0))=2*Q.coeff (2*p+ell) :=by
    rw [sum_eq_single 2]
    · norm_num [palindromicRatResidue,momentRatSigned,momentRat,boundaryMinus];ring
    · intro v hv hne
      by_cases hv3 : 3 ≤ v
      · have hi : P.H N+p ≤ v*p+ell :=by nlinarith only [hwidth,hp.out.pos,hv3]
        rw [weighted_prime_coeff_zero_high hp.out.pos F hF hi,zero_mul]
      · have hc : v=0 ∨ v=1 :=by omega
        rcases hc with rfl | rfl <;>
          norm_num [palindromicRatResidue,momentRatSigned,momentRatNegOne,momentRat,boundaryPlus,boundaryMinus]
    · intro hn;exact (hn (mem_range.mpr (by omega))).elim
  have hD : (∑ v ∈ range (P.H N),G.coeff (v*p+ell)*
      palindromicRatResidue p (zetaRat v 0))=G.coeff (p+ell) :=by
    rw [sum_eq_single 1]
    · norm_num [palindromicRatResidue,zetaRat,harmonicRat,sum_range_succ]
    · intro v hv hne
      by_cases hv2 : 2 ≤ v
      · have hi : P.H N ≤ v*p+ell :=by nlinarith only [hwidth,hp.out.pos,hv2]
        rw [hG _ hi,zero_mul]
      · have hv0 : v=0 :=by omega
        subst v;norm_num [palindromicRatResidue,zetaRat,harmonicRat]
    · intro hn;exact (hn (mem_range.mpr (by omega))).elim
  rw [hM,hD]
  unfold paramLeadingV
  have hcomm : Q=X*F*oddPrimeWeight p :=by dsimp only [Q];ring
  rw [hcomm]

theorem paramRawEntry_high_leading {P : Parameters} (hAdm : Admissible P)
    {p N r ell : ℕ} [hp : Fact p.Prime] (hp2 : p≠2) (hN : 0<N)
    (hell : ell<p) (hwidth : P.H N ≤ ell+2*p) (hhigh : p+ell<P.H N)
    (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0) :
    (((p:ℚ)^2*rawEntryRat P z N r (p+ell)).den : ZMod p)≠0 ∧
      palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N r (p+ell))=
        paramLeadingU P p N r ell-paramLeadingV P p N r ell :=by
  have hlo :=paramRawEntry_low_leading (r :=r) hAdm hp2 hN hell hwidth hhigh z hz
  have hpair :=paramRawEntry_pair_leading (r :=r) hAdm hp2 hN hell hwidth hhigh z hz
  have hp3 : 3 ≤ p :=by have hh :=hp.out.two_le;omega
  have hH : P.H N<p^2 :=by nlinarith only [hwidth,hell,hp3]
  have hhi :=(scaledRawEntry_transfer (r :=r) hp2 hH hhigh z hz).1
  refine ⟨hhi,?_⟩
  have hadd :=palindromicRatResidue_add hlo.1 hhi
  have he : (p:ℚ)^2*(rawEntryRat P z N r ell+rawEntryRat P z N r (p+ell))=
      (p:ℚ)^2*rawEntryRat P z N r ell+(p:ℚ)^2*rawEntryRat P z N r (p+ell) :=by ring
  rw [he,hadd,hlo.2] at hpair
  linear_combination hpair.2

end
end CatalanMeasure.Parametric
