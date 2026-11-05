module
public import Submission.CatalanMeasure.Parametric.PrimeDigitSampling
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem rawEntry_primeDigitPair {P : Parameters} {p N r j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hp2 : p≠2) (hH : P.H N<p^2)
    (hj : j<P.H N) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N r j)=
      primeDigitPair (P.H N) p j ((rowP P N r).map (Int.castRingHom (ZMod p)))
        ((rowD P N r).map (Int.castRingHom (ZMod p))) := by
  rw [(scaledRawEntry_transfer hp2 hH hj z hzp).2]
  have hraw :=(raw_zero_digit_reduction P (r:=r) hp2 hH hj).2
  let F :=(rowP P N r).map (Int.castRingHom (ZMod p))
  let G :=(rowD P N r).map (Int.castRingHom (ZMod p))
  have hF (i : ℕ) (hi : P.H N ≤ i) : F.coeff i=0 := by
    simp only [F,coeff_map,rowP_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hG (i : ℕ) (hi : P.H N ≤ i) : G.coeff i=0 := by
    simp only [G,coeff_map,rowD_coeff_eq_zero_of_ge hAdm hN hi,map_zero]
  have hell :=Nat.mod_lt j hp.out.pos
  have hdecomp : j=j/p*p+j%p :=by
    simpa only [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div j p).symm
  have hP :=oddPrime_P_coefficient_contraction_support (k:=j/p) hp.out.pos hell F hF
    (fun v => palindromicRatResidue p (momentRatSigned v (j/p)))
  have hD :=oddPrime_residue_sum_gather hp.out.pos hell (fun i => G.coeff i)
    (fun v => palindromicRatResidue p (zetaRat v (j/p))) hG
  simp only [F,G,coeff_map,ZModIntCast_apply,← hdecomp] at hP hD
  simp only [palindromicRatResidue] at hP hD
  change palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P 0 N r j)=_ at hraw
  rw [hraw]
  unfold primeDigitPair primeDigitSample
  rw [show X*oddPrimeWeight p*F=X*F*oddPrimeWeight p by ring]
  simp only [F,G,coeff_map,ZModIntCast_apply,palindromicRatResidue]
  rw [← hP,← hD]
  apply congrArg₂ (fun a b : ZMod p => a-(3/2)*b) rfl
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_ite,mul_zero,palindromicRatResidue]

theorem sparseRowPDelta_zero_mod {P : Parameters} {p N d : ℕ} [hp : Fact p.Prime]
    (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N) :
    (sparseRowPDelta P N p 0 d).map (Int.castRingHom (ZMod p))=0 := by
  suffices hh : (sparseRowPDelta P N p 0 d).map (Int.castRingHom (ZMod p))=
      (0:ℤ[X]).map (Int.castRingHom (ZMod p)) by simpa using hh
  apply intPolynomial_mod_eq_of_ratW_eval
  have hp0 : 0<p :=hp.out.pos
  rw [sparseRowPDelta_eval₂ _ P N p 0 d hdg (by omega) palindromicRatW_ne_zero]
  simp only [zero_mul,Nat.cast_zero]
  rw [chebyshev_T_difference ℤ (0:ℤ) d]
  simp [Chebyshev.U_neg_one]

end
end CatalanMeasure.Parametric
