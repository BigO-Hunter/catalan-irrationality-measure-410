module
public import Submission.CatalanMeasure.Parametric.PrimeDigitSampling
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem sparseRowCore_mod_digit {P : Parameters} {p N d : ℕ}
    (hd : 0<d) (hp : 0<p) (hcut : 3*p+d ≤ P.C N) (hhi : P.H N ≤ 4*p)
    {i : ℕ} (hc : ((sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).coeff i≠0) :
    2*p ≤ i ∧ i<3*p := by
  apply sparseRowCore_second_digit P N p d hd hp hcut hhi
  intro hz
  apply hc
  simp [coeff_map,hz]

theorem sparseRowCore_low_mod_digit {P : Parameters} {p N d : ℕ}
    (hd : 0<d) (hp : 0<p) (hcut : 3*p+d ≤ P.C N) (hhi : P.H N ≤ 4*p)
    {i : ℕ} (hc : ((sparseRowCore P N (2*p) d).map (Int.castRingHom (ZMod p))).coeff i≠0) :
    p ≤ i ∧ i<2*p := by
  have hnonzero : (sparseRowCore P N (2*p) d).coeff i≠0 := by
    intro hz
    apply hc
    simp [coeff_map,hz]
  have hl : P.C N-2*p-d ≤ i := by
    by_contra hh
    exact hnonzero (sparseRowCore_coeff_below P N (2*p) d hd (by omega) (by omega))
  have hu : i<P.H N-2*p := by
    by_contra hh
    exact hnonzero (sparseRowCore_coeff_above P N (2*p) d (by omega) (by omega))
  constructor <;> omega

theorem sparseRowCore_mod_coeff_shift {P : Parameters} {p N d ell : ℕ}
    (hd : 0<d) (hcut : 3*p+d ≤ P.C N) :
    ((sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).coeff (2*p+ell)=
      ((sparseRowCore P N (2*p) d).map (Int.castRingHom (ZMod p))).coeff (p+ell) := by
  rw [sparseRowCore_shift P N p d hd (by omega),Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_X,coeff_X_pow_mul']
  rw [ite_eq_left (by omega),show 2*p+ell-p=p+ell by omega]

theorem sparseSample_one {P : Parameters} {p N d j : ℕ} [hp : Fact p.Prime]
    (hp2 : p≠2) (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) :
    primeDigitPair (P.H N) p j ((sparseRowPDelta P N p 1 d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p 1 d).map (Int.castRingHom (ZMod p))) =
    ((sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).coeff (2*p+j%p)*
      sparseDigitOneResidue p (j/p) := by
  let Q :=(sparseRowCore P N p d).map (Int.castRingHom (ZMod p))
  have hs (i : ℕ) : Q.coeff i≠0 → 2*p ≤ i ∧ i<(2+1)*p :=
    sparseRowCore_mod_digit hd hp.out.pos hcut hhi
  unfold primeDigitPair
  rw [sparseRowPDelta_one_weighted_mod hp2 hd hdg hcut,sparseRowDDelta_one_mod hp2 hd hdg hcut]
  change primeDigitSample (P.H N+1) p (j%p)
    (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p))) ((1-X^(2*p))*Q)-
    (3/2:ZMod p)*primeDigitSample (P.H N) p (j%p)
      (fun v => palindromicRatResidue p (zetaRat v (j/p))) Q=_
  rw [show (1-X^(2*p))*Q=Q-X^(2*p)*Q by ring,primeDigitSample_sub,
    primeDigitSample_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs,
    primeDigitSample_shift_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs,
    primeDigitSample_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs]
  norm_num only
  unfold sparseDigitOneResidue
  ring

theorem sparseSample_two {P : Parameters} {p N d j : ℕ} [hp : Fact p.Prime]
    (hp2 : p≠2) (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) :
    primeDigitPair (P.H N) p j ((sparseRowPDelta P N p 2 d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p 2 d).map (Int.castRingHom (ZMod p))) =
    ((sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).coeff (2*p+j%p)*
      sparseDigitTwoResidue p (j/p) := by
  let Q :=(sparseRowCore P N p d).map (Int.castRingHom (ZMod p))
  let Qlo :=(sparseRowCore P N (2*p) d).map (Int.castRingHom (ZMod p))
  have hs (i : ℕ) : Q.coeff i≠0 → 2*p ≤ i ∧ i<(2+1)*p :=
    sparseRowCore_mod_digit hd hp.out.pos hcut hhi
  have hslow (i : ℕ) : Qlo.coeff i≠0 → 1*p ≤ i ∧ i<(1+1)*p :=by
    simpa only [one_mul] using (sparseRowCore_low_mod_digit hd hp.out.pos hcut hhi (i:=i))
  unfold primeDigitPair
  rw [sparseRowPDelta_two_weighted_mod hp2 hd hdg hcut,sparseRowDDelta_two_mod hp2 hd hdg hcut]
  simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_ofNat,
    Polynomial.map_pow,Polynomial.map_X]
  change primeDigitSample (P.H N+1) p (j%p)
    (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p))) (2*(1-X^(2*p))*Qlo)-
    (3/2:ZMod p)*primeDigitSample (P.H N) p (j%p)
      (fun v => palindromicRatResidue p (zetaRat v (j/p))) (2*Qlo-X^p*Q)=_
  rw [show 2*(1-X^(2*p))*Qlo=2*(Qlo-X^(2*p)*Qlo) by ring,
    show 2*Qlo-X^p*Q=2*Qlo-X^(1*p)*Q by simp,
    primeDigitSample_two_mul,primeDigitSample_sub,primeDigitSample_sub,primeDigitSample_two_mul,
    primeDigitSample_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Qlo hslow,
    primeDigitSample_shift_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Qlo hslow,
    primeDigitSample_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Qlo hslow,
    primeDigitSample_shift_single hp.out.pos (Nat.mod_lt j hp.out.pos) (by omega) _ Q hs]
  have hc : Q.coeff (2*p+j%p)=Qlo.coeff (1*p+j%p) :=by
    simpa only [Q,Qlo,one_mul] using sparseRowCore_mod_coeff_shift (ell:=j%p) hd hcut
  rw [← hc]
  norm_num only
  unfold sparseDigitTwoResidue
  have htwo : (2:ZMod p)≠0 :=by
    intro hz
    have hpgt : 2<p :=by have :=hp.out.two_le; omega
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0<2) hpgt)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  dsimp only [Q]
  field_simp
  ring

end
end CatalanMeasure.Parametric
