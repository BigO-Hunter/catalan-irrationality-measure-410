module
public import Submission.CatalanMeasure.Parametric.SparseSampleFormulas
public import Submission.CatalanMeasure.Parametric.RawDigitFunctional
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem sparseSample_zero {P : Parameters} {p N d j : ℕ} [hp : Fact p.Prime]
    (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) :
    primeDigitPair (P.H N) p j ((sparseRowPDelta P N p 0 d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p 0 d).map (Int.castRingHom (ZMod p))) =
    ((sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).coeff (2*p+j%p)*
      sparseDigitZeroResidue p (j/p) := by
  let Q :=(sparseRowCore P N p d).map (Int.castRingHom (ZMod p))
  have hs (i : ℕ) : Q.coeff i≠0 → 2*p ≤ i ∧ i<(2+1)*p :=
    sparseRowCore_mod_digit hd hp.out.pos hcut hhi
  unfold primeDigitPair
  rw [sparseRowPDelta_zero_mod hdg hcut,sparseRowDDelta_zero_mod hd hdg hcut]
  simp only [mul_zero,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  have hz : primeDigitSample (P.H N+1) p (j%p)
      (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p))) 0=0 :=by
    simp [primeDigitSample]
  rw [hz,zero_sub]
  have hsample :=primeDigitSample_shift_single (t:=1) hp.out.pos (Nat.mod_lt j hp.out.pos)
    (show 2+1<P.H N by omega) (fun v => palindromicRatResidue p (zetaRat v (j/p))) Q hs
  simp only [one_mul] at hsample
  rw [hsample]
  unfold sparseDigitZeroResidue
  ring

theorem sparse_primeDigitPair_relation {P : Parameters} {p N d j : ℕ} [hp : Fact p.Prime]
    (hlarge : 1000000 ≤ p) (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) (hwindow : P.H N ≤ 3*p+P.b N)
    (hjb : P.b N ≤ j) (hjL : j<P.L N) :
    primeDigitPair (P.H N) p j ((sparseRowPDelta P N p 2 d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p 2 d).map (Int.castRingHom (ZMod p))) =
    (292/59:ZMod p)*primeDigitPair (P.H N) p j
      ((sparseRowPDelta P N p 1 d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p 1 d).map (Int.castRingHom (ZMod p))) -
    (3281/177:ZMod p)*primeDigitPair (P.H N) p j
      ((sparseRowPDelta P N p 0 d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p 0 d).map (Int.castRingHom (ZMod p))) := by
  have hp2 : p≠2 :=by omega
  rw [sparseSample_two hp2 hd hdg hcut hhi hH,
    sparseSample_one hp2 hd hdg hcut hhi hH,sparseSample_zero hd hdg hcut hhi hH]
  by_cases hc : ((sparseRowCore P N p d).map (Int.castRingHom (ZMod p))).coeff (2*p+j%p)=0
  · simp [hc]
  · have hcint : (sparseRowCore P N p d).coeff (2*p+j%p)≠0 :=by
      intro hz
      apply hc
      simp [coeff_map,hz]
    have hpos :=sparseRowCore_raw_digit_position P N p d j hd hp.out.pos hcut hdg hwindow hjb hjL hcint
    have hrel : sparseDigitTwoResidue p (j/p)=
      (292/59:ZMod p)*sparseDigitOneResidue p (j/p)-
      (3281/177:ZMod p)*sparseDigitZeroResidue p (j/p) :=by
      rcases hpos with h1 | h2
      · simpa [h1] using sparseDigit_identity_residue hlarge (0:Fin 2)
      · simpa [h2] using sparseDigit_identity_residue hlarge (1:Fin 2)
    rw [hrel]
    ring

def sparseRawResidueDelta (P : Parameters) (p N k d j : ℕ) [Fact p.Prime] (z : ℚ) : ZMod p :=
  palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N (P.g N+k*p+d) j)-
    palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N (P.g N+k*p-d) j)

theorem sparseRawResidueDelta_as_pair {P : Parameters} {p N k d j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hp2 : p≠2) (hH : P.H N<p^2)
    (hj : j<P.H N) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    sparseRawResidueDelta P p N k d j z=primeDigitPair (P.H N) p j
      ((sparseRowPDelta P N p k d).map (Int.castRingHom (ZMod p)))
      ((sparseRowDDelta P N p k d).map (Int.castRingHom (ZMod p))) := by
  unfold sparseRawResidueDelta
  rw [rawEntry_primeDigitPair hAdm hN hp2 hH hj z hzp,
    rawEntry_primeDigitPair hAdm hN hp2 hH hj z hzp]
  rw [← primeDigitPair_sub]
  simp only [sparseRowPDelta,sparseRowDDelta,Polynomial.map_sub]

theorem sparse_raw_residue_relation {P : Parameters} {p N d j : ℕ} [hp : Fact p.Prime]
    (hAdm : Admissible P) (hN : 0<N) (hlarge : 1000000 ≤ p) (hHsq : P.H N<p^2)
    (hd : 0<d) (hdg : d ≤ P.g N) (hcut : 3*p+d ≤ P.C N)
    (hhi : P.H N ≤ 4*p) (hH : 4<P.H N) (hwindow : P.H N ≤ 3*p+P.b N)
    (hjb : P.b N ≤ j) (hjL : j<P.L N) (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    sparseRawResidueDelta P p N 2 d j z=
      (292/59:ZMod p)*sparseRawResidueDelta P p N 1 d j z-
      (3281/177:ZMod p)*sparseRawResidueDelta P p N 0 d j z := by
  have hp2 : p≠2 :=by omega
  have hjH : j<P.H N :=by unfold Parameters.H Parameters.C; omega
  rw [sparseRawResidueDelta_as_pair hAdm hN hp2 hHsq hjH z hzp,
    sparseRawResidueDelta_as_pair hAdm hN hp2 hHsq hjH z hzp,
    sparseRawResidueDelta_as_pair hAdm hN hp2 hHsq hjH z hzp]
  exact sparse_primeDigitPair_relation hlarge hd hdg hcut hhi hH hwindow hjb hjL

end
end CatalanMeasure.Parametric
