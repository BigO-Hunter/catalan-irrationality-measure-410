module
public import Submission.CatalanMeasure.Parametric.UpperPrimeReconstruction
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Finset Matrix
open scoped BigOperators
noncomputable section

def upperPrimeLoss (P : Parameters) (N p : ℕ) : ℕ :=
  min (2*P.n N) (min (P.n N+paramUpperRetainedSize P p N)
    (2*paramUpperRetainedSize P p N+paramUpperPairedSize P p N+paramUpperExceptionalSize P p N))

theorem upperPhysicalCombination_valuation (P : Parameters) (hAdm : Admissible P)
    {N p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hN : 0<N) (hHsq : P.H N<p^2)
    (hpH : p ≤ P.H N) (hH : P.H N ≤ 2*p) (hA : P.A N ≤ p) (hLH : P.L N<P.H N)
    (z : ℚ) (hz : (z.den : ZMod p)≠0)
    (g : paramUpperPhysicalIndex P p N → Fin (P.n N) → ℚ)
    (hg : ∀ i k,((g i k).den : ZMod p)≠0) :
    -(upperPrimeLoss P N p:ℤ) ≤ padicValRat p
      (Matrix.of fun r k : Fin (P.n N) =>∑ i,paramUpperPhysicalColumn P z p N i r*g i k).det :=by
  have hh :=oddPhysicalCombination_valuation_lower (p :=p) (n :=P.n N)
    (paramUpperRetainedVector P z p N) (paramUpperPairedVector P z p N)
    (paramUpperIntegralVector P z p N) (paramUpperExceptionalVector P p N)
    (paramUpperExceptionalCoeff P p N) g
    (paramUpperRetainedVector_den_ne_zero P hAdm hp2 hHsq z hz)
    (paramUpperPairedVector_den_ne_zero P hAdm hp2 hN hpH hH hA hLH z hz)
    (paramUpperIntegralVector_den_ne_zero P hAdm hp2 hN hpH hH z hz)
    (paramUpperExceptionalVector_den_ne_zero P)
    (paramUpperExceptionalCoeff_den_ne_zero P) hg
  simpa only [upperPrimeLoss,paramUpperPhysicalColumn] using hh

def upperFilteredCoeff (P : Parameters) (N p : ℕ)
    (i : paramUpperPhysicalIndex P p N) (k : Fin (P.n N)) : ℚ :=
  ∑ v : Fin (P.q N+1),filterCoeffRat P N v.val*
    paramUpperInverseCoeff P p N i (P.b N+k.val+v.val)

theorem upperFilteredCoeff_den (P : Parameters) {N p : ℕ} [Fact p.Prime]
    (i : paramUpperPhysicalIndex P p N) (k : Fin (P.n N)) :
    ((upperFilteredCoeff P N p i k).den : ZMod p)≠0 :=by
  unfold upperFilteredCoeff
  apply (rational_residue_sum univ _ ?_).1
  intro v hv
  have hc : filterCoeffRat P N v.val=(lowerFilterInt P N v.val:ℚ) :=by
    simp [filterCoeffRat,lowerFilterInt]
  apply (rational_residue_mul _ (paramUpperInverseCoeff_den_ne_zero P i _)).1
  rw [hc]
  simp

theorem filteredEntry_eq_upper_physical_sum (P : Parameters) {N p : ℕ} [Fact p.Prime]
    (hN : 0<N) (hH : P.H N ≤ 2*p) (hbp : P.b N<p) (hJL : P.H N-p ≤ P.L N)
    (z : ℚ) (r k : Fin (P.n N)) :
    filteredEntryRat P z N r.val k.val=∑ i : paramUpperPhysicalIndex P p N,
      paramUpperPhysicalColumn P z p N i r*upperFilteredCoeff P N p i k :=by
  unfold filteredEntryRat
  rw [← Fin.sum_univ_eq_sum_range (fun v =>filterCoeffRat P N v*
    rawEntryRat P z N r.val (P.b N+k.val+v))]
  have hraw (v : Fin (P.q N+1)) : rawEntryRat P z N r.val (P.b N+k.val+v.val)=
      ∑ i : paramUpperPhysicalIndex P p N,paramUpperPhysicalColumn P z p N i r*
        paramUpperInverseCoeff P p N i (P.b N+k.val+v.val) :=
    paramRawEntryRat_eq_upper_physical_sum P hN hH hbp hJL z (lowerRawColumn k v) r
  simp_rw [hraw,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  unfold upperFilteredCoeff
  rw [mul_sum]
  apply sum_congr rfl
  intro v hv
  ring

/-- A uniform upper-range valuation for the actual filtered determinant. -/
theorem determinantRat_upper_prime_valuation (P : Parameters) (hAdm : Admissible P)
    {N p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hN : 0<N) (hHsq : P.H N<p^2)
    (hpH : p ≤ P.H N) (hH : P.H N ≤ 2*p) (hA : P.A N ≤ p) (hLH : P.L N<P.H N)
    (hbp : P.b N<p) (hJL : P.H N-p ≤ P.L N)
    (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(upperPrimeLoss P N p:ℤ) ≤ padicValRat p (determinantRat P z N) :=by
  have hmatrix : (fun r k : Fin (P.n N) =>filteredEntryRat P z N r.val k.val)=
      (Matrix.of fun r k : Fin (P.n N) =>∑ i : paramUpperPhysicalIndex P p N,
        paramUpperPhysicalColumn P z p N i r*upperFilteredCoeff P N p i k) :=by
    funext r k
    exact filteredEntry_eq_upper_physical_sum P hN hH hbp hJL z r k
  unfold determinantRat
  rw [hmatrix]
  exact upperPhysicalCombination_valuation P hAdm hp2 hN hHsq hpH hH hA hLH z hz
    (upperFilteredCoeff P N p) (upperFilteredCoeff_den P)

end
end CatalanMeasure.Parametric
