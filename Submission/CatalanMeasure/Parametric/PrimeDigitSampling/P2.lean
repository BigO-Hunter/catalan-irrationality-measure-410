module
public import Submission.CatalanMeasure.Parametric.SparseRowIdentities
public import Submission.CatalanMeasure.Parametric.SparseDigitResidues
public import Submission.CatalanMeasure.Parametric.PrimeDigitSampling.P1
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section


theorem primeDigitSample_shift_single {R : Type*} [Semiring R] {H p ell a t : ℕ}
    (hp : 0<p) (hell : ell<p) (ha : a+t<H) (f : ℕ → R) (Q : R[X])
    (hsupp : ∀ i, Q.coeff i≠0 → a*p ≤ i ∧ i<(a+1)*p) :
    primeDigitSample H p ell f (X^(t*p)*Q)=Q.coeff (a*p+ell)*f (a+t) := by
  have hshift : ∀ i, (X^(t*p)*Q).coeff i≠0 →
      (a+t)*p ≤ i ∧ i<(a+t+1)*p := by
    intro i hi
    rw [coeff_X_pow_mul'] at hi
    split_ifs at hi with hit
    · have hh :=hsupp (i-t*p) hi
      constructor <;> nlinarith [Nat.sub_add_cancel hit]
    · exact (hi rfl).elim
  rw [primeDigitSample_single hp hell ha f _ hshift,coeff_X_pow_mul']
  rw [if_pos (by nlinarith : t*p ≤ (a+t)*p+ell)]
  have hidx : (a+t)*p+ell-t*p=a*p+ell :=by rw [Nat.add_mul]; omega
  rw [hidx]

def primeDigitPair (H p j : ℕ) [Fact p.Prime] (F G : (ZMod p)[X]) : ZMod p :=
  primeDigitSample (H+1) p (j%p)
    (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) (j/p)))
    (X*oddPrimeWeight p*F) -
  (3/2:ZMod p)*primeDigitSample H p (j%p)
    (fun v => palindromicRatResidue p (zetaRat v (j/p))) G

theorem primeDigitPair_sub (H p j : ℕ) [Fact p.Prime] (F G F' G' : (ZMod p)[X]) :
    primeDigitPair H p j (F-F') (G-G')=
      primeDigitPair H p j F G-primeDigitPair H p j F' G' := by
  unfold primeDigitPair
  rw [mul_sub,primeDigitSample_sub,primeDigitSample_sub]
  ring

end
end CatalanMeasure.Parametric
