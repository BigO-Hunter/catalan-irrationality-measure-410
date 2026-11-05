module
public import Submission.CatalanMeasure.Parametric.ChebyshevDifferences
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

theorem chebyshev_U_pair_invariant (R : Type*) [CommRing R] (n : ℕ) :
    Chebyshev.U R (n:ℤ)^2+Chebyshev.U R ((n+1:ℕ):ℤ)^2 -
      2*X*Chebyshev.U R (n:ℤ)*Chebyshev.U R ((n+1:ℕ):ℤ)=1 := by
  induction n with
  | zero => simp [Chebyshev.U_zero,Chebyshev.U_one];ring
  | succ n ih =>
    have hrec : Chebyshev.U R ((n+1+1:ℕ):ℤ)=
        2*X*Chebyshev.U R ((n+1:ℕ):ℤ)-Chebyshev.U R (n:ℤ) := by
      simpa only [Nat.cast_add,Nat.cast_one,show (n:ℤ)+1+1=(n:ℤ)+2 by ring] using
        Chebyshev.U_add_two R (n:ℤ)
    rw [hrec]
    linear_combination (norm :=ring_nf) ih

theorem chebyshev_Pell (R : Type*) [CommRing R] {n : ℕ} (hn : 0<n) :
    Chebyshev.T R (n:ℤ)^2-(X^2-1)*Chebyshev.U R ((n:ℤ)-1)^2=1 := by
  have hp :=chebyshev_U_pair_invariant R (n-1)
  have hn1 : n-1+1=n :=by omega
  have hcast : ((n-1:ℕ):ℤ)=(n:ℤ)-1 :=by omega
  rw [hn1,hcast] at hp
  rw [Chebyshev.T_eq_U_sub_X_mul_U]
  linear_combination (norm :=ring_nf) hp

end
end CatalanMeasure.Parametric
