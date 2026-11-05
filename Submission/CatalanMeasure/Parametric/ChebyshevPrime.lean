module
public import Submission.CatalanMeasure.Parametric.ChebyshevDifferences
public import Submission.CatalanMeasure.Parametric.ChebyshevPell
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

theorem chebyshev_T_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p≠2) :
    Chebyshev.T (ZMod p) (p:ℤ)=(X: (ZMod p)[X])^p := by
  have hp3 : 2<p :=by have :=hp.out.two_le;omega
  have htwo : (2:ZMod p)≠0 := by
    intro hz
    have hh :=(ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0<2) hp3) hh
  letI : NeZero (2:ZMod p) :=⟨htwo⟩
  have hd : (Chebyshev.T (ZMod p) (p:ℤ)).natDegree=p := by
    simp only [Chebyshev.natDegree_T,Int.natAbs_natCast]
  have hder : derivative (Chebyshev.T (ZMod p) (p:ℤ))=0 := by
    rw [Chebyshev.T_derivative_eq_U]
    simp [Int.cast_natCast,show (p:ZMod p)=0 from ZMod.natCast_self p]
  ext i
  by_cases hi : i=p
  · subst i
    have hc : (Chebyshev.T (ZMod p) (p:ℤ)).coeff p =
        (Chebyshev.T (ZMod p) (p:ℤ)).leadingCoeff := by
      simpa only [hd] using (coeff_natDegree (p := Chebyshev.T (ZMod p) (p:ℤ)))
    rw [hc,Chebyshev.leadingCoeff_T]
    simp only [Int.natAbs_natCast,coeff_X_pow,ite_true]
    exact ZMod.pow_card_sub_one_eq_one htwo
  · have hxp : ((X:(ZMod p)[X])^p).coeff i=0 := by
      simp [coeff_X_pow,hi]
    rw [hxp]
    by_cases hi0 : i=0
    · subst i
      rw [coeff_zero_eq_eval_zero]
      exact Chebyshev.T_eval_zero_of_odd (ZMod p)
        (by exact_mod_cast hp.out.odd_of_ne_two hp2)
    · by_cases hil : i<p
      · have hz :=congrArg (fun Q : (ZMod p)[X] =>Q.coeff (i-1)) hder
        rw [coeff_derivative,coeff_zero,show i-1+1=i by omega] at hz
        have hcast : ((i-1:ℕ):ZMod p)+1=(i:ZMod p) := by
          have hiOne : 1 ≤ i := by omega
          rw [Nat.cast_sub hiOne,Nat.cast_one]
          ring
        rw [hcast] at hz
        have hicu : (i:ZMod p)≠0 := by
          intro he
          have hiPos : 0 < i := by omega
          exact (Nat.not_dvd_of_pos_of_lt hiPos hil)
            ((ZMod.natCast_eq_zero_iff i p).mp he)
        exact (mul_eq_zero.mp hz).resolve_right hicu
      · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem chebyshev_U_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Chebyshev.U (ZMod p) ((p:ℤ)-1)=(X^2-1 : (ZMod p)[X])^((p-1)/2) := by
  have hp3 : 2 < p := by have := hp.out.two_le; omega
  have htwo : (2:ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp3)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
  letI : NeZero (2:ZMod p) := ⟨htwo⟩
  have hbase : (X^2-1 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    have hh := congrArg (fun Q : (ZMod p)[X] => Q.coeff 0) hz
    norm_num at hh
  have hpow : (X^2-1 : (ZMod p)[X])^p=X^(2*p)-1 := by
    rw [sub_pow_char,one_pow,← pow_mul]
  have hPell := chebyshev_Pell (ZMod p) hp.out.pos
  rw [chebyshev_T_prime hp2,← pow_mul,Nat.mul_comm p 2] at hPell
  have hfac : (X^2-1 : (ZMod p)[X])*Chebyshev.U (ZMod p) ((p:ℤ)-1)^2 =
      (X^2-1 : (ZMod p)[X])^p := by
    rw [hpow]
    linear_combination (norm := ring_nf) -hPell
  have hfac' : (X^2-1 : (ZMod p)[X])*Chebyshev.U (ZMod p) ((p:ℤ)-1)^2 =
      (X^2-1 : (ZMod p)[X])*(X^2-1)^(p-1) := by
    rw [← pow_succ',Nat.sub_add_cancel hp.out.pos]
    exact hfac
  have hsq := mul_left_cancel₀ hbase hfac'
  let Q : (ZMod p)[X] := (X^2-1)^((p-1)/2)
  have hQsq : Q^2=(X^2-1 : (ZMod p)[X])^(p-1) := by
    dsimp [Q]
    rw [← pow_mul]
    congr 1
    simpa only [Nat.mul_comm] using OAI.InternalCatalan.palindromic_prime_pred_twice_half hp2
  have hprod : (Chebyshev.U (ZMod p) ((p:ℤ)-1)-Q)*
      (Chebyshev.U (ZMod p) ((p:ℤ)-1)+Q)=0 := by
    linear_combination (norm := ring_nf) hsq-hQsq
  have hUlead : (Chebyshev.U (ZMod p) ((p:ℤ)-1)).leadingCoeff=1 := by
    rw [show (p:ℤ)-1=((p-1:ℕ):ℤ) by omega,Chebyshev.leadingCoeff_U_natCast]
    exact ZMod.pow_card_sub_one_eq_one htwo
  have hQmonic : Q.Monic := by
    simpa only [Q,map_one] using (monic_X_pow_sub_C (1:ZMod p) (by decide : (2:ℕ)≠0)).pow ((p-1)/2)
  rcases mul_eq_zero.mp hprod with hm | hpq
  · exact sub_eq_zero.mp hm
  · have he : Chebyshev.U (ZMod p) ((p:ℤ)-1)=-Q := eq_neg_of_add_eq_zero_left hpq
    have hh := congrArg Polynomial.leadingCoeff he
    rw [hUlead,leadingCoeff_neg,hQmonic.leadingCoeff] at hh
    exfalso
    apply htwo
    linear_combination (norm := ring_nf) hh

end
end CatalanMeasure.Parametric
