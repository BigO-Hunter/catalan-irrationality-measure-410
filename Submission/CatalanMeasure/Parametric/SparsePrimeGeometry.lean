module
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

/-- The reciprocal substitution cancels the apparent parity sign. -/
theorem sparse_prime_inverse_geometry {p : ℕ} [hp : Fact p.Prime] (hp2 : p≠2)
    (x : RatFunc (ZMod p)) (hx : x≠0) :
    x*(1-x^2)^((p-1)/2)*((x⁻¹)^2-1)^((p-1)/2+1)=
      (1-x^(2*p))*(x⁻¹)^p := by
  let k : ℕ :=(p-1)/2
  have hk0 : 2*k=p-1 :=palindromic_prime_pred_twice_half hp2
  have hp0 : 0<p :=hp.out.pos
  have hk : k+(k+1)=p :=by omega
  have hk2 : 2*(k+1)=p+1 :=by omega
  have hbase : (x⁻¹)^2-1=(1-x^2)/x^2 := by
    field_simp
    <;> ring
  have hnum : (1-x^2)^k*(1-x^2)^(k+1)=(1-x^2)^p := by rw [← pow_add,hk]
  have hpow : (1-x^2)^p=1-x^(2*p) := by rw [sub_pow_char,one_pow,← pow_mul]
  change x*(1-x^2)^k*((x⁻¹)^2-1)^(k+1)=(1-x^(2*p))*(x⁻¹)^p
  calc
    _ = (1-x^2)^p*(x/x^(p+1)) := by
      rw [hbase,div_pow,← pow_mul,hk2,← hnum]
      ring
    _ = (1-x^2)^p*(x⁻¹)^p := by
      congr 1
      rw [pow_succ,inv_pow]
      field_simp
    _ = _ := by rw [hpow]

end
end CatalanMeasure.Parametric
