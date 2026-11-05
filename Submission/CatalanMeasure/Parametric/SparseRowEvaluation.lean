module
public import Submission.CatalanMeasure.Parametric.SparseRowCore
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem rowP_eval₂_signed {K : Type*} [Field K] (phi : ℤ →+* K)
    {P : Parameters} {N r : ℕ} (hd : rowDistance P N r < P.C N)
    {x : K} (hx : x ≠ 0) :
    (rowP P N r).eval₂ phi x = (1-x)^(P.h N)*x^(P.C N-1)*
      (Chebyshev.T ℤ (rowOffset P N r)).eval₂ phi x⁻¹ := by
  simpa only [rowDistance,Chebyshev.T_natAbs] using rowP_eval₂_of_distance_lt phi hd hx

theorem rowD_eval₂_signed {K : Type*} [Field K] (phi : ℤ →+* K)
    {P : Parameters} {N r : ℕ} (hd : rowDistance P N r < P.C N)
    {x : K} (hx : x ≠ 0) :
    (rowD P N r).eval₂ phi x = (1-x)^(P.h N)*x^(P.C N-1)*
      (Chebyshev.U ℤ (rowOffset P N r-1)).eval₂ phi x⁻¹ := by
  rw [rowD_eval₂_of_distance_lt phi hd hx]
  calc
    _ = (1-x)^(P.h N)*x^(P.C N-1)*
      (phi (Int.sign (rowOffset P N r))*
        (Chebyshev.U ℤ ((rowDistance P N r:ℤ)-1)).eval₂ phi x⁻¹) := by ring
    _ = _ := by rw [rowDistance,chebyshev_U_sign_natAbs_eval]

theorem sparseRowCore_eval₂ {K : Type*} [Field K] (phi : ℤ →+* K)
    (P : Parameters) (N p d : ℕ) (hd : 0 < d) (hcut : p+d ≤ P.C N)
    {x : K} (hx : x ≠ 0) :
    (sparseRowCore P N p d).eval₂ phi x =
      2*(1-x)^(P.h N)*x^(P.C N-p-1)*
        (Chebyshev.U ℤ ((d:ℤ)-1)).eval₂ phi x⁻¹ := by
  have hU : (Chebyshev.U ℤ ((d:ℤ)-1)).natDegree < P.C N-p := by
    simp only [Chebyshev.natDegree_U,sub_add_cancel,Int.natAbs_natCast]
    omega
  unfold sparseRowCore
  rw [eval₂_mul,eval₂_mul,reversedRow_eval₂ phi hU hx]
  simp only [eval₂_C,eval₂_ofNat,map_ofNat,eval₂_pow,eval₂_sub,eval₂_one,eval₂_X]
  ring

theorem chebyshev_T_prime_eval {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (y : RatFunc (ZMod p)) :
    (Chebyshev.T ℤ (p:ℤ)).eval₂ (Int.castRingHom (RatFunc (ZMod p))) y = y^p := by
  rw [← palindromicRat_int_map_eval₂,Chebyshev.map_T,chebyshev_T_prime hp2,eval₂_X_pow]

theorem chebyshev_U_prime_eval {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (y : RatFunc (ZMod p)) :
    (Chebyshev.U ℤ ((p:ℤ)-1)).eval₂ (Int.castRingHom (RatFunc (ZMod p))) y =
      (y^2-1)^((p-1)/2) := by
  rw [← palindromicRat_int_map_eval₂,Chebyshev.map_U,chebyshev_U_prime hp2]
  simp only [eval₂_pow,eval₂_sub,eval₂_X,eval₂_one]

end
end CatalanMeasure.Parametric
