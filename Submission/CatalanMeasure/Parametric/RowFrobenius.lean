module
public import Submission.CatalanMeasure.Parametric.Polynomial
public import Submission.OAI.NumberTheory.Catalan.Determinants.PalindromicRowFrobenius
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

theorem rowP_eval₂_of_distance_lt {K : Type*} [Field K] (φ : ℤ →+* K)
    {P : Parameters} {N r : ℕ} (hd : rowDistance P N r < P.C N) {x : K} (hx : x ≠ 0) :
    (rowP P N r).eval₂ φ x = (1 - x) ^ P.h N * x ^ (P.C N - 1) *
      (Chebyshev.T ℤ (rowDistance P N r : ℤ)).eval₂ φ x⁻¹ := by
  have hT : (Chebyshev.T ℤ (rowDistance P N r : ℤ)).natDegree < P.C N := by
    simpa [Chebyshev.natDegree_T] using hd
  unfold rowP
  rw [eval₂_mul, OAI.InternalCatalan.reversedRow_eval₂ φ hT hx]
  simp only [eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  exact (mul_assoc _ _ _).symm

theorem rowD_eval₂_of_distance_lt {K : Type*} [Field K] (φ : ℤ →+* K)
    {P : Parameters} {N r : ℕ} (hd : rowDistance P N r < P.C N) {x : K} (hx : x ≠ 0) :
    (rowD P N r).eval₂ φ x = φ (Int.sign (rowOffset P N r)) * (1 - x) ^ P.h N *
      x ^ (P.C N - 1) * (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).eval₂ φ x⁻¹ := by
  have hU : (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).natDegree < P.C N := by
    rw [Chebyshev.natDegree_U]
    simp only [sub_add_cancel, Int.natAbs_natCast]
    omega
  unfold rowD
  rw [eval₂_mul, eval₂_mul, OAI.InternalCatalan.reversedRow_eval₂ φ hU hx]
  simp only [eval₂_C, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  ring

def ratRow (P : Parameters) (p N r : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (1 - OAI.InternalCatalan.palindromicRatT p) ^ P.h N *
    OAI.InternalCatalan.palindromicRatT p ^ P.C N *
    OAI.InternalCatalan.palindromicRatW p ^ rowOffset P N r

theorem rat_row_identity {P : Parameters} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {N r : ℕ} (hC : 0 < P.C N) (hd : rowDistance P N r < P.C N) :
    OAI.InternalCatalan.palindromicRatT p *
        (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (OAI.InternalCatalan.palindromicRatT p) -
      OAI.InternalCatalan.palindromicRatF p *
        (rowD P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (OAI.InternalCatalan.palindromicRatT p) =
      ratRow P p N r := by
  have heval := OAI.InternalCatalan.palindromicRat_chebyshev_signed hp2 (rowOffset P N r)
  rw [← Chebyshev.T_natAbs ℤ (rowOffset P N r),
    ← OAI.InternalCatalan.chebyshev_U_sign_natAbs_eval (Int.castRingHom (RatFunc (ZMod p)))
      ((OAI.InternalCatalan.palindromicRatT p)⁻¹) (rowOffset P N r)] at heval
  have hpow : OAI.InternalCatalan.palindromicRatT p ^ (P.C N - 1) *
      OAI.InternalCatalan.palindromicRatT p = OAI.InternalCatalan.palindromicRatT p ^ P.C N := by
    rw [← pow_succ, Nat.sub_add_cancel hC]
  rw [rowP_eval₂_of_distance_lt _ hd (OAI.InternalCatalan.palindromicRat_T_ne_zero hp2),
    rowD_eval₂_of_distance_lt _ hd (OAI.InternalCatalan.palindromicRat_T_ne_zero hp2)]
  unfold ratRow
  calc
    _ = (1 - OAI.InternalCatalan.palindromicRatT p) ^ P.h N *
        OAI.InternalCatalan.palindromicRatT p ^ (P.C N - 1) *
        (OAI.InternalCatalan.palindromicRatT p *
            (Chebyshev.T ℤ (rowDistance P N r : ℤ)).eval₂
              (Int.castRingHom (RatFunc (ZMod p))) ((OAI.InternalCatalan.palindromicRatT p)⁻¹) -
          OAI.InternalCatalan.palindromicRatF p *
            ((Int.castRingHom (RatFunc (ZMod p))) (Int.sign (rowOffset P N r)) *
              (Chebyshev.U ℤ ((rowDistance P N r : ℤ) - 1)).eval₂
                (Int.castRingHom (RatFunc (ZMod p))) ((OAI.InternalCatalan.palindromicRatT p)⁻¹))) := by ring
    _ = (1 - OAI.InternalCatalan.palindromicRatT p) ^ P.h N *
        OAI.InternalCatalan.palindromicRatT p ^ (P.C N - 1) *
        (OAI.InternalCatalan.palindromicRatT p *
          OAI.InternalCatalan.palindromicRatW p ^ rowOffset P N r) := by
      exact congrArg (fun z : RatFunc (ZMod p) =>
        (1 - OAI.InternalCatalan.palindromicRatT p) ^ P.h N *
          OAI.InternalCatalan.palindromicRatT p ^ (P.C N - 1) * z) heval
    _ = _ := by
      calc _ = (1 - OAI.InternalCatalan.palindromicRatT p) ^ P.h N *
          (OAI.InternalCatalan.palindromicRatT p ^ (P.C N - 1) * OAI.InternalCatalan.palindromicRatT p) *
          OAI.InternalCatalan.palindromicRatW p ^ rowOffset P N r := by ring
        _ = _ := by rw [hpow]

theorem C_scale (P : Parameters) (N : ℕ) : P.C N = P.C 1 * N := by
  simp only [Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
    Parameters.g, Nat.mul_one]
  ring

theorem ratRow_successor (P : Parameters) {p : ℕ} [Fact p.Prime] (N r : ℕ) :
    ratRow P p N (r + 1) = ratRow P p N r * OAI.InternalCatalan.palindromicRatW p := by
  simp only [ratRow, rowOffset,
    zpow_natCast_sub_natCast₀ (OAI.InternalCatalan.palindromicRat_W_ne_zero (p := p)), pow_succ]
  ring

theorem ratRow_scale (P : Parameters) {p : ℕ} [Fact p.Prime] (r0 i : ℕ) :
    ratRow P p p (p * r0 + i) = ratRow P p 1 r0 ^ p * OAI.InternalCatalan.palindromicRatW p ^ i := by
  simp only [ratRow, rowOffset, C_scale P p, Parameters.h, Parameters.g, Nat.mul_one,
    zpow_natCast_sub_natCast₀ (OAI.InternalCatalan.palindromicRat_W_ne_zero (p := p)),
    mul_pow, div_pow, ← pow_mul]
  rw [pow_add, Nat.mul_comm r0 p]
  ring

theorem ratRow_expansion (P : Parameters) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (r0 : ℕ) (i : Fin p) :
    ratRow P p p (p * r0 + i.val) * OAI.InternalCatalan.palindromicRatE p =
      ∑ l : Fin p, OAI.InternalCatalan.palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (OAI.InternalCatalan.palindromicTransitionMatrix p l i) * ratRow P p 1 r0 ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (OAI.InternalCatalan.palindromicReversedTransitionMatrix p l i) *
              ratRow P p 1 (r0 + 1) ^ p) := by
  rw [ratRow_scale]
  have he := OAI.InternalCatalan.palindromicRat_expansion hp2 i
  calc
    _ = ratRow P p 1 r0 ^ p *
        (OAI.InternalCatalan.palindromicRatE p * OAI.InternalCatalan.palindromicRatW p ^ i.val) := by ring
    _ = _ := by
      rw [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [ratRow_successor, mul_pow]
      ring

end
end CatalanMeasure.Parametric
