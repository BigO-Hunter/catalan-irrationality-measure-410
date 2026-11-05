module
public import Submission.CatalanMeasure.Parametric.RowFrobenius
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem C_pos {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) :
    0 < P.C N := by
  have hn := n_pos hP hN
  unfold Parameters.C Parameters.L
  omega

theorem base_distance_lt {P : Parameters} (hP : Admissible P) {j : ℕ}
    (hj : j ≤ P.n0) : rowDistance P 1 j < P.C 1 := by
  have hg := hP.2.2.2.2
  have hb := hP.2.1
  simp only [rowDistance, rowOffset, Parameters.g, Parameters.C, Parameters.L,
    Parameters.n, Parameters.b, Parameters.q, Nat.mul_one]
  omega

theorem block_row_lt (P : Parameters) {p r0 : ℕ} [Fact p.Prime]
    (hr : r0 < P.n0) (i : Fin p) : p * r0 + i.val < P.n p := by
  have hm := Nat.mul_le_mul_left p (show r0 + 1 ≤ P.n0 by omega)
  have hi := i.isLt
  simp only [Nat.mul_add, Nat.mul_one] at hm
  unfold Parameters.n
  nlinarith

theorem ratRow_eq_actual {P : Parameters} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {N r : ℕ} (hC : 0 < P.C N)
    (hd : rowDistance P N r < P.C N) :
    ratRow P p N r = palindromicRatT p *
      (rowP P N r).eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) -
      palindromicRatF p * (rowD P N r).eval₂
        (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p) :=
  (rat_row_identity hp2 hC hd).symm

def PBase (P : Parameters) (p j : ℕ) : (ZMod p)[X] :=
  (rowP P 1 j).map (Int.castRingHom (ZMod p))

def DBase (P : Parameters) (p j : ℕ) : (ZMod p)[X] :=
  (rowD P 1 j).map (Int.castRingHom (ZMod p))

def PBaseCombination (P : Parameters) (p r0 : ℕ) (i l : Fin p) : (ZMod p)[X] :=
  C (palindromicTransitionMatrix p l i) * PBase P p r0 +
    C (palindromicReversedTransitionMatrix p l i) * PBase P p (r0 + 1)

def DBaseCombination (P : Parameters) (p r0 : ℕ) (i l : Fin p) : (ZMod p)[X] :=
  C (palindromicTransitionMatrix p l i) * DBase P p r0 +
    C (palindromicReversedTransitionMatrix p l i) * DBase P p (r0 + 1)

def PResidueSum (P : Parameters) (p r0 : ℕ) (i : Fin p) : (ZMod p)[X] :=
  ∑ l : Fin p, X ^ l.val * X ^ p *
    (C (palindromicTransitionMatrix p l i) * (PBase P p r0).comp (X ^ p) +
      C (palindromicReversedTransitionMatrix p l i) *
        (PBase P p (r0 + 1)).comp (X ^ p))

def DResidueSum (P : Parameters) (p r0 : ℕ) (i : Fin p) : (ZMod p)[X] :=
  ∑ l : Fin p, X ^ l.val *
    (C (palindromicTransitionMatrix p l i) * (DBase P p r0).comp (X ^ p) +
      C (palindromicReversedTransitionMatrix p l i) *
        (DBase P p (r0 + 1)).comp (X ^ p))

theorem PResidueSum_eq_X_pow_mul (P : Parameters) (p r0 : ℕ) (i : Fin p) :
    PResidueSum P p r0 i = X ^ p *
      palindromicResidueSum p (PBaseCombination P p r0 i) := by
  classical
  simp only [PResidueSum, palindromicResidueSum,
    PBaseCombination, add_comp, mul_comp, C_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem DResidueSum_eq (P : Parameters) (p r0 : ℕ) (i : Fin p) :
    DResidueSum P p r0 i =
      palindromicResidueSum p (DBaseCombination P p r0 i) := by
  simp only [DResidueSum, palindromicResidueSum,
    DBaseCombination, add_comp, mul_comp, C_comp]

theorem PResidueSum_coeff (P : Parameters) (p r0 u : ℕ) (i ell : Fin p) :
    (PResidueSum P p r0 i).coeff ((u + 1) * p + ell.val) =
      palindromicTransitionMatrix p ell i * (PBase P p r0).coeff u +
        palindromicReversedTransitionMatrix p ell i *
          (PBase P p (r0 + 1)).coeff u := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le ell.val) ell.isLt
  have hindex : (u + 1) * p + ell.val = (u * p + ell.val) + p := by ring
  rw [PResidueSum_eq_X_pow_mul P, hindex, coeff_X_pow_mul,
    palindromicResidueSum_coeff hp]
  simp only [PBaseCombination, coeff_add, coeff_C_mul]

theorem DResidueSum_coeff (P : Parameters) (p r0 u : ℕ) (i ell : Fin p) :
    (DResidueSum P p r0 i).coeff (u * p + ell.val) =
      palindromicTransitionMatrix p ell i * (DBase P p r0).coeff u +
        palindromicReversedTransitionMatrix p ell i *
          (DBase P p (r0 + 1)).coeff u := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le ell.val) ell.isLt
  rw [DResidueSum_eq P, palindromicResidueSum_coeff hp]
  simp only [DBaseCombination, coeff_add, coeff_C_mul]

theorem PResidueSum_coeff_below (P : Parameters) (p r0 : ℕ) (i ell : Fin p) :
    (PResidueSum P p r0 i).coeff ell.val = 0 := by
  rw [PResidueSum_eq_X_pow_mul P, coeff_X_pow_mul',
    ite_eq_right (Nat.not_le_of_lt ell.isLt)]

theorem PResidueSum_eval₂ (P : Parameters) {p : ℕ} [Fact p.Prime]
    (r0 : ℕ) (i : Fin p) :
    (PResidueSum P p r0 i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      ∑ l : Fin p, palindromicRatT p ^ l.val * palindromicRatT p ^ p *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicTransitionMatrix p l i) *
            ((rowP P 1 r0).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
            ((rowP P 1 (r0 + 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p) := by
  simp only [PResidueSum, eval₂_finsetSum, eval₂_mul,
    eval₂_X_pow, eval₂_add, eval₂_C, palindromicRat_polynomial_comp_X_pow_eval₂,
    PBase, palindromicRat_int_map_eval₂]

theorem DResidueSum_eval₂ (P : Parameters) {p : ℕ} [Fact p.Prime]
    (r0 : ℕ) (i : Fin p) :
    (DResidueSum P p r0 i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p) =
      ∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicTransitionMatrix p l i) *
            ((rowD P 1 r0).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
            ((rowD P 1 (r0 + 1)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
              (palindromicRatT p)) ^ p) := by
  simp only [DResidueSum, eval₂_finsetSum, eval₂_mul,
    eval₂_X_pow, eval₂_add, eval₂_C, palindromicRat_polynomial_comp_X_pow_eval₂,
    DBase, palindromicRat_int_map_eval₂]

theorem rows_separated (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < P.n0) (i : Fin p) :
    (palindromicRatT p *
        (rowP P p (p * r₀ + i.val)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
          (palindromicRatT p) * palindromicRatE p =
      (PResidueSum P p r₀ i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) ∧
    ((rowD P p (p * r₀ + i.val)).eval₂ (Int.castRingHom (RatFunc (ZMod p)))
        (palindromicRatT p) =
      (DResidueSum P p r₀ i).eval₂
        (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)) := by
  let ev : ℤ[X] → RatFunc (ZMod p) := fun P =>
    P.eval₂ (Int.castRingHom (RatFunc (ZMod p))) (palindromicRatT p)
  let evp : (ZMod p)[X] → RatFunc (ZMod p) := fun P =>
    P.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p))) (palindromicRatT p)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmain := ratRow_eq_actual (P := P) hp2 (C_pos hP hp)
    (rowDistance_lt_C hP hp (block_row_lt P hr i))
  have hbase := ratRow_eq_actual (P := P) hp2 (N := 1) (r := r₀)
    (C_pos hP (by decide)) (base_distance_lt hP (by omega))
  have hnext := ratRow_eq_actual (P := P) hp2 (N := 1) (r := r₀ + 1)
    (C_pos hP (by decide)) (base_distance_lt hP (by omega))
  have hraw := ratRow_expansion P hp2 r₀ i
  rw [hmain, hbase, hnext] at hraw
  have hleft :
      (palindromicRatT p * ev (rowP P p (p * r₀ + i.val)) -
        palindromicRatF p * ev (rowD P p (p * r₀ + i.val))) * palindromicRatE p =
      palindromicRatT p * ev (rowP P p (p * r₀ + i.val)) * palindromicRatE p -
        palindromicRatF p ^ p * ev (rowD P p (p * r₀ + i.val)) := by
    rw [← palindromicRat_F_mul_E hp2]
    ring
  have hright :
      (∑ l : Fin p, palindromicRatT p ^ l.val *
        (algebraMap (ZMod p) (RatFunc (ZMod p)) (palindromicTransitionMatrix p l i) *
            (palindromicRatT p * ev (rowP P 1 r₀) - palindromicRatF p * ev (rowD P 1 r₀)) ^ p +
          algebraMap (ZMod p) (RatFunc (ZMod p))
            (palindromicReversedTransitionMatrix p l i) *
              (palindromicRatT p * ev (rowP P 1 (r₀ + 1)) -
                palindromicRatF p * ev (rowD P 1 (r₀ + 1))) ^ p)) =
        evp (PResidueSum P p r₀ i) -
          palindromicRatF p ^ p * evp (DResidueSum P p r₀ i) := by
    dsimp only [evp]
    rw [PResidueSum_eval₂ P, DResidueSum_eval₂ P,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [sub_pow_char, mul_pow]
    dsimp only [ev]
    ring
  change (palindromicRatT p * ev (rowP P p (p * r₀ + i.val)) -
      palindromicRatF p * ev (rowD P p (p * r₀ + i.val))) * palindromicRatE p = _ at hraw
  rw [hleft, hright] at hraw
  have hstar := congrArg (palindromicRatStar p) hraw
  dsimp only [ev, evp] at hstar
  simp only [map_sub, map_mul, palindromicRatStar_T, palindromicRatStar_E,
    palindromicRatStar_eval₂_int, palindromicRatStar_F_pow hp2,
    palindromicRatStar_eval₂] at hstar
  have hP : palindromicRatT p * ev (rowP P p (p * r₀ + i.val)) * palindromicRatE p =
      evp (PResidueSum P p r₀ i) := by
    apply mul_left_cancel₀ (palindromicRat_two_ne_zero hp2)
    dsimp only [ev, evp] at *
    linear_combination hraw + hstar
  have hD : ev (rowD P p (p * r₀ + i.val)) = evp (DResidueSum P p r₀ i) := by
    apply mul_left_cancel₀ (pow_ne_zero p (palindromicRat_F_ne_zero (p := p)))
    linear_combination hP - hraw
  exact ⟨hP, hD⟩

theorem rowP_frobenius (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < P.n0) (i : Fin p) :
    X * (rowP P p (p * r₀ + i.val)).map (Int.castRingHom (ZMod p)) *
        (1 - X ^ 2) ^ ((p - 1) / 2) = PResidueSum P p r₀ i := by
  apply palindromicRatT_eval₂RingHom_injective hp2
  change eval₂ _ _ _ = eval₂ _ _ _
  simp only [eval₂_mul, eval₂_X, eval₂_pow, eval₂_sub, eval₂_one,
    palindromicRat_int_map_eval₂]
  exact (rows_separated P hP hp2 hr i).1

theorem rowD_frobenius (P : Parameters) {p : ℕ} [Fact p.Prime]
    (hP : Admissible P) (hp2 : p ≠ 2) {r₀ : ℕ} (hr : r₀ < P.n0) (i : Fin p) :
    (rowD P p (p * r₀ + i.val)).map (Int.castRingHom (ZMod p)) =
      DResidueSum P p r₀ i := by
  apply palindromicRatT_eval₂RingHom_injective hp2
  change eval₂ _ _ _ = eval₂ _ _ _
  rw [palindromicRat_int_map_eval₂]
  exact (rows_separated P hP hp2 hr i).2

end
end CatalanMeasure.Parametric
