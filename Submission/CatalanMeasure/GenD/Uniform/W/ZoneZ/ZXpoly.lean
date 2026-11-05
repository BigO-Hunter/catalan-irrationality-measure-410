module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZPoly
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.LemmaX2
@[expose] public section
set_option Elab.async false

/-!
# Lemma X for atoms: the top block and block 0

For symmetric/antisymmetric data `s, a : F^{hp+1}` of one block with `s_δ + a_δ = 0` for
`r < δ ≤ hp` (the rows `c + δ` beyond the last actual row are virtual), the `hi`-part of
`Pi_poly s` plus `La_poly a` has degree `< h + r`:

    (Pi_poly s).coeff (i + p) + (La_poly a).coeff i = 0   for   i ≥ h + r.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The row vector of one block: `c_δ = s_δ + a_δ`, `c_{-δ} = s_δ - a_δ`. -/
def rowVec {hp : ℕ} (s a : Fin (hp + 1) → ZMod p) : ℤ →₀ ZMod p :=
  ∑ d : Fin (hp + 1), (Finsupp.single ((d : ℕ) : ℤ) (s d + a d) +
    Finsupp.single (-((d : ℕ) : ℤ)) (s d - a d))

theorem Tl_rowVec {hp : ℕ} (s a : Fin (hp + 1) → ZMod p) :
    Tl (rowVec s a) = 2 * tpoly s := by
  unfold rowVec tpoly
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_add, Tl_single, Tl_single, Chebyshev.T_neg]
  simp only [smul_eq_C_mul]
  have : (C (s d + a d) + C (s d - a d) : (ZMod p)[X]) = 2 * C (s d) := by
    simp only [map_add, map_sub]; ring
  rw [← add_mul, this]; ring

theorem Ul_rowVec {hp : ℕ} (s a : Fin (hp + 1) → ZMod p) :
    Ul (rowVec s a) = 2 * upoly a := by
  unfold rowVec upoly
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_add, Ul_single, Ul_single]
  have h1 : Chebyshev.U (ZMod p) (-((d : ℕ) : ℤ) - 1) = - Chebyshev.U (ZMod p) (((d : ℕ) : ℤ) - 1) :=
    Chebyshev.U_neg_sub_one (R := ZMod p) ((d : ℕ) : ℤ)
  rw [h1]
  simp only [smul_eq_C_mul, map_add, map_sub]
  ring

theorem rowVec_apply {hp : ℕ} (s a : Fin (hp + 1) → ZMod p) (m : ℤ) :
    rowVec s a m = ∑ d : Fin (hp + 1), ((if m = ((d : ℕ) : ℤ) then s d + a d else 0) +
      (if m = -((d : ℕ) : ℤ) then s d - a d else 0)) := by
  unfold rowVec
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [eq_comm]

theorem rowVec_supp_abs {hp : ℕ} (s a : Fin (hp + 1) → ZMod p) :
    ∀ m : ℤ, hp < m.natAbs → rowVec s a m = 0 := by
  intro m hm
  rw [rowVec_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  have := d.isLt
  rw [if_neg (by omega), if_neg (by omega)]; simp

theorem rowVec_supp_pos {hp : ℕ} (s a : Fin (hp + 1) → ZMod p) (r : ℕ)
    (h : ∀ d : Fin (hp + 1), r < (d : ℕ) → s d + a d = 0) :
    ∀ m : ℤ, (r : ℤ) < m → rowVec s a m = 0 := by
  intro m hm
  rw [rowVec_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases h1 : m = ((d : ℕ) : ℤ)
  · rw [if_pos h1, if_neg (by omega)]
    have : r < (d : ℕ) := by omega
    rw [h d this]; simp
  · rw [if_neg h1, if_neg (by omega)]; simp

/-- **Lemma X for a block.** -/
theorem blockX (hp2 : p ≠ 2) {hp : ℕ} (hhp : P.h N + hp < p) (s a : Fin (hp + 1) → ZMod p)
    (r : ℕ) (h : ∀ d : Fin (hp + 1), r < (d : ℕ) → s d + a d = 0) (i : ℕ) (hi : P.h N + r ≤ i) :
    (Pi_poly P N p s).coeff (i + p) + (La_poly P N p a).coeff i = 0 := by
  obtain ⟨L, Hh, e1, e2, e3⟩ := lemmaX_iter hp2 (h := P.h N) (r := r) (B := hp) (by omega)
    (rowVec s a) (rowVec_supp_abs s a) (rowVec_supp_pos s a r h)
  rw [Tl_rowVec] at e1
  rw [Ul_rowVec] at e3
  have hw := chebyshev_U_prime (p := p) hp2
  rw [hw] at e1
  have h2 : ((2 * X - 2 : (ZMod p)[X])) = C 2 * (X - 1) := by simp only [map_ofNat]; ring
  have hc : ((2 : ZMod p) ^ P.h N) ≠ 0 := pow_ne_zero _ (two_ne_zero_zmod hp2)
  -- identify the polynomials
  have eP : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * ((2 * X - 2 : (ZMod p)[X]) ^ P.h N * (2 * tpoly s)) =
      C ((2 : ZMod p) ^ P.h N) * Pi_poly P N p s := by
    rw [Pi_poly_eq, h2, mul_pow, ← C_pow]
    ring
  have eL : (2 * X - 2 : (ZMod p)[X]) ^ P.h N * (2 * upoly a) =
      C ((2 : ZMod p) ^ P.h N) * La_poly P N p a := by
    rw [La_poly_eq, h2, mul_pow, ← C_pow]; ring
  rw [eP] at e1
  rw [eL] at e3
  have c1 : ((C ((2 : ZMod p) ^ P.h N) * Pi_poly P N p s)).coeff (i + p) = Hh.coeff i := by
    rw [e1, coeff_add, coeff_X_pow_mul, coeff_eq_zero_of_degree_lt (by
      calc L.degree < p := e2
        _ ≤ ((i + p : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : p ≤ i + p)), zero_add]
  have c2 := e3 i hi
  rw [coeff_add, coeff_C_mul] at c2
  rw [coeff_C_mul] at c1
  have : (2 : ZMod p) ^ P.h N * ((Pi_poly P N p s).coeff (i + p) + (La_poly P N p a).coeff i) = 0 := by
    rw [mul_add, c1, c2]
  exact (mul_eq_zero.mp this).resolve_left hc

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
