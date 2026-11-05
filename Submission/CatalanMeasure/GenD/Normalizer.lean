module

public import Submission.CatalanMeasure.Parametric.RawDigitReduction
public import Submission.CatalanMeasure.Parametric.Degree
public import Submission.CatalanMeasure.Parametric.Polynomial
public import Submission.CatalanMeasure.IntegerValued
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

/-!
# Normalizer and Theorem C (coefficient divisibility), generic in the design (module 6)

`Normalizer P` is the data of a denominator `D N` with `D N * Δ_N(i) ∈ ℤ` for all `i : ℕ` and
`q ^ (2 n) ∣ D N` for the recycling primes `N < q ≤ 2 N`.  From it we build the integer polynomial
`Q_N = (n-g)! * D_N * Δ_N` (degree `≤ n - g`) and prove **Theorem C**: `q ^ (2 j) ∣ coeff_j Q_N`
for every recycling prime `q` (generic port of `TwentyCoefficientDivisibility`).
-/

namespace CatalanMeasure.GenD

open Polynomial Matrix Finset CatalanMeasure.Parametric OAI.InternalCatalan
open scoped BigOperators Nat

noncomputable section

/-- The denominator data. -/
structure Normalizer (P : Parameters) where
  adm : Admissible P
  N0 : ℕ
  hN0 : P.H 1 < N0
  D : ℕ → ℕ
  D_ne : ∀ N, D N ≠ 0
  int_val : ∀ N, N0 ≤ N → ∀ i : ℕ,
    ∃ m : ℤ, (D N : ℚ) * Parametric.determinantRat P (i : ℚ) N = m
  recycle : ∀ N q : ℕ, N0 ≤ N → q.Prime → N < q → q ≤ 2 * N → q ^ (2 * P.n N) ∣ D N

namespace Normalizer

variable {P : Parameters} (Z : Normalizer P)

theorem natDegree_denom_mul_delta_le (N : ℕ) (hN : 0 < N) :
    (C (Z.D N : ℚ) * Parametric.deltaPoly P N).natDegree ≤ P.n N - P.g N :=
  (natDegree_C_mul_le _ _).trans (natDegree_deltaPoly_le_ng Z.adm hN)

theorem N0_pos : 0 < Z.N0 := lt_of_le_of_lt (Nat.zero_le _) Z.hN0

theorem denom_mul_delta_int_values {N : ℕ} (hN : Z.N0 ≤ N) (i : ℕ) :
    ∃ m : ℤ, (C (Z.D N : ℚ) * Parametric.deltaPoly P N).eval (i : ℚ) = m := by
  rw [eval_mul, eval_C, Parametric.eval_deltaPoly]
  exact Z.int_val N hN i

/-- The integer polynomial `Q_N = (n-g)! · D_N · Δ_N` (and `0` for `N < N0`). -/
def Q (N : ℕ) : ℤ[X] :=
  if hN : Z.N0 ≤ N then
    Classical.choose (CatalanMeasure.exists_int_poly_factorial_mul
      (C (Z.D N : ℚ) * Parametric.deltaPoly P N)
      (Z.natDegree_denom_mul_delta_le N (lt_of_lt_of_le Z.N0_pos hN))
      (Z.denom_mul_delta_int_values hN))
  else 0

theorem Q_spec {N : ℕ} (hN : Z.N0 ≤ N) :
    (Z.Q N).map (Int.castRingHom ℚ) =
        C ((((P.n N - P.g N) ! : ℕ)) : ℚ) * (C (Z.D N : ℚ) * Parametric.deltaPoly P N) ∧
      (Z.Q N).natDegree ≤ P.n N - P.g N := by
  unfold Q
  rw [dif_pos hN]
  exact Classical.choose_spec (CatalanMeasure.exists_int_poly_factorial_mul
      (C (Z.D N : ℚ) * Parametric.deltaPoly P N)
      (Z.natDegree_denom_mul_delta_le N (lt_of_lt_of_le Z.N0_pos hN))
      (Z.denom_mul_delta_int_values hN))

theorem Q_natDegree_le (N : ℕ) : (Z.Q N).natDegree ≤ P.n N - P.g N := by
  by_cases hN : Z.N0 ≤ N
  · exact (Z.Q_spec hN).2
  · unfold Q
    rw [dif_neg hN]
    simp

theorem aeval_Q {N : ℕ} (hN : Z.N0 ≤ N) (x : ℝ) :
    aeval x (Z.Q N) = (((P.n N - P.g N) ! : ℕ) : ℝ) * (Z.D N : ℝ) *
      aeval x (Parametric.deltaPoly P N) := by
  rw [← aeval_map_algebraMap ℚ x (Z.Q N), algebraMap_int_eq, (Z.Q_spec hN).1]
  simp only [map_mul, aeval_C, eq_ratCast, Rat.cast_natCast]
  try ring

end Normalizer

/-! ### Coefficientwise local polynomials -/

def coefficientLocalRing (q : ℕ) [Fact q.Prime] : Subring ℚ where
  carrier := {a | (a.den : ZMod q) ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun ha hb => (rational_residue_add ha hb).1
  mul_mem' := fun ha hb => (rational_residue_mul ha hb).1
  neg_mem' := by intro a ha; simpa using ha

def coefficientLocalPolynomials (q : ℕ) [Fact q.Prime] : Subring ℚ[X] :=
  Polynomial.liftsRing (coefficientLocalRing q).subtype

theorem mem_coefficientLocalPolynomials_iff {q : ℕ} [Fact q.Prime] (f : ℚ[X]) :
    f ∈ coefficientLocalPolynomials q ↔ ∀ j, ((f.coeff j).den : ZMod q) ≠ 0 := by
  rw [coefficientLocalPolynomials, ← Polynomial.lifts_iff_liftsRing,
    Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h j
    obtain ⟨a, ha⟩ := h j
    rw [← ha]
    exact a.property
  · intro h j
    exact ⟨⟨f.coeff j, h j⟩, rfl⟩

theorem C_mem_coefficientLocalPolynomials {q : ℕ} [Fact q.Prime] {a : ℚ}
    (ha : (a.den : ZMod q) ≠ 0) : C a ∈ coefficientLocalPolynomials q := by
  apply (Polynomial.lifts_iff_liftsRing _ _).mp
  exact Polynomial.C_mem_lifts (coefficientLocalRing q).subtype ⟨a, ha⟩

theorem X_mem_coefficientLocalPolynomials (q : ℕ) [Fact q.Prime] :
    (X : ℚ[X]) ∈ coefficientLocalPolynomials q := by
  apply (Polynomial.lifts_iff_liftsRing _ _).mp
  exact Polynomial.X_mem_lifts (coefficientLocalRing q).subtype

theorem det_mem_coefficientLocalPolynomials {q : ℕ} [Fact q.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ[X])
    (hA : ∀ i j, A i j ∈ coefficientLocalPolynomials q) :
    A.det ∈ coefficientLocalPolynomials q := by
  rw [Matrix.det_apply']
  apply (coefficientLocalPolynomials q).sum_mem
  intro σ hσ
  apply (coefficientLocalPolynomials q).mul_mem
  · exact intCast_mem (coefficientLocalPolynomials q) _
  · exact (coefficientLocalPolynomials q).prod_mem fun i hi => hA _ _

/-- `q² ·` the base matrix is `q`-integral (generic design). -/
theorem scaled_base_den (P : Parameters) {N q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hH : P.H N < q ^ 2) (r k : Fin (P.n N)) :
    (((q : ℚ)^2 * Parametric.measureBaseMatrix P N r k).den : ZMod q) ≠ 0 := by
  change (((q : ℚ)^2 * Parametric.filteredEntryRat P 0 N r.val k.val).den : ZMod q) ≠ 0
  unfold Parametric.filteredEntryRat
  rw [mul_sum]
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  have hraw : (((q : ℚ)^2 * rawEntryRat P 0 N r.val
      (P.b N + k.val + v)).den : ZMod q) ≠ 0 := by
    apply (raw_zero_digit_reduction P hq2 hH ?_).1
    have hk := k.isLt
    have hv' := Finset.mem_range.mp hv
    simp only [Parameters.H, Parameters.C, Parameters.L]
    omega
  have he : (q : ℚ)^2 * (filterCoeffRat P N v *
      rawEntryRat P 0 N r.val (P.b N + k.val + v)) =
      filterCoeffRat P N v * ((q : ℚ)^2 *
        rawEntryRat P 0 N r.val (P.b N + k.val + v)) := by ring
  rw [he]
  exact (rational_residue_mul (filterCoeff_den P N v) hraw).1

theorem catalan_matrix_den (P : Parameters) {N q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (r k : Fin (P.n N)) :
    ((Parametric.measureCatalanMatrix P N r k).den : ZMod q) ≠ 0 := by
  change ((Parametric.filteredCatalanCoeffRat P N r.val k.val).den : ZMod q) ≠ 0
  unfold Parametric.filteredCatalanCoeffRat
  apply (rational_residue_sum _ _ ?_).1
  intro v hv
  exact (rational_residue_mul (filterCoeff_den P N v)
    (rawCatalanCoeff_den P hq2 N r.val (P.b N + k.val + v))).1

theorem int_prime_power_dvd_of_div_den {q : ℕ} [hq : Fact q.Prime]
    (a : ℤ) (k : ℕ)
    (h : ((((a : ℚ)/(q : ℚ)^k).den) : ZMod q) ≠ 0) :
    (q : ℤ)^k ∣ a := by
  let x : ℚ := (a : ℚ)/(q : ℚ)^k
  have hd : ¬q ∣ x.den := by
    intro hv
    exact h ((ZMod.natCast_eq_zero_iff x.den q).mpr hv)
  have hco : IsCoprime ((q : ℤ)^k) (x.den : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using ((hq.out.coprime_iff_not_dvd.mpr hd).pow_left k)
  apply hco.dvd_of_dvd_mul_right
  have hx : (a : ℚ)*(x.den : ℚ) = (x.num : ℚ)*(q : ℚ)^k := by
    have hn := Rat.mul_den_eq_num x
    dsimp only [x] at hn
    have hq0 : (q : ℚ)^k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.out.ne_zero)
    field_simp at hn
    nlinarith only [hn]
  have hxi : a*(x.den : ℤ)=x.num*(q : ℤ)^k := by exact_mod_cast hx
  exact ⟨x.num, by rw [hxi]; ring⟩

/-- Rescaling an affine determinant is an identity of polynomials. -/
theorem affine_det_rescale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℚ) (c : ℚ) (hc : c ≠ 0) :
    (C c) ^ Fintype.card ι *
        (det ((X : ℚ[X]) • B.map C + A.map C)).comp (C c⁻¹ * X) =
      det ((X : ℚ[X]) • B.map C + (c • A).map C) := by
  have hm := RingHom.map_det (Polynomial.compRingHom (C c⁻¹ * X))
    ((X : ℚ[X]) • B.map C + A.map C)
  change (C c)^Fintype.card ι *
    (Polynomial.compRingHom (C c⁻¹ * X))
      (det ((X : ℚ[X]) • B.map C + A.map C)) = _
  rw [hm, ← Matrix.det_smul]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
    smul_eq_mul, RingHom.mapMatrix_apply, Polynomial.coe_compRingHom,
    Polynomial.add_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp]
  rw [mul_add]
  simp only [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc,
    Polynomial.C_1, one_mul]

namespace Normalizer

variable {P : Parameters} (Z : Normalizer P)

/-- Geometry of the recycling primes: `q ≠ 2` and `H N < q²`. -/
theorem recycling_geometry {N q : ℕ} (hN : Z.N0 ≤ N) (hNq : N < q) :
    q ≠ 2 ∧ P.H N < q ^ 2 := by
  have hH2 : 2 ≤ P.H 1 := by
    have := Z.adm
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
      Parameters.q, Parameters.g, Parameters.h, Admissible] at this ⊢
    omega
  have h0 := Z.hN0
  have hs := H_scale P N
  refine ⟨by omega, ?_⟩
  rw [hs]
  have h1 : P.H 1 * N < N * N := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  nlinarith [Nat.mul_le_mul hNq.le hNq.le]

/-- The canonical polynomial at `X/q²` has `q`-integral coefficients. -/
theorem Q_rescaled_local {N q : ℕ} [hq : Fact q.Prime]
    (hN : Z.N0 ≤ N) (hNq : N < q) (hqN : q ≤ 2 * N) :
    ((Z.Q N).map (Int.castRingHom ℚ)).comp
      (C (((q : ℚ)^2)⁻¹) * X) ∈ coefficientLocalPolynomials q := by
  obtain ⟨d, hd⟩ := Z.recycle N q hN hq.out hNq hqN
  have hg := Z.recycling_geometry hN hNq
  let A := Parametric.measureBaseMatrix P N
  let B := Parametric.measureCatalanMatrix P N
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hpow : (C ((q : ℚ)^2) : ℚ[X])^(P.n N) = C ((q : ℚ)^(2 * P.n N)) := by
    rw [← Polynomial.C_pow, ← pow_mul]
  have hs := affine_det_rescale A B ((q : ℚ)^2) (pow_ne_zero _ hq0)
  rw [Fintype.card_fin, hpow] at hs
  have hid : ((Z.Q N).map (Int.castRingHom ℚ)).comp
      (C (((q : ℚ)^2)⁻¹) * X) =
      C ((((P.n N - P.g N) ! : ℕ) : ℚ) * (d : ℚ)) *
        det ((X : ℚ[X]) • B.map C + (((q : ℚ)^2) • A).map C) := by
    rw [(Z.Q_spec hN).1]
    rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.C_comp]
    have hdQ : (Z.D N : ℚ) = (q : ℚ)^(2 * P.n N)*(d : ℚ) := by
      exact_mod_cast hd
    rw [hdQ, Polynomial.C_mul]
    rw [← hs]
    dsimp only [A, B]
    unfold Parametric.deltaPoly
    rw [Polynomial.C_mul]
    ring
  rw [hid]
  apply (coefficientLocalPolynomials q).mul_mem
  · have hc : ((((P.n N - P.g N) ! : ℕ) : ℚ) * (d : ℚ)).den = 1 := by
      calc
        _ = ((((P.n N - P.g N) ! * d : ℕ) : ℚ)).den := by
          congr 1
          exact (Nat.cast_mul _ _).symm
        _ = 1 := Rat.den_natCast _
    apply C_mem_coefficientLocalPolynomials
    rw [hc]
    simpa only [Nat.cast_one] using (one_ne_zero : (1 : ZMod q) ≠ 0)
  · apply det_mem_coefficientLocalPolynomials
    intro r k
    change X * C (B r k) + C ((q : ℚ)^2 * A r k) ∈ _
    apply (coefficientLocalPolynomials q).add_mem
    · exact (coefficientLocalPolynomials q).mul_mem (X_mem_coefficientLocalPolynomials q)
        (C_mem_coefficientLocalPolynomials (catalan_matrix_den P hg.1 r k))
    · exact C_mem_coefficientLocalPolynomials (scaled_base_den P hg.1 hg.2 r k)

/-- **Theorem C.**  Coefficientwise recycling divisibility for every prime `N < q ≤ 2N`. -/
theorem Q_coeff_prime_pow_dvd {N q : ℕ} [Fact q.Prime]
    (hN : Z.N0 ≤ N) (hNq : N < q) (hqN : q ≤ 2 * N) (j : ℕ) :
    (q : ℤ)^(2 * j) ∣ (Z.Q N).coeff j := by
  apply int_prime_power_dvd_of_div_den
  have h := (mem_coefficientLocalPolynomials_iff _).mp
    (Z.Q_rescaled_local hN hNq hqN) j
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h
  change ((((((Z.Q N).coeff j : ℤ) : ℚ) *
    (((q : ℚ)^2)⁻¹)^j).den) : ZMod q) ≠ 0 at h
  simpa only [inv_pow, ← pow_mul, div_eq_mul_inv] using h

end Normalizer

end
end CatalanMeasure.GenD
