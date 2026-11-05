module
public import Submission.CatalanMeasure.Parametric.SecondaryTentDimension
public import Submission.CatalanMeasure.Parametric.SparseFilteredRelation
public import Mathlib.Algebra.Group.ForwardDiff
@[expose] public section

namespace CatalanMeasure.Parametric
open Matrix Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- The alternating binomial filter annihilates every polynomial of degree
below its order, in arbitrary characteristic. -/
theorem secondaryTent_polynomial_filter_zero {K : Type*} [Field K]
    (F : K[X]) {q : ℕ} (hF : F.natDegree < q) (y : K) :
    (∑ v ∈ Finset.range (q + 1),
      (-1 : K) ^ v * (q.choose v : K) * F.eval (y + (v : K))) = 0 := by
  have hf := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hF) y
  rw [fwdDiff_iter_eq_sum_shift] at hf
  have hs : (∑ v ∈ Finset.range (q + 1),
      (-1 : K) ^ (q - v) * (q.choose v : K) * F.eval (y + (v : K))) = 0 := by
    simpa only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, nsmul_one, Pi.zero_apply] using hf
  calc
    _ = (-1 : K) ^ q * ∑ v ∈ Finset.range (q + 1),
        (-1 : K) ^ (q - v) * (q.choose v : K) * F.eval (y + (v : K)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      have hvq : v ≤ q := by have := Finset.mem_range.mp hv; omega
      have hsq : (-1 : K) ^ (q - v) * (-1 : K) ^ (q - v) = 1 := by
        rcases neg_one_pow_eq_or K (q - v) with h | h <;> simp [h]
      have hsign : (-1 : K) ^ q * (-1 : K) ^ (q - v) = (-1 : K) ^ v := by
        calc
          _ = ((-1 : K) ^ v * (-1 : K) ^ (q - v)) * (-1 : K) ^ (q - v) := by
            rw [← pow_add (-1 : K) v (q - v), Nat.add_sub_of_le hvq]
          _ = (-1 : K) ^ v := by rw [mul_assoc, hsq, mul_one]
      calc
        _ = ((-1 : K) ^ q * (-1 : K) ^ (q - v)) *
            (q.choose v : K) * F.eval (y + (v : K)) := by rw [hsign]
        _ = _ := by ring
    _ = 0 := by rw [hs, mul_zero]

/-- A row whose actual raw residue response is polynomial of degree below
the filter order belongs to the left kernel of the actual filtered residue
matrix.  This uses the existing coefficientwise scaled residue identity. -/
theorem secondaryTent_raw_polynomial_response_kernel {P : Parameters} {p N : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0)
    (u : Fin (P.n N) → ZMod p) (F : (ZMod p)[X])
    (hF : F.natDegree < P.q N)
    (hraw : ∀ j, P.b N ≤ j → j < P.L N →
      (∑ r : Fin (P.n N),
        palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P z N r.val j) * u r) =
          F.eval (j : ZMod p)) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P z N r.val k.val)).transpose.mulVecLin u = 0 := by
  classical
  funext k
  change (∑ r : Fin (P.n N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat P z N r.val k.val) * u r) = 0
  simp_rw [(filteredEntry_scaled_residue_sum_general hp2 hH k.isLt z hzp).2,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ v ∈ Finset.range (P.q N + 1),
        palindromicRatResidue p (filterCoeffRat P N v) *
          F.eval ((P.b N + k.val + v : ℕ) : ZMod p) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvq : v ≤ P.q N := by have := Finset.mem_range.mp hv; omega
      have hj : P.b N + k.val + v < P.L N := rawColumn_lt_L k.isLt hvq
      rw [← hraw _ (by omega) hj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = 0 := by
      simp_rw [filterCoeff_residue]
      simpa only [Nat.cast_add] using
        secondaryTent_polynomial_filter_zero F hF ((P.b N + k.val : ℕ) : ZMod p)

/-- Complete finite-dimensional bridge from constrained polynomial raw
responses to the rank of the existing canonical filtered residue matrix.
The remaining analytic/source work is exactly the construction of `J`
and its stated raw-response property. -/
theorem secondaryTent_rank_of_raw_polynomial_responses
    {P : Parameters} {p N : ℕ} [Fact p.Prime]
    {V C : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Fintype C]
    (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0)
    (cost : C → ℕ) (B : ∀ i, V →ₗ[ZMod p] (Fin (cost i) → ZMod p))
    (J : LinearMap.ker (secondaryTentConstraintMap cost B) →ₗ[ZMod p]
      (Fin (P.n N) → ZMod p)) (hJ : Function.Injective J)
    (hraw : ∀ v, ∃ F : (ZMod p)[X], F.natDegree < P.q N ∧
      ∀ j, P.b N ≤ j → j < P.L N →
        (∑ r : Fin (P.n N),
          palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P z N r.val j) * J v r) =
            F.eval (j : ZMod p)) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P z N r.val k.val)).rank +
        (Module.finrank (ZMod p) V - ∑ i, cost i) ≤ P.n N := by
  apply secondaryTent_rank_of_constraints _ cost B J hJ
  intro v
  obtain ⟨F, hF, hresp⟩ := hraw v
  exact secondaryTent_raw_polynomial_response_kernel hp2 hH z hzp (J v) F hF hresp

end
end CatalanMeasure.Parametric
