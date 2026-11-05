module
public import Submission.CatalanMeasure.GenD.RankU
@[expose] public section

/-!
# Filtered-column digit formula (GenD, shared layer of Theorems U6g and S)

For a design `P`, `N > 0`, an odd prime `p` with `H < p^2`, and a filtered column `k` whose raw
columns `b+k+v` (`0 ≤ v ≤ q`) share one digit (`(b+k) % p + q < p`), the response of the row
combination `c` is
`∑_u alpha(u,J) Qh[u p + mu] + beta(u,J) Dh[u p + mu]`, `mu = (b+k) % p + q`, `J = (b+k) / p`,
with `Qh = (X-1)^q X W F`, `Dh = (X-1)^q G`, `F = (1-X)^h S_c`, `G = (1-X)^h U_c`.
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

theorem binom_filter' {R : Type*} [CommRing R] (A : R[X]) (m n : ℕ) :
    ∑ v ∈ Finset.range (n + 1), (-1 : R) ^ v * (n.choose v : R) * A.coeff (m + v) =
      ((X - 1) ^ n * A).coeff (m + n) := by
  have h1 : (X - 1 : R[X]) ^ n = ∑ i ∈ Finset.range (n + 1),
      X ^ i * C ((-1 : R) ^ (n - i) * (n.choose i : R)) := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [map_mul, map_pow]; ring
  rw [h1, Finset.sum_mul, finsetSum_coeff]
  have h2 : ∀ i ∈ Finset.range (n + 1), (X ^ i * C ((-1 : R) ^ (n - i) * (n.choose i : R)) * A).coeff
      (m + n) = (-1 : R) ^ (n - i) * (n.choose i : R) * A.coeff (m + n - i) := by
    intro i hi
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [mul_assoc, coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
      coeff_C_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvn : v ≤ n := by have := Finset.mem_range.mp hv; omega
  rw [show n + 1 - 1 - v = n - v by omega, Nat.choose_symm hvn, Nat.add_sub_assoc hvn]

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- `F = (1-X)^h S_c`. -/
def fP (P : Parameters) (N p : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : (ZMod p)[X] :=
  (1 - X) ^ P.h N * uS p (P.C N) (P.g N) (P.n N) c

/-- `G = (1-X)^h U_c`. -/
def gP (P : Parameters) (N p : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : (ZMod p)[X] :=
  (1 - X) ^ P.h N * uU p (P.C N) (P.g N) (P.n N) c

/-- `Qh = (X-1)^q X W F`. -/
def qhP (P : Parameters) (N p : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : (ZMod p)[X] :=
  (X - 1) ^ P.q N * (X * oddPrimeWeight p * fP P N p c)

/-- `Dh = (X-1)^q G`. -/
def dhP (P : Parameters) (N p : ℕ) [Fact p.Prime] (c : Fin (P.n N) → ZMod p) : (ZMod p)[X] :=
  (X - 1) ^ P.q N * gP P N p c

/-- Response of the row combination `c` at filtered column `k`. -/
def fResp (P : Parameters) (N p k : ℕ) [Fact p.Prime] :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun c := ∑ r : Fin (P.n N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat P 0 N r.val k) * c r
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_left_comm]

theorem fResp_eq_mulVec (c : Fin (P.n N) → ZMod p) (k : Fin (P.n N)) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).transpose.mulVecLin
        c k = fResp P N p k.val c := rfl

theorem fResp_eq_sum_uResp (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {k : ℕ} (hk : k < P.n N) (c : Fin (P.n N) → ZMod p) :
    fResp P N p k c = ∑ v ∈ Finset.range (P.q N + 1),
      (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) * uResp P N p (P.b N + k + v) c := by
  have hzp : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  change (∑ r : Fin (P.n N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat P 0 N r.val k) * c r) = _
  simp_rw [(filteredEntry_scaled_residue_sum_general hp2 hH hk 0 hzp).2, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [filterCoeff_residue]
  simp only [uResp, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- Digit formula for a filtered column whose raw columns share one digit. -/
theorem fResp_digit (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {k : ℕ} (hk : k < P.n N) (hmu : (P.b N + k) % p + P.q N < p)
    (c : Fin (P.n N) → ZMod p) :
    fResp P N p k c =
      ∑ u ∈ Finset.range (P.H N + 1),
        palindromicRatResidue p (momentRatSigned ((u : ℤ) - 1) ((P.b N + k) / p)) *
          (qhP P N p c).coeff (u * p + ((P.b N + k) % p + P.q N)) -
      (3 / 2 : ZMod p) * ∑ u ∈ Finset.range (P.H N),
        palindromicRatResidue p (zetaRat u ((P.b N + k) / p)) *
          (dhP P N p c).coeff (u * p + ((P.b N + k) % p + P.q N)) := by
  have hpos := hp.out.pos
  rw [fResp_eq_sum_uResp hP hN hp2 hH hk c]
  have hLH : P.L N ≤ P.H N := by
    have h1 : P.C N = P.L N + P.g N := rfl
    have h2 : P.H N = P.C N + P.h N := rfl
    omega
  have hlt0 : ∀ v ≤ P.q N, P.b N + k + v < P.L N := fun v hv => rawColumn_lt_L hk hv
  generalize hs : P.b N + k = s at hmu hlt0 ⊢
  have hsd := Nat.div_add_mod s p
  generalize hJ : s / p = J at hsd ⊢
  generalize hl : s % p = l at hsd hmu ⊢
  have hv : ∀ v ∈ Finset.range (P.q N + 1), (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) *
      uResp P N p (s + v) c = (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) *
        (∑ u ∈ Finset.range (P.H N + 1),
          (X * oddPrimeWeight p * fP P N p c).coeff (u * p + (l + v)) *
            palindromicRatResidue p (momentRatSigned ((u : ℤ) - 1) J) -
        (3 / 2 : ZMod p) * ∑ u ∈ Finset.range (P.H N),
          (gP P N p c).coeff (u * p + (l + v)) *
            palindromicRatResidue p (zetaRat u J)) := by
    intro v hv
    have hvq : v ≤ P.q N := by have := Finset.mem_range.mp hv; omega
    have hlt := hlt0 v hvq
    have hsv : s + v = p * J + (l + v) := by rw [← hsd]; ring
    have h1 : (s + v) / p = J := by
      rw [hsv, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), add_zero]
    have h2 : (s + v) % p = l + v := by
      rw [hsv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [uResp_eq hP hN hp2 hH (by omega) c]
    unfold primeDigitPair primeDigitSample
    rw [h1, h2]
    rfl
  rw [Finset.sum_congr rfl hv]
  have hQ : ∀ u, ((qhP P N p c).coeff (u * p + (l + P.q N))) =
      ∑ v ∈ Finset.range (P.q N + 1), (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) *
        (X * oddPrimeWeight p * fP P N p c).coeff (u * p + (l + v)) := by
    intro u
    unfold qhP
    rw [show u * p + (l + P.q N) = (u * p + l) + P.q N by ring, ← binom_filter']
    exact Finset.sum_congr rfl fun v _ => by rw [show u * p + l + v = u * p + (l + v) by ring]
  have hD : ∀ u, ((dhP P N p c).coeff (u * p + (l + P.q N))) =
      ∑ v ∈ Finset.range (P.q N + 1), (-1 : ZMod p) ^ v * ((P.q N).choose v : ZMod p) *
        (gP P N p c).coeff (u * p + (l + v)) := by
    intro u
    unfold dhP
    rw [show u * p + (l + P.q N) = (u * p + l) + P.q N by ring, ← binom_filter']
    exact Finset.sum_congr rfl fun v _ => by rw [show u * p + l + v = u * p + (l + v) by ring]
  simp only [hQ, hD, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    refine Finset.sum_congr rfl fun v _ => by ring

/-- Vanishing digits give a vanishing response. -/
theorem fResp_eq_zero (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {k : ℕ} (hk : k < P.n N) (hmu : (P.b N + k) % p + P.q N < p)
    (c : Fin (P.n N) → ZMod p)
    (hQ : ∀ u ≤ P.H N, (qhP P N p c).coeff (u * p + ((P.b N + k) % p + P.q N)) = 0)
    (hD : ∀ u < P.H N, (dhP P N p c).coeff (u * p + ((P.b N + k) % p + P.q N)) = 0) :
    fResp P N p k c = 0 := by
  rw [fResp_digit hP hN hp2 hH hk hmu c]
  rw [Finset.sum_eq_zero (fun u hu => by rw [hQ u (by have := Finset.mem_range.mp hu; omega),
      mul_zero]),
    Finset.sum_eq_zero (fun u hu => by rw [hD u (Finset.mem_range.mp hu), mul_zero])]
  simp

end
end
end CatalanMeasure.GenD
