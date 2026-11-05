module
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Choose.Dvd
@[expose] public section
set_option Elab.async false

/-!
# The Lucas lemma for the `q`-th difference (`q ≥ p`)

Let `p` be an odd prime and `q ≥ p`.  A sequence `R(j) = A(j mod p) + (j / p) B(j mod p)` whose slope
`B` is a polynomial function of degree `< q - p` has vanishing `q`-th forward difference.

Proof: in characteristic `p` the `p`-th difference is the shift by `p` (`fwdDiff_iter_prime`), which
turns `R` into the polynomial `B(j)`; the remaining `(q - p)`-th difference kills it.

`filter_sum_of_fwdDiff_zero` converts `Δ^q S = 0` into the alternating binomial filter
`∑_{v ≤ q} (-1)^v C(q,v) S(y+v) = 0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Finset Polynomial fwdDiff
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- In characteristic `p` (odd) the `p`-th forward difference is `f(z + p) - f(z)`. -/
theorem fwdDiff_iter_prime (hp2 : p ≠ 2) (f : ℤ → ZMod p) (z : ℤ) :
    Δ_[(1 : ℤ)]^[p] f z = f (z + p) - f z := by
  have hp : p.Prime := Fact.out
  rw [fwdDiff_iter_eq_sum_shift]
  have hp0 : 0 ∈ range (p + 1) := mem_range.mpr (by omega)
  have hpp : p ∈ range (p + 1) := mem_range.mpr (by omega)
  have hne : (0 : ℕ) ≠ p := hp.ne_zero.symm
  rw [Finset.sum_eq_add_of_mem 0 p hp0 hpp hne]
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, pow_zero, one_mul, mul_one, hodd.neg_one_pow, nsmul_eq_mul, Nat.cast_zero,
      add_zero]
    ring
  · intro k hk hkab
    have hkp : k < p := by
      have := mem_range.mp hk
      have := hkab.2
      omega
    have hk0 : k ≠ 0 := hkab.1
    have hd : p ∣ p.choose k := Nat.Prime.dvd_choose_self hp hk0 hkp
    have : ((p.choose k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simp [zsmul_eq_mul, this]

/-- Differences commute with the cast `ℤ → ZMod p`. -/
theorem fwdDiff_iter_cast (G : ZMod p → ZMod p) (n : ℕ) (z : ℤ) :
    Δ_[(1 : ℤ)]^[n] (fun w : ℤ => G (w : ZMod p)) z = (Δ_[(1 : ZMod p)]^[n] G) (z : ZMod p) := by
  induction n generalizing G with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have : Δ_[(1 : ℤ)] (fun w : ℤ => G (w : ZMod p)) =
        fun w : ℤ => (Δ_[(1 : ZMod p)] G) (w : ZMod p) := by
      funext w
      simp [fwdDiff]
    rw [this]
    exact ih (Δ_[(1 : ZMod p)] G)

/-- A polynomial function of degree `< n` has vanishing `n`-th difference (degree form). -/
theorem fwdDiff_iter_eval_zero {n : ℕ} (B : (ZMod p)[X]) (hB : B.degree < (n : WithBot ℕ)) :
    Δ_[(1 : ZMod p)]^[n] (fun y => B.eval y) = 0 := by
  by_cases h0 : B = 0
  · subst h0
    clear hB
    simp only [eval_zero]
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      have : Δ_[(1 : ZMod p)] (fun _ : ZMod p => (0 : ZMod p)) = fun _ => 0 := by
        funext w; simp [fwdDiff]
      rw [this]
      exact ih
  · have : B.natDegree < n := by
      rw [Polynomial.degree_eq_natDegree h0] at hB
      exact_mod_cast hB
    exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt this

/-- The sequence `A(j) + (j / p) B(j)`. -/
def lucasSeq (p : ℕ) [Fact p.Prime] (A : ZMod p → ZMod p) (B : (ZMod p)[X]) : ℤ → ZMod p :=
  fun z => A (z : ZMod p) + ((z / (p : ℤ) : ℤ) : ZMod p) * B.eval (z : ZMod p)

/-- **Lucas lemma.** `Δ^q (A(j) + (j/p) B(j)) = 0` for `q ≥ p` and `deg B < q - p`. -/
theorem fwdDiff_lucasSeq (hp2 : p ≠ 2) {q : ℕ} (hpq : p ≤ q) (A : ZMod p → ZMod p)
    (B : (ZMod p)[X]) (hB : B.degree < ((q - p : ℕ) : WithBot ℕ)) (z : ℤ) :
    Δ_[(1 : ℤ)]^[q] (lucasSeq p A B) z = 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : Δ_[(1 : ℤ)]^[p] (lucasSeq p A B) = fun w : ℤ => B.eval (w : ZMod p) := by
    funext w
    rw [fwdDiff_iter_prime hp2]
    have hc : (((w + p : ℤ)) : ZMod p) = (w : ZMod p) := by simp
    have hd : ((w + p) / (p : ℤ) : ℤ) = w / (p : ℤ) + 1 := by
      have := Int.add_mul_ediv_right w 1 hp0
      simpa using this
    unfold lucasSeq
    rw [hc, hd]
    push_cast
    ring
  have h2 : q = (q - p) + p := by omega
  rw [h2, Function.iterate_add_apply, h1]
  rw [fwdDiff_iter_cast (fun y => B.eval y) (q - p) z, fwdDiff_iter_eval_zero B hB]
  rfl

/-- The binomial filter form of `Δ^q S = 0`. -/
theorem filter_sum_of_fwdDiff_zero {K : Type*} [Field K] (S : ℤ → K) (q : ℕ) (y : ℤ)
    (h : Δ_[(1 : ℤ)]^[q] S y = 0) :
    ∑ v ∈ range (q + 1), (-1 : K) ^ v * (q.choose v : K) * S (y + (v : ℤ)) = 0 := by
  rw [fwdDiff_iter_eq_sum_shift] at h
  have hs : (∑ v ∈ range (q + 1),
      (-1 : K) ^ (q - v) * (q.choose v : K) * S (y + (v : ℤ))) = 0 := by
    simpa only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, nsmul_eq_mul, mul_one] using h
  calc
    _ = (-1 : K) ^ q * ∑ v ∈ range (q + 1),
        (-1 : K) ^ (q - v) * (q.choose v : K) * S (y + (v : ℤ)) := by
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
            (q.choose v : K) * S (y + (v : ℤ)) := by rw [hsign]
        _ = _ := by ring
    _ = 0 := by rw [hs, mul_zero]

/-- **Lucas filter lemma, window form.**  If `R(j) = A(j) + (j/p) B(j)` for `j0 ≤ j ≤ j0 + q`
(`B` of degree `< q - p`), the `q`-fold alternating binomial filter of `R` at `j0` vanishes. -/
theorem lucas_filter_zero (hp2 : p ≠ 2) {q : ℕ} (hpq : p ≤ q) (A : ZMod p → ZMod p)
    (B : (ZMod p)[X]) (hB : B.degree < ((q - p : ℕ) : WithBot ℕ)) (R : ℕ → ZMod p) (j0 : ℕ)
    (hR : ∀ j, j0 ≤ j → j ≤ j0 + q →
      R j = A (j : ZMod p) + ((j / p : ℕ) : ZMod p) * B.eval (j : ZMod p)) :
    ∑ v ∈ range (q + 1), (-1 : ZMod p) ^ v * (q.choose v : ZMod p) * R (j0 + v) = 0 := by
  have h := filter_sum_of_fwdDiff_zero (lucasSeq p A B) q (j0 : ℤ)
    (fwdDiff_lucasSeq hp2 hpq A B hB (j0 : ℤ))
  rw [← h]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq : v ≤ q := by have := Finset.mem_range.mp hv; omega
  rw [hR (j0 + v) (by omega) (by omega)]
  unfold lucasSeq
  have e1 : (j0 : ℤ) + (v : ℤ) = ((j0 + v : ℕ) : ℤ) := by push_cast; ring
  rw [e1]
  have e2 : ((((j0 + v : ℕ) : ℤ)) / (p : ℤ) : ℤ) = (((j0 + v) / p : ℕ) : ℤ) := by
    exact_mod_cast (Int.natCast_div (j0 + v) p).symm
  rw [e2]
  simp only [Int.cast_natCast]

end
end CatalanMeasure.GenD.Uniform.W.Lucas
