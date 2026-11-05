module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.SlotNativeSource
public import Mathlib.Algebra.Polynomial.Taylor
@[expose] public section
set_option Elab.async false

/-!
# Slot-space membership is a jet condition (points `1, -1, ∞`)

The accepted Prefix lemmas `native_A_split`, `native_C_split_positive`, `native_C_split_zero`
describe membership of the Frobenius-split pair `(F, E)` in the physical slot spaces by
divisibility by `(X - 1)^s`, `(X + 1)^s` and degree bounds.  Here these become **Taylor jets** at
`1`, `-1` and at `∞` (coefficients of index `≥ r`), i.e. exactly the rows of the four-point chart
(`sourcejet`, `source_top`, `degree`) that the host charges as jet groups.

* `pow_dvd_iff_taylor` : `(X - c)^n ∣ f ↔` Taylor coefficients `< n` at `c` vanish;
* `degree_lt_iff_top`  : `deg f < r ↔` coefficients of index `≥ r` vanish;
* `native_A_jets`, `native_C_jets_positive`, `native_C_jets_zero` : the three slot spaces.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Polynomial CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {K : Type*} [Field K]

theorem pow_dvd_iff_taylor (c : K) (n : ℕ) (f : K[X]) :
    (X - C c) ^ n ∣ f ↔ ∀ k < n, (taylor c f).coeff k = 0 := by
  rw [← Polynomial.X_pow_dvd_iff (f := taylor c f) (n := n)]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨taylor c g, ?_⟩
    rw [taylor_mul, taylor_pow]
    simp [taylor_X, taylor_C]
  · rintro ⟨g, hg⟩
    refine ⟨taylor (-c) g, ?_⟩
    have h := congrArg (taylor (-c)) hg
    rw [taylor_taylor, taylor_mul, taylor_pow, taylor_X] at h
    simp only [neg_add_cancel, taylor_zero] at h
    rw [h]
    simp [sub_eq_add_neg]

theorem degree_lt_iff_top (r : ℕ) (f : K[X]) : f.degree < r ↔ ∀ i, r ≤ i → f.coeff i = 0 :=
  Polynomial.degree_lt_iff_coeff_zero f r

variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- **A slots as jets.**  `(F, E)` (Frobenius split, `deg F < p`) lies in the A slot space of
remainder `r < p` iff the order-`r + (p-1)/2` jet at `1` (on `F`, or on `E` after `F = 0` when the
order reaches `p`) and the top jets of `E` vanish. -/
theorem native_A_jets (hp : p ≠ 2) (r : ℕ) (hr : r < p) (F E : Fp[X]) (hF : F.degree < p) :
    (∃ A ∈ Submodule.span Fp (Set.range (plusVectors (p := p))),
      F + (X ^ p - 1) * E = (X - 1) ^ r * A) ↔
    ((if r + (p - 1) / 2 < p then ∀ k < r + (p - 1) / 2, (taylor 1 F).coeff k = 0
      else F = 0 ∧ ∀ k < r + (p - 1) / 2 - p, (taylor 1 E).coeff k = 0) ∧
      ∀ i, r ≤ i → E.coeff i = 0) := by
  rw [native_A_split hp r hr F E hF, degree_lt_iff_top]
  have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
  by_cases hd : r + (p - 1) / 2 < p
  · simp only [hd, if_true, h1, pow_dvd_iff_taylor]
  · simp only [hd, if_false, h1, pow_dvd_iff_taylor]

/-- **C slots (remainder `r > 0`) as jets**: order `r` at `1` on `F`, order `(p-1)/2` at `-1` on
`F - 2E`, and top jets of `E` above `r - 1`. -/
theorem native_C_jets_positive (hp : p ≠ 2) (r : ℕ) (hr : 0 < r) (hrp : r < p)
    (F E : Fp[X]) (hF : F.degree < p) :
    (∃ A ∈ Submodule.span Fp (Set.range (minusVectors (p := p))),
      F + (X ^ p - 1) * E = (X - 1) ^ r * A) ↔
    ((∀ k < r, (taylor 1 F).coeff k = 0) ∧
      (∀ k < (p - 1) / 2, (taylor (-1) (F - 2 * E)).coeff k = 0) ∧
      ∀ i, r - 1 ≤ i → E.coeff i = 0) := by
  rw [native_C_split_positive hp r hr hrp F E hF]
  have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
  have h2 : (X + 1 : Fp[X]) = X - C (-1) := by simp
  rw [h1, h2, pow_dvd_iff_taylor, pow_dvd_iff_taylor]
  rw [degree_lt_iff_top (r - 1) E]

/-- **C slots, remainder `0`**: `E = 0`, top coefficient of `F` (degree `≤ p - 2`) and order
`(p-1)/2` at `-1` on `F`. -/
theorem native_C_jets_zero (hp : p ≠ 2) (F E : Fp[X]) (hF : F.degree < p) :
    (∃ A ∈ Submodule.span Fp (Set.range (minusVectors (p := p))),
      F + (X ^ p - 1) * E = A) ↔
    (E = 0 ∧ (∀ i, p - 1 ≤ i → F.coeff i = 0) ∧
      ∀ k < (p - 1) / 2, (taylor (-1) F).coeff k = 0) := by
  rw [native_C_split_zero hp F E hF]
  have h2 : (X + 1 : Fp[X]) = X - C (-1) := by simp
  rw [h2, pow_dvd_iff_taylor, degree_lt_iff_top]

end
end CatalanMeasure.GenD.Uniform.W.Charts3
