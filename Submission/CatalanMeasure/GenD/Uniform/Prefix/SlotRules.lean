module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.FrobeniusSplit
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K] {p : Nat} [Fact p.Prime] [CharP K p]

/-- Low-order conditions at1 depend only on F in the exact slot split. -/
theorem slot_order_one (F E : Polynomial K) {r : Nat} (hr : r ≤ p) :
    (X-1)^r ∣ F+(X^p-1)*E ↔ (X-1)^r ∣ F := by
  have hfrob : (X-1 : Polynomial K)^p = X^p-1 := by
    simpa only [one_pow] using sub_pow_char (X : Polynomial K) 1 (p := p)
  have ht : (X-1 : Polynomial K)^r ∣ (X^p-1)*E := by
    rw [← hfrob]
    exact (pow_dvd_pow (X-1) hr).mul_right E
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using dvd_sub h ht
  · intro h
    exact dvd_add h ht

/-- At-1 the same slot is F-2E modulo the actual Frobenius factor. This is an
identity of polynomial divisibility, not an assumed local source flag. -/
theorem slot_order_neg_one (F E : Polynomial K) {r : Nat} (hr : r ≤ p) :
    (X+1)^r ∣ F+(X^p-1)*E ↔ (X+1)^r ∣ F-2*E := by
  have hfrob : (X+1 : Polynomial K)^p = X^p+1 := by
    simpa only [one_pow] using add_pow_char (X : Polynomial K) 1 p
  have ht : (X+1 : Polynomial K)^r ∣ (X^p+1)*E := by
    rw [← hfrob]
    exact (pow_dvd_pow (X+1) hr).mul_right E
  have heq : F+(X^p-1)*E = (F-2*E)+(X^p+1)*E := by ring
  rw [heq]
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using dvd_sub h ht
  · intro h
    exact dvd_add h ht

/-- When the required1-order reaches p, the small F part must vanish. -/
theorem slot_high_order_F_zero (F E : Polynomial K)
    (hF : F.degree < p) {r : Nat} (hr : p ≤ r)
    (hQ : (X-1)^r ∣ F+(X^p-1)*E) : F = 0 := by
  have hd : (X-1 : Polynomial K)^p ∣ F :=
    (slot_order_one F E (le_refl p)).mp ((pow_dvd_pow (X-1) hr).trans hQ)
  apply Polynomial.eq_zero_of_dvd_of_degree_lt hd
  have hdeg : ((X-1 : Polynomial K)^p).degree = p := by
    rw [show (X-1 : Polynomial K) = X-C (1 : K) by simp, Polynomial.degree_pow, Polynomial.degree_X_sub_C]
    simp
  rw [hdeg]
  exact hF

/-- Exact Taylor-prefix interpretation, without inverses of factorials. -/
theorem prefix_iff_divisibility (a : K) (r : Nat) (F : Polynomial K) :
    (∀ i < r, (taylor a F).coeff i = 0) ↔ (X-C a)^r ∣ F := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := X_pow_dvd_iff.mpr h
    refine ⟨g.comp (X-C a), ?_⟩
    have hF : F = (taylor a F).comp (X-C a) := by
      rw [taylor_apply, comp_assoc]
      simp
    conv_lhs => rw [hF,hg]
    rw [mul_comp,pow_comp,X_comp]
  · rintro ⟨g,rfl⟩
    have ht : taylor a ((X-C a)^r*g) = X^r*taylor a g := by simp
    rw [ht]
    exact X_pow_dvd_iff.mp (dvd_mul_right _ _)

#print axioms slot_order_one
#print axioms slot_order_neg_one
#print axioms prefix_iff_divisibility
end CatalanMeasure.GenD.Uniform.Prefix
