module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeSpans
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.SlotRules
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.SlotDegree
public import Mathlib.Algebra.Polynomial.RingDivision
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]

 theorem native_factor_degree_lt (f A : K[X]) (hf : f ≠ 0) (h d : ℕ)
    (hdeg : f.degree = h) : (f*A).degree < (h+d : ℕ) ↔ A.degree < d := by
  by_cases ha : A = 0
  · simp [ha]
  · rw [degree_mul,hdeg,degree_eq_natDegree ha]
    norm_cast
    omega

 theorem native_factor_window (f Q : K[X]) (hf : f ≠ 0) (h d : ℕ)
    (hdeg : f.degree = h) :
    (∃ A : K[X], A.degree < d ∧ Q=f*A) ↔ f ∣ Q ∧ Q.degree < (h+d : ℕ) := by
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨dvd_mul_right _ _,(native_factor_degree_lt f A hf h d hdeg).mpr hA⟩
  · rintro ⟨⟨A,rfl⟩,hQ⟩
    exact ⟨A,(native_factor_degree_lt f A hf h d hdeg).mp hQ,rfl⟩

variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The high-order branch is an equivalence: no residual free F survives. -/
theorem slot_high_order_iff (F E : K[X]) (hF : F.degree < p)
    (d : ℕ) (hd : p ≤ d) :
    (X-1)^d ∣ F+(X^p-1)*E ↔ F=0 ∧ (X-1)^(d-p) ∣ E := by
  have hz : (X-1 : K[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1:K)
  have hfrob : (X-1 : K[X])^p = X^p-1 := by
    simpa only [one_pow] using sub_pow_char (X:K[X]) 1 (p:=p)
  constructor
  · intro h
    have hzero := slot_high_order_F_zero F E hF hd h
    refine ⟨hzero,?_⟩
    rw [hzero,zero_add,← hfrob,show d=p+(d-p) by omega,pow_add] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero p hz)).mp h
  · rintro ⟨rfl,hE⟩
    rw [zero_add,← hfrob,show d=p+(d-p) by omega,pow_add]
    exact mul_dvd_mul_left _ hE

/-- Exact A-slot conditions after the unique Frobenius split. -/
theorem slot_A_conditions (F E : K[X]) (hF : F.degree < p) (r hp : ℕ)
    (hr : r ≤ p) :
    ((X-1)^(r+hp) ∣ F+(X^p-1)*E ∧
      (F+(X^p-1)*E).degree < (↑(p+r) : WithBot ℕ)) ↔
    ((if r+hp < p then (X-1)^(r+hp) ∣ F
       else F=0 ∧ (X-1)^(r+hp-p) ∣ E) ∧ E.degree < r) := by
  rw [slot_degree_shift p r (Fact.out:p.Prime).pos F E hF]
  by_cases hd : r+hp < p
  · simp only [hd,ite_true]
    rw [slot_order_one F E hd.le]
  · simp only [hd,ite_false]
    rw [slot_high_order_iff F E hF (r+hp) (by omega)]

/-- Exact positive-r C-slot conditions, including the true r-1 degree window. -/
theorem slot_C_positive_conditions (F E : K[X]) (hF : F.degree < p)
    (r hp : ℕ) (hr : 0<r) (hrp : r ≤ p) (hhp : hp ≤ p) :
    ((X-1)^r ∣ F+(X^p-1)*E ∧ (X+1)^hp ∣ F+(X^p-1)*E ∧
      (F+(X^p-1)*E).degree < (↑(p+(r-1)) : WithBot ℕ)) ↔
    ((X-1)^r ∣ F ∧ (X+1)^hp ∣ F-2*E ∧ E.degree < (↑(r-1) : WithBot ℕ)) := by
  rw [slot_order_one F E hrp,slot_order_neg_one F E hhp,
    slot_degree_shift p (r-1) (Fact.out:p.Prime).pos F E hF]

/-- The zero-r C branch has no E coordinate and retains the p-2 top cutoff. -/
theorem slot_C_zero_conditions (F E : K[X]) (hF : F.degree < p) (hp : ℕ)
    (hhp : hp ≤ p) :
    ((X+1)^hp ∣ F+(X^p-1)*E ∧ (F+(X^p-1)*E).degree < (↑(p-1) : WithBot ℕ)) ↔
    E=0 ∧ F.degree < (↑(p-1) : WithBot ℕ) ∧ (X+1)^hp ∣ F := by
  have hsmall : (↑(p-1) : WithBot ℕ) < p := by
    exact_mod_cast (Nat.sub_lt (Fact.out:p.Prime).pos (by omega : 0<1))
  constructor
  · rintro ⟨hd,hdeg⟩
    have hE : E=0 := by
      by_contra hn
      have hprod : (p:WithBot ℕ) ≤ (F+(X^p-1)*E).degree := by
        rw [slot_degree_max p (Fact.out:p.Prime).pos F E hF]
        apply le_trans _ (le_max_right _ _)
        rw [degree_eq_natDegree hn]
        exact_mod_cast (Nat.le_add_right p E.natDegree)
      exact (not_lt_of_ge hprod) (hdeg.trans hsmall)
    simp only [hE,mul_zero,add_zero] at hd hdeg
    exact ⟨hE,hdeg,hd⟩
  · rintro ⟨rfl,hdeg,hd⟩
    simpa using And.intro hd hdeg

#print axioms slot_high_order_iff
#print axioms slot_A_conditions
#print axioms slot_C_positive_conditions
#print axioms slot_C_zero_conditions
end CatalanMeasure.GenD.Uniform.Prefix

