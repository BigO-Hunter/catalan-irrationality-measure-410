module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PStep
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Ring
@[expose] public section
/-! The low filter on the actual finite interval. The sequence outside that
interval is arbitrary; no global recurrence is assumed. -/
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {R : Type*} [CommRing R]

def lowDiff : Module.End R (ℕ → R) := shift-1
@[simp] theorem lowDiff_apply (f : ℕ → R) (b : ℕ) : lowDiff f b = f (b+1)-f b := rfl

theorem lowDiff_pow_iter (r : ℕ) (f : ℕ → R) (b : ℕ) :
    (lowDiff^r) f b = (fwdDiff (1:ℕ))^[r] f b := by
  rw [Module.End.pow_apply]
  rfl

/-- Exact binomial action of the actual forward shift; coefficients are integers,
so no division by a factorial is hidden here. -/
theorem filter_binomial_action (r : ℕ) (f : ℕ → R) (b : ℕ) :
    (lowDiff^r) f b = ∑ k ∈ range (r+1),(-1:R)^(r-k)*(r.choose k:R)*f (b+k) := by
  rw [lowDiff_pow_iter]
  simpa only [nsmul_eq_mul,mul_one,Nat.cast_id,zsmul_eq_mul,Int.cast_mul,Int.cast_pow,
    Int.cast_neg,Int.cast_one,Int.cast_natCast] using
    fwdDiff_iter_eq_sum_shift (h := (1:ℕ)) f r b

/-- Exact Gregory-Newton identity, again before any characteristic assumption. -/
theorem newton_expansion (f : ℕ → R) (b i : ℕ) :
    f (b+i) = ∑ k ∈ range (i+1),(i.choose k:R)*(lowDiff^k) f b := by
  simp only [lowDiff_pow_iter]
  simpa only [nsmul_eq_mul,mul_one,Nat.cast_id] using shift_eq_sum_fwdDiff_iter (h := (1:ℕ)) f i b

/-- Only n actual r-th differences are used to kill a higher difference at the
left end; its complete binomial stencil remains inside the observed interval. -/
theorem higher_difference_zero (f : ℕ → R) (b n r k : ℕ)
    (hf : ∀ j < n,(lowDiff^r) f (b+j) = 0) (hrk : r ≤ k) (hk : k < n+r) :
    (lowDiff^k) f b = 0 := by
  have he : k = (k-r)+r := by omega
  rw [he,pow_add,Module.End.mul_apply,filter_binomial_action]
  apply Finset.sum_eq_zero
  intro j hj
  have hji := mem_range.mp hj
  have hjn : j < n := by omega
  rw [hf j hjn,mul_zero]

/-- Finite active-interval Newton representation. This retains the original b,
n and r; no coordinates from the large filter quotient are introduced. -/
theorem active_newton_expansion (f : ℕ → R) (b n r i : ℕ)
    (hf : ∀ j < n,(lowDiff^r) f (b+j) = 0) (hi : i < n+r) :
    f (b+i) = ∑ k ∈ range r,(i.choose k:R)*(lowDiff^k) f b := by
  rw [newton_expansion f b i]
  by_cases hr : r ≤ i+1
  · symm
    apply Finset.sum_subset (Finset.range_mono hr)
    intro k hk hkr
    have hki := mem_range.mp hk
    have hkr' : r ≤ k := by simpa only [mem_range,not_lt] using hkr
    rw [higher_difference_zero f b n r k hf hkr' (by omega),mul_zero]
  · apply Finset.sum_subset (Finset.range_mono (show i+1 ≤ r by omega))
    intro k hk hki
    have hik : i < k := by simp only [mem_range,not_lt] at hki;omega
    simp [Nat.choose_eq_zero_of_lt hik]

variable {p : ℕ} [Fact p.Prime]

/-- Only factorials strictly below p are inverted. -/
theorem factorial_cast_ne_zero {k : ℕ} (hk : k < p) : (k.factorial : ZMod p) ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ,Nat.cast_mul]
    apply mul_ne_zero
    · intro hz
      exact Nat.not_dvd_of_pos_of_lt (by omega) hk ((ZMod.natCast_eq_zero_iff (k+1) p).mp hz)
    · exact ih (by omega)

noncomputable def pascalPolynomial (k : ℕ) : (ZMod p)[X] :=
  C ((k.factorial : ZMod p)⁻¹)*descPochhammer (ZMod p) k

theorem eval_pascalPolynomial (k i : ℕ) (hk : k < p) :
    (pascalPolynomial (p := p) k).eval (i : ZMod p) = (i.choose k : ZMod p) := by
  rw [pascalPolynomial,eval_mul,eval_C,descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  exact inv_mul_cancel_left₀ (factorial_cast_ne_zero hk) _

theorem natDegree_pascalPolynomial_le (k : ℕ) :
    (pascalPolynomial (p := p) k).natDegree ≤ k := by
  exact (natDegree_C_mul_le _ _).trans (by rw [descPochhammer_natDegree])

noncomputable def newtonPolynomial (f : ℕ → ZMod p) (b r : ℕ) : (ZMod p)[X] :=
  ∑ k ∈ range r,C ((lowDiff^k) f b)*pascalPolynomial k

theorem degree_newtonPolynomial_lt (f : ℕ → ZMod p) (b r : ℕ) :
    (newtonPolynomial f b r).degree < r := by
  apply Polynomial.mem_degreeLT.mp
  apply Submodule.sum_mem
  intro k hk
  apply Polynomial.mem_degreeLT.mpr
  apply lt_of_le_of_lt (degree_le_natDegree)
  apply WithBot.coe_lt_coe.mpr
  have hd := (natDegree_C_mul_le ((lowDiff^k) f b) (pascalPolynomial (p := p) k)).trans
    (natDegree_pascalPolynomial_le (p := p) k)
  exact hd.trans_lt (mem_range.mp hk)

theorem eval_newtonPolynomial (f : ℕ → ZMod p) (b n r i : ℕ) (hr : r < p)
    (hf : ∀ j < n,(lowDiff^r) f (b+j) = 0) (hi : i < n+r) :
    (newtonPolynomial f b r).eval (i : ZMod p) = f (b+i) := by
  rw [active_newton_expansion f b n r i hf hi]
  unfold newtonPolynomial
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval_mul,eval_C,eval_pascalPolynomial k i ((mem_range.mp hk).trans hr)]
  ring
end CatalanMeasure.GenD.Uniform.Prefix


