module
public import Submission.CatalanMeasure.Parametric.Polynomial
public import Mathlib.Data.List.GetD
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial

/-- A computable coefficient list interpreted as an integer polynomial. -/
noncomputable def intPolynomial : List ℤ → ℤ[X]
  | [] => 0
  | a :: p => C a + X * intPolynomial p

def intAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a+b) :: intAdd p q

def intSmul (a : ℤ) (p : List ℤ) : List ℤ := p.map (a * ·)

def intMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => intAdd (intSmul a q) (0 :: intMul p q)

def intPow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => intMul (intPow p n) p

@[simp] theorem intPolynomial_add (p q : List ℤ) :
    intPolynomial (intAdd p q) = intPolynomial p + intPolynomial q := by
  induction p generalizing q with
  | nil => simp [intAdd, intPolynomial]
  | cons a p ih =>
    cases q with
    | nil => simp [intAdd, intPolynomial]
    | cons b q => simp [intAdd, intPolynomial, ih]; ring

@[simp] theorem intPolynomial_smul (a : ℤ) (p : List ℤ) :
    intPolynomial (intSmul a p) = C a * intPolynomial p := by
  induction p with
  | nil => simp [intSmul, intPolynomial]
  | cons b p ih =>
    simp only [intSmul, List.map_cons, intPolynomial] at ih ⊢
    rw [ih]
    simp only [map_mul]
    ring

@[simp] theorem intPolynomial_mul (p q : List ℤ) :
    intPolynomial (intMul p q) = intPolynomial p * intPolynomial q := by
  induction p with
  | nil => simp [intMul, intPolynomial]
  | cons a p ih =>
    simp [intMul, intPolynomial, ih]
    ring

@[simp] theorem intPolynomial_pow (p : List ℤ) (n : ℕ) :
    intPolynomial (intPow p n) = intPolynomial p ^ n := by
  induction n with
  | zero => simp [intPow, intPolynomial]
  | succ n ih => simp [intPow, ih, pow_succ]

theorem intPolynomial_coeff (p : List ℤ) (i : ℕ) :
    (intPolynomial p).coeff i = p.getD i 0 := by
  induction p generalizing i with
  | nil => simp [intPolynomial]
  | cons a p ih =>
    cases i with
    | zero => simp [intPolynomial]
    | succ i => simp only [intPolynomial, coeff_add, coeff_C, coeff_X_mul,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, zero_add,
        List.getD_cons_succ, ih]

def intChebTPair : ℕ → List ℤ × List ℤ
  | 0 => ([1], [0,1])
  | n+1 => ((intChebTPair n).2,
      intAdd (0 :: intSmul 2 (intChebTPair n).2) (intSmul (-1) (intChebTPair n).1))

def intChebUPair : ℕ → List ℤ × List ℤ
  | 0 => ([1], [0,2])
  | n+1 => ((intChebUPair n).2,
      intAdd (0 :: intSmul 2 (intChebUPair n).2) (intSmul (-1) (intChebUPair n).1))

theorem intChebTPair_spec (n : ℕ) :
    intPolynomial (intChebTPair n).1 = Chebyshev.T ℤ (n : ℤ) ∧
      intPolynomial (intChebTPair n).2 = Chebyshev.T ℤ ((n+1 : ℕ) : ℤ) := by
  induction n with
  | zero => simp [intChebTPair, intPolynomial]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : ((n+1+1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e' : ((n+1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, Chebyshev.T_add_two]
    simp only [intChebTPair, intPolynomial_add, intPolynomial_smul, intPolynomial,
      map_zero, zero_add, map_ofNat, map_neg, map_one]
    rw [ih.1, ih.2, e']
    ring

theorem intChebUPair_spec (n : ℕ) :
    intPolynomial (intChebUPair n).1 = Chebyshev.U ℤ (n : ℤ) ∧
      intPolynomial (intChebUPair n).2 = Chebyshev.U ℤ ((n+1 : ℕ) : ℤ) := by
  induction n with
  | zero => simp [intChebUPair, intPolynomial]; ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : ((n+1+1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e' : ((n+1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e, Chebyshev.U_add_two]
    simp only [intChebUPair, intPolynomial_add, intPolynomial_smul, intPolynomial,
      map_zero, zero_add, map_ofNat, map_neg, map_one]
    rw [ih.1, ih.2, e']
    ring

def intReverse (c : ℕ) (p : List ℤ) : List ℤ :=
  (List.range c).map (fun i => p.getD (c-1-i) 0)

theorem intPolynomial_reverse (c : ℕ) (p : List ℤ) :
    intPolynomial (intReverse c p) = OAI.InternalCatalan.reversedRow c (intPolynomial p) := by
  ext i
  rw [intPolynomial_coeff, OAI.InternalCatalan.reversedRow_coeff, intPolynomial_coeff]
  by_cases hi : i < c
  · rw [if_pos hi, List.getD_eq_getElem _ 0 (by simpa [intReverse] using hi)]
    simp [intReverse]
  · rw [if_neg hi]
    exact List.getD_eq_default _ 0 (by simpa [intReverse] using Nat.le_of_not_gt hi)

def intRowP (P : Parameters) (N r : ℕ) : List ℤ :=
  intMul (intPow [1,-1] (P.h N))
    (intReverse (P.C N) (intChebTPair (rowDistance P N r)).1)

def intRowD (P : Parameters) (N r : ℕ) : List ℤ :=
  if rowDistance P N r = 0 then [] else
    intSmul (Int.sign (rowOffset P N r))
      (intMul (intPow [1,-1] (P.h N))
        (intReverse (P.C N) (intChebUPair (rowDistance P N r - 1)).1))

theorem intPolynomial_one_sub_X : intPolynomial [1,-1] = (1-X : ℤ[X]) := by
  simp [intPolynomial, sub_eq_add_neg]

theorem intRowP_spec (P : Parameters) (N r : ℕ) : intPolynomial (intRowP P N r) = rowP P N r := by
  simp only [intRowP, intPolynomial_mul, intPolynomial_pow, intPolynomial_reverse,
    intPolynomial_one_sub_X, (intChebTPair_spec _).1]
  rfl

theorem intRowD_spec (P : Parameters) (N r : ℕ) : intPolynomial (intRowD P N r) = rowD P N r := by
  by_cases hd : rowDistance P N r = 0
  · simp [intRowD, hd, intPolynomial, rowD, OAI.InternalCatalan.reversedRow_zero]
  · have he : ((rowDistance P N r - 1 : ℕ) : ℤ) = (rowDistance P N r : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ rowDistance P N r)]
      norm_num
    simp only [intRowD, if_neg hd, intPolynomial_smul, intPolynomial_mul,
      intPolynomial_pow, intPolynomial_reverse, intPolynomial_one_sub_X,
      (intChebUPair_spec _).1, he, rowD]
    ring

theorem rowP_coeff_algorithm (P : Parameters) (N r i : ℕ) :
    (rowP P N r).coeff i = (intRowP P N r).getD i 0 := by
  rw [← intRowP_spec, intPolynomial_coeff]

theorem rowD_coeff_algorithm (P : Parameters) (N r i : ℕ) :
    (rowD P N r).coeff i = (intRowD P N r).getD i 0 := by
  rw [← intRowD_spec, intPolynomial_coeff]

end CatalanMeasure.Parametric
