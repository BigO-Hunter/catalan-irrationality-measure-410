module
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Algebra.Polynomial.Div
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]
noncomputable section

/-- A triangular family in a fixed principal ideal, with exactly the advertised
successive degrees. The divisibility is checked on the actual native vectors. -/
structure NativeBasis (factor : K[X]) (offset d : Nat) where
  vectors : Fin d → K[X]
  factor_ne_zero : factor ≠ 0
  factor_degree : factor.natDegree=offset
  divides : ∀ i, factor ∣ vectors i
  vector_degree : ∀ i, (vectors i).degree = (offset+i.val : Nat)

def NativeBasis.quotient {f : K[X]} {h d : Nat} (B : NativeBasis f h d) (i : Fin d) : K[X] :=
  Classical.choose (B.divides i)

theorem NativeBasis.factor_quotient {f : K[X]} {h d : Nat}
    (B : NativeBasis f h d) (i : Fin d) : B.vectors i=f*B.quotient i :=
  Classical.choose_spec (B.divides i)

theorem NativeBasis.quotient_ne_zero {f : K[X]} {h d : Nat}
    (B : NativeBasis f h d) (i : Fin d) : B.quotient i ≠ 0 := by
  intro hz
  have hv : B.vectors i = 0 := by rw [B.factor_quotient i,hz,mul_zero]
  have hd := B.vector_degree i
  rw [hv,degree_zero] at hd
  exact WithBot.bot_ne_coe hd

theorem NativeBasis.quotient_degree {f : K[X]} {h d : Nat}
    (B : NativeBasis f h d) (i : Fin d) : (B.quotient i).degree=i.val := by
  have hn := natDegree_eq_of_degree_eq_some (B.vector_degree i)
  rw [B.factor_quotient i,natDegree_mul B.factor_ne_zero (B.quotient_ne_zero i),B.factor_degree] at hn
  rw [degree_eq_natDegree (B.quotient_ne_zero i)]
  congr 1
  omega

def NativeBasis.sequence {f : K[X]} {h d : Nat} (B : NativeBasis f h d) : Polynomial.Sequence K where
  elems' i := if hi : i<d then B.quotient ⟨i,hi⟩ else X^i
  degree_eq' i := by
    split_ifs with hi
    · exact B.quotient_degree ⟨i,hi⟩
    · exact degree_X_pow i

/-- Native quotients fill the complete small polynomial space; no selected
subfamily or unproved spanning assumption is used. -/
theorem NativeBasis.quotient_span {f : K[X]} {h d : Nat}
    (B : NativeBasis f h d) :
    Submodule.span K (Set.range B.quotient)=degreeLT K d := by
  have hs : Set.range B.quotient=B.sequence '' Set.Iio d := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.is_lt,by simp [NativeBasis.sequence,i.is_lt]⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,by simp [NativeBasis.sequence,show i<d from hi]⟩
  rw [hs]
  apply B.sequence.span_degreeLT
  intro i hi
  exact isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (B.sequence.ne_zero i))

/-- Exact native span, including d=0: multiplying every low polynomial by the
common factor is precisely the span of the actual triangular family. -/
theorem NativeBasis.native_span {f : K[X]} {h d : Nat} (B : NativeBasis f h d) :
    Submodule.span K (Set.range B.vectors)=
      (degreeLT K d).map (LinearMap.mulLeft K f) := by
  rw [← B.quotient_span,Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨B.quotient i,⟨i,rfl⟩, (B.factor_quotient i).symm⟩
  · rintro ⟨q,⟨i,rfl⟩,rfl⟩
    exact ⟨i,B.factor_quotient i⟩

#print axioms NativeBasis.native_span
end
end CatalanMeasure.GenD.Uniform.Prefix

