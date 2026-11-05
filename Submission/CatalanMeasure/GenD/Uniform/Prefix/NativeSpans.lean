module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeSlots
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable {p : Nat} [Fact p.Prime]
noncomputable section
local notation "K" => ZMod p

theorem native_two_ne_zero (hp : p≠2) : (2 : K)≠0 := by
  intro hz
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp hz))

theorem native_half_identity (hp : p≠2) : p=2*((p-1)/2)+1 := by
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  omega

def plusVectors (i : Fin ((p-1)/2+1)) : K[X] :=
  if i.val<(p-1)/2 then nativePlus (((p-1)/2 : Nat)-(i.val : Int)) else nativeCenter

def minusVectors (i : Fin ((p-1)/2)) : K[X] :=
  nativeMinus (((p-1)/2 : Nat)-(i.val : Int))

def plusNativeBasis (hp : p≠2) :
    NativeBasis ((X-1 : K[X])^((p-1)/2)) ((p-1)/2) ((p-1)/2+1) where
  vectors := plusVectors
  factor_ne_zero := by
    exact pow_ne_zero _ (by simpa using (X_sub_C_ne_zero (1 : K)))
  factor_degree := by
    rw [natDegree_pow,show (X-1 : K[X]).natDegree=1 by simpa using (natDegree_X_sub_C (1 : K)),mul_one]
  divides i := by
    dsimp [plusVectors]
    split_ifs with hi
    · exact nativePlus_dvd hp _
    · rw [nativeCenter_factors]
      exact dvd_mul_right _ _
  vector_degree i := by
    dsimp [plusVectors]
    split_ifs with hi
    · exact (native_pair_degrees hp i.val hi).1
    · have he : i.val=(p-1)/2 := by have := i.is_lt; omega
      letI : NeZero (2 : K) := ⟨native_two_ne_zero hp⟩
      dsimp [nativeCenter]
      rw [← CatalanMeasure.Parametric.chebyshev_U_prime hp,
        show (p : Int)-1=((p-1 : Nat) : Int) by have := (Fact.out : p.Prime).pos; omega,
        degree_U_natCast]
      congr 1
      have := native_half_identity hp
      omega

def minusNativeBasis (hp : p≠2) :
    NativeBasis ((X+1 : K[X])^((p-1)/2)) ((p-1)/2) ((p-1)/2) where
  vectors := minusVectors
  factor_ne_zero := by
    exact pow_ne_zero _ (by simpa using (X_sub_C_ne_zero (-1 : K)))
  factor_degree := by
    simpa using (natDegree_pow (X+1 : K[X]) ((p-1)/2))
  divides i := nativeMinus_dvd hp _
  vector_degree i := (native_pair_degrees hp i.val i.is_lt).2

theorem plus_native_span (hp : p≠2) :
    Submodule.span K (Set.range (plusVectors (p := p)))=
      (degreeLT K ((p-1)/2+1)).map (LinearMap.mulLeft K ((X-1)^((p-1)/2))) :=
  (plusNativeBasis hp).native_span

theorem minus_native_span (hp : p≠2) :
    Submodule.span K (Set.range (minusVectors (p := p)))=
      (degreeLT K ((p-1)/2)).map (LinearMap.mulLeft K ((X+1)^((p-1)/2))) :=
  (minusNativeBasis hp).native_span

#print axioms plus_native_span
#print axioms minus_native_span
end
end CatalanMeasure.GenD.Uniform.Prefix



