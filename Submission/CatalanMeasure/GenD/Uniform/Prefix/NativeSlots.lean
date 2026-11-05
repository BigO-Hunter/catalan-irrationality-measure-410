module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalPairs
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeBasis
public import Submission.CatalanMeasure.Parametric.ChebyshevPrime
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Polynomial.Chebyshev
variable {p : Nat} [Fact p.Prime]
noncomputable section
local notation "K" => ZMod p

def nativePlus (j : Int) : K[X] := U K (j-1)+U K ((p : Int)-j-1)
def nativeMinus (j : Int) : K[X] := U K (j-1)-U K ((p : Int)-j-1)
def nativeCenter : K[X] := (X^2-1)^((p-1)/2)

theorem nativePlus_formula (hp : p≠2) (j : Int) :
    nativePlus (p := p) j=nativeCenter*T K j+(1-X^p)*U K (j-1) := by
  rw [nativePlus,chebyshev_U_reflect,CatalanMeasure.Parametric.chebyshev_U_prime hp,
    CatalanMeasure.Parametric.chebyshev_T_prime hp]
  dsimp [nativeCenter]
  ring

theorem nativeMinus_formula (hp : p≠2) (j : Int) :
    nativeMinus (p := p) j=(1+X^p)*U K (j-1)-nativeCenter*T K j := by
  rw [nativeMinus,chebyshev_U_reflect,CatalanMeasure.Parametric.chebyshev_U_prime hp,
    CatalanMeasure.Parametric.chebyshev_T_prime hp]
  dsimp [nativeCenter]
  ring

theorem nativeCenter_factors : nativeCenter (p := p)=
    (X-1 : K[X])^((p-1)/2)*(X+1)^((p-1)/2) := by
  dsimp [nativeCenter]
  rw [← mul_pow]
  congr 1
  ring

theorem nativePlus_dvd (hp : p≠2) (j : Int) :
    (X-1 : K[X])^((p-1)/2) ∣ nativePlus (p := p) j := by
  rw [nativePlus_formula hp,nativeCenter_factors]
  apply dvd_add
  · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · have hh : (p-1)/2≤p := by omega
    have hd : (X-1 : K[X])^((p-1)/2) ∣ (X-1)^p := pow_dvd_pow _ hh
    have he : (1-X^p : K[X])= -(X-1)^p := by rw [sub_pow_char,one_pow]; ring
    rw [he]
    exact dvd_mul_of_dvd_left (dvd_neg.mpr hd) _

theorem nativeMinus_dvd (hp : p≠2) (j : Int) :
    (X+1 : K[X])^((p-1)/2) ∣ nativeMinus (p := p) j := by
  rw [nativeMinus_formula hp,nativeCenter_factors]
  apply dvd_sub
  · have hh : (p-1)/2≤p := by omega
    have hd : (X+1 : K[X])^((p-1)/2) ∣ (X+1)^p := pow_dvd_pow _ hh
    have he : (1+X^p : K[X])=(X+1)^p := by rw [add_pow_char,one_pow]; ring
    rw [he]
    exact dvd_mul_of_dvd_left hd _
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

/-- Degree progression of actual physical pair vectors, in increasing degree
order. The lower U index is allowed to be -1 at the central boundary. -/
theorem native_pair_degrees (hp : p≠2) (i : Nat) (hi : i<(p-1)/2) :
    (nativePlus (p := p) (((p-1)/2 : Nat) - (i : Int))).degree=((p-1)/2+i : Nat) ∧
    (nativeMinus (p := p) (((p-1)/2 : Nat) - (i : Int))).degree=((p-1)/2+i : Nat) := by
  have h2 : (2 : K)≠0 := by
    intro hz
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp hz))
  letI : NeZero (2 : K) := ⟨h2⟩
  have hodd : p=2*((p-1)/2)+1 := by
    obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
    omega
  have hlow : (U K (((p-1)/2 : Nat)-(i : Int)-1)).degree=((p-1)/2-i-1 : Nat) := by
    rw [show (((p-1)/2 : Nat) : Int)-(i : Int)-1=(((p-1)/2-i-1 : Nat) : Int) by omega]
    exact degree_U_natCast K _
  have hhigh : (U K ((p : Int)-(((p-1)/2 : Nat)-(i : Int))-1)).degree=((p-1)/2+i : Nat) := by
    rw [show (p : Int)-(((p-1)/2 : Nat)-(i : Int))-1=(((p-1)/2+i : Nat) : Int) by omega]
    exact degree_U_natCast K _
  have hlt : (U K (((p-1)/2 : Nat)-(i : Int)-1)).degree <
      (U K ((p : Int)-(((p-1)/2 : Nat)-(i : Int))-1)).degree := by
    rw [hlow,hhigh]
    exact_mod_cast (show (p-1)/2-i-1<(p-1)/2+i by omega)
  exact ⟨(degree_add_eq_right_of_degree_lt hlt).trans hhigh,
    (degree_sub_eq_right_of_degree_lt hlt).trans hhigh⟩

#print axioms nativePlus_dvd
#print axioms native_pair_degrees
end
end CatalanMeasure.GenD.Uniform.Prefix


