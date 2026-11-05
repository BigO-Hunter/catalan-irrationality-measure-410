module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.SlotNativeRules
public import Mathlib.RingTheory.Coprime.Lemmas
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]

 theorem scaled_native_map (f g Q : K[X]) (d : ℕ) :
    (∃ A ∈ (degreeLT K d).map (LinearMap.mulLeft K g), Q=f*A) ↔
      ∃ B : K[X], B.degree < d ∧ Q=(f*g)*B := by
  constructor
  · rintro ⟨A,⟨B,hB,hBA⟩,hQ⟩
    change g*B=A at hBA
    exact ⟨B,mem_degreeLT.mp hB,by rw [hQ,←hBA,mul_assoc]⟩
  · rintro ⟨B,hB,hQ⟩
    exact ⟨g*B,⟨B,mem_degreeLT.mpr hB,rfl⟩,by rw [hQ,mul_assoc]⟩

variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

 theorem native_power_degree (a : Fp) (r : ℕ) :
    ((X-C a : Fp[X])^r).degree = r := by
  rw [degree_pow,degree_X_sub_C]
  simp

 theorem native_pair_coprime (hp : p≠2) (r s : ℕ) :
    IsCoprime ((X-1 : Fp[X])^r) ((X+1)^s) := by
  have hunit : IsUnit ((1: Fp)-(-1)) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [sub_neg_eq_add,←one_add_one_eq_two] using native_two_ne_zero hp
  simpa only [map_one,map_neg,sub_neg_eq_add] using
    (isCoprime_X_sub_C_of_isUnit_sub hunit).pow (m:=r) (n:=s)

/-- Actual plus native span, multiplied by the remainder of omega. -/
theorem native_A_source (hp : p≠2) (r : ℕ) (Q : Fp[X]) :
    (∃ A ∈ Submodule.span Fp (Set.range (plusVectors (p:=p))), Q=(X-1)^r*A) ↔
    (X-1)^(r+(p-1)/2) ∣ Q ∧ Q.degree < (↑(p+r) : WithBot ℕ) := by
  rw [plus_native_span hp,scaled_native_map,←pow_add]
  have hz : (X-1 : Fp[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1:Fp)
  rw [native_factor_window _ _ (pow_ne_zero _ hz) (r+(p-1)/2) ((p-1)/2+1)
    (by simpa only [map_one] using native_power_degree (p:=p) 1 (r+(p-1)/2))]
  have hn := native_half_identity hp
  have he : r+(p-1)/2+((p-1)/2+1)=p+r := by omega
  rw [he]

/-- Actual minus native span, multiplied by omega, with both coprime factors. -/
theorem native_C_source (hp : p≠2) (r : ℕ) (Q : Fp[X]) :
    (∃ A ∈ Submodule.span Fp (Set.range (minusVectors (p:=p))), Q=(X-1)^r*A) ↔
    (X-1)^r ∣ Q ∧ (X+1)^((p-1)/2) ∣ Q ∧
      Q.degree < (↑(r+p-1) : WithBot ℕ) := by
  rw [minus_native_span hp,scaled_native_map]
  have hz : (X-1 : Fp[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1:Fp)
  have ht : (X+1 : Fp[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (-1:Fp)
  have hdeg : ((X-1 : Fp[X])^r*(X+1)^((p-1)/2)).degree = (↑(r+(p-1)/2) : WithBot ℕ) := by
    rw [degree_mul]
    have h1 := native_power_degree (p:=p) 1 r
    have h2 := native_power_degree (p:=p) (-1) ((p-1)/2)
    simp only [map_one,map_neg,sub_neg_eq_add] at h1 h2
    rw [h1,h2]
    rfl
  rw [native_factor_window _ _ (mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ ht))
    (r+(p-1)/2) ((p-1)/2) hdeg]
  have hdiv : ((X-1 : Fp[X])^r*(X+1)^((p-1)/2) ∣ Q) ↔
      (X-1)^r ∣ Q ∧ (X+1)^((p-1)/2) ∣ Q := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right _ _).trans h,(dvd_mul_left _ _).trans h⟩
    · rintro ⟨h1,h2⟩
      exact (native_pair_coprime hp r ((p-1)/2)).mul_dvd h1 h2
  rw [hdiv,and_assoc]
  have hn := native_half_identity hp
  have he : r+(p-1)/2+(p-1)/2=r+p-1 := by omega
  rw [he]

/-- The source-free A equivalence on the full unique split coordinates. -/
theorem native_A_split (hp : p≠2) (r : ℕ) (hr : r<p) (F E : Fp[X])
    (hF : F.degree < p) :
    (∃ A ∈ Submodule.span Fp (Set.range (plusVectors (p:=p))),
      F+(X^p-1)*E=(X-1)^r*A) ↔
    ((if r+(p-1)/2<p then (X-1)^(r+(p-1)/2) ∣ F
      else F=0 ∧ (X-1)^(r+(p-1)/2-p) ∣ E) ∧ E.degree < r) := by
  rw [native_A_source hp,slot_A_conditions F E hF r ((p-1)/2) hr.le]

/-- Positive remainder C equivalence on the actual native physical span. -/
theorem native_C_split_positive (hp : p≠2) (r : ℕ) (hr : 0<r) (hrp : r<p)
    (F E : Fp[X]) (hF : F.degree < p) :
    (∃ A ∈ Submodule.span Fp (Set.range (minusVectors (p:=p))),
      F+(X^p-1)*E=(X-1)^r*A) ↔
    ((X-1)^r ∣ F ∧ (X+1)^((p-1)/2) ∣ F-2*E ∧
      E.degree < (↑(r-1) : WithBot ℕ)) := by
  rw [native_C_source hp]
  have he : r+p-1=p+(r-1) := by omega
  rw [he,slot_C_positive_conditions F E hF r ((p-1)/2) hr hrp.le (by omega)]

/-- Zero remainder C equivalence retains E=0 and degree at most p-2. -/
theorem native_C_split_zero (hp : p≠2) (F E : Fp[X]) (hF : F.degree < p) :
    (∃ A ∈ Submodule.span Fp (Set.range (minusVectors (p:=p))),
      F+(X^p-1)*E=A) ↔
    E=0 ∧ F.degree < (↑(p-1) : WithBot ℕ) ∧ (X+1)^((p-1)/2) ∣ F := by
  have hs := native_C_source hp 0 (F+(X^p-1)*E)
  simp only [pow_zero,one_mul,one_dvd,true_and,zero_add] at hs
  rw [hs,slot_C_zero_conditions F E hF ((p-1)/2) (by omega)]

#print axioms native_A_split
#print axioms native_C_split_positive
#print axioms native_C_split_zero
end CatalanMeasure.GenD.Uniform.Prefix

