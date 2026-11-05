module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.SlotNativeSource
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

noncomputable def centerGenerator (r : ℕ) : Fp[X] := (X-1)^r*nativeCenter

theorem centerGenerator_factors (r : ℕ) : centerGenerator (p:=p) r =
    (X-1)^(r+(p-1)/2)*(X+1)^((p-1)/2) := by
  rw [centerGenerator,nativeCenter_factors,←mul_assoc,←pow_add]

theorem centerGenerator_ne_zero (r : ℕ) : centerGenerator (p:=p) r ≠ 0 := by
  rw [centerGenerator_factors]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1:Fp))
  · exact pow_ne_zero _ (by simpa using X_sub_C_ne_zero (-1:Fp))

theorem centerGenerator_degree (hp : p≠2) (r : ℕ) :
    (centerGenerator (p:=p) r).degree = (↑(r+p-1) : WithBot ℕ) := by
  rw [centerGenerator_factors,degree_mul]
  have h1 := native_power_degree (p:=p) 1 (r+(p-1)/2)
  have h2 := native_power_degree (p:=p) (-1) ((p-1)/2)
  simp only [map_one,map_neg,sub_neg_eq_add] at h1 h2
  rw [h1,h2]
  norm_cast
  have := native_half_identity hp
  omega

/-- A constant line is obtained from the actual center vector, not a dimension
postulate on split coordinates. -/
theorem center_source_conditions (hp : p≠2) (r : ℕ) (Q : Fp[X]) :
    (∃ c : Fp,Q=c • centerGenerator r) ↔
    (X-1)^(r+(p-1)/2) ∣ Q ∧ (X+1)^((p-1)/2) ∣ Q ∧
      Q.degree < (↑(p+r) : WithBot ℕ) := by
  have hs : (∃ c : Fp,Q=c • centerGenerator r) ↔
      ∃ A : Fp[X],A.degree<(↑(1:ℕ):WithBot ℕ) ∧ Q=centerGenerator r*A := by
    constructor
    · rintro ⟨c,rfl⟩
      refine ⟨C c,?_,?_⟩
      · exact degree_C_le.trans_lt (by decide)
      · rw [mul_comm,C_mul']
    · rintro ⟨A,hA,hQ⟩
      have hdeg : A.degree ≤ 0 := by
        by_cases hzero : A=0
        · simp [hzero]
        · rw [degree_eq_natDegree hzero] at hA ⊢
          have hn : A.natDegree < 1 := by exact_mod_cast hA
          exact_mod_cast (show A.natDegree ≤ 0 by omega)
      refine ⟨A.coeff 0,?_⟩
      rw [hQ,eq_C_of_degree_le_zero hdeg,mul_comm,C_mul']
      simp only [coeff_C_zero]
  rw [hs,native_factor_window _ _ (centerGenerator_ne_zero r) (r+p-1) 1
    (centerGenerator_degree hp r),centerGenerator_factors]
  have hdiv : ((X-1 : Fp[X])^(r+(p-1)/2)*(X+1)^((p-1)/2) ∣ Q) ↔
      (X-1)^(r+(p-1)/2) ∣ Q ∧ (X+1)^((p-1)/2) ∣ Q := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right _ _).trans h,(dvd_mul_left _ _).trans h⟩
    · rintro ⟨h1,h2⟩
      exact (native_pair_coprime hp _ _).mul_dvd h1 h2
  rw [hdiv,and_assoc]
  have he : r+p-1+1=p+r := by have := (Fact.out:p.Prime).pos;omega
  rw [he]

/-- Exact center conditions are A conditions plus the -1 prefix. -/
theorem native_center_split (hp : p≠2) (r : ℕ) (hr : r<p)
    (F E : Fp[X]) (hF : F.degree < p) :
    (∃ c : Fp,F+(X^p-1)*E=c • centerGenerator r) ↔
    ((if r+(p-1)/2<p then (X-1)^(r+(p-1)/2) ∣ F
      else F=0 ∧ (X-1)^(r+(p-1)/2-p) ∣ E) ∧ E.degree < r) ∧
      (X+1)^((p-1)/2) ∣ F-2*E := by
  rw [center_source_conditions hp]
  constructor
  · rintro ⟨h1,h2,hdeg⟩
    exact ⟨(slot_A_conditions F E hF r ((p-1)/2) hr.le).mp ⟨h1,hdeg⟩,
      (slot_order_neg_one F E (show (p-1)/2≤p by omega)).mp h2⟩
  · rintro ⟨hA,h2⟩
    obtain ⟨h1,hdeg⟩ := (slot_A_conditions F E hF r ((p-1)/2) hr.le).mpr hA
    exact ⟨h1,(slot_order_neg_one F E (show (p-1)/2≤p by omega)).mpr h2,hdeg⟩
theorem center_scalar_unique (r : ℕ) (Q : Fp[X])
    (h : ∃ c : Fp,Q=c • centerGenerator r) : ∃! c : Fp,Q=c • centerGenerator r := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c,hc,?_⟩
  intro d hd
  exact (smul_left_injective Fp (centerGenerator_ne_zero r)) (hd.symm.trans hc)

theorem center_dimension_one (r : ℕ) :
    Module.finrank Fp (Submodule.span Fp {centerGenerator (p:=p) r})=1 :=
  finrank_span_singleton (centerGenerator_ne_zero r)

#print axioms native_center_split
#print axioms center_dimension_one
end CatalanMeasure.GenD.Uniform.Prefix



