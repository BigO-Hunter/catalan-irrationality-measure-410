module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaDeg
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Thin Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- A profile map from per-kind coefficient polynomials. -/
def sumProf {K b ex : ℕ} (hK : K = b * 4 + 2 + ex) (G : CK b ex → Fp[X]) :
    (Fin K → Fp) →ₗ[Fp] Fp[X] :=
  ∑ idx : Fin K, (LinearMap.proj idx : (Fin K → Fp) →ₗ[Fp] Fp).smulRight (G (ckEquiv hK idx))

theorem sumProf_apply {K b ex : ℕ} (hK : K = b * 4 + 2 + ex) (G : CK b ex → Fp[X])
    (y : Fin K → Fp) : sumProf hK G y = ∑ idx : Fin K, y idx • G (ckEquiv hK idx) := by
  simp [sumProf, LinearMap.sum_apply]

/-- The forward map `Θ`. -/
def Theta (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex) :
    (Fin (P.n N) → Fp) →ₗ[Fp] (Fin p → Fin K → Fp) :=
  LinearMap.pi fun e : Fin p => LinearMap.pi fun idx : Fin K =>
    (lcoeff Fp (e : ℕ)).comp (kindPoly (P := P) (N := N) hp2 hn (ckEquiv hK idx))

theorem Theta_apply (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex)
    (c : Fin (P.n N) → Fp) (e : Fin p) (idx : Fin K) :
    Theta hp2 hn hK c e idx = (kindPoly (P := P) (N := N) hp2 hn (ckEquiv hK idx) c).coeff e := rfl

theorem sum_coeff_smul_X (f : Fp[X]) (hf : f.degree < p) :
    ∑ e : Fin p, f.coeff (e : ℕ) • (X : Fp[X]) ^ (e : ℕ) = f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hnd : f.natDegree < p := by
    have := hf; rw [degree_eq_natDegree h0] at this; exact_mod_cast this
  rw [Fin.sum_univ_eq_sum_range (fun e => f.coeff e • (X : Fp[X]) ^ e) p]
  conv_rhs => rw [Polynomial.as_sum_range' f p hnd]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_X_eq_monomial]

/-- The swapped sum: the monomial atoms of `Θ c` against a per-kind coefficient family. -/
theorem Theta_sum (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex)
    (G : CK (bN P N p) ex → Fp[X]) (c : Fin (P.n N) → Fp) :
    ∑ e : Fin p, X ^ (e : ℕ) * (sumProf hK G (Theta hp2 hn hK c e)).comp (X ^ p) =
      ∑ i : CK (bN P N p) ex, kindPoly (P := P) (N := N) hp2 hn i c * (G i).comp (X ^ p) := by
  have h1 : ∀ e : Fin p, (sumProf hK G (Theta hp2 hn hK c e)).comp (X ^ p) =
      ∑ idx : Fin K, (Theta hp2 hn hK c e idx) • (G (ckEquiv hK idx)).comp (X ^ p) := by
    intro e
    rw [sumProf_apply, sum_comp']
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [Polynomial.smul_comp]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Equiv.sum_comp (ckEquiv hK)]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have hd := kindPoly_degree (P := P) (N := N) hp2 hn (ckEquiv hK idx) c
  calc ∑ x : Fin p, X ^ (x : ℕ) * (Theta hp2 hn hK c x idx • (G (ckEquiv hK idx)).comp (X ^ p))
      = (∑ x : Fin p, (kindPoly (P := P) (N := N) hp2 hn (ckEquiv hK idx) c).coeff (x : ℕ) •
          (X : Fp[X]) ^ (x : ℕ)) * (G (ckEquiv hK idx)).comp (X ^ p) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Theta_apply, smul_eq_C_mul, smul_eq_C_mul]
        ring
    _ = _ := by rw [sum_coeff_smul_X _ hd]

end
end CatalanMeasure.GenD.Uniform.W.Charts4
