module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyFun
@[expose] public section
set_option Elab.async false

/-!
# The HY+ conditions as one linear map, and the kernel dimension
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The Taylor-jet polynomial `F^-_t = U_{hh-t-1} - U_{hh+t}`. -/
def hmF (p t : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  Chebyshev.U (ZMod p) (hh p - t - 1) - Chebyshev.U (ZMod p) (hh p + t)

theorem hmLam_eq (P : Parameters) (N p t : ℕ) [Fact p.Prime] :
    hmLam P N p t = (X - 1) ^ P.h N * hmF p t := rfl

/-- `a ↦ (taylor 1 σ_C).coeff i`, `σ_C = Σ C_t F^-_t`. -/
def jetL (p Dn nQ : ℕ) [Fact p.Prime] (i : ℕ) : HyA p Dn nQ →ₗ[ZMod p] ZMod p :=
  ∑ t : Fin Dn, ((taylor 1 (hmF p (t : ℕ))).coeff i) • pjD p Dn nQ t

theorem jetL_apply (Dn nQ i : ℕ) (a : HyA p Dn nQ) :
    jetL p Dn nQ i a = (taylor 1 (∑ t : Fin Dn, C (a.2.2 t) * hmF p (t : ℕ))).coeff i := by
  simp only [jetL, LinearMap.sum_apply, LinearMap.smul_apply, pjD, LinearMap.comp_apply,
    LinearMap.coe_proj, Function.eval, LinearMap.snd_apply, smul_eq_mul, map_sum, finset_sum_coeff]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← smul_eq_C_mul, map_smul, coeff_smul, smul_eq_mul, mul_comm]

theorem X_sub_one_pow_dvd_of_jets (f : ℕ) (g : (ZMod p)[X]) (h : ∀ i < f, (taylor 1 g).coeff i = 0) :
    ((X - 1 : (ZMod p)[X]) ^ f) ∣ g := by
  have h1 : (X : (ZMod p)[X]) ^ f ∣ taylor 1 g := (X_pow_dvd_iff).mpr h
  obtain ⟨r, hr⟩ := h1
  have hg : g = (taylor 1 g).comp (X - 1) := by
    rw [taylor_apply, comp_assoc]
    simp
  refine ⟨r.comp (X - 1), ?_⟩
  rw [hg, hr, mul_comp, pow_comp, X_comp]

/-- Linear functional on data. -/
def datL (K' D' : ℕ) [Fact p.Prime] (t : Fin D') (k : Fin K') :
    (Fin D' → Fin K' → ZMod p) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj k : (Fin K' → ZMod p) →ₗ[ZMod p] ZMod p).comp
    (LinearMap.proj t : (Fin D' → Fin K' → ZMod p) →ₗ[ZMod p] _)

/-- The linear response of a slot system. -/
def respL (S : SlotSystem P N p) (J ℓ : ℕ) :
    (Fin S.D → Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ e ∈ Finset.range S.emax,
    if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ℓ - e then
      (S.prof.psi (P.H N) J (((P.H N : ℤ) - 1 - ℓ - e) / p)).comp (wvL S.lam e) else 0

theorem respL_apply (S : SlotSystem P N p) (J ℓ : ℕ) (x : Fin S.D → Fin S.K → ZMod p) :
    respL S J ℓ x = S.resp J ℓ x := by
  unfold respL SlotSystem.resp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · simp [wvL_apply]
  · simp

/-- Edge set. -/
def edgeSet (P : Parameters) (N p a0 nQ s η Dn : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range p ×ˢ Finset.range (P.L N / p + 2)).filter fun lj =>
    P.b N ≤ lj.2 * p + lj.1 ∧ lj.2 * p + lj.1 < P.L N ∧
      HyBad (P.h N + (p - 1) / 2 + Dn) a0 nQ s p η lj.1 lj.2

/-- Number of missing rows (both sides). -/
def hyMiss (P : Parameters) (N p K Dn : ℕ) [Fact p.Prime] (k0 : ℤ) : ℕ :=
  (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hlo p K k0 tk.2 tk.1)).card +
  (Finset.univ.filter fun tk : Fin Dn × Fin K => ¬ InRange P N (hhi p K k0 tk.2 tk.1)).card

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
