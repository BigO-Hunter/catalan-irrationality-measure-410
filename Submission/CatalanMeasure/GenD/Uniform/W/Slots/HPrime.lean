module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.FlatCount
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HInst
@[expose] public section
set_option Elab.async false

/-!
# Theorem H' on the slot API

`hPrime_le_nullity`: H+ pairs of blocks `k0, …, k0+K-1`, slots `t < D` (so `j = (p-1)/2 - t`),
digit `s` (`η = H-1-sp`), jets `e0`, and a set `JJ` of digits that see the window; the profiles
`x` are taken in the common kernel of `ψ(J,s) - ψ(J0,s)`, `J ∈ JJ \ {J0}`:

    (D - e0) (K - |JJ \ {J0}|) - #virtual ≤ ν.

Hypotheses are linear in `(n, b, q, g, h, p)` and `s, k0, K, D, e0`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem sub_one_pow_prime : ((X - 1 : (ZMod p)[X])) ^ p = X ^ p - 1 := by
  rw [sub_pow_char, one_pow]

/-- `U_{h-t-1} + U_{h+t} = (X²-1)^h T_{h-t} - (X-1)^p U_{h-t-1}` (`h = (p-1)/2`). -/
theorem hf_expand (hp2 : p ≠ 2) (t : ℤ) :
    Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t) =
      (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) * Chebyshev.T (ZMod p) (hh p - t) -
        (X - 1) ^ p * Chebyshev.U (ZMod p) (hh p - t - 1) := by
  have hpe := p_eq_hh hp2
  have h2 := chebyshev_U_reflect (ZMod p) (p : ℤ) (hh p - t)
  rw [chebyshev_T_prime hp2, chebyshev_U_prime hp2] at h2
  have e2 : (p : ℤ) - (hh p - t) - 1 = hh p + t := by rw [hpe]; ring
  rw [e2] at h2
  rw [h2, sub_one_pow_prime]
  ring

theorem hLam_dvd (hp2 : p ≠ 2) (t : ℕ) :
    ((X - 1) ^ (P.h N + (p - 1) / 2) : (ZMod p)[X]) ∣ hLam P N p t := by
  unfold hLam
  rw [pow_add]
  refine mul_dvd_mul_left _ ?_
  rw [hf_expand hp2]
  refine dvd_sub ?_ ?_
  · refine dvd_mul_of_dvd_left ?_ _
    have : ((X - 1 : (ZMod p)[X])) ∣ X ^ 2 - 1 := ⟨X + 1, by ring⟩
    exact pow_dvd_pow_of_dvd this _
  · refine dvd_mul_of_dvd_left ?_ _
    exact pow_dvd_pow _ (by omega)

/-- Kernel of finitely many covectors. -/
theorem exists_common_kernel {K : ℕ} (T : Finset ℕ) (ψ : ℕ → (Fin K → ZMod p) →ₗ[ZMod p] ZMod p) :
    ∃ V : Submodule (ZMod p) (Fin K → ZMod p), K - T.card ≤ finrank (ZMod p) V ∧
      ∀ J ∈ T, ∀ y ∈ V, ψ J y = 0 := by
  refine ⟨LinearMap.ker (LinearMap.pi fun i : Fin T.card => ψ (T.equivFin.symm i).1), ?_, ?_⟩
  · have := kappa_ge (LinearMap.pi fun i : Fin T.card => ψ (T.equivFin.symm i).1)
    simpa using this
  · intro J hJ y hy
    have := congrFun (LinearMap.mem_ker.mp hy) (T.equivFin ⟨J, hJ⟩)
    simpa using this

/-- **Theorem H' (slot form).** -/
theorem hPrime_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D e0 s : ℕ} (k0 : ℤ) (hD : D ≤ (p - 1) / 2) (JJ : Finset ℕ) (J0 : ℕ)
    (hv : P.h N + (p - 1) / 2 < p) (hq : p ≤ P.q N + (P.h N + (p - 1) / 2))
    (hs : s * p + 1 ≤ P.H N)
    (hdeg : P.h N + (p - 1) / 2 + D ≤ (P.H N - 1 - s * p) + 1)
    (he0 : (P.H N - 1 - s * p) + 1 ≤ e0 + p)
    (hJJ : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ P.H N - 1 - s * p →
      P.H N - 1 - s * p ≤ j % p + (P.h N + (p - 1) / 2 + D - 1) → j / p ∈ JJ) :
    (D - e0) * (K - (JJ.erase J0).card) - hVirt P N p K D k0 ≤ nullity P N p := by
  classical
  set S := hSystem P N p hp2 K D k0 hD with hS
  obtain ⟨V, hV1, hV2⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => S.prof.psi (P.H N) J s - S.prof.psi (P.H N) J0 s)
  have hdeg' : ∀ t : Fin S.D, (S.lam t).natDegree ≤ P.h N + (p - 1) / 2 + D - 1 := by
    intro t
    have := hLam_natDegree_lt (P := P) (N := N) hp2 hD t
    have ht := t.isLt
    show (hLam P N p t).natDegree ≤ _
    omega
  have h1 : finrank (ZMod p) (S.atoms V) ≤ nullity P N p + e0 * finrank (ZMod p) V +
      (p - P.q N - (P.h N + (p - 1) / 2)) := S.slot_nullity_flat hP hN hp2 hH V (S.prof.psi (P.H N) J0 s)
    (eta := P.H N - 1 - s * p) (s := s) (e0 := e0) (v := P.h N + (p - 1) / 2)
    (dm := P.h N + (p - 1) / 2 + D - 1) hv (by omega)
    (fun t => hLam_dvd hp2 t) hdeg' he0 (by omega)
    (fun j h1 h2 h3 h4 y hy => by
      have hJ := hJJ j h1 h2 h3 h4
      by_cases hc : j / p = J0
      · rw [hc]
      · have := hV2 (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) y hy
        exact sub_eq_zero.mp this)
  have h2 := S.finrank_atoms_ge V (hBad P N p K D k0) (fun x => Iff.rfl)
  have h3 : D * finrank (ZMod p) V ≤ finrank (ZMod p) (S.atoms V) + hVirt P N p K D k0 := h2
  have h4 : (D - e0) * (K - (JJ.erase J0).card) ≤ (D - e0) * finrank (ZMod p) V :=
    Nat.mul_le_mul_left _ hV1
  by_cases hDe : D ≤ e0
  · have : D - e0 = 0 := by omega
    rw [this, zero_mul, Nat.zero_sub]
    exact Nat.zero_le _
  have h5 : D * finrank (ZMod p) V = (D - e0) * finrank (ZMod p) V + e0 * finrank (ZMod p) V := by
    rw [← add_mul, Nat.sub_add_cancel (by omega)]
  have hc : p - P.q N - (P.h N + (p - 1) / 2) = 0 := by omega
  rw [hc, add_zero] at h1
  rw [Nat.sub_le_iff_le_add]
  clear h2
  generalize (D - e0) * (K - (JJ.erase J0).card) = a at *
  generalize (D - e0) * finrank (ZMod p) V = b at *
  generalize D * finrank (ZMod p) V = c at *
  generalize e0 * finrank (ZMod p) V = d at *
  generalize finrank (ZMod p) (S.atoms V) = e at *
  omega

#print axioms hPrime_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Slots
