module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaRep
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Thin Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

theorem rem_ne_zero (h : ℕ) : (X - 1 : Fp[X]) ^ (h % p) ≠ 0 := by
  exact pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : Fp))

theorem nativeCenter_ne_zero : nativeCenter (p := p) ≠ 0 := by
  unfold nativeCenter
  exact pow_ne_zero _ (by simpa using X_pow_sub_C_ne_zero (R := Fp) (by norm_num : 0 < 2) (1 : Fp))

theorem kindPoly_zero_of_Theta (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ}
    (hK : K = bN P N p * 4 + 2 + ex) (c : Fin (P.n N) → Fp) (h : Theta hp2 hn hK c = 0)
    (i : CK (bN P N p) ex) : kindPoly (P := P) (N := N) hp2 hn i c = 0 := by
  ext m
  by_cases hm : m < p
  · have := congrFun (congrFun h ⟨m, hm⟩) ((ckEquiv hK).symm i)
    rw [Theta_apply] at this
    simpa using this
  · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (kindPoly_degree hp2 hn i c)
      (by exact_mod_cast not_lt.mp hm))

theorem Theta_injective (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ}
    (hK : K = bN P N p * 4 + 2 + ex) : Function.Injective (Theta (P := P) (N := N) hp2 hn hK) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c h
  have hk := kindPoly_zero_of_Theta hp2 hn hK c h
  have hsplit : ∀ Λ : Fp[X], fpart p Λ = 0 → epart p Λ = 0 → Λ = 0 := by
    intro Λ h1 h2
    rw [← fpart_epart Λ, h1, h2]; simp
  have hA : ∀ k, QA (tL hp2 hn c) k = 0 := by
    intro k
    have h0 := hk (Sum.inl (k, 0)); have h1 := hk (Sum.inl (k, 1))
    rw [kp_A0] at h0; rw [kp_A1] at h1
    have := hsplit _ h0 h1
    exact (mul_eq_zero.mp this).resolve_left (rem_ne_zero (P.h N))
  have hC : ∀ k, QC (tL hp2 hn c) k = 0 := by
    intro k
    have h0 := hk (Sum.inl (k, 2)); have h1 := hk (Sum.inl (k, 3))
    rw [kp_C0] at h0; rw [kp_C1] at h1
    have := hsplit _ h0 h1
    exact (mul_eq_zero.mp this).resolve_left (rem_ne_zero (P.h N))
  have hZ : (tL hp2 hn c).2 0 = 0 := by
    have h0 := hk (Sum.inr (Sum.inl 0)); have h1 := hk (Sum.inr (Sum.inl 1))
    rw [kp_Z0] at h0; rw [kp_Z1] at h1
    have := hsplit _ h0 h1
    have h2 := (mul_eq_zero.mp this).resolve_left (rem_ne_zero (P.h N))
    exact (smul_eq_zero.mp h2).resolve_right nativeCenter_ne_zero
  have ht : tL hp2 hn c = 0 := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext i
      have hi := (finProdFinEquiv.apply_symm_apply i).symm
      rcases hkj : finProdFinEquiv.symm i with ⟨k, j⟩
      rw [hkj] at hi
      rw [hi]
      exact (QA_zero hp2 _ k (hA k)).2 j
    · funext i
      have hi := (finProdFinEquiv.apply_symm_apply i).symm
      rcases hkj : finProdFinEquiv.symm i with ⟨k, j⟩
      rw [hkj] at hi
      rw [hi]
      exact QC_zero hp2 _ k (hC k) j
    · funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · exact hZ
      · exact (QA_zero hp2 _ k (hA k)).1
  have h3 : rowsExt (P.n N) (P.g N) p (Fact.out : p.Prime).pos hn c = 0 := by
    have := congrArg (physicalTilingEquiv (bN P N p) ((p - 1) / 2) p (native_half_identity hp2)
      (native_two_ne_zero hp2)) ht
    simpa [tL] using this
  exact rowsExt_injective (P.n N) (P.g N) p (Fact.out : p.Prime).pos hn (by simpa using h3)

/-- **`MonoData` of the four-point frame**, for every design (no window hypothesis). -/
def monoData (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex) :
    MonoData P N p K :=
  monoOfForward (monoProfile P N p hK) (Theta hp2 hn hK) (Theta_injective hp2 hn hK)
    (Theta_repU hp2 hn hK) (Theta_repT hp2 hn hK)

end
end CatalanMeasure.GenD.Uniform.W.Charts4
