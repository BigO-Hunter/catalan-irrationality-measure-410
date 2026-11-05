module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.Transfer
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.TpPlain
@[expose] public section
set_option Elab.async false

/-!
# Source covectors of the `T+` / `T-` slot profiles on rational cells

For the plain `T+` system (`Ty = Σ y_k U_{k-1}`, `Gy = Σ y_k T_k`) and the `T-` system
(`Ty = Σ y_k T_k`, `Gy = (X²-1) Σ y_k U_{k-1}`), the covector `ψ(J,σ)` of the profile
`k ↦ res(z_k)` is the residue of the rational form `fTp` / `fTm`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem PhiQ_mem (hm : MomUnits p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) :
    Q.PhiQ a b J σ ∈ unitSub p := by
  unfold Q.PhiQ
  refine Subring.sum_mem _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  exact Subring.add_mem _
    (Subring.mul_mem _ (alpha_mem hm (by omega) hJ) (intCast_mem _ _))
    (Subring.mul_mem _ (beta_mem hm (by omega) hJ) (intCast_mem _ _))

/-- The profile `k ↦ res(z_k)`. -/
def zvec (p : ℕ) [Fact p.Prime] (K : ℕ) (z : ℕ → ℚ) : Fin K → ZMod p :=
  fun k => palindromicRatResidue p (z k)

/-- Profile maps of the plain `T+` system and of the `T-` system. -/
def profTp (p K : ℕ) [Fact p.Prime] : Prof p K := ⟨uyMap p K 0, tyMap p K 0⟩
def profTm (p K : ℕ) [Fact p.Prime] : Prof p K := ⟨tyMap p K 0, gyMap p K 0⟩

theorem tyMap_single (K : ℕ) (k : Fin K) :
    tyMap p K 0 (Pi.single k 1) = Chebyshev.T (ZMod p) ((k : ℕ) : ℤ) := by
  rw [tyMap_apply, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'; simp [Pi.single_apply, hk']
  · simp

theorem uyMap_single (K : ℕ) (k : Fin K) :
    uyMap p K 0 (Pi.single k 1) = Chebyshev.U (ZMod p) (((k : ℕ) : ℤ) - 1) := by
  rw [uyMap_apply, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'; simp [Pi.single_apply, hk']
  · simp

theorem psiTp_single (hm : MomUnits p) {K : ℕ} (k : Fin K) {J σ H : ℕ} (hJ : J < 7)
    (hσ : σ + 3 ≤ 9) (hH : σ + 3 ≤ H) :
    (profTp p K).psi H J (σ : ℤ) (Pi.single k 1) =
      palindromicRatResidue p (Q.PhiTp k J σ) := by
  unfold Prof.psi profTp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [tyMap_single, uyMap_single]
  exact digitPhi_eq_res_PhiQ hm (Q.tc k) (Q.ucm k) _ _ (T_coeff (ZMod p) k) (Um_coeff (ZMod p) k) hJ hσ hH

theorem psiTm_single (hm : MomUnits p) {K : ℕ} (k : Fin K) {J σ H : ℕ} (hJ : J < 7)
    (hσ : σ + 3 ≤ 9) (hH : σ + 3 ≤ H) :
    (profTm p K).psi H J (σ : ℤ) (Pi.single k 1) =
      palindromicRatResidue p (Q.PhiTm k J σ) := by
  unfold Prof.psi profTm
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : tyMap p K 0 (Pi.single k 1) = Chebyshev.T (ZMod p) ((k : ℕ) : ℤ) := tyMap_single K k
  have h2 : gyMap p K 0 (Pi.single k 1) =
      (X ^ 2 - 1) * Chebyshev.U (ZMod p) (((k : ℕ) : ℤ) - 1) := by
    rw [gyMap_apply, uyMap_single]
  rw [h1, h2]
  exact digitPhi_eq_res_PhiQ hm (Q.aTm k) (Q.tc k) _ _ (Am_coeff (ZMod p) k) (T_coeff (ZMod p) k) hJ hσ hH

/-- Linearity of `ψ` over the profile coordinates. -/
theorem psi_apply_sum {K : ℕ} (F : Prof p K) (H J : ℕ) (a : ℤ) (y : Fin K → ZMod p) :
    F.psi H J a y = ∑ k : Fin K, y k * F.psi H J a (Pi.single k 1) := by
  have hy : y = ∑ k : Fin K, y k • (Pi.single k 1 : Fin K → ZMod p) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
