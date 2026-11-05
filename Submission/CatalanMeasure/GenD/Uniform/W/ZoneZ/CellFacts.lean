module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.PsiCells
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsShape
@[expose] public section
set_option Elab.async false

/-!
# Cell facts in `ZMod p`

For `p ∤ Zbad` the cell properties, the Lemma-S shapes and (P*) (all proved exactly over `ℚ` in
`CellsH`, `CellsL`, `CellsShape`) hold for the covectors `ψ(J,σ)` of the slot systems on the
residue profiles `zvec`.  `Zbad` is an explicit integer (lcm of the moment denominators, the
cell-vector denominators and the (P*) coefficients): Lemma B -- no factoring needed.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem res_comb {K : ℕ} (z f : ℕ → ℚ) (hz : ∀ k < K, z k ∈ unitSub p)
    (hf : ∀ k < K, f k ∈ unitSub p) :
    palindromicRatResidue p (Q.comb K z f) =
      ∑ k : Fin K, palindromicRatResidue p (z k) * palindromicRatResidue p (f k) := by
  unfold Q.comb
  rw [palindromicRatResidue_sum _ _ (fun k hk => (Subring.mul_mem _
    (hz k (Finset.mem_range.mp hk)) (hf k (Finset.mem_range.mp hk))))]
  rw [← Fin.sum_univ_eq_sum_range (fun k => palindromicRatResidue p (z k * f k)) K]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (rational_residue_mul (hz k k.2) (hf k k.2)).2

theorem PhiTp_mem (hm : MomUnits p) (k : ℕ) {J σ : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) :
    Q.PhiTp k J σ ∈ unitSub p := PhiQ_mem hm _ _ hJ hσ

theorem PhiTm_mem (hm : MomUnits p) (k : ℕ) {J σ : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) :
    Q.PhiTm k J σ ∈ unitSub p := PhiQ_mem hm _ _ hJ hσ

/-- **ψ of a `T+` cell is the residue of `fTp`.** -/
theorem psiTp_zvec (hm : MomUnits p) {K : ℕ} (z : ℕ → ℚ) (hz : ∀ k < K, z k ∈ unitSub p)
    {J σ H : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) (hH : σ + 3 ≤ H) :
    (profTp p K).psi H J (σ : ℤ) (zvec p K z) = palindromicRatResidue p (Q.fTp K z J σ) := by
  rw [psi_apply_sum]
  unfold Q.fTp
  rw [res_comb z _ hz (fun k _ => PhiTp_mem hm k hJ hσ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [psiTp_single hm k hJ hσ hH]; rfl

theorem psiTm_zvec (hm : MomUnits p) {K : ℕ} (z : ℕ → ℚ) (hz : ∀ k < K, z k ∈ unitSub p)
    {J σ H : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) (hH : σ + 3 ≤ H) :
    (profTm p K).psi H J (σ : ℤ) (zvec p K z) = palindromicRatResidue p (Q.fTm K z J σ) := by
  rw [psi_apply_sum]
  unfold Q.fTm
  rw [res_comb z _ hz (fun k _ => PhiTm_mem hm k hJ hσ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [psiTm_single hm k hJ hσ hH]; rfl

/-- Transfer of a rational identity of the (P*) shape to residues. -/
theorem res_pstar_form {V1 V2 V3 V4 m2 m3 n r T B : ℚ} (h1 : V1 ∈ unitSub p) (h2 : V2 ∈ unitSub p)
    (h3 : V3 ∈ unitSub p) (h4 : V4 ∈ unitSub p) (hm2 : m2 ∈ unitSub p) (hm3 : m3 ∈ unitSub p)
    (hn : n ∈ unitSub p) (hr : r ∈ unitSub p) (hT : T ∈ unitSub p) (hB : B ∈ unitSub p)
    (h : V4 - V1 = m2 * (V2 - V1) + m3 * (V3 - V1) + n * T + r * B) :
    palindromicRatResidue p V4 - palindromicRatResidue p V1 =
      palindromicRatResidue p m2 * (palindromicRatResidue p V2 - palindromicRatResidue p V1) +
      palindromicRatResidue p m3 * (palindromicRatResidue p V3 - palindromicRatResidue p V1) +
      palindromicRatResidue p n * palindromicRatResidue p T +
      palindromicRatResidue p r * palindromicRatResidue p B := by
  have := congrArg (resHom p)
    (Subtype.ext h : (⟨V4, h4⟩ : unitSub p) - ⟨V1, h1⟩ =
      ⟨m2, hm2⟩ * (⟨V2, h2⟩ - ⟨V1, h1⟩) + ⟨m3, hm3⟩ * (⟨V3, h3⟩ - ⟨V1, h1⟩) +
        ⟨n, hn⟩ * ⟨T, hT⟩ + ⟨r, hr⟩ * ⟨B, hB⟩)
  simpa only [map_sub, map_add, map_mul, resHom_apply] using this

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
