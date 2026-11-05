module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.QSpan
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Slots
@[expose] public section
set_option Elab.async false

/-!
# From native-basis coordinates of the slots back to tiling coordinates
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Polynomial Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Tiling coordinates with prescribed native-basis coordinates `gA, gC` and outer centre `z`. -/
def tilingOfSlots {b : ℕ} (gA' : Fin b → Fin ((p - 1) / 2 + 1) → Fp)
    (gC' : Fin b → Fin ((p - 1) / 2) → Fp) (z : Fp) :
    TilingCoordinates (K := Fp) b ((p - 1) / 2) :=
  ((fun i => gA' (finProdFinEquiv.symm i).1 (Fin.castSucc (Fin.rev (finProdFinEquiv.symm i).2)),
    fun i => gC' (finProdFinEquiv.symm i).1 (Fin.rev (finProdFinEquiv.symm i).2)),
   Fin.cons z (fun k => gA' k (Fin.last _)))

theorem gA_tilingOfSlots {b : ℕ} (gA' : Fin b → Fin ((p - 1) / 2 + 1) → Fp)
    (gC' : Fin b → Fin ((p - 1) / 2) → Fp) (z : Fp) (k : Fin b) (i : Fin ((p - 1) / 2 + 1)) :
    gA (tilingOfSlots gA' gC' z) k i = gA' k i := by
  unfold gA tilingOfSlots
  by_cases h : i.val < (p - 1) / 2
  · rw [dif_pos h]
    simp only [Equiv.symm_apply_apply, Fin.rev_rev]
    congr 1
  · rw [dif_neg h]
    have : i = Fin.last _ := Fin.ext (by have := i.isLt; simp; omega)
    subst this
    simp

theorem gC_tilingOfSlots {b : ℕ} (gA' : Fin b → Fin ((p - 1) / 2 + 1) → Fp)
    (gC' : Fin b → Fin ((p - 1) / 2) → Fp) (z : Fp) (k : Fin b) (i : Fin ((p - 1) / 2)) :
    gC (tilingOfSlots gA' gC' z) k i = gC' k i := by
  unfold gC tilingOfSlots
  simp only [Equiv.symm_apply_apply, Fin.rev_rev]

theorem z_tilingOfSlots {b : ℕ} (gA' : Fin b → Fin ((p - 1) / 2 + 1) → Fp)
    (gC' : Fin b → Fin ((p - 1) / 2) → Fp) (z : Fp) :
    (tilingOfSlots gA' gC' z).2 0 = z := by
  simp [tilingOfSlots]

theorem QA_tilingOfSlots {b : ℕ} (gA' : Fin b → Fin ((p - 1) / 2 + 1) → Fp)
    (gC' : Fin b → Fin ((p - 1) / 2) → Fp) (z : Fp) (k : Fin b) :
    QA (tilingOfSlots gA' gC' z) k = ∑ i, gA' k i • plusVectors (p := p) i := by
  rw [QA_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [gA_tilingOfSlots]

theorem QC_tilingOfSlots {b : ℕ} (gA' : Fin b → Fin ((p - 1) / 2 + 1) → Fp)
    (gC' : Fin b → Fin ((p - 1) / 2) → Fp) (z : Fp) (k : Fin b) :
    QC (tilingOfSlots gA' gC' z) k = ∑ i, gC' k i • minusVectors (p := p) i := by
  rw [QC_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [gC_tilingOfSlots]

/-- Polynomial of one coordinate of monomial atoms. -/
def polx {K : ℕ} (x : Fin p → Fin K → Fp) (idx : Fin K) : Fp[X] :=
  ∑ e : Fin p, C (x e idx) * X ^ (e : ℕ)

theorem polx_degree {K : ℕ} (x : Fin p → Fin K → Fp) (idx : Fin K) : (polx x idx).degree < p := by
  unfold polx
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro e _
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast e.isLt)

theorem polx_coeff {K : ℕ} (x : Fin p → Fin K → Fp) (idx : Fin K) (e : Fin p) :
    (polx x idx).coeff (e : ℕ) = x e idx := by
  unfold polx
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hne (Fin.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ e) h

theorem fpart_epart_of (F E : Fp[X]) (hF : F.degree < p) :
    fpart p (F + (X ^ p - 1) * E) = F ∧ epart p (F + (X ^ p - 1) * E) = E := by
  have := div_modByMonic_unique (f := F + (X ^ p - 1) * E) (g := qY p) E F qY_monic
    ⟨rfl, by rwa [qY_degree]⟩
  exact ⟨this.2, this.1⟩

end
end CatalanMeasure.GenD.Uniform.W.Charts4
