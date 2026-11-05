module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCount2
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.JFlat
@[expose] public section
set_option Elab.async false

/-!
# The flat value is a polynomial function of degree `< p - v`

`foldPoly τ1 = Σ_{r<p} (π1[r] + π1[r+p]) X^r` is divisible by `(X-1)^v` when `(X-1)^v ∣ π1`
(`v ≤ p`), and `ℓ ↦ fold(π1)[(H-1-ℓ) mod p]` is a polynomial function of degree `< p - v`
(`jflat_poly`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `Σ_{r<p} (π[r] + π[r+p]) X^r`. -/
def foldPoly (P : Parameters) (N p : ℕ) [Fact p.Prime] {D : ℕ} (τ : Fin D → ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ Finset.range p, C (piSeq P N p τ r + piSeq P N p τ (r + p)) * X ^ r

theorem coeff_sumCX (f : ℕ → ZMod p) (r : ℕ) :
    (∑ b ∈ Finset.range p, C (f b) * X ^ b).coeff r = if r < p then f r else 0 := by
  rw [finset_sum_coeff]
  by_cases hr : r < p
  · rw [if_pos hr, Finset.sum_eq_single r]
    · rw [coeff_C_mul, coeff_X_pow_self]; ring
    · intro b _ hb; rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_range.mpr hr) h
  · rw [if_neg hr]
    refine Finset.sum_eq_zero fun b hb => ?_
    have := Finset.mem_range.mp hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega)]; ring

theorem foldPoly_coeff {D : ℕ} (τ : Fin D → ZMod p) (r : ℕ) (hr : r < p) :
    (foldPoly P N p τ).coeff r = piSeq P N p τ r + piSeq P N p τ (r + p) := by
  unfold foldPoly
  rw [coeff_sumCX (fun b => piSeq P N p τ b + piSeq P N p τ (b + p)) r, if_pos hr]

theorem foldPoly_natDegree {D : ℕ} (τ : Fin D → ZMod p) : (foldPoly P N p τ).natDegree < p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold foldPoly
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p - 1) fun r hr => ?_) (by omega)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.mp hr
  omega

/-- The `hi` part `Σ_{r<p} π[r+p] X^r`. -/
def hiPoly (P : Parameters) (N p : ℕ) [Fact p.Prime] {D : ℕ} (τ : Fin D → ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ Finset.range p, C (piSeq P N p τ (r + p)) * X ^ r

theorem hiPoly_coeff {D : ℕ} (τ : Fin D → ZMod p) (r : ℕ) :
    (hiPoly P N p τ).coeff r = if r < p then piSeq P N p τ (r + p) else 0 := by
  unfold hiPoly
  exact coeff_sumCX (fun b => piSeq P N p τ (b + p)) r

theorem fold_coeff_all {D : ℕ} (τ : Fin D → ZMod p) (r : ℕ) :
    (foldPoly P N p τ).coeff r = if r < p then piSeq P N p τ r + piSeq P N p τ (r + p) else 0 := by
  by_cases hr : r < p
  · rw [if_pos hr, foldPoly_coeff τ r hr]
  · rw [if_neg hr]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (foldPoly_natDegree τ) (by omega))

/-- `Pi_poly = fold + (X^p - 1) hi` (degree `< 2p`). -/
theorem Pi_eq_fold (hp2 : p ≠ 2) {hp : ℕ} (hhp : P.h N + hp ≤ p - 1) (τ : Fin (hp + 1) → ZMod p) :
    Pi_poly P N p τ = foldPoly P N p τ + (X ^ p - 1) * hiPoly P N p τ := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  ext i
  rw [← piSeq_eq, coeff_add, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul', fold_coeff_all]
  by_cases h1 : i < p
  · rw [if_pos h1, if_neg (by omega), hiPoly_coeff, if_pos h1]; ring
  · rw [if_neg h1, if_pos (by omega), hiPoly_coeff τ (i - p), hiPoly_coeff τ i, if_neg h1]
    by_cases h2 : i - p < p
    · rw [if_pos h2, Nat.sub_add_cancel (by omega)]; ring
    · have h3 : piSeq P N p τ i = 0 := piSeq_hi_zero hp2 τ i (by omega)
      rw [if_neg h2, h3]; ring

theorem foldPoly_dvd (hp2 : p ≠ 2) {hp : ℕ} (hhp : P.h N + hp ≤ p - 1) (τ : Fin (hp + 1) → ZMod p)
    (v : ℕ) (hv : v ≤ p) (hdv : ((X - 1) ^ v : (ZMod p)[X]) ∣ Pi_poly P N p τ) :
    ((X - 1) ^ v : (ZMod p)[X]) ∣ foldPoly P N p τ := by
  have hX : ((X - 1) ^ p : (ZMod p)[X]) = X ^ p - 1 := by rw [sub_pow_char]; simp
  have h2 : ((X - 1) ^ v : (ZMod p)[X]) ∣ (X ^ p - 1) * hiPoly P N p τ := by
    rw [← hX]; exact Dvd.dvd.mul_right (pow_dvd_pow _ hv) _
  have : foldPoly P N p τ = Pi_poly P N p τ - (X ^ p - 1) * hiPoly P N p τ := by
    rw [Pi_eq_fold hp2 hhp τ]; ring
  rw [this]
  exact dvd_sub hdv h2

/-- The residue position `r = (H-1-ℓ) mod p` of the column residue `x = ℓ`. -/
def rOf (p H : ℕ) (x : ZMod p) : ℕ := (((H : ℤ) - 1 - (x.val : ℤ)) % p).toNat

theorem rOf_lt (H : ℕ) (x : ZMod p) : rOf p H x < p := by
  have hp1 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h0 : (0 : ℤ) ≤ ((H : ℤ) - 1 - (x.val : ℤ)) % p := Int.emod_nonneg _ hp1.ne'
  have h1 := Int.emod_lt_of_pos ((H : ℤ) - 1 - (x.val : ℤ)) hp1
  unfold rOf; omega

theorem val_sub_H (H : ℕ) (x : ZMod p) : (x - (H : ZMod p)).val = p - 1 - rOf p H x := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hr := rOf_lt (p := p) H x
  have hcast : ((rOf p H x : ℕ) : ZMod p) = (H : ZMod p) - 1 - x := by
    unfold rOf
    have hp1 : (0 : ℤ) < p := by exact_mod_cast hp0
    have h0 : (0 : ℤ) ≤ ((H : ℤ) - 1 - (x.val : ℤ)) % p := Int.emod_nonneg _ hp1.ne'
    have : ((((H : ℤ) - 1 - (x.val : ℤ)) % p).toNat : ℤ) = ((H : ℤ) - 1 - (x.val : ℤ)) % p :=
      Int.toNat_of_nonneg h0
    have h2 : ((((H : ℤ) - 1 - (x.val : ℤ)) % p).toNat : ZMod p) =
        (((((H : ℤ) - 1 - (x.val : ℤ)) % p).toNat : ℤ) : ZMod p) := by norm_cast
    rw [h2, this, ZMod.intCast_mod]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have : (((p - 1 - rOf p H x : ℕ)) : ZMod p) = x - (H : ZMod p) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self, hcast]
    ring
  rw [← this, ZMod.val_cast_of_lt (by omega)]

/-- **The flat value is a polynomial function of degree `< p - v`.** -/
theorem flat_value_poly (hp2 : p ≠ 2) {hp : ℕ} (hhp : P.h N + hp ≤ p - 1)
    (τ : Fin (hp + 1) → ZMod p) (v : ℕ) (hv : v < p)
    (hdv : ((X - 1) ^ v : (ZMod p)[X]) ∣ Pi_poly P N p τ) (H : ℕ) :
    ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ x : ZMod p, G.eval x =
        piSeq P N p τ (rOf p H x) + piSeq P N p τ (rOf p H x + p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨G0, hG0, hG0e⟩ := jflat_poly (p := p) hv (foldPoly P N p τ)
    (foldPoly_dvd hp2 hhp τ v hv.le hdv) (p - 1) (by
      have := foldPoly_natDegree (P := P) (N := N) τ; omega)
    (fun i hi => by
      exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (foldPoly_natDegree τ) (by omega)))
  refine ⟨G0.comp (X - C (H : ZMod p)), ?_, fun x => ?_⟩
  · have hq : 0 < (X - C (H : ZMod p)).degree := by rw [degree_X_sub_C]; exact zero_lt_one
    rw [degree_comp hq, degree_X_sub_C, mul_one]; exact hG0
  · rw [eval_comp, eval_sub, eval_X, eval_C, ← hG0e, if_pos (by have := ZMod.val_lt (x - (H : ZMod p)); omega),
      val_sub_H H x]
    have hr := rOf_lt (p := p) H x
    have : p - 1 - (p - 1 - rOf p H x) = rOf p H x := by omega
    rw [this, foldPoly_coeff τ _ hr]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
