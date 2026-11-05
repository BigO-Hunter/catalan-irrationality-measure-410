module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZFlat2
@[expose] public section
set_option Elab.async false

/-!
# Digit conclusions: `J = 1,2,3` from the main condition, `J = 4` from (P*) and Lemma X
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem dotc_congr (v w : ℕ → ZMod p) (π1 π2 l1 l2 : ℕ → ZMod p) (p' r : ℕ)
    (h : ∀ c < 4, v c = w c) :
    dotc v π1 π2 l1 l2 p' r = dotc w π1 π2 l1 l2 p' r := by
  unfold dotc
  exact Finset.sum_congr rfl fun c hc => by rw [h c (Finset.mem_range.mp hc)]

/-- `J = 1, 2, 3`: the main functional `(v_2 - v_1) . seq[r]` kills `v_J . seq[r]`. -/
theorem dot_J123 {K H : ℕ} {u u2 y1 y2 : Fin K → ZMod p} {μ2 μ3 ν ρ : ZMod p} {ktop k0 : Fin K}
    (hc : CellHyp p K H u u2 y1 y2 μ2 μ3 ν ρ ktop k0) (π1 π2 l1 l2 : ℕ → ZMod p) (r : ℕ)
    (hW : dotc (fun c => vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c) π1 π2 l1 l2 p r = 0) :
    dotc (vv p K H u u2 y1 y2 1) π1 π2 l1 l2 p r = 0 ∧
    dotc (vv p K H u u2 y1 y2 2) π1 π2 l1 l2 p r = 0 ∧
    dotc (vv p K H u u2 y1 y2 3) π1 π2 l1 l2 p r = 0 := by
  have h1 : dotc (vv p K H u u2 y1 y2 1) π1 π2 l1 l2 p r = 0 := by
    rw [dotc_congr _ (fun c => -3 * (vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c)) _ _ _ _ _ _
      (fun c hc' => hc.r1 c hc'), dotc_smul, hW]; ring
  have h3 : dotc (vv p K H u u2 y1 y2 3) π1 π2 l1 l2 p r = 0 := by
    rw [dotc_congr _ (fun c => (-3 / 2) * (vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c)) _ _ _ _ _ _
      (fun c hc' => hc.r3 c hc'), dotc_smul, hW]; ring
  refine ⟨h1, ?_, h3⟩
  rw [dotc_sub] at hW
  linear_combination hW + h1

/-- Block vector with a sign on the antisymmetric coordinates. -/
def blkv {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (sgn : ZMod p) (k : Fin K) (c : ℕ) : ZMod p :=
  match c with
  | 0 => u k
  | 1 => u2 k
  | 2 => sgn * y1 k
  | 3 => sgn * y2 k
  | _ => 0

theorem piSeq_lin {D : ℕ} (a b : ZMod p) (τ1 τ2 : Fin D → ZMod p) (e : ℕ) :
    piSeq P N p (fun d => a * τ1 d + b * τ2 d) e =
      a * piSeq P N p τ1 e + b * piSeq P N p τ2 e := by
  unfold piSeq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem laSeq_lin {D : ℕ} (a b : ZMod p) (τ1 τ2 : Fin D → ZMod p) (e : ℕ) :
    laSeq P N p (fun d => a * τ1 d + b * τ2 d) e =
      a * laSeq P N p τ1 e + b * laSeq P N p τ2 e := by
  unfold laSeq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- The top-block combination `dotc topv` is the `hi`-part of a block (Lemma X). -/
theorem dotc_topv {K hp : ℕ} (u u2 y1 y2 : Fin K → ZMod p) (τ1 τ2 : Fin (hp + 1) → ZMod p)
    (σ1 σ2 : Fin hp → ZMod p) (k : Fin K) (r : ℕ) (sgn : ZMod p) :
    dotc (blkv u u2 y1 y2 sgn k)
      (piSeq P N p τ1) (piSeq P N p τ2) (laSeq P N p (Aext σ1)) (laSeq P N p (Aext σ2)) p r =
    piSeq P N p (fun d => u k * τ1 d + u2 k * τ2 d) (r + p) +
      laSeq P N p (fun d => sgn * (y1 k * Aext σ1 d + y2 k * Aext σ2 d)) r := by
  rw [dotc_expand]
  have e1 : (fun d => sgn * (y1 k * Aext σ1 d + y2 k * Aext σ2 d)) =
      fun d => (sgn * y1 k) * Aext σ1 d + (sgn * y2 k) * Aext σ2 d := by
    funext d; ring
  rw [e1, piSeq_lin, laSeq_lin]
  simp [blkv]
  ring

/-- **Digit `s` implied** (P* plus Lemma X): if the main functional and the two block-`Q`
functionals vanish at `r`, so does `v_4 . seq[r]`. -/
theorem dot_J4_implied {K H : ℕ} {u u2 y1 y2 : Fin K → ZMod p} {μ2 μ3 ν ρ : ZMod p}
    {ktop k0 : Fin K} (hc : CellHyp p K H u u2 y1 y2 μ2 μ3 ν ρ ktop k0)
    (π1 π2 l1 l2 : ℕ → ZMod p) (r : ℕ)
    (hW : dotc (fun c => vv p K H u u2 y1 y2 2 c - vv p K H u u2 y1 y2 1 c) π1 π2 l1 l2 p r = 0)
    (hT : dotc (topv u u2 y1 y2 ktop) π1 π2 l1 l2 p r = 0)
    (hZ : dotc (zerov u u2 y1 y2 k0) π1 π2 l1 l2 p r = 0) :
    dotc (vv p K H u u2 y1 y2 4) π1 π2 l1 l2 p r = 0 := by
  obtain ⟨h1, h2, h3⟩ := dot_J123 hc π1 π2 l1 l2 r hW
  have p0 := hc.ps 0 (by norm_num)
  have p1 := hc.ps 1 (by norm_num)
  have p2 := hc.ps 2 (by norm_num)
  have p3 := hc.ps 3 (by norm_num)
  simp only [dotc_expand, topv, zerov] at *
  linear_combination p0 * π1 (r + p) + p1 * π2 (r + p) + p2 * l1 r + p3 * l2 r + h1 +
    μ2 * hW + μ3 * (h3 - h1) + ν * hT + ρ * hZ

/-- Top block: `Q_top[i] = 0` for `i ≥ h + rt`. -/
theorem Qtop_zero (hp2 : p ≠ 2) {K hp : ℕ} (hhp : P.h N + hp < p) (u u2 y1 y2 : Fin K → ZMod p)
    (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (ktop : Fin K) (rt : ℕ)
    (hvirt : ∀ d : Fin (hp + 1), rt < (d : ℕ) →
      (u ktop * τ1 d + u2 ktop * τ2 d) + (y1 ktop * Aext σ1 d + y2 ktop * Aext σ2 d) = 0)
    (i : ℕ) (hi : P.h N + rt ≤ i) :
    dotc (topv u u2 y1 y2 ktop) (piSeq P N p τ1) (piSeq P N p τ2) (laSeq P N p (Aext σ1))
      (laSeq P N p (Aext σ2)) p i = 0 := by
  have e : topv u u2 y1 y2 ktop = blkv u u2 y1 y2 1 ktop := by
    funext c; rcases c with _ | _ | _ | _ | c <;> simp [topv, blkv]
  rw [e, dotc_topv]
  have := blockX (P := P) (N := N) hp2 hhp (fun d => u ktop * τ1 d + u2 ktop * τ2 d)
    (fun d => (1 : ZMod p) * (y1 ktop * Aext σ1 d + y2 ktop * Aext σ2 d)) rt
    (fun d hd => by simpa using hvirt d hd) i hi
  rw [piSeq_eq, laSeq_eq]
  exact this

/-- Block `0`: `Q_0[i] = 0` for `i ≥ h + g`. -/
theorem Qzero_zero (hp2 : p ≠ 2) {K hp : ℕ} (hhp : P.h N + hp < p) (u u2 y1 y2 : Fin K → ZMod p)
    (τ1 τ2 : Fin (hp + 1) → ZMod p) (σ1 σ2 : Fin hp → ZMod p) (k0 : Fin K) (g : ℕ)
    (hvirt : ∀ d : Fin (hp + 1), g < (d : ℕ) →
      (u k0 * τ1 d + u2 k0 * τ2 d) - (y1 k0 * Aext σ1 d + y2 k0 * Aext σ2 d) = 0)
    (i : ℕ) (hi : P.h N + g ≤ i) :
    dotc (zerov u u2 y1 y2 k0) (piSeq P N p τ1) (piSeq P N p τ2) (laSeq P N p (Aext σ1))
      (laSeq P N p (Aext σ2)) p i = 0 := by
  have e : zerov u u2 y1 y2 k0 = blkv u u2 y1 y2 (-1) k0 := by
    funext c; rcases c with _ | _ | _ | _ | c <;> simp [zerov, blkv]
  rw [e, dotc_topv]
  have := blockX (P := P) (N := N) hp2 hhp (fun d => u k0 * τ1 d + u2 k0 * τ2 d)
    (fun d => (-1 : ZMod p) * (y1 k0 * Aext σ1 d + y2 k0 * Aext σ2 d)) g
    (fun d hd => by have := hvirt d hd; linear_combination this) i hi
  rw [piSeq_eq, laSeq_eq]
  exact this

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
