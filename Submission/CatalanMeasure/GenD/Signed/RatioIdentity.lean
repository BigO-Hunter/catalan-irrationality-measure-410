module

public import Submission.CatalanMeasure.HeineAndreief
public import Submission.CatalanMeasure.GenD.Signed.BernsteinSzego
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# The ratio identity without `SO(d)` (route II)

Algebraic layer: concatenated Vandermonde determinants and pair-product identities.
-/

open Polynomial Finset MeasureTheory

namespace CatalanMeasure.GenD.Signed

section Algebra

/-- `Δ(v) = det (vandermonde v)`. -/
theorem prod_Ioi_eq_ite {k : ℕ} {M : Type*} [CommMonoid M] (i : Fin k) (f : Fin k → M) :
    ∏ j ∈ Ioi i, f j = ∏ j, if i < j then f j else 1 := by
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

theorem det_vandermonde_append {s k : ℕ} (τ : Fin s → ℝ) (t : Fin k → ℝ) :
    (Matrix.vandermonde (Fin.append τ t)).det =
      (Matrix.vandermonde τ).det * (Matrix.vandermonde t).det * ∏ l, ∏ b, (t b - τ l) := by
  have hcc : ∀ a a' : Fin s, (Fin.castAdd k a < Fin.castAdd k a') ↔ a < a' := by
    intro a a'; simp only [Fin.lt_def, Fin.val_castAdd]
  have hcn : ∀ (a : Fin s) (b : Fin k), Fin.castAdd k a < Fin.natAdd s b := by
    intro a b; simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; have := a.2; omega
  have hnc : ∀ (b : Fin k) (a : Fin s), ¬ (Fin.natAdd s b < Fin.castAdd k a) := by
    intro b a; simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; have := a.2; omega
  have hnn : ∀ b b' : Fin k, (Fin.natAdd s b < Fin.natAdd s b') ↔ b < b' := by
    intro b b'; simp only [Fin.lt_def, Fin.val_natAdd]; omega
  simp only [Matrix.det_vandermonde, prod_Ioi_eq_ite]
  rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, hcc, hcn, hnc, hnn, ite_true,
    ite_false, Finset.prod_const_one]
  rw [Finset.prod_mul_distrib]
  ring_nf

/-- Pair products over `i < j`. -/
theorem prod_pairs_mul {k : ℕ} (f : Fin k → ℝ) :
    ∏ i, ∏ j ∈ Ioi i, (f i * f j) = ∏ i, f i ^ (k - 1) := by
  have h1 : ∏ i, ∏ j ∈ Ioi i, (f i * f j) =
      (∏ i, f i ^ (k - 1 - (i : ℕ))) * ∏ i, ∏ j ∈ Ioi i, f j := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Ioi]
  have h2 : ∏ i, ∏ j ∈ Ioi i, f j = ∏ j, f j ^ (j : ℕ) := by
    rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun j => Finset.Iio j)]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [Finset.prod_const, Fin.card_Iio]
    · intro x y; simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  congr 1
  have := i.2
  omega

theorem prod_pairs_const {k : ℕ} (c : ℝ) :
    ∏ i : Fin k, ∏ _j ∈ Ioi i, c = ∏ i : Fin k, c ^ (i : ℕ) := by
  have h : ∏ i : Fin k, ∏ _j ∈ Ioi i, c = ∏ j : Fin k, ∏ _i ∈ Iio j, c := by
    rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun j => Finset.Iio j)]
    intro x y; simp
  rw [h]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_const, Fin.card_Iio]


/-- The sign of the reversal permutation. -/
theorem sign_revPerm (k : ℕ) :
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤˣ) : ℤ) : ℝ) =
      ∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ) := by
  set v : Fin k → ℝ := fun i => (i : ℕ) with hv
  have hinj : Function.Injective v := by
    intro a b hab
    simp only [hv, Nat.cast_inj] at hab
    exact Fin.ext hab
  have hΔ : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have h1 : (Matrix.vandermonde (v ∘ Fin.revPerm)).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℝ) * (Matrix.vandermonde v).det := by
    have := Matrix.det_permute (Fin.revPerm : Equiv.Perm (Fin k)) (Matrix.vandermonde v)
    rw [← this]
    congr 1
  have h2 : (Matrix.vandermonde (v ∘ Fin.revPerm)).det =
      (∏ a : Fin k, (-1 : ℝ) ^ (k - 1 - (a : ℕ))) * (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde, Matrix.det_vandermonde]
    have e1 : ∏ i : Fin k, ∏ j ∈ Ioi i, ((v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i) =
        ∏ j : Fin k, ∏ i ∈ Iio j, ((v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i) := by
      rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun j => Finset.Iio j)]
      intro x y; simp
    rw [e1]
    have e2 : ∏ j : Fin k, ∏ i ∈ Iio j, ((v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i) =
        ∏ a : Fin k, ∏ i ∈ Iio (Fin.revPerm a),
          ((v ∘ Fin.revPerm) (Fin.revPerm a) - (v ∘ Fin.revPerm) i) :=
      (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin k))
        (fun j => ∏ i ∈ Iio j, ((v ∘ Fin.revPerm) j - (v ∘ Fin.revPerm) i))).symm
    rw [e2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hmap : Finset.Iio (Fin.revPerm a) = (Finset.Ioi a).map Fin.revPerm.toEmbedding := by
      rw [Fin.map_revPerm_Ioi]; rfl
    rw [hmap, Finset.prod_map]
    have : ∀ c ∈ Finset.Ioi a,
        ((v ∘ Fin.revPerm) (Fin.revPerm a) - (v ∘ Fin.revPerm) (Fin.revPerm.toEmbedding c)) =
          (-1 : ℝ) * (v c - v a) := by
      intro c _
      simp only [Function.comp_apply, Equiv.coe_toEmbedding, Fin.revPerm_apply, Fin.rev_rev]
      ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Ioi]
  have h3 : ∏ a : Fin k, (-1 : ℝ) ^ (k - 1 - (a : ℕ)) = ∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ) := by
    rw [← Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin k))
      (fun j : Fin k => (-1 : ℝ) ^ (j : ℕ))]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [h1] at h2
  have := mul_right_cancel₀ hΔ h2
  rw [this, h3]

end Algebra

section Core

variable (μ : Measure ℝ) (W : ℝ → ℝ)

/-- The Hankel moment matrix of the weight `W μ`. -/
noncomputable def hankelMat (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun r i => ∫ τ, τ ^ (r : ℕ) * (τ ^ (i : ℕ) * W τ) ∂μ

/-- `∫ Δ(τ)² ∏ W(τ_l) ∏_{l,b} (t_b - τ_l) dμ^s`. -/
noncomputable def nodeIntegral (s : ℕ) {k : ℕ} (t : Fin k → ℝ) : ℝ :=
  ∫ τ, (Matrix.vandermonde τ).det ^ 2 * (∏ l, W (τ l)) * (∏ l, ∏ b, (t b - τ l))
    ∂(Measure.pi fun _ : Fin s => μ)

variable {μ W}

theorem det_heineMatrix_block {s k : ℕ} (Q : Fin (s + k) → ℝ[X])
    (hQx : ∀ r : Fin s, Q (Fin.castAdd k r) = X ^ (r : ℕ))
    (horth : ∀ (j : Fin k) (i : Fin s),
      ∫ τ, (Q (Fin.natAdd s j)).eval τ * (τ ^ (i : ℕ) * W τ) ∂μ = 0)
    (t : Fin k → ℝ) :
    (heineMatrix μ (fun r y => (Q r).eval y) t (fun (i : Fin s) y => y ^ (i : ℕ) * W y)).det =
      (hankelMat μ W s).det *
        (Matrix.of fun j' j : Fin k => (Q (Fin.natAdd s j')).eval (t j)).det := by
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin s ⊕ Fin k ≃ Fin (s + k))]
  have : (heineMatrix μ (fun r y => (Q r).eval y) t
      (fun (i : Fin s) y => y ^ (i : ℕ) * W y)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (hankelMat μ W s)
        (Matrix.of fun (r : Fin s) (j : Fin k) => (Q (Fin.castAdd k r)).eval (t j)) 0
        (Matrix.of fun j' j : Fin k => (Q (Fin.natAdd s j')).eval (t j)) := by
    ext x y
    rcases x with r | r <;> rcases y with i | j
    · simp [heineMatrix, hankelMat, hQx]
    · simp [heineMatrix]
    · simp [heineMatrix, horth]
    · simp [heineMatrix]
  rw [this, Matrix.det_fromBlocks_zero₂₁]

/-- Heine's identity with fixed nodes, in cross-multiplied form. -/
theorem heine_core [IsFiniteMeasure μ] {s k : ℕ} (Q : Fin (s + k) → ℝ[X])
    (hQdeg : ∀ r, (Q r).natDegree = r) (hQmon : ∀ r, (Q r).Monic)
    (hQx : ∀ r : Fin s, Q (Fin.castAdd k r) = X ^ (r : ℕ))
    (hint : ∀ (p : ℝ[X]) (i : ℕ), Integrable (fun τ => p.eval τ * (τ ^ i * W τ)) μ)
    (horth : ∀ (j : Fin k) (i : Fin s),
      ∫ τ, (Q (Fin.natAdd s j)).eval τ * (τ ^ (i : ℕ) * W τ) ∂μ = 0)
    (t : Fin k → ℝ) :
    (Matrix.vandermonde t).det * nodeIntegral μ W s t =
      (s.factorial : ℝ) * (hankelMat μ W s).det *
        (Matrix.of fun j' j : Fin k => (Q (Fin.natAdd s j')).eval (t j)).det := by
  have hA := integral_rowDet_mul_det (μ := μ) (F := fun r y => (Q r).eval y) t
    (G := fun (i : Fin s) y => y ^ (i : ℕ) * W y) (fun r i => hint (Q r) i)
  rw [det_heineMatrix_block Q hQx horth t] at hA
  have hpt : ∀ τ : Fin s → ℝ,
      rowDet (fun r y => (Q r).eval y) t τ *
          (Matrix.of fun j i : Fin s => τ j ^ (i : ℕ) * W (τ j)).det =
        (Matrix.vandermonde t).det *
          ((Matrix.vandermonde τ).det ^ 2 * (∏ l, W (τ l)) * ∏ l, ∏ b, (t b - τ l)) := by
    intro τ
    have h1 : rowDet (fun r y => (Q r).eval y) t τ = (Matrix.vandermonde (Fin.append τ t)).det := by
      rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (Fin.append τ t) Q hQdeg hQmon]
      rw [← Matrix.det_transpose]
      rfl
    have h2 : (Matrix.of fun j i : Fin s => τ j ^ (i : ℕ) * W (τ j)).det =
        (∏ l, W (τ l)) * (Matrix.vandermonde τ).det := by
      rw [← Matrix.det_mul_column (fun j => W (τ j)) (Matrix.vandermonde τ)]
      congr 1
      ext j i
      simp [Matrix.vandermonde_apply, mul_comm]
    rw [h1, h2, det_vandermonde_append]
    ring
  simp_rw [hpt] at hA
  rw [integral_const_mul] at hA
  unfold nodeIntegral
  rw [hA]
  ring

/-- The `k = 0` instance: `∫ Δ² ∏ W = s! det H`. -/
theorem zero_integral_eq [IsFiniteMeasure μ] {s : ℕ}
    (hint : ∀ (p : ℝ[X]) (i : ℕ), Integrable (fun τ => p.eval τ * (τ ^ i * W τ)) μ) :
    nodeIntegral μ W s (fun _ : Fin 0 => (0 : ℝ)) = (s.factorial : ℝ) * (hankelMat μ W s).det := by
  have := heine_core (μ := μ) (W := W) (s := s) (k := 0)
    (fun r => X ^ (r : ℕ)) (by intro r; simp) (by intro r; exact monic_X_pow _)
    (by intro r; simp) hint (by intro j; exact j.elim0) (fun _ : Fin 0 => (0 : ℝ))
  simpa using this.symm.symm

/-- Heine's identity with fixed nodes, divided form: `Δ(t) I(t) = I(∅) · det Q(t)`. -/
theorem heine_cross [IsFiniteMeasure μ] {s k : ℕ} (Q : Fin (s + k) → ℝ[X])
    (hQdeg : ∀ r, (Q r).natDegree = r) (hQmon : ∀ r, (Q r).Monic)
    (hQx : ∀ r : Fin s, Q (Fin.castAdd k r) = X ^ (r : ℕ))
    (hint : ∀ (p : ℝ[X]) (i : ℕ), Integrable (fun τ => p.eval τ * (τ ^ i * W τ)) μ)
    (horth : ∀ (j : Fin k) (i : Fin s),
      ∫ τ, (Q (Fin.natAdd s j)).eval τ * (τ ^ (i : ℕ) * W τ) ∂μ = 0)
    (t : Fin k → ℝ) :
    (Matrix.vandermonde t).det * nodeIntegral μ W s t =
      nodeIntegral μ W s (fun _ : Fin 0 => (0 : ℝ)) *
        (Matrix.of fun j' j : Fin k => (Q (Fin.natAdd s j')).eval (t j)).det := by
  rw [heine_core Q hQdeg hQmon hQx hint horth t, zero_integral_eq hint]

open Matrix in
/-- Positivity of the Hankel determinant of a positive weight. -/
theorem hankel_det_pos {s : ℕ}
    (hint : ∀ (p : ℝ[X]) (i : ℕ), Integrable (fun τ => p.eval τ * (τ ^ i * W τ)) μ)
    (hpos : ∀ p : ℝ[X], p ≠ 0 → 0 < ∫ τ, (p.eval τ) ^ 2 * W τ ∂μ) :
    0 < (hankelMat μ W s).det := by
  apply Matrix.PosDef.det_pos
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, hankelMat, Matrix.of_apply, star_trivial]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    ring
  · intro x hx
    set p : ℝ[X] := ∑ i : Fin s, C (x i) * X ^ (i : ℕ) with hp
    have hp0 : p ≠ 0 := by
      intro h0
      apply hx
      funext i
      have := congrArg (fun q : ℝ[X] => q.coeff (i : ℕ)) h0
      simp only [hp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
      simpa [Fin.val_inj] using this
    have hI : ∀ r i : Fin s,
        Integrable (fun τ => x r * x i * (τ ^ (r : ℕ) * (τ ^ (i : ℕ) * W τ))) μ := by
      intro r i
      have := (hint (X ^ (r : ℕ)) i).const_mul (x r * x i)
      simpa using this
    have hI' : ∀ r i : Fin s, Integrable (fun τ => τ ^ (r : ℕ) * (τ ^ (i : ℕ) * W τ)) μ := by
      intro r i
      simpa using hint (X ^ (r : ℕ)) i
    have hq : star x ⬝ᵥ (hankelMat μ W s *ᵥ x) = ∫ τ, (p.eval τ) ^ 2 * W τ ∂μ := by
      have e1 : ∀ τ : ℝ, (p.eval τ) ^ 2 * W τ =
          ∑ r : Fin s, ∑ i : Fin s, x r * x i * (τ ^ (r : ℕ) * (τ ^ (i : ℕ) * W τ)) := by
        intro τ
        simp only [hp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      simp_rw [e1]
      rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun i _ => hI r i))]
      simp only [dotProduct, mulVec, hankelMat, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_finsetSum _ (fun i _ => hI r i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
      ring
    rw [hq]
    exact hpos p hp0

end Core

section Application

open Real

/-- The pushforward of Lebesgue measure on `(0, π]` under `cos`. -/
noncomputable def cosMeasure : Measure ℝ := Measure.map Real.cos (volume.restrict (Set.Ioc 0 π))

instance : IsFiniteMeasure cosMeasure := by
  unfold cosMeasure
  infer_instance

/-- The Heine form `Z(f) = ∫_{(0,π]^s} Δ(cos θ)² ∏ f(cos θ_l) dθ`. -/
noncomputable def heineZ (s : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ θ : Fin s → ℝ, (Matrix.vandermonde fun l => Real.cos (θ l)).det ^ 2 *
      ∏ l, f (Real.cos (θ l)) ∂(Measure.pi fun _ : Fin s => volume.restrict (Set.Ioc 0 π))

theorem integral_cosMeasure {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ τ, g τ ∂cosMeasure = ∫ θ in Set.Ioc 0 π, g (Real.cos θ) :=
  integral_map Real.continuous_cos.aemeasurable hg.aestronglyMeasurable

theorem measurable_det_vandermonde (s : ℕ) :
    Measurable fun τ : Fin s → ℝ => (Matrix.vandermonde τ).det := by
  simp_rw [Matrix.det_vandermonde]
  exact Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ =>
    (measurable_pi_apply j).sub (measurable_pi_apply i)

theorem heineZ_eq (s : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    heineZ s f = ∫ τ, (Matrix.vandermonde τ).det ^ 2 * ∏ l, f (τ l)
      ∂(Measure.pi fun _ : Fin s => cosMeasure) := by
  have hmp : MeasurePreserving (fun (θ : Fin s → ℝ) l => Real.cos (θ l))
      (Measure.pi fun _ : Fin s => volume.restrict (Set.Ioc 0 π))
      (Measure.pi fun _ : Fin s => cosMeasure) :=
    measurePreserving_pi _ _ (fun _ => Real.measurable_cos.measurePreserving _)
  have hg : Measurable fun τ : Fin s → ℝ => (Matrix.vandermonde τ).det ^ 2 * ∏ l, f (τ l) :=
    ((measurable_det_vandermonde s).pow_const 2).mul
      (Finset.measurable_prod _ fun l _ => hf.comp (measurable_pi_apply l))
  unfold heineZ
  rw [← hmp.map_eq, integral_map hmp.aemeasurable hg.aestronglyMeasurable]

theorem hAbs2_pos (h : ℝ[X]) (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) (θ : ℝ) :
    0 < hAbs2 h θ := by
  unfold hAbs2
  have := hnz (Complex.exp (θ * Complex.I)) (le_of_eq (Complex.norm_exp_ofReal_mul_I θ))
  exact pow_pos (norm_pos_iff.mpr this) 2

variable {h : ℝ[X]} (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) {ρ : ℝ[X]}
  (hρ : ∀ θ : ℝ, ρ.eval (Real.cos θ) = hAbs2 h θ)

include hnz hρ in
theorem rho_pos (θ : ℝ) : 0 < ρ.eval (Real.cos θ) := by
  rw [hρ]; exact hAbs2_pos h hnz θ

include hnz hρ in
theorem integrable_cos_weight (p : ℝ[X]) (i : ℕ) :
    Integrable (fun τ => p.eval τ * (τ ^ i * (ρ.eval τ)⁻¹)) cosMeasure := by
  have hm : Measurable (fun τ : ℝ => p.eval τ * (τ ^ i * (ρ.eval τ)⁻¹)) :=
    (p.continuous.measurable).mul ((measurable_id.pow_const i).mul (ρ.continuous.measurable.inv))
  unfold cosMeasure
  rw [integrable_map_measure hm.aestronglyMeasurable Real.continuous_cos.aemeasurable]
  have hc : Continuous fun θ : ℝ => (p.eval (Real.cos θ)) *
      (Real.cos θ ^ i * (ρ.eval (Real.cos θ))⁻¹) := by
    refine (p.continuous.comp Real.continuous_cos).mul ((Real.continuous_cos.pow i).mul ?_)
    exact Continuous.inv₀ (ρ.continuous.comp Real.continuous_cos)
      (fun θ => (rho_pos hnz hρ θ).ne')
  exact hc.integrableOn_Ioc

include hnz hρ in
theorem orth_cos (n i : ℕ) (hin : i < n) :
    ∫ τ, (bsPoly h n).eval τ * (τ ^ i * (ρ.eval τ)⁻¹) ∂cosMeasure = 0 := by
  have hm : Measurable (fun τ : ℝ => (bsPoly h n).eval τ * (τ ^ i * (ρ.eval τ)⁻¹)) :=
    ((bsPoly h n).continuous.measurable).mul
      ((measurable_id.pow_const i).mul (ρ.continuous.measurable.inv))
  rw [integral_cosMeasure hm, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  refine Eq.trans ?_ (bsPoly_orthogonal h hnz n i hin)
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hρ θ]
  ring

include hnz hρ in
theorem pos_cos (p : ℝ[X]) (hp : p ≠ 0) :
    0 < ∫ τ, (p.eval τ) ^ 2 * (ρ.eval τ)⁻¹ ∂cosMeasure := by
  have hm : Measurable (fun τ : ℝ => (p.eval τ) ^ 2 * (ρ.eval τ)⁻¹) :=
    ((p.continuous.measurable).pow_const 2).mul (ρ.continuous.measurable.inv)
  rw [integral_cosMeasure hm]
  set f : ℝ → ℝ := fun θ => (p.eval (Real.cos θ)) ^ 2 * (ρ.eval (Real.cos θ))⁻¹ with hf
  have hc : Continuous f := by
    refine ((p.continuous.comp Real.continuous_cos).pow 2).mul ?_
    exact Continuous.inv₀ (ρ.continuous.comp Real.continuous_cos)
      (fun θ => (rho_pos hnz hρ θ).ne')
  have hnn : 0 ≤ f := fun θ => mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (rho_pos hnz hρ θ).le)
  -- a point where `f` is positive
  have hex : ∃ θ0 ∈ Set.Ioo 0 π, p.eval (Real.cos θ0) ≠ 0 := by
    by_contra H0
    have H : ∀ θ ∈ Set.Ioo 0 π, p.eval (Real.cos θ) = 0 := fun θ hθ => by
      by_contra hne
      exact H0 ⟨θ, hθ, hne⟩
    apply hp
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : (Real.cos '' Set.Ioo 0 π).Infinite :=
      (Set.Ioo_infinite Real.pi_pos).image
        (Real.injOn_cos.mono Set.Ioo_subset_Icc_self)
    refine hinf.mono ?_
    rintro _ ⟨θ, hθ, rfl⟩
    exact H θ hθ
  obtain ⟨θ0, hθ0, hne⟩ := hex
  have hfi : Integrable f (volume.restrict (Set.Ioc 0 π)) := hc.integrableOn_Ioc
  rw [integral_pos_iff_support_of_nonneg hnn hfi]
  have hopen : IsOpen (Function.support f) := hc.isOpen_support
  rw [Measure.restrict_apply hopen.measurableSet]
  have hU : IsOpen (Function.support f ∩ Set.Ioo 0 π) := hopen.inter isOpen_Ioo
  have hne' : (Function.support f ∩ Set.Ioo 0 π).Nonempty := by
    refine ⟨θ0, ⟨?_, hθ0⟩⟩
    simp only [Function.mem_support, hf]
    exact mul_ne_zero (pow_ne_zero 2 hne) (inv_ne_zero (rho_pos hnz hρ θ0).ne')
  exact lt_of_lt_of_le (hU.measure_pos volume hne')
    (measure_mono (Set.inter_subset_inter_right _ Set.Ioo_subset_Ioc_self))

end Application

section Nodes

/-- The node `t_b = -(x_b + 1/x_b)/2`. -/
noncomputable def tNode (y : ℝ) : ℝ := -(y + y⁻¹) / 2

/-- The Blaschke factor `B_G(y) = y^q h(-1/y) / h(-y)` of the multiset `G` with `h = ∏ (1 + g X)`. -/
noncomputable def blaschkeG (h : ℝ[X]) (q : ℕ) (y : ℝ) : ℝ :=
  y ^ q * h.eval (-y⁻¹) / h.eval (-y)

/-- The `k × k` matrix `[x_b^j + B_G(x_b) x_b^{m-j}]`. -/
noncomputable def dMat (h : ℝ[X]) (q m : ℕ) {k : ℕ} (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun b j => x b ^ (j : ℕ) + blaschkeG h q (x b) * x b ^ (m - (j : ℕ))

/-- **R5.** The value of the Bernstein–Szegő polynomial at the node. -/
theorem bsPoly_at_node (h : ℝ[X]) (q m s k : ℕ) (hm : m + q + 2 = 2 * s + 2 * k)
    (hs : q < 2 * s)
    (y : ℝ) (hy : y ≠ 0) (hh : h.eval (-y) ≠ 0) (j : ℕ) (hj : j < k) :
    2 * y ^ (s + k - 1) * (bsPoly h (s + j)).eval (tNode y) =
      (-1) ^ (s + j) * h.eval (-y) *
        (y ^ (k - 1 - j) + blaschkeG h q y * y ^ (m - (k - 1 - j))) := by
  have ht : tNode y = ((-y) + (-y)⁻¹) / 2 := by unfold tNode; rw [inv_neg]; ring
  rw [ht, bsPoly_eval_laurent h (s + j) (-y) (neg_ne_zero.mpr hy)]
  unfold blaschkeG
  set n := s + j with hn
  set e := k - 1 - j with he
  have h1 : s + k - 1 = n + e := by omega
  have h2 : m - e + q = 2 * n + e := by omega
  have hqm : y ^ (m - e) = y ^ (2 * n + e) / y ^ q := by
    rw [eq_div_iff (pow_ne_zero _ hy), ← pow_add, h2]
  rw [h1, neg_pow, inv_neg, mul_inv, hqm, pow_add y n e]
  have hsq : ((-1 : ℝ) ^ n)⁻¹ = (-1) ^ n := by
    rw [← inv_pow, inv_neg_one]
  rw [hsq]
  have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
  have hyq : y ^ q ≠ 0 := pow_ne_zero _ hy
  have hye : y ^ e ≠ 0 := pow_ne_zero _ hy
  field_simp
  ring

/-- **R6 (rows).** The determinant of the node matrix of the Bernstein–Szegő polynomials. -/
theorem det_bsPoly_nodes (h : ℝ[X]) (q m s k : ℕ) (hm : m + q + 2 = 2 * s + 2 * k)
    (hs : q < 2 * s) (x : Fin k → ℝ) (hx : ∀ b, x b ≠ 0) (hh : ∀ b, h.eval (-x b) ≠ 0) :
    (Matrix.of fun b j : Fin k => (bsPoly h (s + j)).eval (tNode (x b))).det =
      (∏ b, h.eval (-x b) / (2 * x b ^ (s + k - 1))) * (-1) ^ (s * k) * (dMat h q m x).det := by
  set M : Matrix (Fin k) (Fin k) ℝ := (dMat h q m x).submatrix id Fin.revPerm with hM
  set c : Fin k → ℝ := fun b => h.eval (-x b) / (2 * x b ^ (s + k - 1)) with hc
  set σ : Fin k → ℝ := fun j => (-1 : ℝ) ^ (s + (j : ℕ)) with hσ
  have hentry : (Matrix.of fun b j : Fin k => (bsPoly h (s + j)).eval (tNode (x b))) =
      Matrix.of fun b j : Fin k => c b * (σ j * M b j) := by
    ext b j
    have := bsPoly_at_node h q m s k hm hs (x b) (hx b) (hh b) j j.2
    have hrev : ((Fin.revPerm j : Fin k) : ℕ) = k - 1 - (j : ℕ) := by
      simp only [Fin.revPerm_apply, Fin.val_rev]; omega
    have hpos : (2 * x b ^ (s + k - 1)) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ (hx b))
    simp only [Matrix.of_apply, hM, Matrix.submatrix_apply, id, dMat, hrev, hc, hσ]
    have hxk : x b ^ (s + k - 1) ≠ 0 := pow_ne_zero _ (hx b)
    apply mul_left_cancel₀ hpos
    rw [this]
    field_simp
  have e2 : (Matrix.of fun i j => σ j * M i j).det = (∏ j, σ j) * M.det :=
    Matrix.det_mul_row σ M
  have e1 : (Matrix.of fun i j => c i * (Matrix.of fun i j => σ j * M i j) i j).det =
      (∏ i, c i) * (Matrix.of fun i j => σ j * M i j).det :=
    Matrix.det_mul_column c _
  have e3 : M.det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℝ) *
      (dMat h q m x).det := Matrix.det_permute' _ _
  rw [hentry]
  have e4 : (Matrix.of fun b j : Fin k => c b * (σ j * M b j)) =
      Matrix.of fun i j => c i * (Matrix.of fun i j => σ j * M i j) i j := rfl
  rw [e4, e1, e2, e3, sign_revPerm]
  have h1 : ∏ j : Fin k, σ j = ((-1 : ℝ) ^ s) ^ k * ∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ) := by
    simp_rw [hσ, pow_add]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ)) * ∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← mul_pow]; simp
  rw [h1, ← pow_mul]
  calc _ = (∏ b, c b) * (-1) ^ (s * k) *
      ((∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ)) * ∏ j : Fin k, (-1 : ℝ) ^ (j : ℕ)) * (dMat h q m x).det := by ring
    _ = _ := by rw [h2]; ring

/-- **R6 (columns).** `Δ(t) · 2^{C(k,2)} ∏ x_b^{k-1} = V(x) ∏_{i<j} (1 - x_i x_j)`. -/
theorem det_vandermonde_tNode {k : ℕ} (x : Fin k → ℝ) (hx : ∀ b, x b ≠ 0) :
    (Matrix.vandermonde fun b => tNode (x b)).det *
        ((∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1)) =
      (Matrix.vandermonde x).det * ∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j) := by
  have hB : (∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1) =
      ∏ i : Fin k, ∏ j ∈ Ioi i, (2 * (x i * x j)) := by
    have : ∀ i : Fin k, ∏ j ∈ Ioi i, (2 * (x i * x j)) =
        (∏ _j ∈ Ioi i, (2 : ℝ)) * ∏ j ∈ Ioi i, (x i * x j) := fun i => Finset.prod_mul_distrib
    simp_rw [this]
    rw [Finset.prod_mul_distrib, prod_pairs_const, prod_pairs_mul, Finset.prod_pow]
  rw [hB, Matrix.det_vandermonde, Matrix.det_vandermonde, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hi := hx i
  have hj := hx j
  unfold tNode
  field_simp
  ring

end Nodes

section Family

/-- The monic family: `X^r` for `r < s`, then the normalised Bernstein–Szegő polynomials. -/
noncomputable def qFam (h : ℝ[X]) (s k : ℕ) : Fin (s + k) → ℝ[X] :=
  Fin.addCases (fun r : Fin s => (X : ℝ[X]) ^ (r : ℕ))
    (fun j : Fin k => C (((2 : ℝ) ^ (s + (j : ℕ) - 1))⁻¹) * bsPoly h (s + (j : ℕ)))

theorem qFam_left (h : ℝ[X]) (s k : ℕ) (r : Fin s) :
    qFam h s k (Fin.castAdd k r) = X ^ (r : ℕ) := by
  simp [qFam]

theorem qFam_right (h : ℝ[X]) (s k : ℕ) (j : Fin k) :
    qFam h s k (Fin.natAdd s j) =
      C (((2 : ℝ) ^ (s + (j : ℕ) - 1))⁻¹) * bsPoly h (s + (j : ℕ)) := by
  simp [qFam]

theorem qFam_natDegree_monic (h : ℝ[X]) (q s k : ℕ) (h0 : h.coeff 0 = 1)
    (hdeg : h.natDegree ≤ q) (hs : q < 2 * s) (r : Fin (s + k)) :
    (qFam h s k r).natDegree = r ∧ (qFam h s k r).Monic := by
  refine Fin.addCases (fun r => ?_) (fun j => ?_) r
  · rw [qFam_left]
    simp only [Fin.val_castAdd, natDegree_pow, natDegree_X, mul_one]
    exact ⟨trivial, monic_X_pow _⟩
  · rw [qFam_right]
    have hn : 0 < s + (j : ℕ) := by omega
    obtain ⟨hd, hl⟩ := bsPoly_natDegree_and_lc h h0 (s + j) hn (by omega)
    have hc : ((2 : ℝ) ^ (s + (j : ℕ) - 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ two_ne_zero)
    refine ⟨?_, ?_⟩
    · rw [natDegree_C_mul hc, hd]; simp
    · unfold Monic
      rw [leadingCoeff_mul, leadingCoeff_C, hl]
      exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)

end Family

section Final

theorem key_identity (h : ℝ[X]) (k s : ℕ) (hk : 0 < k) (hs : 0 < s) (x : Fin k → ℝ)
    (hx : ∀ b, x b ≠ 0) (hh : ∀ b, h.eval (-x b) ≠ 0) :
    (∏ b, (h.eval (-x b))⁻¹) * (∏ b, (-2 * x b)) ^ s * (∏ j : Fin k, ((2 : ℝ) ^ (s + (j : ℕ) - 1))⁻¹) *
      (∏ b, h.eval (-x b) / (2 * x b ^ (s + k - 1))) * (-1) ^ (s * k) *
      ((∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1)) = 1 := by
  have hH : ∏ b, h.eval (-x b) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hh b
  have hP : ∏ b, x b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hx b
  have e1 : ∏ b, (h.eval (-x b))⁻¹ = (∏ b, h.eval (-x b))⁻¹ := Finset.prod_inv_distrib _
  have e2 : ∏ b, (-2 * x b) = (-2) ^ k * ∏ b, x b := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e3 : ∏ b, h.eval (-x b) / (2 * x b ^ (s + k - 1)) =
      (∏ b, h.eval (-x b)) / (2 ^ k * (∏ b, x b) ^ (s + k - 1)) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have e4 : ∏ j : Fin k, ((2 : ℝ) ^ (s' + 1 + (j : ℕ) - 1))⁻¹ =
      (((2 : ℝ) ^ s') ^ k * ∏ j : Fin k, (2 : ℝ) ^ (j : ℕ))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    have : ∀ j : Fin k, (2 : ℝ) ^ (s' + 1 + (j : ℕ) - 1) = 2 ^ s' * 2 ^ (j : ℕ) := by
      intro j; rw [← pow_add]; congr 1; omega
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e1, e2, e3, e4]
  have hT : (∏ j : Fin k, (2 : ℝ) ^ (j : ℕ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ two_ne_zero
  have hPk : (∏ b, x b) ^ (s' + 1 + k - 1) = (∏ b, x b) ^ (s' + 1) * (∏ b, x b) ^ (k - 1) := by
    rw [← pow_add]; congr 1; omega
  have hA : ((2 : ℝ) ^ s') ^ k * 2 ^ k = 2 ^ ((s' + 1) * k) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have hB : ((-2 : ℝ) ^ k) ^ (s' + 1) * (-1) ^ ((s' + 1) * k) = 2 ^ ((s' + 1) * k) := by
    rw [← pow_mul, mul_comm k, ← mul_pow]; norm_num
  rw [hPk, mul_pow]
  have h2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have h3 : ((2 : ℝ) ^ s') ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  have h4 : (∏ b, x b) ^ (s' + 1) ≠ 0 := pow_ne_zero _ hP
  have h5 : (∏ b, x b) ^ (k - 1) ≠ 0 := pow_ne_zero _ hP
  field_simp
  exact hB.trans hA.symm

theorem eval_ne_zero_of_abs_lt_one (h : ℝ[X]) (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) (y : ℝ)
    (hy : |y| < 1) : h.eval y ≠ 0 := by
  have := hnz (y : ℂ) (by simpa using hy.le)
  intro h0
  apply this
  have : aeval (y : ℂ) h = ((h.eval y : ℝ) : ℂ) := by
    rw [← Complex.coe_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rw [this, h0]; simp

/-- **The ratio identity (route II instance of Theorem R).** -/
theorem ratio_identity (h : ℝ[X]) (q s k m : ℕ) (hk : 0 < k) (hm : m + q + 2 = 2 * s + 2 * k)
    (hs : q < 2 * s) (h0 : h.coeff 0 = 1) (hdeg : h.natDegree ≤ q)
    (hnz : ∀ z : ℂ, ‖z‖ ≤ 1 → aeval z h ≠ 0) (ρ : ℝ[X])
    (hρ : ∀ θ : ℝ, ρ.eval (Real.cos θ) = hAbs2 h θ)
    (x : Fin k → ℝ) (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1) :
    (dMat h q m x).det / (Matrix.vandermonde x).det =
      (∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j)) * (∏ b, (h.eval (-x b))⁻¹) *
        (heineZ s (fun τ => (∏ b, (1 + 2 * x b * τ + x b ^ 2)) / ρ.eval τ) /
          heineZ s (fun τ => 1 / ρ.eval τ)) := by
  have hh : ∀ b, h.eval (-x b) ≠ 0 := fun b =>
    eval_ne_zero_of_abs_lt_one h hnz _ (by simpa using hx1 b)
  set t : Fin k → ℝ := fun b => tNode (x b) with ht
  set wt : ℝ → ℝ := fun τ => (ρ.eval τ)⁻¹ with hwt
  set c : ℝ := ∏ b, (-2 * x b) with hc
  have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hW2 : ∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have h1 := hx1 i
    have h2 := hx1 j
    rw [abs_lt] at h1 h2
    intro hz
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hρm : Measurable fun τ : ℝ => ρ.eval τ := ρ.continuous.measurable
  have hφm : Measurable fun τ : ℝ => ∏ b, (1 + 2 * x b * τ + x b ^ 2) :=
    Finset.measurable_prod _ fun b _ => by fun_prop
  -- (a) the numerator Heine integral
  have hZφ : heineZ s (fun τ => (∏ b, (1 + 2 * x b * τ + x b ^ 2)) / ρ.eval τ) =
      c ^ s * nodeIntegral cosMeasure wt s t := by
    have hmeas : Measurable fun τ : ℝ => (∏ b, (1 + 2 * x b * τ + x b ^ 2)) / ρ.eval τ :=
      hφm.div hρm
    rw [heineZ_eq s _ hmeas]
    unfold nodeIntegral
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    have hφ : ∀ y : ℝ, ∏ b, (1 + 2 * x b * y + x b ^ 2) = c * ∏ b, (t b - y) := by
      intro y
      rw [hc, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      have := hx0 b
      simp only [ht, tNode]
      field_simp
      ring
    simp_rw [hφ, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hwt]
    ring
  -- (b) the denominator Heine integral
  have hZ0 : heineZ s (fun τ => 1 / ρ.eval τ) =
      nodeIntegral cosMeasure wt s (fun _ : Fin 0 => (0 : ℝ)) := by
    have hmeas : Measurable fun τ : ℝ => 1 / ρ.eval τ := measurable_const.div hρm
    rw [heineZ_eq s _ hmeas]
    unfold nodeIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp [hwt, one_div]
  -- (c) Heine's identity with fixed nodes
  have hcross := heine_cross (μ := cosMeasure) (W := wt) (s := s) (k := k) (qFam h s k)
    (fun r => (qFam_natDegree_monic h q s k h0 hdeg hs r).1)
    (fun r => (qFam_natDegree_monic h q s k h0 hdeg hs r).2)
    (fun r => qFam_left h s k r)
    (fun p i => integrable_cos_weight hnz hρ p i)
    (by
      intro j i
      rw [qFam_right]
      simp only [eval_mul, eval_C, mul_assoc]
      rw [integral_const_mul, orth_cos hnz hρ (s + j) i (by have := i.2; omega), mul_zero])
    t
  -- (d) the denominator is positive
  have hint := fun (p : ℝ[X]) (i : ℕ) => integrable_cos_weight hnz hρ p i
  have hZ0pos : 0 < heineZ s (fun τ => 1 / ρ.eval τ) := by
    rw [hZ0, zero_integral_eq hint]
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos s))
      (hankel_det_pos hint (fun p hp => pos_cos hnz hρ p hp))
  -- (e) the algebra
  set Z0 := heineZ s (fun τ => 1 / ρ.eval τ) with hZ0def
  set Zφ := heineZ s (fun τ => (∏ b, (1 + 2 * x b * τ + x b ^ 2)) / ρ.eval τ) with hZφdef
  set I := nodeIntegral cosMeasure wt s t with hI
  set Dq := (Matrix.of fun j' j : Fin k => ((qFam h s k) (Fin.natAdd s j')).eval (t j)).det with hDq
  set Pdet := (Matrix.of fun b j : Fin k => (bsPoly h (s + j)).eval (tNode (x b))).det with hPdet
  set A : ℝ := ∏ j : Fin k, ((2 : ℝ) ^ (s + (j : ℕ) - 1))⁻¹ with hA
  have E4 : Dq = A * Pdet := by
    have : (Matrix.of fun j' j : Fin k => ((qFam h s k) (Fin.natAdd s j')).eval (t j)) =
        Matrix.of fun i j : Fin k => ((2 : ℝ) ^ (s + (i : ℕ) - 1))⁻¹ *
          Matrix.transpose (Matrix.of fun b j : Fin k => (bsPoly h (s + j)).eval (tNode (x b))) i j := by
      ext i j
      simp only [Matrix.of_apply, Matrix.transpose_apply, qFam_right, eval_mul, eval_C, ht]
    rw [hDq, this, Matrix.det_mul_column, Matrix.det_transpose]
  have E5 := det_bsPoly_nodes h q m s k hm hs x hx0 hh
  have E6 := det_vandermonde_tNode x hx0
  have E7 := key_identity h k s hk (by omega) x hx0 hh
  rw [← hZ0] at hcross
  rw [← hPdet] at E5
  have hmain : (Matrix.vandermonde x).det *
      (∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j)) * (∏ b, (h.eval (-x b))⁻¹) * Zφ =
      Z0 * (dMat h q m x).det := by
    calc (Matrix.vandermonde x).det * (∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j)) *
          (∏ b, (h.eval (-x b))⁻¹) * Zφ
        = ((Matrix.vandermonde fun b => tNode (x b)).det *
            ((∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1))) *
            (∏ b, (h.eval (-x b))⁻¹) * Zφ := by rw [E6]
      _ = ((∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1)) *
            (∏ b, (h.eval (-x b))⁻¹) * c ^ s *
            ((Matrix.vandermonde t).det * I) := by rw [hZφ]; simp only [ht]; ring
      _ = ((∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1)) *
            (∏ b, (h.eval (-x b))⁻¹) * c ^ s * (Z0 * Dq) := by rw [hcross]
      _ = Z0 * (dMat h q m x).det *
            ((∏ b, (h.eval (-x b))⁻¹) * c ^ s * A *
              (∏ b, h.eval (-x b) / (2 * x b ^ (s + k - 1))) * (-1) ^ (s * k) *
              ((∏ i : Fin k, (2 : ℝ) ^ (i : ℕ)) * (∏ b, x b) ^ (k - 1))) := by
          rw [E4, E5]; ring
      _ = Z0 * (dMat h q m x).det := by rw [hc, E7]; ring
  have hZ0ne : Z0 ≠ 0 := hZ0pos.ne'
  generalize (∏ b, (h.eval (-x b))⁻¹) = Hi at hmain ⊢
  generalize (∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j)) = W2 at hmain ⊢
  rw [div_eq_iff hV]
  field_simp
  linear_combination (-1 : ℝ) * hmain

end Final

section Lemma51

/-- `w(y) = ∏_c (1 - x_c y)`. -/
noncomputable def wFun {k : ℕ} (x : Fin k → ℝ) (y : ℝ) : ℝ := ∏ c, (1 - x c * y)

/-- `∏_{c' ≠ c} (x_c - x_{c'})`. -/
noncomputable def nodalProd {k : ℕ} (x : Fin k → ℝ) (c : Fin k) : ℝ :=
  ∏ c' ∈ Finset.univ.erase c, (x c - x c')

theorem nodalProd_ne_zero {k : ℕ} {x : Fin k → ℝ} (hinj : Function.Injective x) (c : Fin k) :
    nodalProd x c ≠ 0 := by
  unfold nodalProd
  refine Finset.prod_ne_zero_iff.mpr fun c' hc' => ?_
  have : c' ≠ c := (Finset.mem_erase.mp hc').1
  exact sub_ne_zero.mpr (fun h => this (hinj h).symm)

/-- **Lagrange interpolation form of the Cauchy-matrix identity** (R7). -/
theorem lagrange_sum {k : ℕ} (x : Fin k → ℝ) (hinj : Function.Injective x)
    (hx0 : ∀ b, x b ≠ 0) (hw : ∀ a c, 1 - x c * x a ≠ 0) (a : Fin k) (j : ℕ) (hj : j < k) :
    ∑ c, x c ^ j / ((1 - x a * x c) * nodalProd x c) = x a ^ (k - 1 - j) / wFun x (x a) := by
  have hf := Lagrange.eq_interpolate (s := Finset.univ) (v := x) (f := (X : ℝ[X]) ^ j)
    hinj.injOn (by
      rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]; exact_mod_cast hj)
  have hy := congrArg (Polynomial.eval (x a)⁻¹) hf
  simp only [eval_pow, eval_X, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C,
    Lagrange.basis, eval_prod, Lagrange.basisDivisor, Finset.prod_mul_distrib, eval_sub,
    Finset.prod_inv_distrib] at hy
  set y := (x a)⁻¹ with hydef
  have hxa := hx0 a
  have hxy : x a * y = 1 := by rw [hydef]; field_simp
  have hwne : wFun x (x a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hw a c
  have hE : ∀ c, ∏ c' ∈ Finset.univ.erase c, (y - x c') =
      y ^ (k - 1) * (wFun x (x a) / (1 - x c * x a)) := by
    intro c
    have step : ∀ c', y - x c' = y * (1 - x a * x c') := by
      intro c'
      have : y * (x a * x c') = x c' := by rw [← mul_assoc, mul_comm y, hxy, one_mul]
      linarith [this]
    rw [Finset.prod_congr rfl (fun c' _ => step c'), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [eq_div_iff (hw a c)]
    unfold wFun
    rw [← Finset.prod_erase_mul Finset.univ (fun c' => 1 - x c' * x a) (Finset.mem_univ c)]
    congr 1
    exact Finset.prod_congr rfl (fun c' _ => by rw [mul_comm])
  have hy' : y ^ j = y ^ (k - 1) * wFun x (x a) *
      ∑ c, x c ^ j / ((1 - x a * x c) * nodalProd x c) := by
    rw [hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hE c]
    have h1 := hw a c
    have h2 : 1 - x a * x c ≠ 0 := by rw [mul_comm]; exact hw a c
    have h3 := nodalProd_ne_zero hinj c
    unfold nodalProd at h3 ⊢
    rw [mul_comm (x a) (x c)] at *
    field_simp
  set S := ∑ c, x c ^ j / ((1 - x a * x c) * nodalProd x c) with hS
  rw [eq_div_iff hwne]
  have hk1 : k - 1 = (k - 1 - j) + j := by omega
  calc S * wFun x (x a) = (x a ^ (k - 1) * y ^ (k - 1)) * (S * wFun x (x a)) := by
        rw [← mul_pow, hxy, one_pow, one_mul]
    _ = x a ^ (k - 1) * (y ^ (k - 1) * wFun x (x a) * S) := by ring
    _ = x a ^ (k - 1) * y ^ j := by rw [← hy']
    _ = x a ^ (k - 1 - j) * (x a * y) ^ j := by
        rw [mul_pow, hk1, pow_add, ← hk1]; ring
    _ = x a ^ (k - 1 - j) := by rw [hxy]; simp

/-- The Cauchy-type matrix `K = [1/(1 - x_a x_b)]`. -/
noncomputable def kMat {k : ℕ} (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a b => 1 / (1 - x a * x b)

/-- `B_-'(x_b) = ∏_{c ≠ b}(x_b - x_c) / w(x_b)` for `B_-(z) = ∏_c (z - x_c)/(1 - x_c z)`. -/
noncomputable def negBlaschkeDeriv {k : ℕ} (x : Fin k → ℝ) (b : Fin k) : ℝ :=
  nodalProd x b / wFun x (x b)

/-- `D_- = diag(B'(x_b) x_b^e)` with `B' (x_b) = B_G(x_b) B_-'(x_b)`. -/
noncomputable def dMinus (h : ℝ[X]) (q e : ℕ) {k : ℕ} (x : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun b => blaschkeG h q (x b) * negBlaschkeDeriv x b * x b ^ e

/-- **Lemma 5.1.** `det (K + D_-) / det K = det [x_b^j + B_G(x_b) x_b^{m-j}] / V(x)`, `m = e + k - 1`. -/
theorem lemma51 (h : ℝ[X]) (q e : ℕ) {k : ℕ} (x : Fin k → ℝ)
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1) :
    (kMat x + dMinus h q e x).det / (kMat x).det =
      (dMat h q (e + k - 1) x).det / (Matrix.vandermonde x).det := by
  have hw : ∀ a c, 1 - x c * x a ≠ 0 := by
    intro a c hz
    have h1 := hx1 a
    have h2 := hx1 c
    rw [abs_lt] at h1 h2
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hw' : ∀ a, wFun x (x a) ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.mpr fun c _ => hw a c
  have hn : ∀ c, nodalProd x c ≠ 0 := nodalProd_ne_zero hinj
  set V := Matrix.vandermonde x with hV
  set rv : Equiv.Perm (Fin k) := Fin.revPerm with hrv
  have hrev : ∀ j : Fin k, ((rv j : Fin k) : ℕ) = k - 1 - (j : ℕ) := by
    intro j; simp only [hrv, Fin.revPerm_apply, Fin.val_rev]; omega
  set Q : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun c j => x c ^ (j : ℕ) / nodalProd x c with hQ
  have hQdiag : Q = Matrix.diagonal (fun c => (nodalProd x c)⁻¹) * V := by
    ext c j
    simp [hQ, hV, Matrix.diagonal_mul, Matrix.vandermonde_apply, div_eq_inv_mul]
  have hKQ : kMat x * Q = Matrix.diagonal (fun a => (wFun x (x a))⁻¹) * V.submatrix id rv := by
    ext a j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, kMat, hQ, Matrix.of_apply, Matrix.submatrix_apply, id, hV,
      Matrix.vandermonde_apply, hrev]
    have := lagrange_sum x hinj hx0 hw a j j.2
    rw [← div_eq_inv_mul, ← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h2 : 1 - x a * x c ≠ 0 := by rw [mul_comm]; exact hw a c
    have h3 := hn c
    field_simp
  have hDQ : dMinus h q e x * Q = Matrix.diagonal (fun a => (wFun x (x a))⁻¹) *
      (Matrix.diagonal (fun a => blaschkeG h q (x a) * x a ^ e) * V) := by
    ext a j
    simp only [dMinus, Matrix.diagonal_mul, hQ, Matrix.of_apply, hV, Matrix.vandermonde_apply,
      negBlaschkeDeriv]
    have h3 := hn a
    have h4 := hw' a
    field_simp
  have hdM : (dMat h q (e + k - 1) x).submatrix id rv =
      V.submatrix id rv + Matrix.diagonal (fun a => blaschkeG h q (x a) * x a ^ e) * V := by
    ext a j
    simp only [dMat, Matrix.of_apply, Matrix.add_apply, hV, Matrix.vandermonde_apply,
      Matrix.diagonal_mul, Matrix.submatrix_apply, id, hrev]
    have : e + k - 1 - (k - 1 - (j : ℕ)) = e + (j : ℕ) := by have := j.2; omega
    rw [this, pow_add]
    ring
  have hKDQ : (kMat x + dMinus h q e x) * Q =
      Matrix.diagonal (fun a => (wFun x (x a))⁻¹) * (dMat h q (e + k - 1) x).submatrix id rv := by
    rw [add_mul, hKQ, hDQ, hdM, mul_add]
  set sg : ℝ := (((Equiv.Perm.sign rv : ℤˣ) : ℤ) : ℝ) with hsg
  have hsg0 : sg ≠ 0 := by
    rw [hsg, hrv, sign_revPerm]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (by norm_num)
  have hX : (∏ a, (wFun x (x a))⁻¹) * sg ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => inv_ne_zero (hw' a)) hsg0
  have hVdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hQdet : Q.det ≠ 0 := by
    rw [hQdiag, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => inv_ne_zero (hn c)) hVdet
  have A1 : (kMat x + dMinus h q e x).det * Q.det =
      ((∏ a, (wFun x (x a))⁻¹) * sg) * (dMat h q (e + k - 1) x).det := by
    rw [← Matrix.det_mul, hKDQ, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute']
    ring
  have A2 : (kMat x).det * Q.det = ((∏ a, (wFun x (x a))⁻¹) * sg) * V.det := by
    rw [← Matrix.det_mul, hKQ, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute']
    ring
  have hK0 : (kMat x).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at A2
    exact mul_ne_zero hX hVdet A2.symm
  rw [div_eq_div_iff hK0 hVdet]
  apply mul_right_cancel₀ (mul_ne_zero hQdet hX)
  linear_combination (V.det * ((∏ a, (wFun x (x a))⁻¹) * sg)) * A1 -
    ((dMat h q (e + k - 1) x).det * ((∏ a, (wFun x (x a))⁻¹) * sg)) * A2

end Lemma51

section RouteII

variable {q : ℕ} (g : Fin q → ℝ)

/-- `h(z) = ∏_i (1 + g_i z)`. -/
noncomputable def hOfRoots : ℝ[X] := ∏ i, (1 + C (g i) * X)

/-- `ρ(τ) = ∏_i (1 + 2 g_i τ + g_i²)`. -/
noncomputable def rhoOfRoots : ℝ[X] := ∏ i, (1 + C (2 * g i) * X + C (g i ^ 2))

theorem hOfRoots_eval (y : ℝ) : (hOfRoots g).eval y = ∏ i, (1 + g i * y) := by
  simp [hOfRoots, eval_prod]

theorem rhoOfRoots_eval (y : ℝ) :
    (rhoOfRoots g).eval y = ∏ i, (1 + 2 * g i * y + g i ^ 2) := by
  simp [rhoOfRoots, eval_prod]

theorem hOfRoots_aeval (z : ℂ) : aeval z (hOfRoots g) = ∏ i, (1 + (g i : ℂ) * z) := by
  simp [hOfRoots, map_prod]

theorem hOfRoots_coeff_zero : (hOfRoots g).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, hOfRoots_eval]; simp

theorem hOfRoots_natDegree_le : (hOfRoots g).natDegree ≤ q := by
  unfold hOfRoots
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (1 + C (g i) * X : ℝ[X]).natDegree ≤ ∑ _i : Fin q, 1 :=
        Finset.sum_le_sum fun i _ => by
          refine (natDegree_add_le _ _).trans ?_
          simp only [natDegree_one, zero_le, max_eq_right]
          exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = q := by simp

theorem hOfRoots_nonzero (hg : ∀ i, |g i| < 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    aeval z (hOfRoots g) ≠ 0 := by
  rw [hOfRoots_aeval]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  intro h0
  have h1 : (g i : ℂ) * z = -1 := by linear_combination h0
  have h2 : ‖(g i : ℂ) * z‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h2
  have := hg i
  nlinarith [norm_nonneg z, abs_nonneg (g i)]

theorem hOfRoots_abs2 (θ : ℝ) :
    (rhoOfRoots g).eval (Real.cos θ) = hAbs2 (hOfRoots g) θ := by
  unfold hAbs2
  rw [rhoOfRoots_eval, hOfRoots_aeval, norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem blaschkeG_prod (y : ℝ) (hy : y ≠ 0) :
    blaschkeG (hOfRoots g) q y = ∏ i, ((y - g i) / (1 - g i * y)) := by
  unfold blaschkeG
  rw [hOfRoots_eval, hOfRoots_eval, Finset.prod_div_distrib]
  have : y ^ q = ∏ _i : Fin q, y := by simp
  rw [this, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    field_simp
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    ring

/-- `D_-` in the paper's form: `diag (B_G(x_b) B_-'(x_b) x_b^e)` with `B_G = ∏ (z - g)/(1 - g z)`. -/
theorem dMinus_hOfRoots {k : ℕ} (e : ℕ) (x : Fin k → ℝ) (hx0 : ∀ b, x b ≠ 0) :
    dMinus (hOfRoots g) q e x = Matrix.diagonal fun b =>
      (∏ i, ((x b - g i) / (1 - g i * x b))) * negBlaschkeDeriv x b * x b ^ e := by
  unfold dMinus
  congr 1
  funext b
  rw [blaschkeG_prod g (x b) (hx0 b)]

/-- **Route II ratio identity.** For `h = ∏ (1 + g_i z)` (the positive nodes `g`), negative nodes
`x`, and `e + q + 1 = 2 s + k`:
`det (K + D_-) / det K = ∏_{a<b} (1 - x_a x_b) ∏_{b,i} (1 - g_i x_b)⁻¹ · Z(φ_x/ρ) / Z(1/ρ)`. -/
theorem route_two (hg : ∀ i, |g i| < 1) (s k e : ℕ) (hk : 0 < k) (hs : q < 2 * s)
    (he : e + q + 1 = 2 * s + k) (x : Fin k → ℝ) (hinj : Function.Injective x)
    (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1) :
    (kMat x + dMinus (hOfRoots g) q e x).det / (kMat x).det =
      (∏ i : Fin k, ∏ j ∈ Ioi i, (1 - x i * x j)) * (∏ b, ∏ i, (1 - g i * x b)⁻¹) *
        (heineZ s (fun τ => (∏ b, (1 + 2 * x b * τ + x b ^ 2)) /
            ∏ i, (1 + 2 * g i * τ + g i ^ 2)) /
          heineZ s (fun τ => 1 / ∏ i, (1 + 2 * g i * τ + g i ^ 2))) := by
  have hm : (e + k - 1) + q + 2 = 2 * s + 2 * k := by omega
  have key := ratio_identity (hOfRoots g) q s k (e + k - 1) hk hm hs (hOfRoots_coeff_zero g)
    (hOfRoots_natDegree_le g) (hOfRoots_nonzero g hg) (rhoOfRoots g) (hOfRoots_abs2 g) x hinj hx0 hx1
  rw [lemma51 (hOfRoots g) q e x hinj hx0 hx1, key]
  simp only [rhoOfRoots_eval, hOfRoots_eval]
  have e1 : ∀ b, ∏ i, (1 + g i * -x b) = ∏ i, (1 - g i * x b) := fun b =>
    Finset.prod_congr rfl fun i _ => by ring
  simp only [e1, Finset.prod_inv_distrib]

end RouteII

end CatalanMeasure.GenD.Signed

#print axioms CatalanMeasure.GenD.Signed.heine_cross
#print axioms CatalanMeasure.GenD.Signed.hankel_det_pos
#print axioms CatalanMeasure.GenD.Signed.ratio_identity
#print axioms CatalanMeasure.GenD.Signed.lemma51
#print axioms CatalanMeasure.GenD.Signed.route_two
