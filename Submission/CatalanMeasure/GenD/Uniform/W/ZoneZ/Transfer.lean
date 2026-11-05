module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ChebCoeff
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsL
@[expose] public section
set_option Elab.async false

/-!
# From `ℚ` to `ZMod p`: the source covector of a cell

`digitPhi` of the actual polynomials (Chebyshev `T_k`, `U_{k-1}`, `(X²-1) U_{k-1}`) equals the
residue of the design-free rational form `PhiQ` (`QForms`), provided the finitely many moment
denominators are units (`¬ p ∣ Zmom`).  Hence every exact rational cell identity (cell
properties, shapes, (P*)) holds in `ZMod p` for `p ∤ Zbad`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Common denominator of the moments `α(u,J)`, `Z(u,J)`, `u < 9`, `J < 7`. -/
def Zmom : ℕ :=
  ((List.range 9).flatMap fun u => (List.range 7).flatMap fun J =>
    [(Q.alphaQ u J).den, (zetaRat u J).den]).foldl Nat.lcm 1

theorem alpha_den_dvd : ∀ u < 9, ∀ J < 7, (Q.alphaQ u J).den ∣ Zmom := by decide +kernel
theorem zeta_den_dvd : ∀ u < 9, ∀ J < 7, (zetaRat u J).den ∣ Zmom := by decide +kernel

theorem mem_unitSub_of_dvd {q : ℚ} {Z : ℕ} (h : q.den ∣ Z) (hp : ¬ p ∣ Z) : q ∈ unitSub p := by
  show ((q.den : ℕ) : ZMod p) ≠ 0
  intro h0
  exact hp (((ZMod.natCast_eq_zero_iff q.den p).mp h0).trans h)

theorem half3_mem (hp2 : p ≠ 2) : (3 / 2 : ℚ) ∈ unitSub p := by
  show (((3 / 2 : ℚ).den : ℕ) : ZMod p) ≠ 0
  have : (3 / 2 : ℚ).den = 2 := by decide +kernel
  rw [this]
  intro h0
  have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)

theorem res_half3 (hp2 : p ≠ 2) : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := by
  unfold palindromicRatResidue
  have n : (3 / 2 : ℚ).num = 3 := by decide +kernel
  have d : (3 / 2 : ℚ).den = 2 := by decide +kernel
  rw [n, d]; push_cast; rfl

/-- Unit hypotheses for the moment table. -/
structure MomUnits (p : ℕ) [Fact p.Prime] : Prop where
  hp2 : p ≠ 2
  hZ : ¬ p ∣ Zmom

theorem alpha_mem (hm : MomUnits p) {u J : ℕ} (hu : u < 9) (hJ : J < 7) :
    Q.alphaQ u J ∈ unitSub p := mem_unitSub_of_dvd (alpha_den_dvd u hu J hJ) hm.hZ

theorem zeta_mem (hm : MomUnits p) {u J : ℕ} (hu : u < 9) (hJ : J < 7) :
    zetaRat u J ∈ unitSub p := mem_unitSub_of_dvd (zeta_den_dvd u hu J hJ) hm.hZ

theorem beta_mem (hm : MomUnits p) {u J : ℕ} (hu : u < 9) (hJ : J < 7) :
    Q.betaQ u J ∈ unitSub p := by
  unfold Q.betaQ
  exact Subring.mul_mem _ (Subring.neg_mem _ (half3_mem hm.hp2)) (zeta_mem hm hu hJ)

/-- The residue of `PhiQ` is the finite digit sum with the residues of the moments. -/
theorem res_PhiQ (hm : MomUnits p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) :
    palindromicRatResidue p (Q.PhiQ a b J σ) =
      ∑ u ∈ Finset.range (σ + 3),
        (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf a ((σ : ℤ) + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf b ((σ : ℤ) - u) : ZMod p)) := by
  let f : ℕ → unitSub p := fun u =>
    if hu : u < σ + 3 then
      ⟨Q.alphaQ u J, alpha_mem hm (by omega) hJ⟩ * ((Q.cf a ((σ : ℤ) + 1 - u) : ℤ) : unitSub p) +
        ⟨Q.betaQ u J, beta_mem hm (by omega) hJ⟩ * ((Q.cf b ((σ : ℤ) - u) : ℤ) : unitSub p)
    else 0
  have hsum : (⟨Q.PhiQ a b J σ, by
      unfold Q.PhiQ
      refine Subring.sum_mem _ fun u hu => ?_
      have hu' := Finset.mem_range.mp hu
      exact Subring.add_mem _
        (Subring.mul_mem _ (alpha_mem hm (by omega) hJ) (intCast_mem _ _))
        (Subring.mul_mem _ (beta_mem hm (by omega) hJ) (intCast_mem _ _))⟩ :
      unitSub p) = ∑ u ∈ Finset.range (σ + 3), f u := by
    apply Subtype.ext
    simp only [Q.PhiQ, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    simp [f, hu']
  have := congrArg (resHom p) hsum
  rw [map_sum] at this
  rw [resHom_apply] at this
  refine this.trans (Finset.sum_congr rfl fun u hu => ?_)
  have hu' := Finset.mem_range.mp hu
  simp [f, hu', map_add, map_mul, resHom_apply]


theorem intrinsicCoeff_cast (a : (ZMod p)[X]) (af : ℕ → ℤ) (ha : ∀ n, a.coeff n = (af n : ZMod p))
    (i : ℤ) : intrinsicCoeff a i = ((Q.cf af i : ℤ) : ZMod p) := by
  unfold intrinsicCoeff Q.cf
  split_ifs <;> simp [ha]

/-- **Source covector of a cell.**  `digitPhi` of polynomials with integer coefficients equals the
residue of the rational form `PhiQ`. -/
theorem digitPhi_eq_res_PhiQ (hm : MomUnits p) (af bf : ℕ → ℤ) (a b : (ZMod p)[X])
    (ha : ∀ n, a.coeff n = (af n : ZMod p)) (hb : ∀ n, b.coeff n = (bf n : ZMod p))
    {J σ H : ℕ} (hJ : J < 7) (hσ : σ + 3 ≤ 9) (hH : σ + 3 ≤ H) :
    digitPhi H (σ : ℤ) (sourceM (p := p) J) (sourceZ (p := p) J) a b (3 / 2) =
      palindromicRatResidue p (Q.PhiQ af bf J σ) := by
  rw [digitPhi_cutoff_signed H (σ + 3) _ hH (by push_cast; omega), res_PhiQ hm af bf hJ hσ]
  unfold digitPhi
  simp only [intrinsicCoeff_cast a af ha, intrinsicCoeff_cast b bf hb]
  rw [Finset.sum_range_succ]
  have hz : Q.cf af ((σ : ℤ) + 1 - ((σ + 3 : ℕ) : ℤ)) = 0 := by
    unfold Q.cf; rw [if_neg]; push_cast; omega
  rw [hz]
  simp only [Int.cast_zero, zero_mul, add_zero]
  have h32 := res_half3 hm.hp2
  have hneg : palindromicRatResidue p (-(3 / 2 : ℚ)) = -(3 / 2 : ZMod p) := by
    have := map_neg (resHom p) ⟨(3 / 2 : ℚ), half3_mem hm.hp2⟩
    simpa [resHom_apply, h32] using this
  have hβ : ∀ u ∈ Finset.range (σ + 3), palindromicRatResidue p (Q.betaQ u J) =
      -(3 / 2 : ZMod p) * sourceZ (p := p) J u := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have := map_mul (resHom p) ⟨-(3 / 2 : ℚ), Subring.neg_mem _ (half3_mem hm.hp2)⟩
      ⟨zetaRat u J, zeta_mem hm (by omega) hJ⟩
    simp only [resHom_apply, MulMemClass.coe_mul] at this
    unfold Q.betaQ sourceZ
    rw [this, hneg]
  have hα : ∀ u ∈ Finset.range (σ + 3), palindromicRatResidue p (Q.alphaQ u J) =
      sourceM (p := p) J u := fun u _ => rfl
  have hstep : ∀ u ∈ Finset.range (σ + 3),
      (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf af ((σ : ℤ) + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf bf ((σ : ℤ) - u) : ZMod p)) =
      ((Q.cf af ((σ : ℤ) + 1 - u) : ℤ) : ZMod p) * sourceM (p := p) J u +
        (-(3 / 2 : ZMod p)) * (((Q.cf bf ((σ : ℤ) - u) : ℤ) : ZMod p) * sourceZ (p := p) J u) := by
    intro u hu
    rw [hα u hu, hβ u hu]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
