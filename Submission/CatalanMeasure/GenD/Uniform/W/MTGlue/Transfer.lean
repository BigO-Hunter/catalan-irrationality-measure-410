module
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Cheb
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.QForms
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseWindow
@[expose] public section
set_option Elab.async false

/-!
# From `ℚ` to `ZMod p`: source covectors of the glue profiles for moments `J < 18`, `u < 22`

`ZmG` is the common denominator of the moments `α(u,J)`, `Z(u,J)`, `u < 22`, `J < 18` (and `2`).
For `¬ p ∣ ZmG` (`GUnits p`), `ψ(J,σ)` of the `T-` profile `(tyMap, gyMap)` and of the glue `T+`
profile `(tpTy, tpGy)` at an integer profile `z` is the residue of the rational form
`PhiQ (cmb z k0 K ·) (cmb z k0 K ·) J σ` (`psiY_eq`, `psiU_eq`).  This is the bridge
`Prof.psi ↔ ZoneZ.PhiTm / PhiTd` (integer block index, so that `k0 = -1` is covered): `y2uI, tI` are the
coefficients of `PhiTm κ`, and `xtI, xuI` those of the period form `PhiTd κ = PhiTp κ (S-1) - PhiTp κ S`.
The glue cells use `Q.PhiQ` of the combined coefficient functions directly (linear in the profile).
-/

namespace CatalanMeasure.GenD.Uniform.W.MTGlue
open Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.W.ZoneZ
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots

/-- Common denominator of the moments `α(u,J)`, `Z(u,J)`, `u < 22`, `J < 18`, and of `2`. -/
def ZmG : ℕ :=
  ((List.range 22).flatMap fun u => (List.range 18).flatMap fun J =>
    [(Q.alphaQ u J).den, (zetaRat u J).den]).foldl Nat.lcm 2

theorem two_dvd_ZmG : 2 ∣ ZmG := by
  unfold ZmG
  have h : ∀ (l : List ℕ) (a : ℕ), a ∣ l.foldl Nat.lcm a := by
    intro l
    induction l with
    | nil => intro a; exact dvd_rfl
    | cons y l ih => intro a; exact (Nat.dvd_lcm_left a y).trans (ih _)
  exact h _ 2

theorem alphaG_den_dvd : ∀ u < 22, ∀ J < 18, (Q.alphaQ u J).den ∣ ZmG := by decide +kernel
theorem zetaG_den_dvd : ∀ u < 22, ∀ J < 18, (zetaRat u J).den ∣ ZmG := by decide +kernel

variable {p : ℕ} [Fact p.Prime]

theorem memU_of_dvd {q : ℚ} {Z : ℕ} (h : q.den ∣ Z) (hp : ¬ p ∣ Z) : q ∈ unitSub p := by
  show ((q.den : ℕ) : ZMod p) ≠ 0
  intro h0
  exact hp (((ZMod.natCast_eq_zero_iff q.den p).mp h0).trans h)

theorem half3U (hp2 : p ≠ 2) : (3 / 2 : ℚ) ∈ unitSub p := by
  show (((3 / 2 : ℚ).den : ℕ) : ZMod p) ≠ 0
  have : (3 / 2 : ℚ).den = 2 := by decide +kernel
  rw [this]
  intro h0
  have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)

theorem res_half3G (hp2 : p ≠ 2) : palindromicRatResidue p (3 / 2 : ℚ) = (3 / 2 : ZMod p) := by
  unfold palindromicRatResidue
  have n : (3 / 2 : ℚ).num = 3 := by decide +kernel
  have d : (3 / 2 : ℚ).den = 2 := by decide +kernel
  rw [n, d]; push_cast; rfl

/-- Unit hypotheses for the moment table of the glue cells. -/
structure GUnits (p : ℕ) [Fact p.Prime] : Prop where
  hp2 : p ≠ 2
  hZ : ¬ p ∣ ZmG

theorem GUnits.of_coprime (h : Nat.Coprime p ZmG) : GUnits p where
  hp2 := by
    intro e
    have := two_dvd_ZmG
    rw [← e] at this
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl this)
  hZ := fun hd => (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl hd)

theorem alphaU (hm : GUnits p) {u J : ℕ} (hu : u < 22) (hJ : J < 18) :
    Q.alphaQ u J ∈ unitSub p := memU_of_dvd (alphaG_den_dvd u hu J hJ) hm.hZ

theorem zetaU (hm : GUnits p) {u J : ℕ} (hu : u < 22) (hJ : J < 18) :
    zetaRat u J ∈ unitSub p := memU_of_dvd (zetaG_den_dvd u hu J hJ) hm.hZ

theorem betaU (hm : GUnits p) {u J : ℕ} (hu : u < 22) (hJ : J < 18) :
    Q.betaQ u J ∈ unitSub p := by
  unfold Q.betaQ
  exact Subring.mul_mem _ (Subring.neg_mem _ (half3U hm.hp2)) (zetaU hm hu hJ)

/-- The residue of `PhiQ` is the finite digit sum with the residues of the moments. -/
theorem res_PhiQG (hm : GUnits p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < 18) (hσ : σ + 3 ≤ 22) :
    palindromicRatResidue p (Q.PhiQ a b J σ) =
      ∑ u ∈ Finset.range (σ + 3),
        (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf a ((σ : ℤ) + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf b ((σ : ℤ) - u) : ZMod p)) := by
  let f : ℕ → unitSub p := fun u =>
    if hu : u < σ + 3 then
      ⟨Q.alphaQ u J, alphaU hm (by omega) hJ⟩ * ((Q.cf a ((σ : ℤ) + 1 - u) : ℤ) : unitSub p) +
        ⟨Q.betaQ u J, betaU hm (by omega) hJ⟩ * ((Q.cf b ((σ : ℤ) - u) : ℤ) : unitSub p)
    else 0
  have hsum : (⟨Q.PhiQ a b J σ, by
      unfold Q.PhiQ
      refine Subring.sum_mem _ fun u hu => ?_
      have hu' := Finset.mem_range.mp hu
      exact Subring.add_mem _
        (Subring.mul_mem _ (alphaU hm (by omega) hJ) (intCast_mem _ _))
        (Subring.mul_mem _ (betaU hm (by omega) hJ) (intCast_mem _ _))⟩ :
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

theorem intrinsicCoeff_castG (a : (ZMod p)[X]) (af : ℕ → ℤ) (ha : ∀ n, a.coeff n = (af n : ZMod p))
    (i : ℤ) : intrinsicCoeff a i = ((Q.cf af i : ℤ) : ZMod p) := by
  unfold intrinsicCoeff Q.cf
  split_ifs <;> simp [ha]

/-- **Source covector of a glue cell.**  `digitPhi` of polynomials with integer coefficients equals the
residue of the rational form `PhiQ`. -/
theorem digitPhi_eq_resG (hm : GUnits p) (af bf : ℕ → ℤ) (a b : (ZMod p)[X])
    (ha : ∀ n, a.coeff n = (af n : ZMod p)) (hb : ∀ n, b.coeff n = (bf n : ZMod p))
    {J σ H : ℕ} (hJ : J < 18) (hσ : σ + 3 ≤ 22) (hH : σ + 3 ≤ H) :
    digitPhi H (σ : ℤ) (sourceM (p := p) J) (sourceZ (p := p) J) a b (3 / 2) =
      palindromicRatResidue p (Q.PhiQ af bf J σ) := by
  rw [digitPhi_cutoff_signed H (σ + 3) _ hH (by push_cast; omega), res_PhiQG hm af bf hJ hσ]
  unfold digitPhi
  simp only [intrinsicCoeff_castG a af ha, intrinsicCoeff_castG b bf hb]
  rw [Finset.sum_range_succ]
  have hz : Q.cf af ((σ : ℤ) + 1 - ((σ + 3 : ℕ) : ℤ)) = 0 := by
    unfold Q.cf; rw [if_neg]; push_cast; omega
  rw [hz]
  simp only [Int.cast_zero, zero_mul, add_zero]
  have h32 := res_half3G hm.hp2
  have hneg : palindromicRatResidue p (-(3 / 2 : ℚ)) = -(3 / 2 : ZMod p) := by
    have := map_neg (resHom p) ⟨(3 / 2 : ℚ), half3U hm.hp2⟩
    simpa [resHom_apply, h32] using this
  have hβ : ∀ u ∈ Finset.range (σ + 3), palindromicRatResidue p (Q.betaQ u J) =
      -(3 / 2 : ZMod p) * sourceZ (p := p) J u := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have := map_mul (resHom p) ⟨-(3 / 2 : ℚ), Subring.neg_mem _ (half3U hm.hp2)⟩
      ⟨zetaRat u J, zetaU hm (by omega) hJ⟩
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

/-- Profile maps of the `T-` slot and of the glue `T+` (period form) slot. -/
noncomputable def profY (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : Prof p K := ⟨tyMap p K k0, gyMap p K k0⟩
noncomputable def profU (p K : ℕ) [Fact p.Prime] (k0 : ℤ) : Prof p K := ⟨tpTy p K k0, tpGy p K k0⟩

/-- **`ψ` of the `T-` profile `z`** is the residue of the rational form of the combined polynomials. -/
theorem psiY_eq (hm : GUnits p) (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) {J σ H : ℕ} (hJ : J < 18)
    (hσ : σ + 3 ≤ 22) (hH : σ + 3 ≤ H) :
    (profY p K k0).psi H J (σ : ℤ) (zprof p K z) =
      palindromicRatResidue p (Q.PhiQ (cmb z k0 K y2uI) (cmb z k0 K tI) J σ) :=
  digitPhi_eq_resG hm _ _ _ _ (gyMap_coeff K k0 z) (tyMap_coeff K k0 z) hJ hσ hH

/-- **`ψ` of the glue `T+` profile `z`** (period form). -/
theorem psiU_eq (hm : GUnits p) (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) {J σ H : ℕ} (hJ : J < 18)
    (hσ : σ + 3 ≤ 22) (hH : σ + 3 ≤ H) :
    (profU p K k0).psi H J (σ : ℤ) (zprof p K z) =
      palindromicRatResidue p (Q.PhiQ (cmb z k0 K xtI) (cmb z k0 K xuI) J σ) :=
  digitPhi_eq_resG hm _ _ _ _ (tpGy_coeff K k0 z) (tpTy_coeff K k0 z) hJ hσ hH

theorem res_intCast (c : ℤ) : palindromicRatResidue p (c : ℚ) = (c : ZMod p) := by
  unfold palindromicRatResidue
  simp

end CatalanMeasure.GenD.Uniform.W.MTGlue
end
