module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.PsiCells
@[expose] public section
set_option Elab.async false

/-!
# Generated chart rows: the seen covectors `ψ(J,S)` from profile data

For a slot system whose profile maps `Ty, Gy` are given by integer coefficient functions
(`ProfData`: the `i`-th coefficient of `Gy(e_k)` and `Ty(e_k)`), the source covector
`ψ(J,S)(e_k) = digitPhi H S (M_J) (Z_J) Gy(e_k) Ty(e_k) (3/2)` is the residue of the rational form

    phiQ g_k t_k J S = Σ_{u < S+3} α(u,J) g_k[S+1-u] + β(u,J) t_k[S-u]

(`α, β` the universal rational moments; `S` an arbitrary integer, `S = -1` being the boundary
covector).  `rowInt` is the integerised row `Zmom · phiQ`; `psi_single_eq_rowInt` says that, for
`p ∤ Zmom`, `ψ(J,S)(e_k) · Zmom ≡ rowInt` modulo `p`.  Nothing is design specific.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Integer coefficient functions of the profile polynomials of the coordinates `k < K`:
`g k i = [Y^i] Gy(e_k)`, `t k i = [Y^i] Ty(e_k)`. -/
structure ProfData where
  g : ℕ → ℕ → ℤ
  t : ℕ → ℕ → ℤ

/-- The profile maps of a slot system have the coefficients of `pd` on the coordinate vectors. -/
def ProfData.Realises {K : ℕ} (pd : ProfData) (F : Prof p K) : Prop :=
  ∀ k : Fin K, ∀ i : ℕ, (F.Gy (Pi.single k 1)).coeff i = (pd.g k i : ZMod p) ∧
    (F.Ty (Pi.single k 1)).coeff i = (pd.t k i : ZMod p)

/-- The rational covector `ψ(J,S)` on one coordinate. -/
def phiQ (a b : ℕ → ℤ) (J : ℕ) (S : ℤ) : ℚ :=
  ∑ u ∈ Finset.range (S.toNat + 3),
    (Q.alphaQ u J * (Q.cf a (S + 1 - u) : ℚ) + Q.betaQ u J * (Q.cf b (S - u) : ℚ))

/-- Least common multiple of the denominators of `α(u,J)`, `ζ(u,J)`, `u < Ub`, `J < Jb`. -/
def Lmom (Ub Jb : ℕ) : ℕ :=
  (Finset.range Ub ×ˢ Finset.range Jb).lcm
    (fun uJ => Nat.lcm (Q.alphaQ uJ.1 uJ.2).den (zetaRat uJ.1 uJ.2).den)

/-- Common denominator of the moments `α(u,J)`, `β(u,J)` for `u < Ub`, `J < Jb`. -/
def Zmom (Ub Jb : ℕ) : ℕ := 2 * Lmom Ub Jb

theorem pair_dvd_Lmom {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    Nat.lcm (Q.alphaQ u J).den (zetaRat u J).den ∣ Lmom Ub Jb := by
  unfold Lmom
  have hmem : (u, J) ∈ Finset.range Ub ×ˢ Finset.range Jb :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hu, Finset.mem_range.mpr hJ⟩
  exact Finset.dvd_lcm (f := fun uJ : ℕ × ℕ => Nat.lcm (Q.alphaQ uJ.1 uJ.2).den (zetaRat uJ.1 uJ.2).den) hmem

theorem alpha_den_dvd' {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    (Q.alphaQ u J).den ∣ Zmom Ub Jb :=
  ((Nat.dvd_lcm_left _ _).trans (pair_dvd_Lmom hu hJ)).mul_left 2

theorem zeta_den_dvd' {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    (zetaRat u J).den ∣ Zmom Ub Jb :=
  ((Nat.dvd_lcm_right _ _).trans (pair_dvd_Lmom hu hJ)).mul_left 2

theorem two_dvd_Zmom (Ub Jb : ℕ) : 2 ∣ Zmom Ub Jb := Dvd.intro _ rfl

theorem beta_den_dvd' {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    (Q.betaQ u J).den ∣ Zmom Ub Jb := by
  unfold Q.betaQ
  have h1 : ((-(3 / 2 : ℚ)) * zetaRat u J).den ∣ (-(3 / 2 : ℚ)).den * (zetaRat u J).den :=
    Rat.mul_den_dvd _ _
  have h2 : (-(3 / 2 : ℚ)).den = 2 := by decide +kernel
  rw [h2] at h1
  exact h1.trans (Nat.mul_dvd_mul_left 2 ((Nat.dvd_lcm_right _ _).trans (pair_dvd_Lmom hu hJ)))

theorem alpha_unit {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) (hp : ¬ p ∣ Zmom Ub Jb) :
    Q.alphaQ u J ∈ unitSub p := mem_unitSub_of_dvd (alpha_den_dvd' hu hJ) hp

theorem zeta_unit {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) (hp : ¬ p ∣ Zmom Ub Jb) :
    zetaRat u J ∈ unitSub p := mem_unitSub_of_dvd (zeta_den_dvd' hu hJ) hp

theorem beta_unit {Ub Jb u J : ℕ} (hu : u < Ub) (hJ : J < Jb) (hp : ¬ p ∣ Zmom Ub Jb) :
    Q.betaQ u J ∈ unitSub p := mem_unitSub_of_dvd (beta_den_dvd' hu hJ) hp

theorem p_ne_two_of_Zmom {Ub Jb : ℕ} (hp : ¬ p ∣ Zmom Ub Jb) : p ≠ 2 := by
  rintro rfl
  exact hp (two_dvd_Zmom Ub Jb)

/-- Scaling of a rational with denominator dividing `Z` to an integer. -/
def qscale (q : ℚ) (Z : ℕ) : ℤ := ((Z / q.den : ℕ) : ℤ) * q.num

theorem qscale_cast {q : ℚ} {Z : ℕ} (h : q.den ∣ Z) : ((qscale q Z : ℤ) : ℚ) = Z * q := by
  obtain ⟨m, rfl⟩ := h
  have hd : 0 < q.den := q.den_pos
  have : (q.den * m) / q.den = m := Nat.mul_div_cancel_left m hd
  unfold qscale
  rw [this]
  have h := Rat.mul_den_eq_num q
  push_cast
  rw [← h]
  ring

/-- The integerised row entry `Zmom · ψ(J,S)(e_k)`. -/
def rowInt (pd : ProfData) (Z J : ℕ) (S : ℤ) (k : ℕ) : ℤ :=
  ∑ u ∈ Finset.range (S.toNat + 3),
    (qscale (Q.alphaQ u J) Z * Q.cf (pd.g k) (S + 1 - u) +
      qscale (Q.betaQ u J) Z * Q.cf (pd.t k) (S - u))

theorem rowInt_cast {Ub Jb : ℕ} (pd : ProfData) {J : ℕ} {S : ℤ} (k : ℕ)
    (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub) :
    ((rowInt pd (Zmom Ub Jb) J S k : ℤ) : ℚ) = (Zmom Ub Jb : ℚ) * phiQ (pd.g k) (pd.t k) J S := by
  unfold rowInt phiQ
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  rw [qscale_cast (alpha_den_dvd' (by omega) hJ), qscale_cast (beta_den_dvd' (by omega) hJ)]
  ring

theorem phiQ_unit {Ub Jb : ℕ} (a b : ℕ → ℤ) {J : ℕ} {S : ℤ} (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub)
    (hp : ¬ p ∣ Zmom Ub Jb) : phiQ a b J S ∈ unitSub p := by
  unfold phiQ
  refine Subring.sum_mem _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  exact Subring.add_mem _
    (Subring.mul_mem _ (alpha_unit (by omega) hJ hp) (intCast_mem _ _))
    (Subring.mul_mem _ (beta_unit (by omega) hJ hp) (intCast_mem _ _))

/-- The residue of `phiQ` is the finite digit sum with the residues of the moments. -/
theorem res_phiQ {Ub Jb : ℕ} (hp : ¬ p ∣ Zmom Ub Jb) (a b : ℕ → ℤ) {J : ℕ} {S : ℤ}
    (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub) :
    palindromicRatResidue p (phiQ a b J S) =
      ∑ u ∈ Finset.range (S.toNat + 3),
        (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf a (S + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf b (S - u) : ZMod p)) := by
  let f : ℕ → unitSub p := fun u =>
    if hu : u < S.toNat + 3 then
      ⟨Q.alphaQ u J, alpha_unit (by omega) hJ hp⟩ * ((Q.cf a (S + 1 - u) : ℤ) : unitSub p) +
        ⟨Q.betaQ u J, beta_unit (by omega) hJ hp⟩ * ((Q.cf b (S - u) : ℤ) : unitSub p)
    else 0
  have hsum : (⟨phiQ a b J S, phiQ_unit a b hJ hS hp⟩ : unitSub p) =
      ∑ u ∈ Finset.range (S.toNat + 3), f u := by
    apply Subtype.ext
    simp only [phiQ, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    simp [f, hu']
  have := congrArg (resHom p) hsum
  rw [map_sum] at this
  rw [resHom_apply] at this
  refine this.trans (Finset.sum_congr rfl fun u hu => ?_)
  have hu' := Finset.mem_range.mp hu
  simp [f, hu', map_add, map_mul, resHom_apply]

/-- **Source covector of a profile coordinate** (general integer `S`). -/
theorem digitPhi_eq_res_phiQ {Ub Jb : ℕ} (hp : ¬ p ∣ Zmom Ub Jb) (af bf : ℕ → ℤ)
    (a b : (ZMod p)[X]) (ha : ∀ n, a.coeff n = (af n : ZMod p))
    (hb : ∀ n, b.coeff n = (bf n : ZMod p)) {J : ℕ} {S : ℤ} {H : ℕ}
    (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub) (hH : S.toNat + 3 ≤ H) :
    digitPhi H S (sourceM (p := p) J) (sourceZ (p := p) J) a b (3 / 2) =
      palindromicRatResidue p (phiQ af bf J S) := by
  have hp2 : p ≠ 2 := p_ne_two_of_Zmom hp
  rw [digitPhi_cutoff_signed H (S.toNat + 3) _ hH (by push_cast; omega), res_phiQ hp af bf hJ hS]
  unfold digitPhi
  simp only [intrinsicCoeff_cast a af ha, intrinsicCoeff_cast b bf hb]
  rw [Finset.sum_range_succ]
  have hz : Q.cf af (S + 1 - ((S.toNat + 3 : ℕ) : ℤ)) = 0 := by
    unfold Q.cf; rw [if_neg]; push_cast; omega
  rw [hz]
  simp only [Int.cast_zero, zero_mul, add_zero]
  have h32 := res_half3 hp2
  have hneg : palindromicRatResidue p (-(3 / 2 : ℚ)) = -(3 / 2 : ZMod p) := by
    have := map_neg (resHom p) ⟨(3 / 2 : ℚ), half3_mem hp2⟩
    simpa [resHom_apply, h32] using this
  have hβ : ∀ u ∈ Finset.range (S.toNat + 3), palindromicRatResidue p (Q.betaQ u J) =
      -(3 / 2 : ZMod p) * sourceZ (p := p) J u := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have := map_mul (resHom p) ⟨-(3 / 2 : ℚ), Subring.neg_mem _ (half3_mem hp2)⟩
      ⟨zetaRat u J, zeta_unit (by omega) hJ hp⟩
    simp only [resHom_apply, MulMemClass.coe_mul] at this
    unfold Q.betaQ sourceZ
    rw [this, hneg]
  have hα : ∀ u ∈ Finset.range (S.toNat + 3), palindromicRatResidue p (Q.alphaQ u J) =
      sourceM (p := p) J u := fun u _ => rfl
  have hstep : ∀ u ∈ Finset.range (S.toNat + 3),
      (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf af (S + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf bf (S - u) : ZMod p)) =
      ((Q.cf af (S + 1 - u) : ℤ) : ZMod p) * sourceM (p := p) J u +
        (-(3 / 2 : ZMod p)) * (((Q.cf bf (S - u) : ℤ) : ZMod p) * sourceZ (p := p) J u) := by
    intro u hu
    rw [hα u hu, hβ u hu]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- `ψ(J,S)` on a coordinate vector of a slot system realising `pd`. -/
theorem psi_single_eq {Ub Jb : ℕ} (hp : ¬ p ∣ Zmom Ub Jb) {K : ℕ} (pd : ProfData)
    (F : Prof p K) (hF : pd.Realises F) (k : Fin K) {J : ℕ} {S : ℤ} {H : ℕ}
    (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub) (hH : S.toNat + 3 ≤ H) :
    F.psi H J S (Pi.single k 1) = palindromicRatResidue p (phiQ (pd.g k) (pd.t k) J S) := by
  unfold Prof.psi
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact digitPhi_eq_res_phiQ hp (pd.g k) (pd.t k) _ _ (fun n => (hF k n).1) (fun n => (hF k n).2)
    hJ hS hH

/-- **Integer row of a seen covector.**  For `p ∤ Zmom`: `rowInt ≡ Zmom · ψ(J,S)(e_k)` (mod `p`). -/
theorem rowInt_mod {Ub Jb : ℕ} (hp : ¬ p ∣ Zmom Ub Jb) {K : ℕ} (pd : ProfData)
    (F : Prof p K) (hF : pd.Realises F) (k : Fin K) {J : ℕ} {S : ℤ} {H : ℕ}
    (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub) (hH : S.toNat + 3 ≤ H) :
    ((rowInt pd (Zmom Ub Jb) J S k : ℤ) : ZMod p) =
      (Zmom Ub Jb : ZMod p) * F.psi H J S (Pi.single k 1) := by
  rw [psi_single_eq hp pd F hF k hJ hS hH]
  have hZ : (Zmom Ub Jb : ℚ) ∈ unitSub p := by
    show (((Zmom Ub Jb : ℚ).den : ℕ) : ZMod p) ≠ 0
    simp
  have hq := phiQ_unit (p := p) (pd.g k) (pd.t k) hJ hS hp
  have hm := map_mul (resHom p) ⟨(Zmom Ub Jb : ℚ), hZ⟩ ⟨phiQ (pd.g k) (pd.t k) J S, hq⟩
  simp only [resHom_apply, MulMemClass.coe_mul] at hm
  have hint : palindromicRatResidue p ((rowInt pd (Zmom Ub Jb) J S k : ℤ) : ℚ) =
      ((rowInt pd (Zmom Ub Jb) J S k : ℤ) : ZMod p) := by
    unfold palindromicRatResidue
    simp
  have hZres : palindromicRatResidue p (Zmom Ub Jb : ℚ) = (Zmom Ub Jb : ZMod p) := by
    unfold palindromicRatResidue
    simp
  rw [← hint, rowInt_cast pd k hJ hS, hm, hZres]

end
end CatalanMeasure.GenD.Uniform.W.Charts
