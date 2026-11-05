module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HmProf
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.CellQ
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.Transfer
@[expose] public section
set_option Elab.async false

/-!
# From `ℚ` to `ZMod p` for the H+ / H- profile maps (generalised ranges)

`digitPhi` of the actual H+/H- profile polynomials of an integer profile equals the residue of
the rational form `PhiHp` / `PhiHm`, for `J < 13`, `σ + 3 ≤ 15`, provided the moments are units.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Unit hypotheses for the moment table `u < 15`, `J < 13`. -/
structure MU (p : ℕ) [Fact p.Prime] : Prop where
  hp2 : p ≠ 2
  hα : ∀ u < 15, ∀ J < 13, Q.alphaQ u J ∈ unitSub p
  hζ : ∀ u < 15, ∀ J < 13, zetaRat u J ∈ unitSub p

theorem beta_memG (hm : MU p) {u J : ℕ} (hu : u < 15) (hJ : J < 13) :
    Q.betaQ u J ∈ unitSub p := by
  unfold Q.betaQ
  exact Subring.mul_mem _ (Subring.neg_mem _ (half3_mem hm.hp2)) (hm.hζ u hu J hJ)

theorem PhiQ_memG (hm : MU p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < 13) (hσ : σ + 3 ≤ 15) :
    Q.PhiQ a b J σ ∈ unitSub p := by
  unfold Q.PhiQ
  refine Subring.sum_mem _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  exact Subring.add_mem _
    (Subring.mul_mem _ (hm.hα u (by omega) J hJ) (intCast_mem _ _))
    (Subring.mul_mem _ (beta_memG hm (by omega) hJ) (intCast_mem _ _))

theorem res_PhiQG (hm : MU p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < 13) (hσ : σ + 3 ≤ 15) :
    palindromicRatResidue p (Q.PhiQ a b J σ) =
      ∑ u ∈ Finset.range (σ + 3),
        (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf a ((σ : ℤ) + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf b ((σ : ℤ) - u) : ZMod p)) := by
  let f : ℕ → unitSub p := fun u =>
    if hu : u < σ + 3 then
      ⟨Q.alphaQ u J, hm.hα u (by omega) J hJ⟩ * ((Q.cf a ((σ : ℤ) + 1 - u) : ℤ) : unitSub p) +
        ⟨Q.betaQ u J, beta_memG hm (by omega) hJ⟩ * ((Q.cf b ((σ : ℤ) - u) : ℤ) : unitSub p)
    else 0
  have hsum : (⟨Q.PhiQ a b J σ, PhiQ_memG hm a b hJ hσ⟩ : unitSub p) =
      ∑ u ∈ Finset.range (σ + 3), f u := by
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

theorem digitPhi_eq_res_PhiQG (hm : MU p) (af bf : ℕ → ℤ) (a b : (ZMod p)[X])
    (ha : ∀ n, a.coeff n = (af n : ZMod p)) (hb : ∀ n, b.coeff n = (bf n : ZMod p))
    {J σ H : ℕ} (hJ : J < 13) (hσ : σ + 3 ≤ 15) (hH : σ + 3 ≤ H) :
    digitPhi H (σ : ℤ) (sourceM (p := p) J) (sourceZ (p := p) J) a b (3 / 2) =
      palindromicRatResidue p (Q.PhiQ af bf J σ) := by
  rw [digitPhi_cutoff_signed H (σ + 3) _ hH (by push_cast; omega), res_PhiQG hm af bf hJ hσ]
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
      ⟨zetaRat u J, hm.hζ u (by omega) J hJ⟩
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

/-! ### Coefficients of the profile polynomials -/

theorem Uz_coeff (R : Type*) [CommRing R] (n : ℤ) (i : ℕ) :
    (Chebyshev.U R n).coeff i = (ucZ n i : R) := by
  match n with
  | Int.ofNat m =>
    have := U_coeff R m i
    simpa [ucZ] using this
  | Int.negSucc 0 =>
    have h : Int.negSucc 0 = -1 := rfl
    have e : ucZ (Int.negSucc 0) i = 0 := rfl
    rw [e, h, Chebyshev.U_neg_one]; simp
  | Int.negSucc (m + 1) =>
    have h : Int.negSucc (m + 1) = -(m : ℤ) - 2 := by omega
    rw [h, Chebyshev.U_neg_sub_two, coeff_neg, U_coeff]
    have : ucZ (-(m : ℤ) - 2) i = - Q.uc m i := by
      have h' : -(m : ℤ) - 2 = Int.negSucc (m + 1) := by omega
      rw [h']; rfl
    rw [this]; push_cast; ring

theorem coeff_X_mul'' (R : Type*) [CommRing R] (P : R[X]) (i : ℕ) :
    (X * P).coeff i = if i = 0 then 0 else P.coeff (i - 1) := by
  rcases i with _ | i
  · simp
  · simp [coeff_X_mul]

theorem coeff_vc (n : ℤ) (i : ℕ) :
    (Chebyshev.U (ZMod p) n - Chebyshev.U (ZMod p) (n - 1)).coeff i = (vc n i : ZMod p) := by
  rw [coeff_sub, Uz_coeff, Uz_coeff]; simp [vc]

theorem coeff_wc (n : ℤ) (i : ℕ) :
    (Chebyshev.U (ZMod p) n + Chebyshev.U (ZMod p) (n - 1)).coeff i = (wc n i : ZMod p) := by
  rw [coeff_add, Uz_coeff, Uz_coeff]; simp [wc]

theorem coeff_aHp (n : ℤ) (i : ℕ) :
    ((1 + X) * (Chebyshev.U (ZMod p) n - Chebyshev.U (ZMod p) (n - 1))).coeff i =
      (aHp n i : ZMod p) := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul'']
  simp only [coeff_vc]
  unfold aHp shl1
  split_ifs <;> push_cast <;> ring

theorem coeff_aHm (n : ℤ) (i : ℕ) :
    ((X - 1) * (Chebyshev.U (ZMod p) n + Chebyshev.U (ZMod p) (n - 1))).coeff i =
      (aHm n i : ZMod p) := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul'']
  simp only [coeff_wc]
  unfold aHm shl1
  split_ifs <;> push_cast <;> ring

theorem coeff_comb {K : ℕ} (k0 : ℤ) (zI : ℕ → ℤ) (P : ℤ → (ZMod p)[X]) (f : ℤ → ℕ → ℤ)
    (hP : ∀ n i, (P n).coeff i = (f n i : ZMod p)) (i : ℕ) :
    (∑ k : Fin K, C ((zI k : ℤ) : ZMod p) * P (k0 + ((k : ℕ) : ℤ))).coeff i =
      ((combZ K k0 zI f i : ℤ) : ZMod p) := by
  rw [finset_sum_coeff]
  simp only [coeff_C_mul, hP]
  unfold combZ
  rw [← Fin.sum_univ_eq_sum_range (fun k => zI k * f (k0 + (k : ℤ)) i) K]
  push_cast; rfl

/-- The residue profile of an integer profile. -/
def zv (p K : ℕ) (z : ℕ → ℤ) : Fin K → ZMod p := fun k => ((z k : ℤ) : ZMod p)

theorem psiHp_eq (hm : MU p) (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) {J σ H : ℕ} (hJ : J < 13)
    (hσ : σ + 3 ≤ 15) (hH : σ + 3 ≤ H) :
    (profHp p K k0).psi H J (σ : ℤ) (zv p K z) = palindromicRatResidue p (PhiHp K k0 z J σ) := by
  unfold Prof.psi profHp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine digitPhi_eq_res_PhiQG hm _ _ _ _ (fun n => ?_) (fun n => ?_) hJ hσ hH
  · rw [hGy_apply]
    exact coeff_comb k0 z (fun n => (1 + X) * (Chebyshev.U (ZMod p) n - Chebyshev.U (ZMod p) (n - 1)))
      aHp (fun n i => coeff_aHp n i) n
  · rw [hTy_apply]
    exact coeff_comb k0 z (fun n => Chebyshev.U (ZMod p) n + Chebyshev.U (ZMod p) (n - 1))
      wc (fun n i => coeff_wc n i) n

theorem psiHm_eq (hm : MU p) (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) {J σ H : ℕ} (hJ : J < 13)
    (hσ : σ + 3 ≤ 15) (hH : σ + 3 ≤ H) :
    (profHm p K k0).psi H J (σ : ℤ) (zv p K z) = palindromicRatResidue p (PhiHm K k0 z J σ) := by
  unfold Prof.psi profHm
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine digitPhi_eq_res_PhiQG hm _ _ _ _ (fun n => ?_) (fun n => ?_) hJ hσ hH
  · rw [hmGy_apply]
    exact coeff_comb k0 z (fun n => (X - 1) * (Chebyshev.U (ZMod p) n + Chebyshev.U (ZMod p) (n - 1)))
      aHm (fun n i => coeff_aHm n i) n
  · rw [hmTy_apply]
    exact coeff_comb k0 z (fun n => Chebyshev.U (ZMod p) n - Chebyshev.U (ZMod p) (n - 1))
      vc (fun n i => coeff_vc n i) n

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
