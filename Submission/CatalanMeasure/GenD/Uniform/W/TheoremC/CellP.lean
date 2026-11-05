module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Cell
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Transfer2
@[expose] public section
set_option Elab.async false

/-!
# Theorem C' (`h ≥ p`): interval form

Rational cells with the larger ranges `S ≤ 33`, `J ≤ 29` (`CCell2`).  For `h = p + dh` the family is
`σ = X^lo s̃`, `deg s̃ < hi - lo - dh`, `G = (X-1)^dh σ` (so `(X-1)^h σ = (X^p - 1) G`), with `G`
supported on `[lo, hi)`; the filter is free (`q ≥ p`) and the cost is `dh`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue
noncomputable section

/-- One rational cell of Theorem C' (larger ranges). -/
structure CCell2 where
  S : ℕ
  Jlo : ℕ
  Jhi : ℕ
  K : ℕ
  k0 : ℤ
  y : ℕ → ℤ
  A : ℚ
  ky : ℕ
  hS : 2 ≤ S ∧ S + 3 ≤ 36
  hJ : 1 ≤ Jlo ∧ Jlo ≤ Jhi ∧ Jhi < 30
  hky : ky < K
  heq : ∀ J ∈ List.range' Jlo (Jhi + 1 - Jlo),
    Q.PhiQ (cmb y k0 K y2uI) (cmb y k0 K tI) J (S - 1) -
      Q.PhiQ (cmb y k0 K y2uI) (cmb y k0 K tI) J S = A

/-- The bad-prime integer of a cell. -/
def CCell2.modulus (c : CCell2) : ℕ := ZmD * (c.y c.ky).natAbs

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem CCell2.units (c : CCell2) (h : Nat.Coprime p c.modulus) : DUnits p :=
  DUnits.of_coprime (Nat.Coprime.coprime_dvd_right (dvd_mul_right ZmD _) h)

theorem CCell2.z_ne (c : CCell2) (h : Nat.Coprime p c.modulus) :
    zprof p c.K c.y ≠ 0 := by
  intro h0
  have h1 : ((c.y c.ky : ℤ) : ZMod p) = 0 := congrFun h0 ⟨c.ky, c.hky⟩
  have h2 : (p : ℤ) ∣ c.y c.ky := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  have h3 : p ∣ (c.y c.ky).natAbs := Int.natCast_dvd.mp h2
  have h4 : p ∣ c.modulus := by
    unfold CCell2.modulus
    exact h3.mul_left _
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl h4)

theorem CCell2.psi_diff (c : CCell2) (hm : DUnits p) {H J : ℕ}
    (hJ : c.Jlo ≤ J ∧ J ≤ c.Jhi) (hH : c.S + 3 ≤ H) :
    (profY p c.K c.k0).psi H J (((c.S - 1 : ℕ) : ℤ)) (zprof p c.K c.y) -
      (profY p c.K c.k0).psi H J ((c.S : ℕ) : ℤ) (zprof p c.K c.y) =
      palindromicRatResidue p c.A := by
  have hJ30 : J < 30 := by have := c.hJ.2.2; omega
  have hS := c.hS
  rw [psiY_eqD hm c.K c.k0 c.y hJ30 (by omega) (by omega),
    psiY_eqD hm c.K c.k0 c.y hJ30 (by omega) hH]
  have hmem : J ∈ List.range' c.Jlo (c.Jhi + 1 - c.Jlo) := by
    rw [List.mem_range'_1]; omega
  have he := c.heq J hmem
  have hA := phiQ_memD hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJ30
    (by omega : c.S - 1 + 3 ≤ 36)
  have hB := phiQ_memD hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJ30
    (by omega : c.S + 3 ≤ 36)
  have h1 := res_sub (p := p) hA hB
  rw [← h1.2, he]

theorem degree_pow_mul_lt (m n : ℕ) (f : (ZMod p)[X]) (hf : f.degree < n) :
    ((X - 1 : (ZMod p)[X]) ^ m * f).degree < (m + n : ℕ) := by
  by_cases hG : f = 0
  · rw [hG, mul_zero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [Polynomial.degree_mul, Polynomial.degree_pow]
    have h1 : (X - 1 : (ZMod p)[X]).degree = 1 := by
      have : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
      rw [this]; exact Polynomial.degree_X_sub_C 1
    rw [h1]
    rw [Polynomial.degree_eq_natDegree hG] at hf ⊢
    have h3 : f.natDegree < n := by exact_mod_cast hf
    simp only [nsmul_eq_mul, mul_one]
    have : m + f.natDegree < m + n := by omega
    exact_mod_cast this

/-- The window analysis of a single column: for the position `e0` of the residue, in `[lo, hi)`. -/
theorem hcell_core (hP : Admissible P) (hN : 0 < N) (c : CCell2) (hm : DUnits p) {lo hi : ℕ}
    (hwin : ∀ e, lo ≤ e → e < hi →
      c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
      (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
      P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p))
    {j : ℕ} (hj1 : P.b N ≤ j) (hj2 : j < P.L N)
    (hrng : lo ≤ idxRes (P.H N) p (j % p) ∧ idxRes (P.H N) p (j % p) < hi) :
    psiLin p c.K c.k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) (zprof p c.K c.y) -
      psiLin p c.K c.k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) (zprof p c.K c.y) =
      palindromicRatResidue p c.A := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hS := c.hS
  set ℓ := j % p with hℓdef
  set e0 := idxRes (P.H N) p ℓ with he0def
  have hℓ : ℓ < p := Nat.mod_lt _ hp0
  have he0 := idxRes_lt hp0 (P.H N) ℓ
  have hidx := idx_eq hp0 (P.H N) ℓ
  rw [← he0def] at hidx
  obtain ⟨w1, w2, w3, w4⟩ := hwin e0 hrng.1 hrng.2
  obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = c.S * p := ⟨_, rfl⟩
  obtain ⟨Sp1, hSp1⟩ : ∃ Sp1, Sp1 = (c.S + 1) * p := ⟨_, rfl⟩
  have hSp1' : Sp1 = Sp + p := by rw [hSp, hSp1]; ring
  rw [← hSp] at w1 w3 w4
  rw [← hSp1] at w2
  set ℓe := P.H N - 1 - e0 - Sp with hℓe
  have hℓe_lt : ℓe < p := by omega
  have hq1 : (idxQuo (P.H N) p ℓ) = (c.S : ℤ) ∧ ℓ = ℓe := by
    have hSpz : (Sp : ℤ) = (c.S : ℤ) * p := by rw [hSp]; push_cast; ring
    have h5 : ((idxQuo (P.H N) p ℓ) - c.S) * (p : ℤ) = (ℓe : ℤ) - ℓ := by
      have this' : (ℓe : ℤ) = (P.H N : ℤ) - 1 - e0 - Sp := by omega
      linear_combination (-1 : ℤ) * hidx - this' + hSpz
    have := Thin.no_mult _ _ (by exact_mod_cast hp0) (by omega) (by omega) h5
    omega
  obtain ⟨hq1a, hq1b⟩ := hq1
  have hdig := digit_bounds hp0 c.hJ.1 hℓ (by rw [hq1b]; exact w3) (by
      rw [hq1b]; exact w4) hj1 hj2 rfl
  have e1 : idxQuo (P.H N) p (j % p) - 1 = ((c.S - 1 : ℕ) : ℤ) := by
    rw [hq1a]; push_cast [Nat.cast_sub (by omega : 1 ≤ c.S)]; ring
  rw [e1, hq1a]
  exact c.psi_diff hm hdig (by
    have : c.S * p + 1 ≤ P.H N := by omega
    nlinarith [hS.1, (Fact.out : p.Prime).two_le])

set_option maxHeartbeats 1600000 in
/-- **Theorem C', interval form** (`h ≥ p`, `dh = h - p`). -/
theorem cellCp_le_nullity (hP : Admissible P) (hN : 0 < N) (hH : P.H N < p ^ 2)
    (hq : 0 < P.q N) (c : CCell2) (hcop : Nat.Coprime p c.modulus) {lo hi : ℕ}
    (hhi : hi ≤ p) (hhp : p ≤ P.h N) (hdl : lo + (P.h N - p) ≤ hi)
    (hDp : hi - (P.h N - p) ≤ (p - 1) / 2)
    (hlow : -(P.g N : ℤ) ≤ c.k0 * p - ((hi - (P.h N - p) : ℕ) : ℤ))
    (hup : (c.k0 + (c.K : ℤ) - 1) * p + ((hi - (P.h N - p) : ℕ) : ℤ) < (P.n N : ℤ) - P.g N)
    (hwin : ∀ e, lo ≤ e → e < hi →
      c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
      (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
      P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p)) :
    (hi - lo - (P.h N - p)) - (p - P.q N) ≤ nullity P N p := by
  classical
  have hm := c.units hcop
  have hp2 := hm.hp2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set dh := P.h N - p with hdhdef
  set D := hi - dh with hDdef
  set M := hi - lo - dh with hMdef
  -- s̃ = Σ a_i X^i, σ = X^lo s̃, G = (X-1)^dh σ
  let sL : (Fin M → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    ∑ i : Fin M, (LinearMap.proj i : (Fin M → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
      (X ^ (i : ℕ) : (ZMod p)[X])
  have hsc : ∀ a e, (sL a).coeff e = if h : e < M then a ⟨e, h⟩ else 0 := by
    intro a e
    have : sL a = ∑ i : Fin M, C (a i) * X ^ (i : ℕ) := by
      simp [sL, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]
    rw [this, Polynomial.finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases h : e < M
    · rw [dif_pos h, Finset.sum_eq_single (⟨e, h⟩ : Fin M)]
      · rw [if_pos rfl, mul_one]
      · intro i _ hi'
        have : e ≠ (i : ℕ) := by
          intro he; apply hi'; apply Fin.ext; simp only; omega
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : e ≠ (i : ℕ) := by
        intro he; have := i.isLt; omega
      simp [this]
  have hsdeg : ∀ a, (sL a).degree < M := by
    intro a
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    rw [hsc, dif_neg (by omega)]
  have hsinj : Function.Injective sL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext i
    have := hsc a (i : ℕ)
    rw [ha, dif_pos i.isLt] at this
    simpa using this.symm
  let σL : (Fin M → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    (LinearMap.mulLeft (ZMod p) (X ^ lo : (ZMod p)[X])).comp sL
  have hσinj : Function.Injective σL := by
    intro a b hab
    have hne : (X ^ lo : (ZMod p)[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    exact hsinj (mul_left_cancel₀ hne hab)
  have hσcoef : ∀ a e, (σL a).coeff e = if lo ≤ e then (sL a).coeff (e - lo) else 0 := by
    intro a e
    show ((X ^ lo : (ZMod p)[X]) * sL a).coeff e = _
    rw [coeff_X_pow_mul']
  have hσdeg : ∀ a, σL a ∈ degreeLT (ZMod p) D := by
    intro a
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    rw [hσcoef]
    split_ifs with h
    · rw [hsc, dif_neg (by omega)]
    · rfl
  let ψC : (Fin M → ZMod p) →ₗ[ZMod p] degreeLT (ZMod p) D := LinearMap.codRestrict _ σL hσdeg
  let wm : (Fin M → ZMod p) →ₗ[ZMod p] (Fin D → ZMod p) :=
    (uBasisEquiv hp2 D).symm.toLinearMap.comp ψC
  have hwm : Function.Injective wm := by
    intro a b hab
    have h1 : ψC a = ψC b := (uBasisEquiv hp2 D).symm.injective hab
    exact hσinj (congrArg Subtype.val h1)
  let GmL : (Fin M → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    (LinearMap.mulLeft (ZMod p) ((X - 1 : (ZMod p)[X]) ^ dh)).comp σL
  have hGm : ∀ a, GmL a = (X - 1) ^ dh * σL a := fun a => rfl
  have hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * GmL a := by
    intro a
    have : uComb p D (wm a) = σL a := uBasisEquiv_symm_comb hp2 D (ψC a)
    rw [this, hGm, show P.h N = p + dh by omega, pow_add, sub_one_pow_p]
    ring
  have hGdeg : ∀ a, (GmL a).degree < hi := by
    intro a
    rw [hGm]
    have h1 : (σL a).degree < D := Polynomial.mem_degreeLT.mp (hσdeg a)
    have := degree_pow_mul_lt dh D (σL a) h1
    have e : dh + D = hi := by omega
    rwa [e] at this
  have hsupp : ∀ a e, (GmL a).coeff e ≠ 0 → e < hi := by
    intro a e he
    by_contra hc
    exact he (Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hGdeg a)
      (by exact_mod_cast (by omega : hi ≤ e))))
  have hlowsupp : ∀ a e, (GmL a).coeff e ≠ 0 → lo ≤ e := by
    intro a e he
    by_contra hc
    apply he
    have : GmL a = X ^ lo * ((X - 1 : (ZMod p)[X]) ^ dh * sL a) := by
      rw [hGm]; show (X - 1) ^ dh * (X ^ lo * sL a) = _; ring
    rw [this, coeff_X_pow_mul', if_neg hc]
  have hgood : ∀ (d : Fin D) (k : Fin c.K), Good P N p c.k0 d k := fun d k =>
    good_of_ends c.k0 hlow hup d k
  have hz := c.z_ne hcop
  have key := fam_le_nullity hP hN hp2 hH hq c.k0 (zprof p c.K c.y) hz (by omega) hgood wm hwm
    GmL hi hrel hsupp hhi (by omega) (palindromicRatResidue p c.A) (by
      intro a j hj1 hj2 hne
      exact hcell_core hP hN c hm hwin hj1 hj2
        ⟨hlowsupp a _ hne, hsupp a _ hne⟩)
  have hfr : finrank (ZMod p) (Fin M → ZMod p) = M := by simp
  rw [hfr] at key
  exact key

#print axioms cellCp_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.TheoremC
