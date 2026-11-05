module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Family
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Transfer
@[expose] public section
set_option Elab.async false

/-!
# Rational cells of Theorem C and the interval form

`CCell`: one rational cell `(S; Jlo..Jhi; blocks k0..k0+K-1; integer profile y)` with
`PhiTm(J,S-1;y) - PhiTm(J,S;y) = A` for all `J ∈ [Jlo, Jhi]` (checked over `ℚ` by `decide +kernel`).

`cellC_le_nullity` (h ≤ p): for an interval `[lo, hi)` of positions `e` all of whose columns lie in the
cell (window `S`, digits `[Jlo, Jhi]`) and all of whose pair offsets stay inside the rows,
`(hi - lo) - (p - q) ≤ ν` for every prime `p` coprime to the modulus.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
  CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.MTGlue
noncomputable section

/-- One rational cell of Theorem C. -/
structure CCell where
  S : ℕ
  Jlo : ℕ
  Jhi : ℕ
  K : ℕ
  k0 : ℤ
  y : ℕ → ℤ
  A : ℚ
  ky : ℕ
  hS : 2 ≤ S ∧ S + 3 ≤ 26
  hJ : 1 ≤ Jlo ∧ Jlo ≤ Jhi ∧ Jhi < 21
  hky : ky < K
  heq : ∀ J ∈ List.range' Jlo (Jhi + 1 - Jlo),
    Q.PhiQ (cmb y k0 K y2uI) (cmb y k0 K tI) J (S - 1) -
      Q.PhiQ (cmb y k0 K y2uI) (cmb y k0 K tI) J S = A

/-- The bad-prime integer of a cell. -/
def CCell.modulus (c : CCell) : ℕ := ZmC * (c.y c.ky).natAbs

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem CCell.units (c : CCell) (h : Nat.Coprime p c.modulus) : CUnits p :=
  CUnits.of_coprime (Nat.Coprime.coprime_dvd_right (dvd_mul_right ZmC _) h)

theorem CCell.z_ne (c : CCell) (h : Nat.Coprime p c.modulus) :
    zprof p c.K c.y ≠ 0 := by
  intro h0
  have h1 : ((c.y c.ky : ℤ) : ZMod p) = 0 := congrFun h0 ⟨c.ky, c.hky⟩
  have h2 : (p : ℤ) ∣ c.y c.ky := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  have h3 : p ∣ (c.y c.ky).natAbs := Int.natCast_dvd.mp h2
  have h4 : p ∣ c.modulus := by
    unfold CCell.modulus
    exact h3.mul_left _
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl h4)

/-- The cell constant: `ψ(S-1) - ψ(S) = res A` for the digits of the cell. -/
theorem CCell.psi_diff (c : CCell) (hm : CUnits p) {H J : ℕ} (hJ : c.Jlo ≤ J ∧ J ≤ c.Jhi)
    (hH : c.S + 3 ≤ H) :
    (profY p c.K c.k0).psi H J (((c.S - 1 : ℕ) : ℤ)) (zprof p c.K c.y) -
      (profY p c.K c.k0).psi H J ((c.S : ℕ) : ℤ) (zprof p c.K c.y) =
      palindromicRatResidue p c.A := by
  have hJ21 : J < 21 := by have := c.hJ.2.2; omega
  have hS := c.hS
  rw [psiY_eqC hm c.K c.k0 c.y hJ21 (by omega) (by omega),
    psiY_eqC hm c.K c.k0 c.y hJ21 (by omega) hH]
  have hmem : J ∈ List.range' c.Jlo (c.Jhi + 1 - c.Jlo) := by
    rw [List.mem_range'_1]; omega
  have he := c.heq J hmem
  have hA := phiQ_mem hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJ21
    (by omega : c.S - 1 + 3 ≤ 26)
  have hB := phiQ_mem hm (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) hJ21
    (by omega : c.S + 3 ≤ 26)
  have h1 := res_sub (p := p) hA hB
  rw [← h1.2, he]

theorem digit_bounds (hp : 0 < p) {Jlo Jhi ℓ b L j : ℕ} (hJlo : 1 ≤ Jlo) (hℓ : ℓ < p)
    (h1 : (Jlo - 1) * p + ℓ < b) (h2 : L ≤ (Jhi + 1) * p + ℓ) (hj1 : b ≤ j) (hj2 : j < L)
    (hjl : j % p = ℓ) : Jlo ≤ j / p ∧ j / p ≤ Jhi := by
  have hdm := Nat.div_add_mod j p
  rw [hjl] at hdm
  constructor
  · by_contra hc
    have : j / p ≤ Jlo - 1 := by omega
    have := Nat.mul_le_mul_left p this
    nlinarith
  · by_contra hc
    have : Jhi + 1 ≤ j / p := by omega
    have := Nat.mul_le_mul_left p this
    nlinarith

theorem good_of_ends {K D : ℕ} (k0 : ℤ)
    (hlow : -(P.g N : ℤ) ≤ k0 * p - (D : ℤ))
    (hup : (k0 + (K : ℤ) - 1) * p + (D : ℤ) < (P.n N : ℤ) - P.g N) (d : Fin D) (k : Fin K) :
    Good P N p k0 d k := by
  have hp0 : (0 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).pos.le
  have hk : (k : ℕ) + 1 ≤ K := k.isLt
  have hd := d.isLt
  have e1 : k0 * p ≤ (k0 + (k : ℕ)) * p := by nlinarith
  have e2 : (k0 + (k : ℕ)) * p ≤ (k0 + (K : ℤ) - 1) * p := by
    apply mul_le_mul_of_nonneg_right _ hp0
    have : ((k : ℕ) : ℤ) + 1 ≤ K := by exact_mod_cast hk
    linarith
  unfold Good InRange cen
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast <;> nlinarith

theorem sub_one_pow_p : ((X - 1 : (ZMod p)[X])) ^ p = X ^ p - 1 := by
  rw [sub_pow_char, one_pow]

set_option maxHeartbeats 1600000 in
/-- **Theorem C, interval form** (`h ≤ p`). -/
theorem cellC_le_nullity (hP : Admissible P) (hN : 0 < N) (hH : P.H N < p ^ 2)
    (hq : 0 < P.q N) (c : CCell) (hcop : Nat.Coprime p c.modulus) {lo hi : ℕ} (hlh : lo ≤ hi)
    (hhi : hi ≤ p) (hhp : P.h N ≤ p) (hDp : hi + (p - P.h N) ≤ (p - 1) / 2)
    (hlow : -(P.g N : ℤ) ≤ c.k0 * p - ((hi + (p - P.h N) : ℕ) : ℤ))
    (hup : (c.k0 + (c.K : ℤ) - 1) * p + ((hi + (p - P.h N) : ℕ) : ℤ) < (P.n N : ℤ) - P.g N)
    (hwin : ∀ e, lo ≤ e → e < hi →
      c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
      (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
      P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p)) :
    hi - lo - (p - P.q N) ≤ nullity P N p := by
  classical
  have hm := c.units hcop
  have hp2 := hm.hp2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set m := p - P.h N with hmdef
  set D := hi + m with hDdef
  set n := hi - lo with hndef
  -- the monomial family
  let GmL : (Fin n → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
    ∑ i : Fin n, (LinearMap.proj i : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
      (X ^ (lo + (i : ℕ)) : (ZMod p)[X])
  have hGm : ∀ a, GmL a = ∑ i : Fin n, C (a i) * X ^ (lo + (i : ℕ)) := by
    intro a
    simp [GmL, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]
  have hcoef : ∀ a e, (GmL a).coeff e =
      if h : lo ≤ e ∧ e < hi then a ⟨e - lo, by omega⟩ else 0 := by
    intro a e
    rw [hGm, Polynomial.finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases h : lo ≤ e ∧ e < hi
    · rw [dif_pos h, Finset.sum_eq_single (⟨e - lo, by omega⟩ : Fin n)]
      · rw [if_pos (by simp only; omega), mul_one]
      · intro i _ hi'
        have : e ≠ lo + (i : ℕ) := by
          intro he; apply hi'; apply Fin.ext; simp only; omega
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : e ≠ lo + (i : ℕ) := by
        intro he; have := i.isLt; omega
      simp [this]
  have hGinj : Function.Injective GmL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext i
    have := hcoef a (lo + (i : ℕ))
    rw [ha, dif_pos (by have := i.isLt; omega)] at this
    simpa using this.symm
  have hGdeg : ∀ a, (GmL a).degree < hi := by
    intro a
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    rw [hcoef, dif_neg (by omega)]
  -- (X-1)^m * G has degree < D
  have hdeg : ∀ a, ((X - 1 : (ZMod p)[X]) ^ m * GmL a) ∈ degreeLT (ZMod p) D := by
    intro a
    rw [Polynomial.mem_degreeLT]
    by_cases hG : GmL a = 0
    · rw [hG, mul_zero]
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe D
    · have hne : ((X - 1 : (ZMod p)[X]) ^ m) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
      rw [Polynomial.degree_mul, Polynomial.degree_pow]
      have h1 : (X - 1 : (ZMod p)[X]).degree = 1 := by
        have : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
        rw [this]; exact Polynomial.degree_X_sub_C 1
      rw [h1]
      have h2 := hGdeg a
      rw [Polynomial.degree_eq_natDegree hG] at h2 ⊢
      have h3 : (GmL a).natDegree < hi := by exact_mod_cast h2
      simp only [nsmul_eq_mul, mul_one]
      have : m + (GmL a).natDegree < D := by omega
      exact_mod_cast this
  let ψC : (Fin n → ZMod p) →ₗ[ZMod p] degreeLT (ZMod p) D :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft (ZMod p) ((X - 1 : (ZMod p)[X]) ^ m)).comp GmL) hdeg
  let wm : (Fin n → ZMod p) →ₗ[ZMod p] (Fin D → ZMod p) :=
    (uBasisEquiv hp2 D).symm.toLinearMap.comp ψC
  have hwm : Function.Injective wm := by
    intro a b hab
    have h1 : ψC a = ψC b := (uBasisEquiv hp2 D).symm.injective hab
    have h2 : ((X - 1 : (ZMod p)[X]) ^ m * GmL a) = (X - 1) ^ m * GmL b := congrArg Subtype.val h1
    have hne : ((X - 1 : (ZMod p)[X]) ^ m) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
    exact hGinj (mul_left_cancel₀ hne h2)
  have hrel : ∀ a, (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D (wm a) = (X ^ p - 1) * GmL a := by
    intro a
    have : uComb p D (wm a) = (X - 1) ^ m * GmL a :=
      uBasisEquiv_symm_comb hp2 D (ψC a)
    rw [this, ← mul_assoc, ← pow_add, show P.h N + m = p by omega, sub_one_pow_p]
  have hsupp : ∀ a e, (GmL a).coeff e ≠ 0 → e < hi := by
    intro a e he
    by_contra hc
    rw [hcoef, dif_neg (by omega)] at he
    exact he rfl
  have hgood : ∀ (d : Fin D) (k : Fin c.K), Good P N p c.k0 d k := fun d k =>
    good_of_ends c.k0 hlow hup d k
  have hz := c.z_ne hcop
  have hS := c.hS
  have key := fam_le_nullity hP hN hp2 hH hq c.k0 (zprof p c.K c.y) hz (by omega) hgood wm hwm
    GmL hi hrel hsupp hhi (by omega) (palindromicRatResidue p c.A) (by
      intro a j hj1 hj2 hne
      have hjH : j < P.H N := lt_of_lt_of_le hj2 (by
        have : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
        omega)
      set ℓ := j % p with hℓdef
      set e0 := idxRes (P.H N) p ℓ with he0def
      have hℓ : ℓ < p := Nat.mod_lt _ hp0
      have he0 := idxRes_lt hp0 (P.H N) ℓ
      have hidx := idx_eq hp0 (P.H N) ℓ
      rw [← he0def] at hidx
      have hrng : lo ≤ e0 ∧ e0 < hi := by
        rw [hcoef] at hne
        by_contra hc
        rw [dif_neg hc] at hne
        exact hne rfl
      obtain ⟨w1, w2, w3, w4⟩ := hwin e0 hrng.1 hrng.2
      -- identify the window and the residue
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
        nlinarith [hS.1, (Fact.out : p.Prime).two_le]))
  have hfr : finrank (ZMod p) (Fin n → ZMod p) = n := by simp
  rw [hfr] at key
  exact key

#print axioms cellC_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.TheoremC
