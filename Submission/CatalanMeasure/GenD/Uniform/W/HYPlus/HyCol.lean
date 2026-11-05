module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyResp
@[expose] public section
set_option Elab.async false

/-!
# The column identity: response = folded coefficient, away from the edge digits
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The folded coefficient `g[η-ℓ] + [p ≤ η-ℓ] g[η-ℓ-p] + g[η-ℓ+p]`. -/
def foldco (p η ℓ : ℕ) (g : ℕ → ZMod p) : ZMod p :=
  g (η - ℓ) + (if p ≤ η - ℓ then g (η - ℓ - p) else 0) + g (η - ℓ + p)

/-- The edge predicate: digit `J` at residue `ℓ` meets a present coefficient outside its good range. -/
def HyBad (emax a0 nQ s p η ℓ J : ℕ) : Prop :=
  (η - ℓ < emax ∧ ¬ (1 ≤ J ∧ J + 1 ≤ s)) ∨
  (p ≤ η - ℓ ∧ ¬ (2 ≤ J ∧ J ≤ s)) ∨
  ((p ≤ η - ℓ ∧ η - ℓ - p < a0 + nQ) ∧ ¬ (2 ≤ J ∧ J + 1 ≤ s)) ∨
  (η - ℓ + p < emax ∧ ¬ (J + 2 ≤ s)) ∨
  (η - ℓ < a0 + nQ ∧ ¬ (1 ≤ J ∧ J + 2 ≤ s))

instance (emax a0 nQ s p η ℓ J : ℕ) : Decidable (HyBad emax a0 nQ s p η ℓ J) := by
  unfold HyBad; infer_instance

theorem alg_col {F : Type*} [CommRing F] (γu γy pu0 pu1 pu2 pv0 pv1 pv2 py0 py1 py2
    a0 a1 a2 c0 c1 c2 Qm Qz : F)
    (h0 : a0 * pu0 + c0 * py0 = a0 * γu + c0 * γy)
    (h1 : a1 * pu1 + c1 * py1 = a1 * γu + c1 * γy)
    (h3 : Qm * pv0 = Qm * pv1)
    (h2 : a2 * pu2 + c2 * py2 + Qz * (pv2 - pv0) = a2 * γu + c2 * γy) :
    (a0 * pu0 + (Qm - Qz) * pv0 + c0 * py0) + (a1 * pu1 + -Qm * pv1 + c1 * py1) +
      (a2 * pu2 + Qz * pv2 + c2 * py2) = γu * (a0 + a1 + a2) + γy * (c0 + c1 + c2) := by
  linear_combination h0 + h1 + h2 + h3

/-- Cancel a nonzero factor. -/
theorem cancel_nz {F : Type*} [Field F] (J x : F) (hJ : J ≠ 0) (h : J * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_left hJ

theorem natCast_ne_zero_of_lt {J : ℕ} (hJ : 0 < J) (hJp : J < p) : (J : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff J p).mp h
  exact absurd (Nat.le_of_dvd hJ this) (by omega)

variable (hp2 : p ≠ 2) {K Dn nQ : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2) (a0 : ℕ)
  (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
  (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
    X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))

theorem bco_eq (c : Fin nQ → ZMod p) (e : ℕ) :
    bco p a0 nQ c e = (if p ≤ e then (Qpoly p a0 nQ c).coeff (e - p) else 0) -
      (Qpoly p a0 nQ c).coeff e := by
  unfold bco; exact lc_period _ e

include hsc in
theorem col_main (a : HyA p Dn nQ) (J ℓ η s : ℕ) (hp0 : 0 < p) (hℓ : ℓ < p) (hpη : p ≤ η)
    (hη2 : η < 2 * p) (hem : P.h N + (p - 1) / 2 + Dn ≤ η + p)
    (hQ : a0 + nQ + p ≤ P.h N + (p - 1) / 2 + Dn) (hHη : (P.H N : ℤ) - 1 = η + s * p)
    (hsp : s < p)
    (γu γy Ψu Ψy Ψu' Ψy' κ : ZMod p)
    (hu1 : ∀ J, 1 ≤ J → J ≤ s - 1 → (profHp p K k0).psi (P.H N) J (s : ℤ) u = γu)
    (hy1 : ∀ J, 1 ≤ J → J ≤ s - 1 → (profHm p K k0).psi (P.H N) J (s : ℤ) y = γy)
    (hv1 : ∀ J, 2 ≤ J → J ≤ s - 1 →
      (profHp p K k0).psi (P.H N) J (s : ℤ) v = (profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) v)
    (hu2 : ∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) u - γu) = Ψu)
    (hy2 : ∀ J, 2 ≤ J → J ≤ s →
      (J : ZMod p) * ((profHm p K k0).psi (P.H N) J ((s : ℤ) + 1) y - γy) = Ψy)
    (hu3 : ∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γu - (profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) u) = Ψu')
    (hy3 : ∀ J, J + 2 ≤ s →
      ((J : ZMod p) + 1) * (γy - (profHm p K k0).psi (P.H N) J ((s : ℤ) - 1) y) = Ψy')
    (hv3 : ∀ J, 1 ≤ J → J + 2 ≤ s →
      ((J : ZMod p) + 1) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) v -
        (profHp p K k0).psi (P.H N) J (s : ℤ) v) = κ)
    (hSp : ∀ e, e + p ≤ η → Ψu * aco P N p a.1 e + Ψy * cco P N p a.2.2 e = 0)
    (hSm : ∀ e, η < e → e ≤ η + p →
      Ψu' * aco P N p a.1 e - κ * (Qpoly p a0 nQ a.2.1).coeff (e - p) +
        Ψy' * cco P N p a.2.2 e = 0)
    (hgood : ¬ HyBad (P.h N + (p - 1) / 2 + Dn) a0 nQ s p η ℓ J) :
    (hySys P N p hp2 K Dn k0 hD).resp J ℓ (xd u v y sc a) =
      γu * foldco p η ℓ (aco P N p a.1) + γy * foldco p η ℓ (cco P N p a.2.2) := by
  rw [resp_atom hp2 k0 hD a0 u v y sc hsc a J ℓ η s hp0 hℓ hpη hη2 hem hQ hHη]
  set emax := P.h N + (p - 1) / 2 + Dn with hemax
  set Qc := Qpoly p a0 nQ a.2.1 with hQc
  have hℓη : ℓ ≤ η := by omega
  set e0 := η - ℓ with he0
  have g1 : e0 < emax → (1 ≤ J ∧ J + 1 ≤ s) := fun h => by
    by_contra hn; exact hgood (Or.inl ⟨h, hn⟩)
  have g2 : p ≤ e0 → (2 ≤ J ∧ J ≤ s) := fun h => by
    by_contra hn; exact hgood (Or.inr (Or.inl ⟨h, hn⟩))
  have g3 : (p ≤ e0 ∧ e0 - p < a0 + nQ) → (2 ≤ J ∧ J + 1 ≤ s) := fun h => by
    by_contra hn; exact hgood (Or.inr (Or.inr (Or.inl ⟨h, hn⟩)))
  have g4 : e0 + p < emax → J + 2 ≤ s := fun h => by
    by_contra hn; exact hgood (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hn⟩))))
  have g5 : e0 < a0 + nQ → (1 ≤ J ∧ J + 2 ≤ s) := fun h => by
    by_contra hn; exact hgood (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hn⟩))))
  have hQz : a0 + nQ ≤ η := by omega
  -- the b-coefficients
  have hbq2 : bco p a0 nQ a.2.1 (e0 + p) = Qc.coeff e0 := by
    rw [bco_eq, if_pos (by omega), Nat.add_sub_cancel, hQc, Qpoly_coeff_zero a0 nQ _ (e0 + p) (by omega)]
    simp
  have hbq0 : bco p a0 nQ a.2.1 e0 =
      (if p ≤ e0 then Qc.coeff (e0 - p) else 0) - Qc.coeff e0 := bco_eq a0 _ e0
  have hcJ : ∀ J' : ℕ, 0 < J' → J' < p → (J' : ZMod p) ≠ 0 := fun J' h1 h2 =>
    natCast_ne_zero_of_lt h1 h2
  have hJs : ∀ J' : ℕ, J' + 1 ≤ s → ((J' : ZMod p) + 1) ≠ 0 := fun J' h => by
    have := natCast_ne_zero_of_lt (p := p) (J := J' + 1) (by omega) (by omega)
    simpa using this
  -- h0
  have h0 : aco P N p a.1 e0 * (profHp p K k0).psi (P.H N) J (s : ℤ) u +
      cco P N p a.2.2 e0 * (profHm p K k0).psi (P.H N) J (s : ℤ) y =
      aco P N p a.1 e0 * γu + cco P N p a.2.2 e0 * γy := by
    by_cases hS : e0 < emax
    · obtain ⟨j1, j2⟩ := g1 hS
      rw [hu1 J j1 (by omega), hy1 J j1 (by omega)]
    · rw [aco_zero hp2 hD _ e0 (by omega), cco_zero hp2 hD _ e0 (by omega)]; simp
  -- h2
  have h2 : aco P N p a.1 (e0 + p) * (profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) u +
      cco P N p a.2.2 (e0 + p) * (profHm p K k0).psi (P.H N) J ((s : ℤ) - 1) y +
      Qc.coeff e0 * ((profHp p K k0).psi (P.H N) J ((s : ℤ) - 1) v -
        (profHp p K k0).psi (P.H N) J (s : ℤ) v) =
      aco P N p a.1 (e0 + p) * γu + cco P N p a.2.2 (e0 + p) * γy := by
    by_cases hS : e0 + p < emax
    · have j4 := g4 hS
      have k3 := hu3 J j4
      have k4 := hy3 J j4
      have k5 := hSm (e0 + p) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at k5
      apply sub_eq_zero.mp
      apply cancel_nz _ _ (hJs J (by omega))
      by_cases hb : e0 < a0 + nQ
      · obtain ⟨j5, j6⟩ := g5 hb
        have k6 := hv3 J j5 j6
        linear_combination (-1 : ZMod p) * k3 * aco P N p a.1 (e0 + p) -
          cco P N p a.2.2 (e0 + p) * k4 + Qc.coeff e0 * k6 - k5
      · have hz : Qc.coeff e0 = 0 := by
          rw [hQc]; exact Qpoly_coeff_zero a0 nQ _ e0 (by omega)
        rw [hz] at k5 ⊢
        linear_combination (-1 : ZMod p) * k3 * aco P N p a.1 (e0 + p) -
          cco P N p a.2.2 (e0 + p) * k4 - k5
    · have hz : Qc.coeff e0 = 0 := by
        rw [hQc]; exact Qpoly_coeff_zero a0 nQ _ e0 (by omega)
      rw [aco_zero hp2 hD _ _ (by omega), cco_zero hp2 hD _ _ (by omega), hz]; simp
  by_cases hc : p ≤ e0
  · -- h1
    have h1 : aco P N p a.1 (e0 - p) * (profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) u +
        cco P N p a.2.2 (e0 - p) * (profHm p K k0).psi (P.H N) J ((s : ℤ) + 1) y =
        aco P N p a.1 (e0 - p) * γu + cco P N p a.2.2 (e0 - p) * γy := by
      obtain ⟨j1, j2⟩ := g2 hc
      have k1 := hu2 J j1 j2
      have k2 := hy2 J j1 j2
      have k3 := hSp (e0 - p) (by omega)
      apply sub_eq_zero.mp
      apply cancel_nz _ _ (hcJ J (by omega) (by omega))
      linear_combination aco P N p a.1 (e0 - p) * k1 + cco P N p a.2.2 (e0 - p) * k2 + k3
    have h3 : (if p ≤ e0 then Qc.coeff (e0 - p) else 0) *
        (profHp p K k0).psi (P.H N) J (s : ℤ) v =
        (if p ≤ e0 then Qc.coeff (e0 - p) else 0) *
        (profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) v := by
      rw [if_pos hc]
      by_cases hb : e0 - p < a0 + nQ
      · obtain ⟨j1, j2⟩ := g3 ⟨hc, hb⟩
        rw [hv1 J j1 (by omega)]
      · rw [hQc, Qpoly_coeff_zero a0 nQ _ (e0 - p) (by omega)]; simp
    have hbq1 : bco p a0 nQ a.2.1 (e0 - p) = -Qc.coeff (e0 - p) := by
      rw [bco_eq, if_neg (by omega)]; ring
    have key := alg_col γu γy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h3 h2
    simp only [tmv, foldco, ← he0, if_pos hc, hbq0, hbq1, hbq2]
    simp only [if_pos hc] at key
    linear_combination key
  · have h3 : (0 : ZMod p) * (profHp p K k0).psi (P.H N) J (s : ℤ) v =
        0 * (profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) v := by simp
    have key := alg_col γu γy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0
      (show (0 : ZMod p) * ((profHp p K k0).psi (P.H N) J ((s : ℤ) + 1) u) +
        0 * (profHm p K k0).psi (P.H N) J ((s : ℤ) + 1) y = 0 * γu + 0 * γy by simp) h3 h2
    simp only [tmv, foldco, ← he0, if_neg hc, hbq0, hbq2]
    linear_combination key

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
