module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.HyInj
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Sum
@[expose] public section
set_option Elab.async false

/-!
# Theorem HY+ (profiles as input)
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem lamA_dvd (hp2 : p ≠ 2) {Dn : ℕ} (A : Fin Dn → ZMod p) :
    ((X - 1 : (ZMod p)[X]) ^ (P.h N + (p - 1) / 2)) ∣ ∑ t : Fin Dn, C (A t) * hLam P N p (t : ℕ) := by
  refine Finset.dvd_sum fun t _ => dvd_mul_of_dvd_right ?_ _
  unfold hLam
  rw [f_eq_gBasis hp2, pow_add]
  exact mul_dvd_mul_left _ (dvd_mul_right _ _)

theorem lamC_dvd {Dn : ℕ} (f : ℕ) (C' : Fin Dn → ZMod p)
    (h : ((X - 1 : (ZMod p)[X]) ^ f) ∣ ∑ t : Fin Dn, C (C' t) * hmF p (t : ℕ)) :
    ((X - 1 : (ZMod p)[X]) ^ (P.h N + f)) ∣ ∑ t : Fin Dn, C (C' t) * hmLam P N p (t : ℕ) := by
  have : ∑ t : Fin Dn, C (C' t) * hmLam P N p (t : ℕ) =
      (X - 1) ^ P.h N * ∑ t : Fin Dn, C (C' t) * hmF p (t : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [hmLam_eq]; ring
  rw [this, pow_add]
  exact mul_dvd_mul_left _ h

set_option maxHeartbeats 1600000 in
/-- **Theorem HY+ (profiles as input).** -/
theorem hy_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K Dn nQ s a0 η : ℕ} (k0 : ℤ) (hD : Dn ≤ (p - 1) / 2)
    (hph : p ≤ P.q N + (P.h N + (p - 1) / 2))
    (hHη : (P.H N : ℤ) - 1 = η + s * p) (hsp : s < p)
    (hpη : p ≤ η) (hη2 : η < 2 * p) (hem : P.h N + (p - 1) / 2 + Dn ≤ η + p)
    (hQ : a0 + nQ + p ≤ P.h N + (p - 1) / 2 + Dn)
    (u v y : Fin K → ZMod p) (sc : Fin nQ → Fin Dn → ZMod p)
    (hsc : ∀ i : Fin nQ, ∑ t, C (sc i t) * hLam P N p (t : ℕ) =
      X ^ p * ((X - 1) ^ a0 * X ^ (i : ℕ)) - ((X - 1) ^ a0 * X ^ (i : ℕ)))
    (hind : LinearIndependent (ZMod p) ![u, v]) (hy0 : y ≠ 0)
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
        (profHp p K k0).psi (P.H N) J (s : ℤ) v) = κ) :
    Dn + nQ + Dn ≤ nullity P N p +
      (hyMiss P N p K Dn k0 + ((η + 1) - p) + ((P.h N + (p - 1) / 2 + Dn) - (η + 1)) +
        (p - P.q N - P.h N) + (edgeSet P N p a0 nQ s η Dn).card) := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  set f := p - P.q N - P.h N with hf
  set Φ := hyCond P N hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f with hΦ
  have hkd := finrank_ker_hyCond (P := P) (N := N) hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f
  have hker : ∀ a : LinearMap.ker Φ, Φ a.1 = 0 := fun a => LinearMap.mem_ker.mp a.2
  have hξ : ∀ a : LinearMap.ker Φ,
      ((xi u v y sc).comp (LinearMap.ker Φ).subtype) a ∈ (hySys P N p hp2 K Dn k0 hD).dom := by
    intro a
    show xi u v y sc a.1 ∈ hyDom P N p K Dn k0
    rw [mem_hyDom]
    refine ⟨?_, ?_, fun t k h => ker_lo hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) t k h,
      fun t k h => ker_hi hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) t k h⟩
    · funext t κ'
      show xd u v y sc a.1 (Fin.castAdd Dn t) (Fin.natAdd K κ') = 0
      simp only [xd, Fin.addCases_left, Fin.addCases_right]
    · funext t κ'
      show xd u v y sc a.1 (Fin.natAdd Dn t) (Fin.castAdd K κ') = 0
      simp only [xd, Fin.addCases_left, Fin.addCases_right]
  have hξi : Function.Injective ((xi u v y sc).comp (LinearMap.ker Φ).subtype) :=
    (xi_injective a0 u v y sc hsc hind hy0).comp (Submodule.subtype_injective _)
  have hmain := (hySys P N p hp2 K Dn k0 hD).slot_nullity_jflat0 hP hN hp2 hH
    ((xi u v y sc).comp (LinearMap.ker Φ).subtype) hξ hξi (p - P.q N)
    (LinearMap.pi fun ℓ : ZMod p =>
      (rhoL P N p Dn nQ γu γy η ℓ.val).comp (LinearMap.ker Φ).subtype)
    (fun a => by
      have hjet : ∀ i < f, (taylor 1 (∑ t : Fin Dn, C (a.1.2.2 t) * hmF p (t : ℕ))).coeff i = 0 :=
        fun i hi => ker_jet hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) i hi
      have hdC := lamC_dvd (P := P) (N := N) f a.1.2.2 (X_sub_one_pow_dvd_of_jets f _ hjet)
      have hdA := lamA_dvd (P := P) (N := N) hp2 a.1.1
      obtain ⟨fp, hfp⟩ : ∃ fp : (ZMod p)[X], fp = C γu * (∑ t : Fin Dn, C (a.1.1 t) * hLam P N p (t : ℕ)) +
          C γy * (∑ t : Fin Dn, C (a.1.2.2 t) * hmLam P N p (t : ℕ)) := ⟨_, rfl⟩
      have hdvd : ((X - 1 : (ZMod p)[X]) ^ (p - P.q N)) ∣ fp := by
        rw [hfp]
        exact dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans hdA) _)
          (dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans hdC) _)
      have hcoef : ∀ e, fp.coeff e = γu * aco P N p a.1.1 e + γy * cco P N p a.1.2.2 e := by
        intro e; rw [hfp]; simp [aco, cco, coeff_add, coeff_C_mul]
      have hdeg : fp.natDegree < η + p := by
        have : fp.natDegree ≤ η + p - 1 := by
          rw [natDegree_le_iff_coeff_eq_zero]
          intro e he
          rw [hcoef, aco_zero hp2 hD _ e (by omega), cco_zero hp2 hD _ e (by omega)]; simp
        omega
      obtain ⟨G, hG, hGe⟩ := fold3_poly (v := p - P.q N) (by omega) hpη hη2 fp hdvd hdeg
      refine ⟨G, hG, fun x => ?_⟩
      rw [← hGe x]
      have hxl := ZMod.val_lt x
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, rhoL_apply,
        foldco, hcoef]
      have e1 : η - x.val + p = η + p - x.val := by omega
      have e2 : η - x.val - p = η - p - x.val := by omega
      rw [e1, e2]
      by_cases hc : p + x.val ≤ η
      · have hc' : p ≤ η - x.val := by omega
        simp only [if_pos hc, if_pos hc']; ring
      · have hc' : ¬ p ≤ η - x.val := by omega
        simp only [if_neg hc, if_neg hc']; ring)
    (fun a j h1 h2 => by
      have hℓ : j % p < p := Nat.mod_lt _ hp0
      have hval : ((j : ℕ) : ZMod p).val = j % p := ZMod.val_natCast ..
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hval, rhoL_apply]
      by_cases hb : HyBad (P.h N + (p - 1) / 2 + Dn) a0 nQ s p η (j % p) (j / p)
      · refine ker_edge hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a)
          (j % p, j / p) ?_
        have hd := Nat.div_add_mod' j p
        have hdl : j / p ≤ P.L N / p := Nat.div_le_div_right h2.le
        simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hℓ, by omega⟩, by omega, by omega, hb⟩
      · refine col_main hp2 k0 hD a0 u v y sc hsc a.1 (j / p) (j % p) η s hp0 hℓ hpη hη2 hem hQ hHη hsp
          γu γy Ψu Ψy Ψu' Ψy' κ hu1 hy1 hv1 hu2 hy2 hu3 hy3 hv3
          (fun e he => ker_sp hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) e he)
          (fun e he1 he2 => ?_) hb
        by_cases he : e < P.h N + (p - 1) / 2 + Dn
        · exact ker_sm hp2 k0 hD a0 u v y sc γu γy Ψu Ψy Ψu' Ψy' κ η s f a.1 (hker a) e he1 he
        · rw [aco_zero hp2 hD _ e (by omega), cco_zero hp2 hD _ e (by omega),
            Qpoly_coeff_zero a0 nQ _ (e - p) (by omega)]
          simp)
  rw [Nat.sub_self, Nat.sub_zero] at hmain
  have hm2 : finrank (ZMod p) (LinearMap.ker Φ) ≤ nullity P N p := hmain
  rw [hΦ] at hm2
  omega


end
end CatalanMeasure.GenD.Uniform.W.HYPlus
