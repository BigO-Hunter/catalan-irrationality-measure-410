module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HSystem
@[expose] public section
set_option Elab.async false

/-!
# The H+ slot system
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The virtual H+ pairs. -/
def hBad (P : Parameters) (N p : ℕ) [Fact p.Prime] (K D : ℕ) (k0 : ℤ) :
    Finset (Fin D × Fin K) :=
  Finset.univ.filter (fun tk : Fin D × Fin K => ¬ HGood P N p k0 tk.1 tk.2)

/-- Number of virtual H+ pairs. -/
def hVirt (P : Parameters) (N p : ℕ) [Fact p.Prime] (K D : ℕ) (k0 : ℤ) : ℕ :=
  (hBad P N p K D k0).card

theorem U_natDegree_le (hp2 : p ≠ 2) (n : ℕ) : (Chebyshev.U (ZMod p) (n : ℤ)).natDegree ≤ n := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  exact (Chebyshev.natDegree_U_natCast (R := ZMod p) n).le

theorem hLam_natDegree_lt (hp2 : p ≠ 2) {D : ℕ} (hD : D ≤ (p - 1) / 2) (t : Fin D) :
    (hLam P N p t).natDegree < P.h N + (p - 1) / 2 + D := by
  have ht := t.isLt
  unfold hLam
  have e1 : hh p - (t : ℕ) - 1 = (((p - 1) / 2 - t - 1 : ℕ) : ℤ) := by unfold hh; omega
  have e2 : hh p + (t : ℕ) = (((p - 1) / 2 + t : ℕ) : ℤ) := by unfold hh; omega
  rw [e1, e2]
  have a : ((X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
    refine natDegree_pow_le.trans ?_
    have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
    nlinarith
  have b : (Chebyshev.U (ZMod p) (((p - 1) / 2 - t - 1 : ℕ) : ℤ) +
      Chebyshev.U (ZMod p) (((p - 1) / 2 + t : ℕ) : ℤ)).natDegree ≤ (p - 1) / 2 + t := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (U_natDegree_le hp2 _).trans (by omega)
    · exact U_natDegree_le hp2 _
  have c := natDegree_mul_le (p := ((X - 1) ^ P.h N : (ZMod p)[X]))
    (q := Chebyshev.U (ZMod p) (((p - 1) / 2 - t - 1 : ℕ) : ℤ) +
      Chebyshev.U (ZMod p) (((p - 1) / 2 + t : ℕ) : ℤ))
  omega

/-- The H+ pair slot system. -/
def hSystem (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (K D : ℕ) (k0 : ℤ)
    (hD : D ≤ (p - 1) / 2) : SlotSystem P N p where
  K := K
  D := D
  emax := P.h N + (p - 1) / 2 + D
  prof := ⟨hTy p K k0, hGy p K k0⟩
  lam := fun t => hLam P N p t
  rows := hRows P N p K D k0
  dom := badDom p K D (hBad P N p K D k0)
  deg := fun t => hLam_natDegree_lt hp2 hD t
  repU := fun x hx => by
    have hx' : ∀ t k, ¬ HGood P N p k0 t k → x t k = 0 :=
      fun t k hg => hx ⟨t, k⟩ (by simp [hBad, hg])
    have h := sum_hPairRows (P := P) (N := N) k0 x hx' (fun m => Chebyshev.U (ZMod p) (m - 1))
    unfold intrinsicU
    rw [show (∑ r : Fin (P.n N), C (hRows P N p K D k0 x r) *
        Chebyshev.U (ZMod p) ((r.val : ℤ) - P.g N - 1)) = _ from h]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    show _ = hLam P N p t * (hTy p K k0 (x t)).comp (X ^ p)
    rw [hTy_apply, sum_comp', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := hU_pair hp2 ((k0 : ℤ) + (k : ℕ)) (t : ℕ)
    have e' : Chebyshev.U (ZMod p) (hlo p K k0 k t - 1) +
        Chebyshev.U (ZMod p) (hhi p K k0 k t - 1) =
        ((Chebyshev.U (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) +
          (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) *
          (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) := by
      unfold hlo hhi cen; exact e
    rw [mul_comm (C (x t k)) _, mul_comm (C (x t k)) _]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.add_comp]
    unfold hLam
    rw [mul_add, e']
    ring
  repT := fun x hx => by
    have hx' : ∀ t k, ¬ HGood P N p k0 t k → x t k = 0 :=
      fun t k hg => hx ⟨t, k⟩ (by simp [hBad, hg])
    have h := sum_hPairRows (P := P) (N := N) k0 x hx' (fun m => Chebyshev.T (ZMod p) m)
    unfold intrinsicT
    rw [show (∑ r : Fin (P.n N), C (hRows P N p K D k0 x r) *
        Chebyshev.T (ZMod p) ((r.val : ℤ) - P.g N)) = _ from h]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    show _ = hLam P N p t * (hGy p K k0 (x t)).comp (X ^ p)
    rw [hGy_apply, sum_comp']
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := hT_pair hp2 ((k0 : ℤ) + (k : ℕ)) (t : ℕ)
    have e' : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2) *
        (Chebyshev.T (ZMod p) (hlo p K k0 k t) + Chebyshev.T (ZMod p) (hhi p K k0 k t)) =
        (1 + X ^ p) * ((Chebyshev.U (ZMod p) (k0 + (k : ℕ))).comp (X ^ p) -
          (Chebyshev.U (ZMod p) (k0 + (k : ℕ) - 1)).comp (X ^ p)) *
          (Chebyshev.U (ZMod p) (hh p - t - 1) + Chebyshev.U (ZMod p) (hh p + t)) := by
      unfold hlo hhi cen; exact e
    unfold hLam
    simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp]
    linear_combination ((X - 1) ^ P.h N * C (x t k)) * e'
  inj := fun x hx h0 => hRows_injective_on hp2 hD k0 x
    (fun t k hg => hx ⟨t, k⟩ (by simp [hBad, hg])) h0

theorem hSystem_psi (hp2 : p ≠ 2) {K D : ℕ} (k0 : ℤ) (hD : D ≤ (p - 1) / 2) (H J : ℕ) (a : ℤ)
    (y : Fin K → ZMod p) :
    (hSystem P N p hp2 K D k0 hD).prof.psi H J a y =
      digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J) (hGy p K k0 y) (hTy p K k0 y) (3 / 2) :=
  rfl

end
end CatalanMeasure.GenD.Uniform.W.Slots
