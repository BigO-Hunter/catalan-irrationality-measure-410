module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.HdomSound
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Geometry of the window from certificates
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.Parametric

def geomCheck (m : Meta) (win : List Aff) (cs : Cert) : Bool :=
  holds win cs (jaA m) && holds win cs (pAff.sub ⟨0, 0, 1⟩ |>.sub (jaA m)) &&
  holds win cs (rhoA m) && holds win cs (pAff.sub ⟨0, 0, 1⟩ |>.sub (rhoA m)) &&
  holds win cs (pAff.sub (rA.add ⟨0, 0, 1⟩)) && decide (0 < m.win.1) && decide (0 < m.b)

theorem geom_sound (m : Meta) (win : List Aff) (cs : Cert) (N p : ℕ) (hodd : p % 2 = 1)
    (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hN : m.win.1 ≤ N) (h : geomCheck m win cs = true) :
    0 < N ∧ gk0 (dsg.g N) p = m.k0 ∧ gk1 (dsg.n N) (dsg.g N) p = m.k0 + m.b - 1 ∧ bN dsg N p = m.b ∧
      dsg.h N % p = 3 * N ∧
      ((gja (dsg.g N) p : ℕ) : ℤ) = (jaA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) ∧
      ((grho (dsg.n N) (dsg.g N) p : ℕ) : ℤ) = (rhoA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
  simp only [geomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have e1 := holds_sound win cs _ _ _ hwin h1
  have e2 := holds_sound win cs _ _ _ hwin h2
  have e3 := holds_sound win cs _ _ _ hwin h3
  have e4 := holds_sound win cs _ _ _ hwin h4
  have e5 := holds_sound win cs _ _ _ hwin h5
  have hN0 : 0 < N := by omega
  have hpe : (p : ℤ) = 2 * (((p : ℤ) - 1) / 2) + 1 := by omega
  generalize hhp : ((p : ℤ) - 1) / 2 = hp' at hpe e1 e2 e3 e4 e5 ⊢
  simp only [Aff.eval_sub, Aff.sub, Aff.add, jaA, rhoA, pAff, rA, Aff.eval] at e1 e2 e3 e4 e5 ⊢
  have key : ∀ q : ℤ, q * (p : ℤ) = 2 * q * hp' + q := fun q => by linear_combination q * hpe
  have hp0 : (0 : ℤ) < p := by omega
  have hp0n : 0 < p := by omega
  have k0p := key m.k0
  have k1p := key (m.k0 + m.b - 1)
  have j0 : 0 ≤ -(5 * (N : ℤ)) - m.k0 * p := by nlinarith
  have j1 : -(5 * (N : ℤ)) - m.k0 * p < p := by nlinarith
  have r0 : 0 ≤ 53 * (N : ℤ) - 1 - (m.k0 + m.b - 1) * p := by nlinarith
  have r1 : 53 * (N : ℤ) - 1 - (m.k0 + m.b - 1) * p < p := by nlinarith
  have hk0 : gk0 (dsg.g N) p = m.k0 := by
    unfold gk0
    rw [Pilot146O.design_g]
    exact ((Int.ediv_emod_unique (r := -(5 * (N : ℤ)) - m.k0 * p) hp0).mpr
      ⟨by push_cast; ring, j0, j1⟩).1
  have hk1 : gk1 (dsg.n N) (dsg.g N) p = m.k0 + m.b - 1 := by
    unfold gk1
    rw [Pilot146O.design_n, Pilot146O.design_g]
    exact ((Int.ediv_emod_unique (r := 53 * (N : ℤ) - 1 - (m.k0 + m.b - 1) * p) hp0).mpr
      ⟨by push_cast; ring, r0, r1⟩).1
  refine ⟨hN0, hk0, hk1, ?_, ?_, ?_, ?_⟩
  · show gb (dsg.n N) (dsg.g N) p = m.b
    unfold gb; rw [hk0, hk1]; omega
  · rw [Pilot146O.design_h]; exact Nat.mod_eq_of_lt (by omega)
  · have := (gja_spec (g := dsg.g N) hp0n).1
    rw [this, hk0, Pilot146O.design_g]; push_cast; linear_combination (-m.k0) * hpe + (0:ℤ)
  · unfold grho
    rw [hk1, Pilot146O.design_n, Pilot146O.design_g]
    have : (0 : ℤ) ≤ ((58 * N : ℕ) : ℤ) - 1 - ((5 * N : ℕ) : ℤ) - (m.k0 + m.b - 1) * p := by push_cast; linarith
    rw [Int.toNat_of_nonneg this]; push_cast; linear_combination (-(m.k0 + m.b - 1)) * hpe

end CatalanMeasure.GenD.Uniform.W.Charts6.Check
