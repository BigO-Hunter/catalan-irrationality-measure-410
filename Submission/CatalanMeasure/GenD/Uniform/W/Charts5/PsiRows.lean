module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.Prof146
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Unique146
@[expose] public section
set_option Elab.async false

/-!
# The psi-row identity for the stored raw rows of `packetO`

For `J = 1..11`, `S ∈ {12, 11}` the stored rows `raw[J,d]` satisfy
`r_c · Zmom = D · rowInt pd146 Zmom J S c` (`c < 42`, `D = -r_42`), `r_42 = -D`, `r_43 = ε r_42`,
hence for `p ∤ Zmom` and a vector in the kernel of the row: `ψ(J,S)(y) = y_42 + ε y_43`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- The moment denominator used for the rows. -/
abbrev ZM : ℕ := Zmom 15 12

/-- Row `i` of stored chart `g` is `D · (ψ(J,S) on slot coordinates, -1 on jet_0, -ε on @low)` (scaled). -/
def rowOK (g i J : ℕ) (S : ℤ) (ε : ℤ) : Bool :=
  let r := (oRows g).getD i []
  decide (i < (oRows g).length) && decide (r.getD 42 0 < 0) &&
    decide ((2310 ^ 40 : ℤ) % (r.getD 42 0) = 0) &&
    decide (r.getD 43 0 = ε * r.getD 42 0) &&
    (List.range 42).all (fun c => decide (r.getD c 0 * (ZM : ℤ) = -(r.getD 42 0) * rowInt pd146 ZM J S c)) &&
    decide (rowInt pd146 ZM J S 42 = 0) && decide (rowInt pd146 ZM J S 43 = 0)

theorem ZM_dvd : ZM ∣ 30030 ^ 10 := by decide +kernel

theorem not_dvd_ZM {p : ℕ} [Fact p.Prime] (hp : 13 < p) : ¬ p ∣ ZM := by
  intro h
  have h1 : p ∣ 30030 ^ 10 := h.trans ZM_dvd
  have hpn := (Fact.out : p.Prime)
  have h2 : p ∣ 30030 := hpn.dvd_of_dvd_pow h1
  have e : (30030 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 := by norm_num
  rw [e] at h2
  rcases (Nat.Prime.dvd_mul hpn).mp h2 with h | h
  · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) h; omega
          · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

set_option maxRecDepth 100000 in
theorem rows_ok :
    (rowOK 1 0 1 12 0 = true) ∧
    (∀ J : Fin 9, rowOK 2 J.val (J.val + 2) 12 0 = true) ∧
    (∀ J : Fin 9, rowOK 1 (J.val + 1) (J.val + 2) 12 0 = true) ∧
    (rowOK 1 10 11 12 1 = true) ∧ (rowOK 2 9 11 12 1 = true) ∧
    (∀ J : Fin 10, rowOK 6 J.val (J.val + 1) 11 0 = true) := by decide +kernel

theorem psi_row {p : ℕ} [Fact p.Prime] (hp : 13 < p) (F : Prof p 44) (hF : pd146.Realises F)
    {g i J : ℕ} {S : ℤ} {ε : ℤ} {H : ℕ}
    (hok : rowOK g i J S ε = true) (hJ : J < 12) (hS : S.toNat + 3 ≤ 15) (hH : S.toNat + 3 ≤ H)
    (y : Fin 44 → ZMod p)
    (hy : ∑ c : Fin 44, ((((oRows g).getD i []).getD c 0 : ℤ) : ZMod p) * y c = 0) :
    F.psi H J S y = y 42 + (ε : ZMod p) * y 43 := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨hi, hneg⟩, hdvd⟩, hε⟩, hall⟩, h42⟩, h43⟩ := hok
  set r := (oRows g).getD i [] with hr
  have hZp : ¬ p ∣ ZM := not_dvd_ZM hp
  have hZ : ((ZM : ℕ) : ZMod p) ≠ 0 := fun h => hZp ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hD : ((r.getD 42 0 : ℤ) : ZMod p) ≠ 0 :=
    unit_of_dvd _ (Int.dvd_of_emod_eq_zero hdvd) (by omega)
  have hm : ∀ c : Fin 44, ((rowInt pd146 ZM J S c : ℤ) : ZMod p) = (ZM : ZMod p) * F.psi H J S (Pi.single c 1) :=
    fun c => rowInt_mod (Ub := 15) (Jb := 12) hZp pd146 F hF c hJ hS hH
  have hpsi0 : ∀ c : Fin 44, 42 ≤ c.val → F.psi H J S (Pi.single c 1) = 0 := by
    intro c hc
    have : c.val = 42 ∨ c.val = 43 := by omega
    have h0 : rowInt pd146 ZM J S c = 0 := by
      rcases this with h | h
      · rw [h]; exact h42
      · rw [h]; exact h43
    have := hm c
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hZ
  have hrow : ∀ c : Fin 44, c.val < 42 →
      ((r.getD c 0 : ℤ) : ZMod p) = -((r.getD 42 0 : ℤ) : ZMod p) * F.psi H J S (Pi.single c 1) := by
    intro c hc
    have e := hall c.val hc
    have e' := congrArg (fun z : ℤ => (z : ZMod p)) e
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] at e'
    rw [hm c] at e'
    apply mul_right_cancel₀ hZ
    simp only [ZM] at e' ⊢
    linear_combination e'
  have hcoef : ∀ c : Fin 44, ((r.getD c 0 : ℤ) : ZMod p) =
      -((r.getD 42 0 : ℤ) : ZMod p) * F.psi H J S (Pi.single c 1) +
        (if c = 42 then ((r.getD 42 0 : ℤ) : ZMod p) else 0) +
        (if c = 43 then ((r.getD 43 0 : ℤ) : ZMod p) else 0) := by
    intro c
    by_cases hc : c.val < 42
    · have h1 : c ≠ 42 := fun h => by rw [h] at hc; simp at hc
      have h2 : c ≠ 43 := fun h => by rw [h] at hc; simp at hc
      rw [if_neg h1, if_neg h2, hrow c hc]; ring
    · rw [hpsi0 c (by omega)]
      by_cases h1 : c = 42
      · subst h1; simp
      · have h2 : c = 43 := by
          have : c.val = 43 := by
            have := c.isLt
            have h1' : c.val ≠ 42 := fun h => h1 (Fin.ext h)
            omega
          exact Fin.ext this
        subst h2; simp
  have hlin : F.psi H J S y = ∑ c : Fin 44, y c * F.psi H J S (Pi.single c 1) := by
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ (F.psi H J S) y]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_eq_mul]
    congr 2
    funext j
    by_cases h : j = c
    · subst h; simp [Pi.single_apply]
    · simp [Pi.single_apply, h, Ne.symm h]
  have hsum : ∑ c : Fin 44, ((r.getD c 0 : ℤ) : ZMod p) * y c =
      -((r.getD 42 0 : ℤ) : ZMod p) * F.psi H J S y + ((r.getD 42 0 : ℤ) : ZMod p) * y 42 +
        ((r.getD 43 0 : ℤ) : ZMod p) * y 43 := by
    have h1 : ∀ c : Fin 44, ((r.getD c 0 : ℤ) : ZMod p) * y c =
        -((r.getD 42 0 : ℤ) : ZMod p) * (y c * F.psi H J S (Pi.single c 1)) +
          (if c = 42 then ((r.getD 42 0 : ℤ) : ZMod p) * y c else 0) +
          (if c = 43 then ((r.getD 43 0 : ℤ) : ZMod p) * y c else 0) := by
      intro c; rw [hcoef c]; split_ifs <;> ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hlin]
    simp
  rw [hsum, hε] at hy
  push_cast at hy
  apply mul_left_cancel₀ hD
  linear_combination -hy

end
end CatalanMeasure.GenD.Uniform.W.Charts5
