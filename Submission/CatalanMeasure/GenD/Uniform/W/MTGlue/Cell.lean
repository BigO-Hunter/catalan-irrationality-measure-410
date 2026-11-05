module
public import Submission.CatalanMeasure.GenD.Uniform.W.MTGlue.Transfer
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueLB
@[expose] public section
set_option Elab.async false

/-!
# A rational glue cell gives `MTGlueOK` at every prime coprime to the cell modulus

`GlueCell` is the rational certificate of Theorem MT (b), `m = 1`: an integer profile pair `(y, u)` on blocks
`k0, …, k0 + K - 1`, constants `(A, B)`, and the equations over `ℚ` on explicit digit sets,

* `Φ-(J, s; y) = A`, `Φ+'(J, s; u) = B` for `J ∈ J1`,
* `Φ-(J, s+1; y) + Φ+'(J, s+1; u) = A + B` for `J ∈ J2`,

with all digits `< 18` and `s ≤ 18`.  `cellMod c = ZmG · |y_{ky}| · |u_{ku}|` is the bad-prime integer
(**Lemma B**): for `Nat.Coprime p (cellMod c)` the equations hold in `ZMod p`
(`ZmG` makes the moment denominators units; the two other factors keep `y`, `u` nonzero mod `p`).
`glueCell_ok` turns this into `SlotsT.MTGlueOK` once the design inequalities and the digit coverage
(`GlueWin`) hold.
-/

namespace CatalanMeasure.GenD.Uniform.W.MTGlue
open Module Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.W.ZoneZ
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD CatalanMeasure.Parametric

/-- The rational certificate of one MT (b) glue cell. -/
structure GlueCell where
  s : ℕ
  K : ℕ
  k0 : ℤ
  y : ℕ → ℤ
  u : ℕ → ℤ
  A : ℤ
  B : ℤ
  J1 : Finset ℕ
  J2 : Finset ℕ
  ky : ℕ
  ku : ℕ
  hs2 : 2 ≤ s
  hs : s + 1 + 3 ≤ 22
  hky : ky < K
  hku : ku < K
  hJ1 : ∀ J ∈ J1, J < 18 ∧
    Q.PhiQ (cmb y k0 K y2uI) (cmb y k0 K tI) J s = (A : ℚ) ∧
    Q.PhiQ (cmb u k0 K xtI) (cmb u k0 K xuI) J s = (B : ℚ)
  hJ2 : ∀ J ∈ J2, J < 18 ∧
    Q.PhiQ (cmb y k0 K y2uI) (cmb y k0 K tI) J (s + 1) +
      Q.PhiQ (cmb u k0 K xtI) (cmb u k0 K xuI) J (s + 1) = (A : ℚ) + (B : ℚ)

/-- The bad-prime integer of a glue cell (Lemma B). -/
def GlueCell.modulus (c : GlueCell) : ℕ := ZmG * (c.y c.ky).natAbs * (c.u c.ku).natAbs

variable {p : ℕ} [Fact p.Prime]

theorem GlueCell.units (c : GlueCell) (h : Nat.Coprime p c.modulus) : GUnits p :=
  GUnits.of_coprime (Nat.Coprime.coprime_dvd_right
    ((dvd_mul_right ZmG _).trans (dvd_mul_right _ _)) h)

theorem GlueCell.y_ne (c : GlueCell) (h : Nat.Coprime p c.modulus) :
    zprof p c.K c.y ≠ 0 := by
  intro h0
  have h1 : ((c.y c.ky : ℤ) : ZMod p) = 0 := congrFun h0 ⟨c.ky, c.hky⟩
  have h2 : (p : ℤ) ∣ c.y c.ky := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  have h3 : p ∣ (c.y c.ky).natAbs := Int.natCast_dvd.mp h2
  have h4 : p ∣ c.modulus := by
    unfold GlueCell.modulus
    exact (h3.mul_left ZmG).mul_right _
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl h4)

theorem GlueCell.u_ne (c : GlueCell) (h : Nat.Coprime p c.modulus) :
    zprof p c.K c.u ≠ 0 := by
  intro h0
  have h1 : ((c.u c.ku : ℤ) : ZMod p) = 0 := congrFun h0 ⟨c.ku, c.hku⟩
  have h2 : (p : ℤ) ∣ c.u c.ku := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h1
  have h3 : p ∣ (c.u c.ku).natAbs := Int.natCast_dvd.mp h2
  have h4 : p ∣ c.modulus := by
    unfold GlueCell.modulus
    exact h3.mul_left _
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl h4)

/-- Main window equations in `ZMod p`. -/
theorem GlueCell.main (c : GlueCell) (h : Nat.Coprime p c.modulus) {H : ℕ} (hH : c.s + 4 ≤ H)
    {J : ℕ} (hJ : J ∈ c.J1) :
    (⟨tyMap p c.K c.k0, gyMap p c.K c.k0⟩ : Prof p c.K).psi H J (c.s : ℤ) (zprof p c.K c.y) =
        (c.A : ZMod p) ∧
      (⟨tpTy p c.K c.k0, tpGy p c.K c.k0⟩ : Prof p c.K).psi H J (c.s : ℤ) (zprof p c.K c.u) =
        (c.B : ZMod p) := by
  obtain ⟨hJ18, e1, e2⟩ := c.hJ1 J hJ
  have hm := c.units h
  have a1 : (⟨tyMap p c.K c.k0, gyMap p c.K c.k0⟩ : Prof p c.K).psi H J (c.s : ℤ) (zprof p c.K c.y) =
      palindromicRatResidue p (Q.PhiQ (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) J c.s) :=
    psiY_eq hm c.K c.k0 c.y hJ18 (by have := c.hs; omega) (by omega)
  have a2 : (⟨tpTy p c.K c.k0, tpGy p c.K c.k0⟩ : Prof p c.K).psi H J (c.s : ℤ) (zprof p c.K c.u) =
      palindromicRatResidue p (Q.PhiQ (cmb c.u c.k0 c.K xtI) (cmb c.u c.k0 c.K xuI) J c.s) :=
    psiU_eq hm c.K c.k0 c.u hJ18 (by have := c.hs; omega) (by omega)
  rw [a1, a2, e1, e2, res_intCast, res_intCast]
  exact ⟨rfl, rfl⟩

/-- Overflow window equations in `ZMod p`. -/
theorem GlueCell.over (c : GlueCell) (h : Nat.Coprime p c.modulus) {H : ℕ} (hH : c.s + 4 ≤ H)
    {J : ℕ} (hJ : J ∈ c.J2) :
    (⟨tyMap p c.K c.k0, gyMap p c.K c.k0⟩ : Prof p c.K).psi H J ((c.s : ℤ) + 1) (zprof p c.K c.y) +
      (⟨tpTy p c.K c.k0, tpGy p c.K c.k0⟩ : Prof p c.K).psi H J ((c.s : ℤ) + 1)
        (zprof p c.K c.u) = (c.A : ZMod p) + (c.B : ZMod p) := by
  obtain ⟨hJ18, e⟩ := c.hJ2 J hJ
  have hm := c.units h
  have hc : ((c.s : ℤ) + 1) = ((c.s + 1 : ℕ) : ℤ) := by push_cast; ring
  have a1 : (⟨tyMap p c.K c.k0, gyMap p c.K c.k0⟩ : Prof p c.K).psi H J ((c.s + 1 : ℕ) : ℤ)
      (zprof p c.K c.y) =
      palindromicRatResidue p
        (Q.PhiQ (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) J (c.s + 1)) :=
    psiY_eq hm c.K c.k0 c.y hJ18 (by have := c.hs; omega) (by omega)
  have a2 : (⟨tpTy p c.K c.k0, tpGy p c.K c.k0⟩ : Prof p c.K).psi H J ((c.s + 1 : ℕ) : ℤ)
      (zprof p c.K c.u) =
      palindromicRatResidue p
        (Q.PhiQ (cmb c.u c.k0 c.K xtI) (cmb c.u c.k0 c.K xuI) J (c.s + 1)) :=
    psiU_eq hm c.K c.k0 c.u hJ18 (by have := c.hs; omega) (by omega)
  rw [hc, a1, a2]
  have hu1 : ∀ J σ : ℕ, J < 18 → σ + 3 ≤ 22 →
      (Q.PhiQ (cmb c.y c.k0 c.K y2uI) (cmb c.y c.k0 c.K tI) J σ) ∈ unitSub p := by
    intro J σ hJ hσ
    unfold Q.PhiQ
    refine Subring.sum_mem _ fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    exact Subring.add_mem _
      (Subring.mul_mem _ (alphaU hm (by omega) hJ) (intCast_mem _ _))
      (Subring.mul_mem _ (betaU hm (by omega) hJ) (intCast_mem _ _))
  have hu2 : ∀ J σ : ℕ, J < 18 → σ + 3 ≤ 22 →
      (Q.PhiQ (cmb c.u c.k0 c.K xtI) (cmb c.u c.k0 c.K xuI) J σ) ∈ unitSub p := by
    intro J σ hJ hσ
    unfold Q.PhiQ
    refine Subring.sum_mem _ fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    exact Subring.add_mem _
      (Subring.mul_mem _ (alphaU hm (by omega) hJ) (intCast_mem _ _))
      (Subring.mul_mem _ (betaU hm (by omega) hJ) (intCast_mem _ _))
  have hadd := map_add (resHom p) ⟨_, hu1 J (c.s + 1) hJ18 (by have := c.hs; omega)⟩
    ⟨_, hu2 J (c.s + 1) hJ18 (by have := c.hs; omega)⟩
  simp only [resHom_apply, AddMemClass.coe_add] at hadd
  rw [← hadd, e, ← Int.cast_add, res_intCast]
  exact Int.cast_add _ _

/-- The design part of the certificate of Theorem MT (b): inequalities between the design integers and
the digit coverage of the raw columns by `J1` and `J2`. -/
def GlueWin (P : Parameters) (N p : ℕ) (c : GlueCell) (D1 elo : ℕ) : Prop :=
  D1 ≤ (p - 1) / 2 ∧ p ≤ P.h N + (p - 1) / 2 ∧ P.h N + (p - 1) / 2 - p < p ∧
    c.s * p + 1 ≤ P.H N ∧ p ≤ P.H N - 1 - c.s * p ∧ P.H N - 1 - c.s * p < 2 * p ∧
    P.h N + D1 ≤ (P.H N - 1 - c.s * p) + 1 ∧ elo ≤ P.H N - 1 - c.s * p - p + 1 ∧
    (∀ j, P.b N ≤ j → j < P.L N →
      P.H N - 1 - c.s * p - (P.h N + D1 - 1) ≤ j % p → j / p ∈ c.J1) ∧
    (∀ j, P.b N ≤ j → j < P.L N → j % p + elo + p ≤ P.H N - 1 - c.s * p → j / p ∈ c.J2)

/-- **Lemma B + cells ⟹ `MTGlueOK`.** -/
theorem glueCell_ok {P : Parameters} {N : ℕ} (c : GlueCell) (hp3 : p ≠ 2)
    (h : Nat.Coprime p c.modulus) {D1 elo : ℕ} (hw : GlueWin P N p c D1 elo) :
    MTGlueOK P N p c.s c.K D1 elo c.k0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hw
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3' : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with h | h
    · exact absurd (by omega) hp3
    · exact h
  have hH : c.s + 4 ≤ P.H N := by
    have := c.hs2
    nlinarith
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, zprof p c.K c.y, zprof p c.K c.u, (c.A : ZMod p),
    (c.B : ZMod p), c.J1, c.J2, c.y_ne h, c.u_ne h, fun J hJ => c.main h hH hJ,
    fun J hJ => c.over h hH hJ, h9, h10⟩

end CatalanMeasure.GenD.Uniform.W.MTGlue
end
