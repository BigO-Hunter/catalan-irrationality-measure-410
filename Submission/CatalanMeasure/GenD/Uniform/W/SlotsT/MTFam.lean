module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MT
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT as design-generic integer bounds

`mtVal` (T- and T+, cost `r = (2p - q - h - hp)_+`) and `mtMinusVal` (T- only, cost `(p - q - h)_+`)
are computed from `(n, b, q, g, h, p)` and the integer parameters `(s, K, k0, D1, e0)` only.
`mtVal_le_nullity` and `mtMinusVal_le_nullity` prove `val ≤ ν` for every admissible design.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

/-- Digits of the raw columns that see the window of digit `s`: residues in `[η - dm, η - e0]`,
`dm = h + D1 - 1`. -/
def mtJJ (P : Parameters) (N p s D1 e0 : ℕ) : Finset ℕ :=
  (Finset.range (P.L N / p + 2)).filter fun J =>
    max (J * p + (hpEta P N p s - (P.h N + D1 - 1))) (P.b N) ≤
      min (J * p + (hpEta P N p s - e0)) (P.L N - 1)

/-- Applicability of Theorem MT (T- and T+). -/
def mtOK (P : Parameters) (N p s D1 e0 : ℕ) : Prop :=
  p ≤ P.h N + (p - 1) / 2 ∧ P.h N + (p - 1) / 2 - p < p ∧ s * p + 1 ≤ P.H N ∧
    P.h N + D1 ≤ hpEta P N p s + 1 ∧ hpEta P N p s + 1 ≤ e0 + p ∧ e0 ≤ D1 ∧ D1 ≤ (p - 1) / 2

instance (P : Parameters) (N p s D1 e0 : ℕ) : Decidable (mtOK P N p s D1 e0) := by
  unfold mtOK; infer_instance

/-- **Theorem MT, variant (1), integer value** (T- and T+ pairs). -/
def mtVal (P : Parameters) (N p s K : ℕ) (k0 : ℤ) (D1 e0 : ℕ) [Fact p.Prime] : ℕ :=
  if mtOK P N p s D1 e0 then
    (D1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) +
      (D1 + 1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) -
      (virtCount P N p K D1 k0 + tpVirt P N p K (D1 + 1) k0) -
      (p - P.q N - (P.h N + (p - 1) / 2 - p))
  else 0

/-- Applicability of the T- only window. -/
def mtMinusOK (P : Parameters) (N p s D1 e0 : ℕ) : Prop :=
  P.h N < p ∧ s * p + 1 ≤ P.H N ∧
    P.h N + D1 ≤ hpEta P N p s + 1 ∧ hpEta P N p s + 1 ≤ e0 + p ∧ e0 ≤ D1 ∧ D1 ≤ (p - 1) / 2

instance (P : Parameters) (N p s D1 e0 : ℕ) : Decidable (mtMinusOK P N p s D1 e0) := by
  unfold mtMinusOK; infer_instance

/-- **Theorem MT, variant (1), T- only.** -/
def mtMinusVal (P : Parameters) (N p s K : ℕ) (k0 : ℤ) (D1 e0 : ℕ) [Fact p.Prime] : ℕ :=
  if mtMinusOK P N p s D1 e0 then
    (D1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) - virtCount P N p K D1 k0 -
      (p - P.q N - P.h N)
  else 0

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem mtJJ_spec (s D1 e0 : ℕ) (hdeg : P.h N + D1 ≤ hpEta P N p s + 1)
    (j : ℕ) (h1 : P.b N ≤ j) (h2 : j < P.L N) (h3 : e0 + j % p ≤ P.H N - 1 - s * p)
    (h4 : P.H N - 1 - s * p ≤ j % p + (P.h N + D1 - 1)) : j / p ∈ mtJJ P N p s D1 e0 := by
  unfold mtJJ
  rw [Finset.mem_filter, Finset.mem_range]
  have hL : j / p ≤ P.L N / p := Nat.div_le_div_right h2.le
  have hjd := Nat.div_add_mod j p
  have e2 : j / p * p + j % p = j := by rw [mul_comm]; exact hjd
  refine ⟨by omega, ?_⟩
  simp only [max_le_iff, le_min_iff]
  unfold hpEta
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem exists_J0 (JJ : Finset ℕ) (K : ℕ) :
    ∃ J0 : ℕ, min K (K + 1 - JJ.card) = K - (JJ.erase J0).card := by
  by_cases hne : JJ.Nonempty
  · obtain ⟨J0, hJ0⟩ := hne
    refine ⟨J0, ?_⟩
    have hcard := Finset.card_erase_of_mem hJ0
    have hpos : 1 ≤ JJ.card := Finset.card_pos.mpr ⟨J0, hJ0⟩
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, ?_⟩
    rw [hne]; simp

/-- **Theorem MT (T- and T+) is a nullity lower bound.** -/
theorem mtVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s K : ℕ) (k0 : ℤ) (D1 e0 : ℕ) : mtVal P N p s K k0 D1 e0 ≤ nullity P N p := by
  classical
  unfold mtVal
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  obtain ⟨hph, hv, hs, hdeg, he0, he0D, hD⟩ := hc
  obtain ⟨J0, hJ0⟩ := exists_J0 (mtJJ P N p s D1 e0) K
  have h := mt_le_nullity hP hN hp2 hH (K := K) (e0 := e0) (s := s) k0 hD hph
    (mtJJ P N p s D1 e0) J0 hv hs (by unfold hpEta at hdeg; exact hdeg)
    (by unfold hpEta at he0; exact he0) he0D
    (fun j h1 h2 h3 h4 => mtJJ_spec s D1 e0 hdeg j h1 h2 h3 h4)
  rw [← hJ0] at h
  generalize (D1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) = a at *
  generalize (D1 + 1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) = b at *
  omega

set_option maxHeartbeats 1600000 in
/-- **Theorem MT (1), T- only.** -/
theorem mtMinus_le_nullity_aux (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D1 e0 s : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) (JJ : Finset ℕ) (J0 : ℕ)
    (hv : P.h N < p) (hs : s * p + 1 ≤ P.H N)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1)
    (he0 : (P.H N - 1 - s * p) + 1 ≤ e0 + p) (he0D : e0 ≤ D1)
    (hJJ : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ P.H N - 1 - s * p →
      P.H N - 1 - s * p ≤ j % p + (P.h N + D1 - 1) → j / p ∈ JJ) :
    (D1 - e0) * (K - (JJ.erase J0).card) ≤
      nullity P N p + virtCount P N p K D1 k0 + (p - P.q N - P.h N) := by
  classical
  set S := tSystem P N p hp2 K D1 k0 hD with hS
  obtain ⟨V, hV1, hV2⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => S.prof.psi (P.H N) J s - S.prof.psi (P.H N) J0 s)
  have hdeg' : ∀ t : Fin S.D, (S.lam t).natDegree ≤ P.h N + D1 - 1 := by
    intro t
    have h1 := lam_natDegree_le (P := P) (N := N) hp2 (t : ℕ)
    have h2 : (t : ℕ) < D1 := t.isLt
    show (Thin.lam P N p (t : ℕ)).natDegree ≤ _
    omega
  have hetaz : (P.H N : ℤ) - 1 - ((P.H N - 1 - s * p : ℕ) : ℤ) = s * p := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : finrank (ZMod p) (S.atoms V) ≤ nullity P N p + e0 * finrank (ZMod p) V +
      (p - P.q N - P.h N) :=
    S.slot_nullity_flat hP hN hp2 hH V (S.prof.psi (P.H N) J0 s)
      (eta := P.H N - 1 - s * p) (s := s) (e0 := e0) (v := P.h N)
      (dm := P.h N + D1 - 1) hv (by omega)
      (fun t => by
        show ((X - 1) ^ P.h N : (ZMod p)[X]) ∣ Thin.lam P N p (t : ℕ)
        unfold Thin.lam
        exact ⟨2 * Chebyshev.U (ZMod p) ((t : ℕ) : ℤ), by ring⟩)
      hdeg' he0 hetaz
      (fun j h1 h2 h3 h4 y hy => by
        have hJ := hJJ j h1 h2 h3 h4
        by_cases hc : j / p = J0
        · rw [hc]
        · have := hV2 (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) y hy
          exact sub_eq_zero.mp this)
  have h2 := S.finrank_atoms_ge V (tBad P N p K D1 k0) (fun x => Iff.rfl)
  have h3 : D1 * finrank (ZMod p) V ≤ finrank (ZMod p) (S.atoms V) + virtCount P N p K D1 k0 := h2
  have h4 : (D1 - e0) * (K - (JJ.erase J0).card) ≤ (D1 - e0) * finrank (ZMod p) V :=
    Nat.mul_le_mul_left _ hV1
  have h5 : D1 * finrank (ZMod p) V = (D1 - e0) * finrank (ZMod p) V + e0 * finrank (ZMod p) V := by
    rw [← add_mul, Nat.sub_add_cancel he0D]
  clear h2
  generalize (D1 - e0) * (K - (JJ.erase J0).card) = a at *
  generalize (D1 - e0) * finrank (ZMod p) V = b at *
  generalize D1 * finrank (ZMod p) V = c at *
  generalize e0 * finrank (ZMod p) V = d at *
  generalize finrank (ZMod p) (S.atoms V) = e at *
  omega

/-- **Theorem MT (T- only) is a nullity lower bound.** -/
theorem mtMinusVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s K : ℕ) (k0 : ℤ) (D1 e0 : ℕ) : mtMinusVal P N p s K k0 D1 e0 ≤ nullity P N p := by
  classical
  unfold mtMinusVal
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  obtain ⟨hv, hs, hdeg, he0, he0D, hD⟩ := hc
  obtain ⟨J0, hJ0⟩ := exists_J0 (mtJJ P N p s D1 e0) K
  have h := mtMinus_le_nullity_aux hP hN hp2 hH (K := K) (e0 := e0) (s := s) k0 hD
    (mtJJ P N p s D1 e0) J0 hv hs (by unfold hpEta at hdeg; exact hdeg)
    (by unfold hpEta at he0; exact he0) he0D
    (fun j h1 h2 h3 h4 => mtJJ_spec s D1 e0 hdeg j h1 h2 h3 h4)
  rw [← hJ0] at h
  generalize (D1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) = a at *
  omega

#print axioms mtVal_le_nullity
#print axioms mtMinusVal_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.SlotsT
