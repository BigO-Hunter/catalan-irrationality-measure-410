module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MTFam2
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT, T+ only (period form), as a `NullityLB`

`(D1 + 1 - e0) m - #virtual - (p - q - a)_+ ≤ ν`, `a = h + (p-1)/2 - p`: the T+ family alone
(`use = (0,1)` of `proof4/thmMT.py`), on `tpSystem` with `D1 + 1` offsets `0, …, D1`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
theorem mtPlus_le_nullity_aux (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D1 e0 s : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) (hph : p ≤ P.h N + (p - 1) / 2)
    (JJ : Finset ℕ) (J0 : ℕ)
    (hv : P.h N + (p - 1) / 2 - p < p) (hs : s * p + 1 ≤ P.H N)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1)
    (he0 : (P.H N - 1 - s * p) + 1 ≤ e0 + p) (he0D : e0 ≤ D1 + 1)
    (hJJ : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ P.H N - 1 - s * p →
      P.H N - 1 - s * p ≤ j % p + (P.h N + D1 - 1) → j / p ∈ JJ) :
    (D1 + 1 - e0) * (K - (JJ.erase J0).card) ≤
      nullity P N p + tpVirt P N p K (D1 + 1) k0 + (p - P.q N - (P.h N + (p - 1) / 2 - p)) := by
  classical
  have hpo := p_odd_half hp2
  have hD2 : D1 + 1 ≤ (p - 1) / 2 + 1 := by omega
  set S := tpSystem P N p hp2 hph K (D1 + 1) k0 hD2 with hS
  obtain ⟨V, hV1, hV2⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => S.prof.psi (P.H N) J s - S.prof.psi (P.H N) J0 s)
  have hdeg' : ∀ t : Fin S.D, (S.lam t).natDegree ≤ P.h N + D1 - 1 := by
    intro t
    have h1 := tpLam_natDegree_le (P := P) (N := N) hp2 (t : ℕ)
    have h2 : (t : ℕ) < D1 + 1 := t.isLt
    show (tpLam P N p (t : ℕ)).natDegree ≤ _
    omega
  have hetaz : (P.H N : ℤ) - 1 - ((P.H N - 1 - s * p : ℕ) : ℤ) = s * p := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : finrank (ZMod p) (S.atoms V) ≤ nullity P N p + e0 * finrank (ZMod p) V +
      (p - P.q N - (P.h N + (p - 1) / 2 - p)) :=
    S.slot_nullity_flat hP hN hp2 hH V (S.prof.psi (P.H N) J0 s)
      (eta := P.H N - 1 - s * p) (s := s) (e0 := e0) (v := P.h N + (p - 1) / 2 - p)
      (dm := P.h N + D1 - 1) hv (by omega)
      (fun t => tpLam_dvd P N p (t : ℕ))
      hdeg' he0 hetaz
      (fun j h1 h2 h3 h4 y hy => by
        have hJ := hJJ j h1 h2 h3 (by omega)
        by_cases hc : j / p = J0
        · rw [hc]
        · have := hV2 (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) y hy
          exact sub_eq_zero.mp this)
  have h2 := S.finrank_atoms_ge V (tpBad P N p K (D1 + 1) k0) (fun x => Iff.rfl)
  have h3 : (D1 + 1) * finrank (ZMod p) V ≤ finrank (ZMod p) (S.atoms V) +
      tpVirt P N p K (D1 + 1) k0 := h2
  have h4 : (D1 + 1 - e0) * (K - (JJ.erase J0).card) ≤ (D1 + 1 - e0) * finrank (ZMod p) V :=
    Nat.mul_le_mul_left _ hV1
  have h5 : (D1 + 1) * finrank (ZMod p) V =
      (D1 + 1 - e0) * finrank (ZMod p) V + e0 * finrank (ZMod p) V := by
    rw [← add_mul, Nat.sub_add_cancel he0D]
  clear h2
  generalize (D1 + 1 - e0) * (K - (JJ.erase J0).card) = a at *
  generalize (D1 + 1 - e0) * finrank (ZMod p) V = b at *
  generalize (D1 + 1) * finrank (ZMod p) V = c at *
  generalize e0 * finrank (ZMod p) V = d at *
  generalize finrank (ZMod p) (S.atoms V) = e at *
  omega

/-- **Theorem MT, T+ only, integer value.** -/
def mtPlusVal (P : Parameters) (N p s K : ℕ) (D1 e0 : ℕ) (k0 : ℤ) [Fact p.Prime] : ℕ :=
  if mtOK P N p s D1 e0 then
    (D1 + 1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) - tpVirt P N p K (D1 + 1) k0 -
      (p - P.q N - (P.h N + (p - 1) / 2 - p))
  else 0

theorem mtPlusVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s K : ℕ) (D1 e0 : ℕ) (k0 : ℤ) : mtPlusVal P N p s K D1 e0 k0 ≤ nullity P N p := by
  classical
  unfold mtPlusVal
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  obtain ⟨hph, hv, hs, hdeg, he0, he0D, hD⟩ := hc
  obtain ⟨J0, hJ0⟩ := exists_J0 (mtJJ P N p s D1 e0) K
  have h := mtPlus_le_nullity_aux hP hN hp2 hH (K := K) (e0 := e0) (s := s) k0 hD hph
    (mtJJ P N p s D1 e0) J0 hv hs (by unfold hpEta at hdeg; exact hdeg)
    (by unfold hpEta at he0; exact he0) (by omega)
    (fun j h1 h2 h3 h4 => mtJJ_spec s D1 e0 hdeg j h1 h2 h3 h4)
  rw [← hJ0] at h
  generalize (D1 + 1 - e0) * min K (K + 1 - (mtJJ P N p s D1 e0).card) = a at *
  omega

/-- The T+ only family. -/
def mtPlusKap (P : Parameters) (N p : ℕ) : ℕ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    mtSup P N p fun s K k0 D1 e0 => mtPlusVal P N p s K D1 e0 k0
  else 0

/-- Theorem MT (1), T+ only, as a nullity lower bound. -/
def mtPlusLB (P : Parameters) (hP : Admissible P) : NullityLB P where
  kap := mtPlusKap P
  ok := fun N p hN hp hp2 hH => by
    haveI : Fact p.Prime := ⟨hp⟩
    unfold mtPlusKap
    rw [dif_pos hp]
    exact mtSup_le P N p _ _ fun s K k0 D1 e0 => mtPlusVal_le_nullity hP hN hp2 hH s K D1 e0 k0

/-- **`mtLB3`**: Theorem MT, single-window variant (1): T- and T+, T- only, T+ only. -/
def mtLB3 (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.supList P [mtBothLB2 P hP, mtMinusLB P hP, mtPlusLB P hP]

theorem mtBothLB2_le_mtLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtBothLB2 P hP).kap N p ≤ (mtLB3 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB3]) N p

theorem mtMinusLB_le_mtLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtMinusLB P hP).kap N p ≤ (mtLB3 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB3]) N p

theorem mtPlusLB_le_mtLB3 (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (mtPlusLB P hP).kap N p ≤ (mtLB3 P hP).kap N p :=
  NullityLB.le_supList_kap (by simp [mtLB3]) N p

#print axioms mtLB3

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
