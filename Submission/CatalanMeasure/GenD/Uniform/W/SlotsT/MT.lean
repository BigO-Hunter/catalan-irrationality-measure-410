module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.AddCount
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT, single-window variant (1), on the slot API

`mtSystem` is the mixed slot system `tSystem ⊞ tpSystem`: T- pairs `e_{c+d'} - e_{c-d'}`
(`d' = 1, …, D1`) and T+ pairs in period form (`d' = 0, …, D1`) about the same centres
`c_k = (k0 + k) p`, `k < K`.

`mt_le_nullity` (**Theorem MT (1)**, design-generic): with `a = h + (p-1)/2 - p ≥ 0`,
`η = H - 1 - s p`, `e0 ≥ η + 1 - p` vanishing jets and a set `JJ` of digits that see the window,

    (D1 - e0) m + (D1 + 1 - e0) m ≤ ν + #virtual + (p - q - a)_+ ,   m = K - |JJ \ {J0}| .

(`proof4/report.md`, Theorem MT, variant (1), T- and T+; `m (dmax - e0) + m (dmax + 1 - e0) - V - r`.)
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem tSystem_sep (hp2 : p ≠ 2) {K D1 : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2)
    (hph : p ≤ P.h N + (p - 1) / 2) (hD2 : D1 + 1 ≤ (p - 1) / 2 + 1) :
    ∀ a ∈ (tSystem P N p hp2 K D1 k0 hD).dom, ∀ b ∈ (tpSystem P N p hp2 hph K (D1 + 1) k0
      hD2).dom, (tSystem P N p hp2 K D1 k0 hD).rows a +
        (tpSystem P N p hp2 hph K (D1 + 1) k0 hD2).rows b = 0 → a = 0 ∧ b = 0 := by
  intro a ha b hb h0
  refine mix_sep (P := P) (N := N) hp2 hD k0 a b (fun d k hg => ?_) (fun d k hg => ?_) (fun r => ?_)
  · exact (mem_badDom _ _).mp ha ⟨d, k⟩
      (by simp only [tBad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hg)
  · exact (mem_badDom _ _).mp hb ⟨d, k⟩
      (by simp only [tpBad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hg)
  · exact congrFun h0 r

/-- The mixed slot system of Theorem MT (T- pairs together with T+ pairs). -/
def mtSystem (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hph : p ≤ P.h N + (p - 1) / 2) (K D1 : ℕ) (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) :
    SlotSystem P N p :=
  addSystem (tSystem P N p hp2 K D1 k0 hD) (tpSystem P N p hp2 hph K (D1 + 1) k0 (by omega))
    (tSystem_sep hp2 k0 hD hph (by omega))

theorem mtSystem_K (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (K D1 : ℕ) (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2) : (mtSystem P N p hp2 hph K D1 k0 hD).K = K + K := rfl

theorem mtSystem_D (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) (K D1 : ℕ) (k0 : ℤ)
    (hD : D1 ≤ (p - 1) / 2) : (mtSystem P N p hp2 hph K D1 k0 hD).D = D1 + (D1 + 1) := rfl

set_option maxHeartbeats 1600000 in
/-- **Theorem MT, variant (1)** (T- and T+ pairs, one window `s`). -/
theorem mt_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D1 e0 s : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) (hph : p ≤ P.h N + (p - 1) / 2)
    (JJ : Finset ℕ) (J0 : ℕ)
    (hv : P.h N + (p - 1) / 2 - p < p)
    (hs : s * p + 1 ≤ P.H N)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1)
    (he0 : (P.H N - 1 - s * p) + 1 ≤ e0 + p) (he0D : e0 ≤ D1)
    (hJJ : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ P.H N - 1 - s * p →
      P.H N - 1 - s * p ≤ j % p + (P.h N + D1 - 1) → j / p ∈ JJ) :
    (D1 - e0) * (K - (JJ.erase J0).card) + (D1 + 1 - e0) * (K - (JJ.erase J0).card)
      ≤ nullity P N p + (virtCount P N p K D1 k0 + tpVirt P N p K (D1 + 1) k0) +
        (p - P.q N - (P.h N + (p - 1) / 2 - p)) := by
  classical
  have hpo := p_odd_half hp2
  have hD2 : D1 + 1 ≤ (p - 1) / 2 + 1 := by omega
  set S1 := tSystem P N p hp2 K D1 k0 hD with hS1
  set S2 := tpSystem P N p hp2 hph K (D1 + 1) k0 hD2 with hS2
  set S := mtSystem P N p hp2 hph K D1 k0 hD with hS
  obtain ⟨V1, hV1a, hV1b⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => S1.prof.psi (P.H N) J s - S1.prof.psi (P.H N) J0 s)
  obtain ⟨V2, hV2a, hV2b⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => S2.prof.psi (P.H N) J s - S2.prof.psi (P.H N) J0 s)
  let V : Submodule (ZMod p) (Fin (K + K) → ZMod p) :=
    (V1.comap (fl1 K K)) ⊓ (V2.comap (fl2 K K))
  have hV : ∀ y, y ∈ V ↔ fl1 K K y ∈ V1 ∧ fl2 K K y ∈ V2 := fun y => by
    simp [V, Submodule.mem_inf]
  have hVdim : finrank (ZMod p) V ≤ finrank (ZMod p) V1 + finrank (ZMod p) V2 :=
    finrank_blocks_le V1 V2 V hV
  have hat := finrank_atoms_add_ge S1 S2 (tSystem_sep hp2 k0 hD hph hD2) V1 V2 V hV
    (tBad P N p K D1 k0) (tpBad P N p K (D1 + 1) k0) (fun x => Iff.rfl) (fun x => Iff.rfl)
  have hbad1 : (tBad P N p K D1 k0).card = virtCount P N p K D1 k0 := tBad_card K D1 k0
  have hbad2 : (tpBad P N p K (D1 + 1) k0).card = tpVirt P N p K (D1 + 1) k0 := rfl
  -- the flat count
  have hdvd : ∀ d, ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ S.lam d := by
    intro d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · show ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ Fin.append S1.lam S2.lam (Fin.castAdd _ i)
      rw [Fin.append_left]
      show _ ∣ Thin.lam P N p (i : ℕ)
      unfold Thin.lam
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _) _
    · show ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ Fin.append S1.lam S2.lam (Fin.natAdd _ j)
      rw [Fin.append_right]
      exact tpLam_dvd P N p (j : ℕ)
  have hdegS : ∀ d, (S.lam d).natDegree ≤ P.h N + D1 - 1 := by
    intro d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · show (Fin.append S1.lam S2.lam (Fin.castAdd _ i)).natDegree ≤ _
      rw [Fin.append_left]
      have h1 := lam_natDegree_le (P := P) (N := N) hp2 (i : ℕ)
      have h2 : (i : ℕ) < D1 := i.isLt
      show (Thin.lam P N p (i : ℕ)).natDegree ≤ _
      omega
    · show (Fin.append S1.lam S2.lam (Fin.natAdd _ j)).natDegree ≤ _
      rw [Fin.append_right]
      have h1 := tpLam_natDegree_le (P := P) (N := N) hp2 (j : ℕ)
      have h2 : (j : ℕ) < D1 + 1 := j.isLt
      show (tpLam P N p (j : ℕ)).natDegree ≤ _
      omega
  have hetaz : (P.H N : ℤ) - 1 - ((P.H N - 1 - s * p : ℕ) : ℤ) = s * p := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hflat := S.slot_nullity_flat hP hN hp2 hH V (S.prof.psi (P.H N) J0 s) (eta := P.H N - 1 - s * p)
    (s := s) (e0 := e0) (v := P.h N + (p - 1) / 2 - p) (dm := P.h N + D1 - 1) hv (by omega)
    hdvd hdegS he0 hetaz
    (fun j h1 h2 h3 h4 y hy => by
      have hJ : j / p ∈ JJ := hJJ j h1 h2 h3 (by omega)
      have hy' := (hV y).mp hy
      have e1 := addSystem_psi S1 S2 (tSystem_sep hp2 k0 hD hph hD2) (P.H N) (j / p) (s : ℤ) y
      have e2 := addSystem_psi S1 S2 (tSystem_sep hp2 k0 hD hph hD2) (P.H N) J0 (s : ℤ) y
      refine e1.trans (Eq.trans ?_ e2.symm)
      by_cases hc : j / p = J0
      · rw [hc]
      · have e1 := hV1b (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) _ hy'.1
        have e2 := hV2b (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) _ hy'.2
        have e1' : S1.prof.psi (P.H N) (j / p) (s : ℤ) (fl1 K K y) =
            S1.prof.psi (P.H N) J0 (s : ℤ) (fl1 K K y) := by
          exact sub_eq_zero.mp e1
        have e2' : S2.prof.psi (P.H N) (j / p) (s : ℤ) (fl2 K K y) =
            S2.prof.psi (P.H N) J0 (s : ℤ) (fl2 K K y) := by
          exact sub_eq_zero.mp e2
        exact congrArg₂ (· + ·) e1' e2')
  -- arithmetic
  have hS1K : S1.K = K := rfl
  have hS2K : S2.K = K := rfl
  have hVdim' : e0 * finrank (ZMod p) V ≤ e0 * (finrank (ZMod p) V1 + finrank (ZMod p) V2) :=
    Nat.mul_le_mul_left _ hVdim
  have hA : (D1 - e0) * (K - (JJ.erase J0).card) ≤ (D1 - e0) * finrank (ZMod p) V1 :=
    Nat.mul_le_mul_left _ hV1a
  have hB : (D1 + 1 - e0) * (K - (JJ.erase J0).card) ≤ (D1 + 1 - e0) * finrank (ZMod p) V2 :=
    Nat.mul_le_mul_left _ hV2a
  have hsplit1 : D1 * finrank (ZMod p) V1 =
      (D1 - e0) * finrank (ZMod p) V1 + e0 * finrank (ZMod p) V1 := by
    rw [← add_mul, Nat.sub_add_cancel he0D]
  have hsplit2 : (D1 + 1) * finrank (ZMod p) V2 =
      (D1 + 1 - e0) * finrank (ZMod p) V2 + e0 * finrank (ZMod p) V2 := by
    rw [← add_mul, Nat.sub_add_cancel (by omega)]
  have hflat' : finrank (ZMod p) (S.atoms V) ≤ nullity P N p +
      e0 * finrank (ZMod p) V + (p - P.q N - (P.h N + (p - 1) / 2 - p)) := hflat
  have hat' : D1 * finrank (ZMod p) V1 + (D1 + 1) * finrank (ZMod p) V2 ≤
      finrank (ZMod p) (S.atoms V) + (tBad P N p K D1 k0).card +
        (tpBad P N p K (D1 + 1) k0).card := hat
  rw [hbad1, hbad2] at hat'
  rw [mul_add] at hVdim'
  generalize (D1 - e0) * (K - (JJ.erase J0).card) = a at *
  generalize (D1 + 1 - e0) * (K - (JJ.erase J0).card) = b at *
  generalize (D1 - e0) * finrank (ZMod p) V1 = c at *
  generalize (D1 + 1 - e0) * finrank (ZMod p) V2 = d at *
  generalize e0 * finrank (ZMod p) V1 = f at *
  generalize e0 * finrank (ZMod p) V2 = g at *
  generalize D1 * finrank (ZMod p) V1 = u at *
  generalize (D1 + 1) * finrank (ZMod p) V2 = w at *
  omega

#print axioms mt_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.SlotsT
