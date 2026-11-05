module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax5
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (variant (1)) with one condition per missing row

`mt_le_nullity'` : the T- and T+ count of `proof4` with the exact number of missing rows `V`
(`mixMiss`), i.e. `m (D1 - e0) + m (D1 + 1 - e0) - V - r ≤ ν`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
/-- **Theorem MT, variant (1)** (T- and T+ pairs, one window `s`), relaxed domain: one condition per missing row. -/
theorem mt_le_nullity' (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D1 e0 s : ℕ} (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) (hph : p ≤ P.h N + (p - 1) / 2)
    (JJ : Finset ℕ) (J0 : ℕ)
    (hv : P.h N + (p - 1) / 2 - p < p)
    (hs : s * p + 1 ≤ P.H N)
    (hdeg : P.h N + D1 ≤ (P.H N - 1 - s * p) + 1)
    (he0 : (P.H N - 1 - s * p) + 1 ≤ e0 + p) (he0D : e0 ≤ D1)
    (hJJ : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ P.H N - 1 - s * p →
      P.H N - 1 - s * p ≤ j % p + (P.h N + D1 - 1) → j / p ∈ JJ) :
    (D1 - e0) * (K - (JJ.erase J0).card) + (D1 + 1 - e0) * (K - (JJ.erase J0).card)
      ≤ nullity P N p + mixMiss P N p K D1 k0 +
        (p - P.q N - (P.h N + (p - 1) / 2 - p)) := by
  classical
  have hpo := p_odd_half hp2
  let F1 : Prof p K := ⟨tyMap p K k0, gyMap p K k0⟩
  let F2 : Prof p K := ⟨tpTy p K k0, tpGy p K k0⟩
  set S := mtSystem' P N p hp2 hph K D1 k0 hD with hS
  obtain ⟨V1, hV1a, hV1b⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => F1.psi (P.H N) J s - F1.psi (P.H N) J0 s)
  obtain ⟨V2, hV2a, hV2b⟩ := exists_common_kernel (K := K) (JJ.erase J0)
    (fun J => F2.psi (P.H N) J s - F2.psi (P.H N) J0 s)
  let V : Submodule (ZMod p) (Fin (K + K) → ZMod p) :=
    (V1.comap (fl1 K K)) ⊓ (V2.comap (fl2 K K))
  have hV : ∀ y, y ∈ V ↔ fl1 K K y ∈ V1 ∧ fl2 K K y ∈ V2 := fun y => by
    simp [V, Submodule.mem_inf]
  have hVdim : finrank (ZMod p) V ≤ finrank (ZMod p) V1 + finrank (ZMod p) V2 :=
    finrank_blocks_le V1 V2 V hV
  have hat := finrank_atoms_relax_ge hp2 hph K D1 k0 hD V1 V2 V hV
  -- the flat count
  have hdvd : ∀ d, ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ S.lam d := by
    intro d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · show ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ Fin.append (fun d : Fin D1 => Thin.lam P N p (d : ℕ)) (fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ)) (Fin.castAdd _ i)
      rw [Fin.append_left]
      show _ ∣ Thin.lam P N p (i : ℕ)
      unfold Thin.lam
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _) _
    · show ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ Fin.append (fun d : Fin D1 => Thin.lam P N p (d : ℕ)) (fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ)) (Fin.natAdd _ j)
      rw [Fin.append_right]
      exact tpLam_dvd P N p (j : ℕ)
  have hdegS : ∀ d, (S.lam d).natDegree ≤ P.h N + D1 - 1 := by
    intro d
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · show (Fin.append (fun d : Fin D1 => Thin.lam P N p (d : ℕ)) (fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ)) (Fin.castAdd _ i)).natDegree ≤ _
      rw [Fin.append_left]
      have h1 := lam_natDegree_le (P := P) (N := N) hp2 (i : ℕ)
      have h2 : (i : ℕ) < D1 := i.isLt
      show (Thin.lam P N p (i : ℕ)).natDegree ≤ _
      omega
    · show (Fin.append (fun d : Fin D1 => Thin.lam P N p (d : ℕ)) (fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ)) (Fin.natAdd _ j)).natDegree ≤ _
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
      have e1 := profAdd_psi F1 F2 (P.H N) (j / p) (s : ℤ) y
      have e2 := profAdd_psi F1 F2 (P.H N) J0 (s : ℤ) y
      refine e1.trans (Eq.trans ?_ e2.symm)
      by_cases hc : j / p = J0
      · rw [hc]
      · have e1 := hV1b (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) _ hy'.1
        have e2 := hV2b (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) _ hy'.2
        have e1' : F1.psi (P.H N) (j / p) (s : ℤ) (fl1 K K y) =
            F1.psi (P.H N) J0 (s : ℤ) (fl1 K K y) := by
          exact sub_eq_zero.mp e1
        have e2' : F2.psi (P.H N) (j / p) (s : ℤ) (fl2 K K y) =
            F2.psi (P.H N) J0 (s : ℤ) (fl2 K K y) := by
          exact sub_eq_zero.mp e2
        exact congrArg₂ (· + ·) e1' e2')
  -- arithmetic
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
      finrank (ZMod p) (S.atoms V) + mixMiss P N p K D1 k0 := hat
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

#print axioms mt_le_nullity'
end
end CatalanMeasure.GenD.Uniform.W.SlotsT
