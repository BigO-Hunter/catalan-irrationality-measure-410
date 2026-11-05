module
public import Submission.CatalanMeasure.GenD.Uniform.W.Tier3.Sum2
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPS
@[expose] public section
set_option Elab.async false

/-!
# HP2: H' at window `s` plus the period slot at the window pair `(s-1, s)` (lane G6)

`hp2_le_nullity` : `hpVal P N p s k0 k1 + perVal P N p (s-1) k0 k1 ilo ≤ ν` (under2 REPORT sec. 1,
"Theorem HP2": the period slot of an HP configuration one window off; needed when `eta_s < p`).
Proof: `sum_nullity2` with the period top `etaP = eta_{s-1} = eta_s + p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Tier3
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
theorem hp2_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s sp : ℕ) (hsp : sp + 1 = s) (k0 k1 : ℤ) (ilo : ℕ) (hc1 : hpOK P N p s k0 k1)
    (hc2 : perOK P N p sp k0 k1 ilo)
    (hx : perPmax P N p sp k0 k1 < (hpElo P N p s : ℤ) ∨ (hpEta P N p s : ℤ) < ilo + p) :
    hpVal P N p s k0 k1 + perVal P N p sp k0 k1 ilo ≤ nullity P N p := by
  classical
  unfold hpVal perVal
  rw [if_pos hc1, if_pos hc2]
  obtain ⟨hq, hv, hs, hdd, hel, hk⟩ := hc1
  obtain ⟨-, hs2, hpe, hd0, hilo1, hilo2, -⟩ := hc2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpe' := p_eq_hh hp2
  have hjs : 1 ≤ hpJstar P N p k0 k1 := le_max_left _ _
  have hjs2 : -(P.g N : ℤ) - k0 * p ≤ hpJstar P N p k0 k1 :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hjs3 : (k1 + 1) * (p : ℤ) - ((P.n N : ℤ) - 1 - P.g N) ≤ hpJstar P N p k0 k1 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hdd1 : hpDD P N p s k0 k1 ≤ hh p - hpJstar P N p k0 k1 := min_le_left _ _
  have hdd2 : hpDD P N p s k0 k1 ≤ (hpEta P N p s : ℤ) - P.h N - hh p := min_le_right _ _
  have hPm1 : perPmax P N p sp k0 k1 ≤ perD0 P N p k0 k1 + P.h N + hh p - p := min_le_left _ _
  have hPm2 : perPmax P N p sp k0 k1 ≤ (hpEta P N p sp : ℤ) - p := min_le_right _ _
  have hhh : hh p = (((p - 1) / 2 : ℕ) : ℤ) := rfl
  have hD0 : perD0 P N p k0 k1 = hh p - hpJstar P N p k0 k1 := rfl
  -- slot counts
  set Dn : ℕ := (perD0 P N p k0 k1).toNat + 1 with hDn
  have hDz : (Dn : ℤ) = perD0 P N p k0 k1 + 1 := by
    rw [hDn]; push_cast; rw [Int.toNat_of_nonneg hd0]
  set Dh : ℕ := hpD P N p s k0 k1 with hDh
  have hDhz : (Dh : ℤ) = hpDD P N p s k0 k1 + 1 := by
    rw [hDh]; unfold hpD; push_cast; rw [Int.toNat_of_nonneg hdd]
  have hKe : ((hpK k0 k1 : ℕ) : ℤ) = k1 - k0 + 1 := by
    unfold hpK; rw [Int.toNat_of_nonneg (by omega)]
  have hDhpn : Dn ≤ (p - 1) / 2 := by
    have : (Dn : ℤ) ≤ hh p := by omega
    omega
  have hDhDn : Dh ≤ Dn := by
    have : (Dh : ℤ) ≤ Dn := by omega
    omega
  have hvirt : hVirt P N p (hpK k0 k1) Dn k0 = 0 := by
    refine hVirt_zero k0 (hpJstar P N p k0 k1) hp2 hjs hjs2 ?_ (by omega)
    have : ((k0 + (hpK k0 k1 : ℕ) : ℤ)) = k1 + 1 := by rw [hKe]; ring
    rw [this]; exact sub_le_comm.mp hjs3
  have hdomAll : ∀ x, x ∈ (hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhpn).dom := by
    intro x
    have hb : hBad P N p (hpK k0 k1) Dn k0 = ∅ := Finset.card_eq_zero.mp hvirt
    exact (mem_badDom (hBad P N p (hpK k0 k1) Dn k0) x).mpr
      (fun b hb' => by rw [hb] at hb'; simp at hb')
  set S := hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhpn with hS
  -- H' side: digits and the common kernel V1
  have hD1 : P.h N + (p - 1) / 2 + Dh ≤ hpEta P N p s + 1 := by
    have : ((P.h N + (p - 1) / 2 + Dh : ℕ) : ℤ) ≤ (hpEta P N p s : ℤ) + 1 := by
      push_cast; rw [hDhz]; omega
    exact_mod_cast this
  have hJ0 : ∃ J0 : ℕ, min (hpK k0 k1) (hpK k0 k1 + 1 - (hpJJ P N p s k0 k1).card) =
      hpK k0 k1 - ((hpJJ P N p s k0 k1).erase J0).card := by
    by_cases hne : (hpJJ P N p s k0 k1).Nonempty
    · obtain ⟨J0, hJ0⟩ := hne
      refine ⟨J0, ?_⟩
      have hcard := Finset.card_erase_of_mem hJ0
      have hpos : 1 ≤ (hpJJ P N p s k0 k1).card := Finset.card_pos.mpr ⟨J0, hJ0⟩
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨0, ?_⟩
      rw [hne]; simp
  obtain ⟨J0, hmult⟩ := hJ0
  obtain ⟨V1, hV1a, hV1b⟩ := exists_common_kernel (K := hpK k0 k1)
    ((hpJJ P N p s k0 k1).erase J0)
    (fun J => S.prof.psi (P.H N) J s - S.prof.psi (P.H N) J0 s)
  -- P side: polynomials and the kernel V2
  set Pm : ℕ := (perPmax P N p sp k0 k1).toNat with hPm
  have hPmz : (Pm : ℤ) = perPmax P N p sp k0 k1 := by
    rw [hPm]; exact Int.toNat_of_nonneg (by omega)
  set m : ℕ := Pm - ilo + 1 with hm
  have hmle : ∀ i : Fin m, ilo + (i : ℕ) ≤ Pm := fun i => by have := i.isLt; omega
  set c0 : ℕ := p - (P.h N + (p - 1) / 2) with hc0
  have hexist : ∀ i : Fin m, ∃ sc : Fin Dn → ZMod p,
      (X - 1 : (ZMod p)[X]) ^ c0 * X ^ (ilo + (i : ℕ)) = ∑ t : Fin Dn, C (sc t) * gBasis p t := by
    intro i
    refine exists_combination hp2 Dn hDhpn _ ?_
    have hdeg : ((X - 1 : (ZMod p)[X]) ^ c0 * X ^ (ilo + (i : ℕ))).natDegree = c0 + (ilo + i) := by
      have h1 : (X - 1 : (ZMod p)[X]).natDegree = 1 := by compute_degree!
      rw [natDegree_mul (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : ZMod p)))
        (pow_ne_zero _ X_ne_zero), natDegree_pow, h1, natDegree_X_pow]; ring
    have hne : ((X - 1 : (ZMod p)[X]) ^ c0 * X ^ (ilo + (i : ℕ))) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : ZMod p)))
        (pow_ne_zero _ X_ne_zero)
    rw [degree_eq_natDegree hne, hdeg]
    have : c0 + (ilo + (i : ℕ)) < Dn := by
      have := hmle i
      have : ((c0 + (ilo + (i : ℕ)) : ℕ) : ℤ) < Dn := by
        push_cast [hc0]
        rw [Nat.cast_sub (by omega : P.h N + (p - 1) / 2 ≤ p)]
        push_cast; omega
      exact_mod_cast this
    exact_mod_cast this
  choose sc hsc using hexist
  have hrel : ∀ i : Fin m, ∑ t : Fin Dn, C (sc i t) * S.lam t =
      X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ)) := by
    intro i
    show ∑ t : Fin Dn, C (sc i t) * hLam P N p t = _
    rw [lam_combination hp2, ← hsc i, ← mul_assoc, ← pow_add]
    have : P.h N + (p - 1) / 2 + c0 = p := by rw [hc0]; omega
    rw [this, sub_one_pow_prime]; ring
  have hind : ∀ cc : Fin m → ZMod p,
      ∑ i, C (cc i) * (X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ))) = 0 →
        cc = 0 := by
    intro cc hcc
    have h1 : (X ^ p - 1 : (ZMod p)[X]) * X ^ ilo * ∑ i : Fin m, C (cc i) * X ^ (i : ℕ) = 0 := by
      rw [← hcc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add]; ring
    have hne : (X ^ p - 1 : (ZMod p)[X]) * X ^ ilo ≠ 0 :=
      mul_ne_zero (by simpa using X_pow_sub_C_ne_zero hp0 (1 : ZMod p)) (pow_ne_zero _ X_ne_zero)
    have h2 : ∑ i : Fin m, C (cc i) * X ^ (i : ℕ) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hne
      · exact h
    funext i
    have := congrArg (fun q => q.coeff (i : ℕ)) h2
    simpa [finset_sum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using this
  obtain ⟨V2, hV2a, hV2b⟩ := exists_common_kernel (K := hpK k0 k1) (perJJ P N p sp k0 k1 ilo)
    (fun J => S.prof.psi (P.H N) J sp - S.prof.psi (P.H N) J ((sp : ℤ) + 1))
  have hetaz : (P.H N : ℤ) - 1 - (hpEta P N p s : ℤ) = s * p := by
    unfold hpEta; omega
  have hetaz' : (P.H N : ℤ) - 1 - (hpEta P N p sp : ℤ) = sp * p := by
    unfold hpEta; omega
  have hPmax : Pm + p ≤ hpEta P N p sp := by
    have : (Pm : ℤ) + p ≤ hpEta P N p sp := by rw [hPmz]; omega
    exact_mod_cast this
  have hDh' : Dh ≤ (p - 1) / 2 := hDhDn.trans hDhpn
  -- the sum count
  have hsum := sum_nullity2 S hP hN hp2 hH hdomAll (eta := hpEta P N p s) (s := s)
    (e0 := hpElo P N p s) (v := P.h N + (p - 1) / 2) (dm := P.h N + (p - 1) / 2 + Dh - 1)
    (Dh := Dh) (etaP := hpEta P N p sp) (sP := sp) V1 (S.prof.psi (P.H N) J0 s) hDhDn hv (by omega)
    (fun t => hLam_dvd hp2 t)
    (fun d hd => by
      have := hLam_natDegree_lt (P := P) (N := N) hp2 hDh' ⟨d.val, hd⟩
      show (hLam P N p d).natDegree ≤ _
      have h' : (hLam P N p (d.val)).natDegree < P.h N + (p - 1) / 2 + Dh := this
      omega)
    (by unfold hpElo hpEta at *; omega) hetaz hetaz'
    (fun j h1 h2 h3 h4 y hy => by
      have hJ : j / p ∈ hpJJ P N p s k0 k1 := by
        unfold hpJJ
        rw [Finset.mem_filter, Finset.mem_range]
        have hL : j / p ≤ P.L N / p := Nat.div_le_div_right h2.le
        have hjd := Nat.div_add_mod j p
        refine ⟨by omega, ?_⟩
        have e2 : j / p * p + j % p = j := by rw [mul_comm]; exact hjd
        simp only [max_le_iff, le_min_iff]
        have e1 : (hpDD P N p s k0 k1).toNat + 1 = Dh := rfl
        unfold hpElo hpEta at *
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
      by_cases hc : j / p = J0
      · rw [hc]
      · have := hV1b (j / p) (Finset.mem_erase.mpr ⟨hc, hJ⟩) y hy
        exact sub_eq_zero.mp this)
    V2 hPmax hilo2 (by unfold hpElo hpEta at hx ⊢; omega) (by omega) (by unfold hpElo hpEta at *; omega) sc hrel
    hind
    (fun j h1 h2 hc hl hr y hy => by
      have hJ : j / p ∈ perJJ P N p sp k0 k1 ilo := by
        unfold perJJ
        rw [Finset.mem_filter, Finset.mem_range]
        have hL : j / p ≤ P.L N / p := Nat.div_le_div_right h2.le
        have hjd := Nat.div_add_mod j p
        have e2 : j / p * p + j % p = j := by rw [mul_comm]; exact hjd
        refine ⟨by omega, ?_⟩
        simp only [max_le_iff, le_min_iff]
        have hPm' : Pm = (perPmax P N p sp k0 k1).toNat := rfl
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
      have := hV2b (j / p) hJ y hy
      exact sub_eq_zero.mp this)
  -- arithmetic
  have hc0' : p - P.q N - (P.h N + (p - 1) / 2) = 0 := by omega
  rw [hc0', add_zero] at hsum
  have hsum' : Dh * finrank (ZMod p) V1 + m * finrank (ZMod p) V2 ≤
      nullity P N p + hpElo P N p s * finrank (ZMod p) V1 := hsum
  clear hsum
  rw [hmult]
  have hdh : Dh = hpD P N p s k0 k1 := rfl
  have hel' : hpElo P N p s < Dh := hel
  have hA : (hpK k0 k1 - ((hpJJ P N p s k0 k1).erase J0).card) * (Dh - hpElo P N p s) ≤
      (Dh - hpElo P N p s) * finrank (ZMod p) V1 := by
    calc _ ≤ finrank (ZMod p) V1 * (Dh - hpElo P N p s) := Nat.mul_le_mul_right _ hV1a
      _ = _ := Nat.mul_comm _ _
  have hB : (hpK k0 k1 - (perJJ P N p sp k0 k1 ilo).card) * m ≤ m * finrank (ZMod p) V2 := by
    calc _ ≤ finrank (ZMod p) V2 * m := Nat.mul_le_mul_right _ hV2a
      _ = _ := Nat.mul_comm _ _
  have hsplit : Dh * finrank (ZMod p) V1 =
      (Dh - hpElo P N p s) * finrank (ZMod p) V1 + hpElo P N p s * finrank (ZMod p) V1 := by
    rw [← add_mul, Nat.sub_add_cancel hel'.le]
  generalize (hpK k0 k1 - ((hpJJ P N p s k0 k1).erase J0).card) * (Dh - hpElo P N p s) = a at *
  generalize (Dh - hpElo P N p s) * finrank (ZMod p) V1 = b at *
  generalize Dh * finrank (ZMod p) V1 = c at *
  generalize hpElo P N p s * finrank (ZMod p) V1 = d at *
  generalize (hpK k0 k1 - (perJJ P N p sp k0 k1 ilo).card) * m = e at *
  generalize m * finrank (ZMod p) V2 = g at *
  omega

#print axioms hp2_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Tier3
