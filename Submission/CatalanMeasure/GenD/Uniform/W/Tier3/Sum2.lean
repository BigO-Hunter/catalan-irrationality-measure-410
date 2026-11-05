module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Sum
@[expose] public section
set_option Elab.async false

/-!
# `sum_nullity2`: J-flat family plus a period family on a different window pair (lane G6, HP2)

As `Slots.SlotSystem.sum_nullity`, but the period part has its own top `etaP` and digit `sP`
(`H - 1 - etaP = sP p`), and the independence of the two atom families is either `Pmax < e0`
(jets) or `eta < ilo + p` (the high copy `+P` of the period slot lies above the J-flat slot degrees).
-/

namespace CatalanMeasure.GenD.Uniform.W.Tier3
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Slots.SlotSystem
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
/-- **Sum of a J-flat family and a period family.** -/
theorem sum_nullity2 (S : SlotSystem P N p) (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hdom : ∀ x, x ∈ S.dom)
    {eta s etaP sP e0 v dm Dh : ℕ}
    (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p)
    (hDh : Dh ≤ S.D) (hv : v < p) (hdm : dm ≤ eta)
    (hdvd : ∀ d, ((X - 1) ^ v : (ZMod p)[X]) ∣ S.lam d)
    (hdeg : ∀ d : Fin S.D, d.val < Dh → (S.lam d).natDegree ≤ dm) (he0 : eta + 1 ≤ e0 + p)
    (heta : (P.H N : ℤ) - 1 - eta = s * p) (hetaP : (P.H N : ℤ) - 1 - etaP = sP * p)
    (hpsi : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ eta → eta ≤ j % p + dm →
      ∀ y ∈ V1, S.prof.psi (P.H N) (j / p) s y = γ y)
    {m ilo Pmax : ℕ} (V2 : Submodule (ZMod p) (Fin S.K → ZMod p))
    (hPmax : Pmax + p ≤ etaP) (hilo : etaP + 1 ≤ ilo + 2 * p) (hsep : Pmax < e0 ∨ eta < ilo + p)
    (hmle : ilo + m ≤ Pmax + 1) (hmp : m ≤ p)
    (sc : Fin m → Fin S.D → ZMod p)
    (hrel : ∀ i : Fin m, ∑ t, C (sc i t) * S.lam t =
      X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ)))
    (hind : ∀ cc : Fin m → ZMod p,
      ∑ i, C (cc i) * (X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ))) = 0 →
        cc = 0)
    (hVpsi : ∀ j, P.b N ≤ j → j < P.L N → p + j % p ≤ etaP → ilo ≤ etaP - p - j % p →
      etaP - p - j % p ≤ Pmax → ∀ y ∈ V2,
        S.prof.psi (P.H N) (j / p) sP y = S.prof.psi (P.H N) (j / p) ((sP : ℤ) + 1) y) :
    Dh * finrank (ZMod p) V1 + m * finrank (ZMod p) V2 ≤
      nullity P N p + e0 * finrank (ZMod p) V1 + (p - P.q N - v) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨Pp, hPpdef⟩ : ∃ Pp : Fin m → (ZMod p)[X],
      Pp = fun i : Fin m => (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) := ⟨_, rfl⟩
  have hPdeg : ∀ i, (Pp i).natDegree ≤ Pmax := fun i => by
    rw [hPpdef]; show (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]).natDegree ≤ Pmax
    rw [natDegree_X_pow]; have := i.isLt; omega
  have hPlo : ∀ i e, e < ilo → (Pp i).coeff e = 0 := fun i e he => by
    rw [hPpdef]; show (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]).coeff e = 0
    rw [coeff_X_pow, if_neg (by omega)]
  have hrel' : ∀ i, ∑ t, C (sc i t) * S.lam t = X ^ p * Pp i - Pp i := by
    intro i; rw [hPpdef]; exact hrel i
  have hind' : ∀ cc : Fin m → ZMod p, ∑ i, C (cc i) * (X ^ p * Pp i - Pp i) = 0 → cc = 0 := by
    intro cc; rw [hPpdef]; exact hind cc
  -- jets of the J-flat component vanish
  have hjetU : ∀ u : Fin Dh → V1, S.lowJets Dh V1 e0 u = 0 → ∀ e < e0,
      wv S.lam (S.lowEmbed Dh V1 u) e = 0 := by
    intro u hu e he
    have := congrFun hu ⟨e, he⟩
    have h3 := S.lowJets_apply Dh V1 e0 u ⟨e, he⟩
    rw [this] at h3
    simpa using h3.symm
  have hhiF : ∀ (u : Fin Dh → V1) (e : ℕ), eta < e → wv S.lam (S.lowEmbed Dh V1 u) e = 0 := by
    intro u e he
    unfold wv
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases hd : d.val < Dh
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ((hdeg d hd).trans hdm) he), zero_smul]
    · rw [S.lowEmbed_zero Dh V1 _ d (by omega), smul_zero]
  have hzero : ∀ (u : Fin Dh → V1) (y : Fin m → V2), S.lowJets Dh V1 e0 u = 0 →
      S.lowEmbed Dh V1 u + S.tensorMap V2 sc y = 0 → u = 0 ∧ y = 0 := by
    intro u y hu ha
    have hy : y = 0 := by
      funext i
      apply Subtype.ext
      funext k
      rcases hsep with hPe0 | hPe1
      · have hw : ∀ e, e < e0 → wv S.lam (S.tensorMap V2 sc y) e = 0 := by
          intro e he
          have h1 : wv S.lam (S.lowEmbed Dh V1 u + S.tensorMap V2 sc y) e = 0 := by
            rw [ha]; unfold wv; simp
          rw [wv_add, hjetU u hu e he, zero_add] at h1
          exact h1
        have hi : ilo + (i : ℕ) < e0 := by have := i.isLt; omega
        have := congrFun (hw (ilo + (i : ℕ)) hi) k
        rw [S.wv_tensor V2 sc Pp hrel'] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        have hcoef : ∀ i' : Fin m, (X ^ p * Pp i' - Pp i').coeff (ilo + (i : ℕ)) =
            if i' = i then -1 else 0 := by
          intro i'
          rw [hPpdef]
          show (X ^ p * (X ^ (ilo + (i' : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i' : ℕ))).coeff _ = _
          rw [← pow_add, coeff_sub, coeff_X_pow, coeff_X_pow]
          have hi1 := i.isLt
          have hi2 := i'.isLt
          by_cases hii : i' = i
          · subst hii
            rw [if_neg (by omega), if_pos rfl, if_pos rfl]; simp
          · rw [if_neg (by omega), if_neg (by intro h; apply hii; exact Fin.ext (by omega))]
            simp [hii]
        simp only [hcoef] at this
        simpa using this
      · have hw : ∀ e, eta < e → wv S.lam (S.tensorMap V2 sc y) e = 0 := by
          intro e he
          have h1 : wv S.lam (S.lowEmbed Dh V1 u + S.tensorMap V2 sc y) e = 0 := by
            rw [ha]; unfold wv; simp
          rw [wv_add, hhiF u e he, zero_add] at h1
          exact h1
        have hi : eta < ilo + (i : ℕ) + p := by omega
        have := congrFun (hw (ilo + (i : ℕ) + p) hi) k
        rw [S.wv_tensor V2 sc Pp hrel'] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        have hcoef : ∀ i' : Fin m, (X ^ p * Pp i' - Pp i').coeff (ilo + (i : ℕ) + p) =
            if i' = i then 1 else 0 := by
          intro i'
          rw [hPpdef]
          show (X ^ p * (X ^ (ilo + (i' : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i' : ℕ))).coeff _ = _
          rw [← pow_add, coeff_sub, coeff_X_pow, coeff_X_pow]
          have hi1 := i.isLt
          have hi2 := i'.isLt
          by_cases hii : i' = i
          · subst hii
            rw [if_pos (by omega), if_neg (by omega)]; simp
          · rw [if_neg (by intro h; apply hii; exact Fin.ext (by omega)), if_neg (by omega)]
            simp [hii]
        simp only [hcoef] at this
        simpa using this
    refine ⟨?_, hy⟩
    have h2 : S.lowEmbed Dh V1 u = 0 := by
      rw [hy, map_zero, add_zero] at ha
      exact ha
    exact S.lowEmbed_injective hDh V1 (by rw [h2, map_zero])
  -- atoms in the range of `sumPsi`
  have hatom : ∀ a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)), ∃ (u : Fin Dh → V1)
      (y : Fin m → V2), S.lowJets Dh V1 e0 u = 0 ∧ a.1.1 = S.lowEmbed Dh V1 u ∧
        a.1.2 = S.tensorMap V2 sc y := by
    intro a
    obtain ⟨⟨u, y⟩, hw⟩ := LinearMap.mem_range.mp a.2
    refine ⟨u.1, y, LinearMap.mem_ker.mp u.2, ?_, ?_⟩
    · rw [← hw]; rfl
    · rw [← hw]; rfl
  have hξinj : Function.Injective (S.sumXi Dh V1 e0 V2 sc) := by
    refine injective_of_zero _ fun a ha => ?_
    obtain ⟨u, y, hu, h1, h2⟩ := hatom a
    rw [sumXi_apply, h1, h2] at ha
    obtain ⟨hu0, hy0⟩ := hzero u y hu ha
    apply Subtype.ext
    apply Prod.ext
    · show a.1.1 = 0
      rw [h1, hu0, map_zero]
    · show a.1.2 = 0
      rw [h2, hy0, map_zero]
  have hflat : ∀ a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)),
      ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ ℓ : ZMod p, (if ℓ.val ≤ eta then γ (wv S.lam a.1.1 (eta - ℓ.val)) else 0) = G.eval ℓ := by
    intro a
    obtain ⟨u, y, hu, h1, h2⟩ := hatom a
    rw [h1]
    exact S.flat_poly_data γ hv hdm hdvd hdeg he0 _ (fun d hd => S.lowEmbed_zero Dh V1 _ d hd)
      (hjetU u hu)
  have hpolyS : ∀ a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)),
      ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
        ∀ x, (S.sumS Dh V1 e0 V2 sc eta γ) a x = G.eval x := fun u => by
    obtain ⟨G, hG, hGe⟩ := hflat u
    exact ⟨G, hG, fun ℓ => (S.sumS_apply Dh V1 e0 V2 sc eta γ u ℓ).trans (hGe ℓ)⟩
  have hrespS : ∀ (a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc))) (j : ℕ),
      P.b N ≤ j → j < P.L N →
        S.resp (j / p) (j % p) (S.sumXi Dh V1 e0 V2 sc a) =
          (S.sumS Dh V1 e0 V2 sc eta γ) a (j : ZMod p) := fun a j h1 h2 => by
    obtain ⟨u, y, hu, hx1, hx2⟩ := hatom a
    have hell : j % p < p := Nat.mod_lt _ hp0
    rw [sumXi_apply, hx1, hx2, resp_add]
    rw [S.period_resp_zero V2 hetaP hPmax hilo Pp hPdeg hPlo sc hrel' hVpsi y j h1 h2,
      add_zero, sumS_apply, hx1]
    have hhi : ∀ e, eta < e → wv S.lam (S.lowEmbed Dh V1 u) e = 0 := by
      intro e he
      unfold wv
      refine Finset.sum_eq_zero fun d _ => ?_
      by_cases hd : d.val < Dh
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ((hdeg d hd).trans hdm) he), zero_smul]
      · rw [S.lowEmbed_zero Dh V1 _ d (by omega), smul_zero]
    rw [S.resp_flat he0 heta (j / p) (j % p) hell _ hhi (hjetU u hu)]
    by_cases hl : j % p ≤ eta
    · simp only [hl, if_true, ZMod.val_natCast]
      by_cases hc : e0 + j % p ≤ eta ∧ eta ≤ j % p + dm
      · exact hpsi j h1 h2 hc.1 hc.2 _ (S.wv_lowEmbed_mem Dh V1 _ _)
      · by_cases hc1 : e0 + j % p ≤ eta
        · have hz : wv S.lam (S.lowEmbed Dh V1 u) (eta - j % p) = 0 := by
            unfold wv
            refine Finset.sum_eq_zero fun d _ => ?_
            by_cases hd : d.val < Dh
            · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg d hd) (by omega)),
                zero_smul]
            · rw [S.lowEmbed_zero Dh V1 _ d (by omega), smul_zero]
          rw [hz, map_zero, map_zero]
        · rw [hjetU u hu (eta - j % p) (by omega), map_zero, map_zero]
    · simp [hl, ZMod.val_natCast]
  have h := S.slot_nullity_jflat0 hP hN hp2 hH (S.sumXi Dh V1 e0 V2 sc) (fun a => hdom _) hξinj v
    (S.sumS Dh V1 e0 V2 sc eta γ) hpolyS hrespS
  -- dimension of the atom space
  have hψinj : Function.Injective (S.sumPsi Dh V1 e0 V2 sc) := by
    intro w w' hww
    rw [sumPsi_apply, sumPsi_apply] at hww
    have h1 : S.lowEmbed Dh V1 w.1.1 = S.lowEmbed Dh V1 w'.1.1 := congrArg Prod.fst hww
    have h2 : S.tensorMap V2 sc w.2 = S.tensorMap V2 sc w'.2 := congrArg Prod.snd hww
    exact Prod.ext (Subtype.ext (S.lowEmbed_injective hDh V1 h1))
      (S.period_injective V2 Pp sc hrel' hind' h2)
  have hA := LinearMap.finrank_range_of_inj hψinj
  have hA2 : finrank (ZMod p) (↥(LinearMap.ker (S.lowJets Dh V1 e0)) × (Fin m → V2)) =
      finrank (ZMod p) (LinearMap.ker (S.lowJets Dh V1 e0)) + m * finrank (ZMod p) V2 := by
    have hpg := finrank_prod_gen (p := p) (M := ↥(LinearMap.ker (S.lowJets Dh V1 e0)))
      (M' := Fin m → V2)
    refine hpg.trans ?_
    rw [Module.finrank_pi_fintype]
    simp
  have hrn := (S.lowJets Dh V1 e0).finrank_range_add_finrank_ker
  have hdim : finrank (ZMod p) (Fin Dh → V1) = Dh * finrank (ZMod p) V1 := by
    simp [Module.finrank_pi_fintype]
  have hjr := S.finrank_range_lowJets_le Dh V1 e0
  omega

#print axioms sum_nullity2
end
end CatalanMeasure.GenD.Uniform.W.Tier3
