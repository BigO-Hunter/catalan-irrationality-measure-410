module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMom

@[expose] public section

/-!
# `constTotal − constant → Q(t)`: the limit glue of `hrA`, `hrB` (Theorem A, lane E1b, item 18)

For a family `D : ℕ → SignedData` of one trial (`Family D F`) with `ν_N = p_N` (the number of free rows),
`sp = σ ν`, `g = γ ν`, `Cb`, `b`, `K` constant, the constant of the `N`-th configuration satisfies
(`const_decomp`, an algebraic identity, `p/ν = 1`, `t = mneg`)

  `constTotal p − constant = −(1+η) log 2 + ‖v‖²/2 + 2η‖p‖² + (1−η) refEnergy μ + 2(‖a‖² − γ Sup − ra)
       + σ² B + ½ ip(R,R) − ½ ip(mpos,mpos) + errTerm`,

with `errTerm (D N) → 0` (`errTerm_tendsto`: damping `e_N → 0`, `ν_N → ∞`, `log (1/(1−τ²))/ν → 0`).
`constTotal_sub_constant_le` is exactly `hrA`/`hrB` of `SignedNearBounds.ofEnds`: from rational bounds of the
five norms/energies (`EvalNorm`, `EvalRefLog.refEnergy_enc`), of `ra`, `ip R R`, of the Σ over `b`, and the eventual
lower bound of `ip(mpos, mpos)` (`EvalRefMom.ip_mpos_lower_eventually`), it gives
`constTotal − constant ≤ rLim … + ε` eventually.  `rLim` is the rational `rA`/`rB`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open OAI.InternalCatalan
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open MeasureTheory Set Filter Topology

noncomputable section

/-- Equality of log forms from the two parts: the per-job literal `Job.lf j = ⟨c0, ts⟩` is the conjunction of two
`decide +kernel` checks `(Job.lf j).c0 = c0` and `(Job.lf j).ts = ts` (rational data of the literals). -/
theorem LF.eq_of_parts {f g : LF} (h0 : f.c0 = g.c0) (h1 : f.ts = g.ts) : f = g := by
  cases f with
  | mk a b =>
    cases g with
    | mk c d =>
      dsimp only at h0 h1
      subst h0
      subst h1
      rfl

/-- Every term of `constTotal − constant` that vanishes as `e → 0`, `ν → ∞`. -/
def errTerm (D : SignedData) : ℝ :=
  4 * D.e * (∑' j, |D.v j|) + pinZeroError D.ν D.e + D.eD7 1 + D.etaErr + D.hadErr +
    2 * trialPairError D.ν D.e D.a +
    2 * ((D.sp : ℝ) / D.ν ^ 2) * (∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2)

/-- `constTotal − constant` at `p = ν` free rows, with `t = mneg` (`Spec.ht`). -/
theorem const_decomp (D : SignedData) (p : ℕ) (hν : D.ν ≠ 0) (hp : (p : ℝ) = D.ν)
    (ht : D.t = mneg D.μ D.τ) :
    D.constTotal p - D.constant =
      -(1 + D.η) * Real.log 2 + barrierTrialNormSq D.v / 2 + 2 * D.η * barrierTrialNormSq D.p +
        (1 - D.η) * refEnergy D.μ +
        2 * (barrierTrialNormSq D.a - ((D.g : ℝ) / D.ν) * D.Sup - D.ra) +
        ((D.sp : ℝ) / D.ν) ^ 2 *
          (∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
        (1 / 2) * ip D.R D.R - (1 / 2) * ip (mpos D.μ D.τ) (mpos D.μ D.τ) + errTerm D := by
  have h1 : (p : ℝ) / D.ν = 1 := by rw [hp]; exact div_self hν
  unfold SignedData.constTotal SignedData.numDenRef SignedData.Kq errTerm
  rw [h1, ht]
  ring

/-- The `r_N` of the `x log x` limit. -/
theorem negLog_facts (e : ℝ) (he0 : 0 < e) (he1 : e < 1) :
    0 ≤ -Real.log e ∧
      -Real.log e ≤ Real.log (1 / (1 - (1 - e) ^ 2)) + Real.log 2 := by
  refine ⟨?_, ?_⟩
  · have := Real.log_nonpos he0.le he1.le
    linarith
  · have hq : 1 - (1 - e) ^ 2 = e * (2 - e) := by ring
    have h2e : 0 < 2 - e := by linarith
    have hlog : Real.log (1 / (1 - (1 - e) ^ 2)) = -(Real.log e + Real.log (2 - e)) := by
      rw [hq, one_div, Real.log_inv, Real.log_mul he0.ne' h2e.ne']
    have hle : Real.log (2 - e) ≤ Real.log 2 :=
      Real.log_le_log h2e (by linarith)
    rw [hlog]
    linarith

/-- The exact decomposition of `errTerm` into the six vanishing sequences. -/
theorem errTerm_eq (D : SignedData) (hν : D.ν ≠ 0) (σ Cb0 η0 cv cp ca B2 : ℝ)
    (hsp : (D.sp : ℝ) = σ * D.ν) (hCb : D.Cb = Cb0) (hη : D.η = η0)
    (hcv : ∑' j, |D.v j| = cv) (hcp : ∑' j, |D.p j| = cp) (hca : ∑' k, |D.a k| = ca)
    (hB2 : ∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2 = B2) :
    errTerm D =
      (4 * cv + 4 * η0 * cp + 4 * η0 + 4 * ca + 17) * D.e +
        ((11 / 4 + η0) * Real.log 2 + 2 * σ * B2) * D.ν⁻¹ +
        (5 / 2) * ((-Real.log D.e) * D.ν⁻¹) +
        (2 * η0 + 5 / 2) * (Real.log (1 / (1 - D.τ ^ 2)) * D.ν⁻¹) +
        ((1 - η0) * (24 * Cb0 + 32)) * (1 - D.τ ^ 2) +
        ((1 - η0) * (24 * Cb0)) * ((1 - D.τ ^ 2) * Real.log (1 / (1 - D.τ ^ 2))) := by
  have hlog : Real.log (1 - D.τ ^ 2) = -Real.log (1 / (1 - D.τ ^ 2)) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hspν : (D.sp : ℝ) / D.ν ^ 2 = σ * D.ν⁻¹ := by
    rw [hsp]; field_simp
  have hτ' : realEnergyTau D.e = D.τ := rfl
  unfold errTerm pinZeroError SignedData.etaErr SignedData.hadErr SignedData.eD7 trialPairError
  rw [hτ', hlog, hspν, hCb, hcv, hcp, hca, hB2, hη]
  ring

theorem errTerm_tendsto {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F)
    (σ Cb0 : ℝ) (hsp : ∀ N, ((D N).sp : ℝ) = σ * (D N).ν) (hCb : ∀ N, (D N).Cb = Cb0)
    (bL : ℕ → ℝ) (KL : ℕ) (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL) :
    Tendsto (fun N => errTerm (D N)) atTop (𝓝 0) := by
  -- the constants
  obtain ⟨cv, hcv⟩ : ∃ cv : ℝ, ∀ N, ∑' j, |(D N).v j| = cv :=
    ⟨∑' j, |(D 0).v j|, fun N => by rw [(hf.spec N).hv, (hf.spec 0).hv]⟩
  obtain ⟨cp, hcp⟩ : ∃ cp : ℝ, ∀ N, ∑' j, |(D N).p j| = cp :=
    ⟨∑' j, |(D 0).p j|, fun N => by rw [(hf.spec N).hp, (hf.spec 0).hp]⟩
  obtain ⟨ca, hca⟩ : ∃ ca : ℝ, ∀ N, ∑' k, |(D N).a k| = ca :=
    ⟨∑' k, |(D 0).a k|, fun N => by rw [(hf.spec N).ha, (hf.spec 0).ha]⟩
  obtain ⟨B2, hB2⟩ : ∃ B2 : ℝ, ∀ N, ∑ i ∈ Finset.range (D N).K, (D N).b (i + 1) ^ 2 = B2 :=
    ⟨∑ i ∈ Finset.range KL, bL (i + 1) ^ 2, fun N => by rw [hKL N, hbL N]⟩
  obtain ⟨η0, hη⟩ : ∃ η0 : ℝ, ∀ N, (D N).η = η0 := ⟨F.η, fun N => (hf.spec N).hη⟩
  have hel : ∀ N, 0 < (D N).e ∧ (D N).e < 1 := fun N => by
    have h1 := (hf.spec N).hτ.2
    have h2 := (hf.spec N).hτ.1
    simp only [SignedData.τ, realEnergyTau] at h1 h2
    constructor <;> linarith
  -- the base sequences
  have hE : Tendsto (fun N => (D N).e) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hf.hτ
    simp only [sub_self] at h
    refine h.congr (fun N => ?_)
    simp [SignedData.τ, realEnergyTau]
  have hA : Tendsto (fun N => ((D N).ν)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hf.hν
  have hq : Tendsto (fun N => 1 - (D N).τ ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hf.hτ.pow 2)
    simpa using h
  have hu : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) * ((D N).ν)⁻¹) atTop (𝓝 0) :=
    hf.hℓ.congr (fun N => div_eq_mul_inv _ _)
  have hr1 : Tendsto (fun N => (1 - (D N).τ ^ 2) * Real.log (1 - (D N).τ ^ 2)) atTop (𝓝 0) := by
    have h := (Real.continuous_mul_log.tendsto 0).comp hq
    rw [zero_mul] at h
    exact h
  have hr : Tendsto (fun N => (1 - (D N).τ ^ 2) * Real.log (1 / (1 - (D N).τ ^ 2))) atTop (𝓝 0) := by
    have h := hr1.neg
    simp only [neg_zero] at h
    refine h.congr (fun N => ?_)
    simp [one_div, Real.log_inv]
  -- w_N = (-log e) / ν, squeezed
  have hw : Tendsto (fun N => (-Real.log (D N).e) * ((D N).ν)⁻¹) atTop (𝓝 0) := by
    have hup : Tendsto (fun N => Real.log (1 / (1 - (D N).τ ^ 2)) * ((D N).ν)⁻¹ +
        Real.log 2 * ((D N).ν)⁻¹) atTop (𝓝 0) := by
      have h := hu.add (hA.const_mul (Real.log 2))
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hf.hν.eventually_gt_atTop 0] with N hN
      exact mul_nonneg (negLog_facts _ (hel N).1 (hel N).2).1 (inv_nonneg.mpr hN.le)
    · filter_upwards [hf.hν.eventually_gt_atTop 0] with N hN
      have h2 := (negLog_facts _ (hel N).1 (hel N).2).2
      have hτe : (D N).τ = 1 - (D N).e := rfl
      show -Real.log (D N).e * ((D N).ν)⁻¹ ≤ Real.log (1 / (1 - (D N).τ ^ 2)) * ((D N).ν)⁻¹ +
        Real.log 2 * ((D N).ν)⁻¹
      rw [hτe]
      have hinv : 0 ≤ ((D N).ν)⁻¹ := inv_nonneg.mpr hN.le
      nlinarith [mul_le_mul_of_nonneg_right h2 hinv]
  -- the combination tends to 0
  have hlim : Tendsto (fun N =>
      (4 * cv + 4 * η0 * cp + 4 * η0 + 4 * ca + 17) * (D N).e +
        ((11 / 4 + η0) * Real.log 2 + 2 * σ * B2) * ((D N).ν)⁻¹ +
        (5 / 2) * ((-Real.log (D N).e) * ((D N).ν)⁻¹) +
        (2 * η0 + 5 / 2) * (Real.log (1 / (1 - (D N).τ ^ 2)) * ((D N).ν)⁻¹) +
        ((1 - η0) * (24 * Cb0 + 32)) * (1 - (D N).τ ^ 2) +
        ((1 - η0) * (24 * Cb0)) * ((1 - (D N).τ ^ 2) *
          Real.log (1 / (1 - (D N).τ ^ 2)))) atTop (𝓝 0) := by
    have h := (((((hE.const_mul (4 * cv + 4 * η0 * cp + 4 * η0 + 4 * ca + 17)).add
      (hA.const_mul ((11 / 4 + η0) * Real.log 2 + 2 * σ * B2))).add
      (hw.const_mul (5 / 2))).add (hu.const_mul (2 * η0 + 5 / 2))).add
      (hq.const_mul ((1 - η0) * (24 * Cb0 + 32)))).add (hr.const_mul ((1 - η0) * (24 * Cb0)))
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [hf.hν.eventually_gt_atTop 0] with N hN
  exact (errTerm_eq (D N) hN.ne' σ Cb0 η0 cv cp ca B2 (hsp N) (hCb N) (hη N) (hcv N) (hcp N)
    (hca N) (hB2 N)).symm

/-- The hypothesis `hM` of `constTotal_sub_constant_le` from `ip_mpos_lower_eventually` (`Spec.bd`, `hμT hμF hμTn hμFn`,
`Family.hτ`, `Spec.hτ`). -/
theorem hM_of_family {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F) (R : RefQ) (hR : R.OK)
    (hμ : ∀ N, IsRefQ (D N).μ R) (K : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ((ipPartQ R K : ℚ) : ℝ) - ε ≤ ip (mpos (D N).μ (D N).τ) (mpos (D N).μ (D N).τ) :=
  fun ε hε => ip_mpos_lower_eventually R hR (C := fun N => (D N).Cb) (fun N => (D N).μ) hμ
    (fun N => (hf.spec N).bd) (fun N => (D N).τ) hf.hτ (fun N => (hf.spec N).hτ) K hε

/-- The rational `rA`/`rB`: the limit of `constTotal − constant`. -/
def rLim (η l2 Vq Pq Rq Aq raq iRRq Lq γ SupV σ Bq : ℝ) : ℝ :=
  -(1 + η) * l2 + Vq / 2 + 2 * η * Pq + (1 - η) * Rq + 2 * (Aq - γ * SupV - raq) +
    σ ^ 2 * Bq + iRRq / 2 - Lq / 2

/-- **Items 15–18 glue: `hrA` / `hrB`.**  `Vq, Pq, Aq` bound `‖v‖², ‖p‖², ‖a‖²` (`EvalNorm`), `Rq` bounds `refEnergy μ`
(`refEnergy_enc`), `raq ≤ ra`, `iRRq ≥ ip R R` (finite sums), `Bq ≥ Σ_{i<K} 2 b_{i+1}²/(i+1)`, `l2 ≤ log 2`
(`log2_bounds`), and `hM` is `ip_mpos_lower_eventually`.  Conclusion: eventually
`(D N).constTotal (p N) − (D N).constant ≤ rLim … + ε`. -/
theorem constTotal_sub_constant_le {D : ℕ → SignedData} {F : TrialForm} (hf : Family D F)
    (p : ℕ → ℕ) (hνp : ∀ N, (D N).ν = (p N : ℝ))
    (σ γ Cb0 : ℝ)
    (hsp : ∀ N, ((D N).sp : ℝ) = σ * (D N).ν) (hg : ∀ N, ((D N).g : ℝ) = γ * (D N).ν)
    (hCb : ∀ N, (D N).Cb = Cb0)
    (bL : ℕ → ℝ) (KL : ℕ) (hbL : ∀ N, (D N).b = bL) (hKL : ∀ N, (D N).K = KL)
    (l2 Vq Pq Rq Aq raq iRRq Lq Bq : ℝ) (hl2 : l2 ≤ Real.log 2)
    (hV : ∀ N, barrierTrialNormSq (D N).v ≤ Vq) (hP : ∀ N, barrierTrialNormSq (D N).p ≤ Pq)
    (hA : ∀ N, barrierTrialNormSq (D N).a ≤ Aq) (hRef : ∀ N, refEnergy (D N).μ ≤ Rq)
    (hra : ∀ N, raq ≤ (D N).ra) (hRR : ∀ N, ip (D N).R (D N).R ≤ iRRq)
    (hB : ∑ i ∈ Finset.range KL, 2 * bL (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) ≤ Bq)
    (hM : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      Lq - ε ≤ ip (mpos (D N).μ (D N).τ) (mpos (D N).μ (D N).τ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (D N).constTotal (p N) - (D N).constant ≤
        rLim F.η l2 Vq Pq Rq Aq raq iRRq Lq γ F.Sup σ Bq + ε := by
  intro ε hε
  have hE := errTerm_tendsto hf σ Cb0 hsp hCb bL KL hbL hKL
  have hE' : ∀ᶠ N in atTop, errTerm (D N) < ε / 2 :=
    hE.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)
  have hM' := hM (ε / 2) (by linarith)
  filter_upwards [hE', hM', hf.hν.eventually_gt_atTop 0] with N h1 h2 h3
  show (D N).constTotal (p N) - (D N).constant ≤
    rLim F.η l2 Vq Pq Rq Aq raq iRRq Lq γ F.Sup σ Bq + ε
  have hspec := hf.spec N
  have hdec := const_decomp (D N) (p N) h3.ne' (hνp N).symm hspec.ht
  have hη : (D N).η = F.η := hspec.hη
  have hSup : (D N).Sup = F.Sup := hspec.hSup
  have hη0 : 0 ≤ F.η := hspec.hηI.1
  have hη1 : F.η < 1 / 2 := hspec.hηI.2
  have hνne : (D N).ν ≠ 0 := h3.ne'
  have hS : ((D N).sp : ℝ) / (D N).ν = σ := by
    rw [hsp N]; field_simp
  have hG : ((D N).g : ℝ) / (D N).ν = γ := by
    rw [hg N]; field_simp
  have hBs : ∑ i ∈ Finset.range (D N).K, 2 * (D N).b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) ≤ Bq := by
    rw [hKL N, hbL N]; exact hB
  rw [hη, hSup, hS, hG] at hdec
  rw [hdec]
  have m1 : (1 + F.η) * l2 ≤ (1 + F.η) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 (by linarith)
  have m2 : F.η * barrierTrialNormSq (D N).p ≤ F.η * Pq :=
    mul_le_mul_of_nonneg_left (hP N) hη0
  have m3 : (1 - F.η) * refEnergy (D N).μ ≤ (1 - F.η) * Rq :=
    mul_le_mul_of_nonneg_left (hRef N) (by linarith)
  have m4 : σ ^ 2 * ∑ i ∈ Finset.range (D N).K, 2 * (D N).b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) ≤
      σ ^ 2 * Bq :=
    mul_le_mul_of_nonneg_left hBs (sq_nonneg σ)
  have n1 := hV N
  have n2 := hA N
  have n3 := hra N
  have n4 := hRR N
  unfold rLim
  nlinarith [m1, m2, m3, m4, n1, n2, n3, n4, h1, h2]

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.const_decomp
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.errTerm_tendsto
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.constTotal_sub_constant_le
