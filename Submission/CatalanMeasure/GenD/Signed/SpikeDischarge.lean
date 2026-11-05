module

public import Submission.CatalanMeasure.GenD.Signed.SpikeCompare
public import Submission.CatalanMeasure.GenD.Signed.Spike
public import Submission.CatalanMeasure.GenD.Signed.EnergyFixed

/-!
# Discharge of `SpikeCompare` and `SpikeCompareFixed` (lane SC)

`spikeCompare_of_class` and `spikeCompareFixed_of_class` derive the A7 hypotheses of
`Energy.lean` / `EnergyFixed.lean` from the raw ingredients `spike_reduction_rows` (`Spike.lean`)
and `spike_compare` (`SpikeCompare.lean`).

* `SpikeWitness` / `SpikeCls`: the concrete class.  It carries the split of the positives into the
  rest `y` (non-spikes, `y ≤ 1 - θ`) and the spikes `z` (`1 - θ < z`), the count `m` with
  `M = 2m` or `M + 1 = 2m` (a phantom spike `zph` for odd `M`), the (P') data on the denominator
  trial, the margin `c'` of the negatives (and, via `c' ≤ θ`, of the non-spike positives), and the
  cost bound per spike (`hcost`, which also accounts for the phantom).
* Matching lemmas: `spikeNumB_eq`, `spikeDenB_eq`, `spikeTerm_eq`, `crossBeta_rows3`, `logRatio_eq`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set MeasureTheory Filter Topology OAI.InternalCatalan
open CatalanMeasure.GenD.Signed (heineZ)

noncomputable section

/-! ### A. Small utilities -/

theorem heineZ_congr_Icc {s : ℕ} {f g : ℝ → ℝ} (h : ∀ u ∈ Icc (-1 : ℝ) 1, f u = g u) :
    heineZ s f = heineZ s g := by
  unfold heineZ
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show (Matrix.vandermonde fun l => Real.cos (θ l)).det ^ 2 * ∏ l, f (Real.cos (θ l)) =
    (Matrix.vandermonde fun l => Real.cos (θ l)).det ^ 2 * ∏ l, g (Real.cos (θ l))
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  exact h _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem sum_rows3 (F : ℝ → ℝ → ℝ) {a b c : ℕ} (w1 y1 : Fin a → ℝ) (w2 y2 : Fin b → ℝ)
    (w3 y3 : Fin c → ℝ) :
    ∑ l : Fin (a + b + c), F (Fin.append (Fin.append w1 w2) w3 l)
        (Fin.append (Fin.append y1 y2) y3 l) =
      ∑ l, F (w1 l) (y1 l) + ∑ l, F (w2 l) (y2 l) + ∑ l, F (w3 l) (y3 l) := by
  rw [sum_fin_append, sum_fin_append]

theorem tsum_eq_range {f : ℕ → ℝ} {K : ℕ} (h : ∀ k, K ≤ k → f k = 0) :
    ∑' k, f k = ∑ k ∈ Finset.range K, f k := by
  rw [tsum_eq_sum (s := Finset.range K)]
  intro k hk
  exact h k (by simpa using hk)

/-! ### B. The extended spike family (phantom for odd `M`) -/

/-- The spike family `z` extended by the phantom `zph` to `2m` members. -/
def extFam {M : ℕ} (z : Fin M → ℝ) (zph : ℝ) (m : ℕ) : Fin (2 * m) → ℝ :=
  fun i => if h : i.val < M then z ⟨i.val, h⟩ else zph

theorem extFam_mem {M m : ℕ} (z : Fin M → ℝ) (zph lo : ℝ) (hz : ∀ i, lo ≤ z i ∧ z i < 1)
    (hph : lo ≤ zph ∧ zph < 1) (p : Fin (2 * m)) :
    lo ≤ extFam z zph m p ∧ extFam z zph m p < 1 := by
  unfold extFam
  split_ifs with h
  · exact hz _
  · exact hph

/-! ### C. Matching `numB`, `denB`, `spikeTerm` and the Heine ratio -/

theorem crossBeta_rows3 (ν τ : ℝ) {k q' M : ℕ} (x : Fin k → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ)
    (n : ℕ) :
    crossBeta τ (Fin.append (negPosW ν k q') (spikeW ν M)) (Fin.append (Fin.append x y) z) n =
      crossBeta τ (crossW (k := k) (q := q' + M) ν) (Fin.append x (Fin.append y z)) n := by
  unfold crossBeta
  congr 2
  have h1 := sum_rows3 (fun w v => w * v ^ n) (fun _ : Fin k => 1 / (2 * ν)) x (spikeW ν q') y
    (spikeW ν M) z
  have h2 := sum_fin_append (fun _ : Fin k => 1 / (2 * ν)) x
    (fun _ : Fin (q' + M) => -(1 / (2 * ν))) (Fin.append y z) (fun w v => w * v ^ n)
  have h3 := row_sum_split (fun v => -(1 / (2 * ν)) * v ^ n) y z
  unfold negPosW
  try simp only at h1 h2 h3
  rw [h1]
  unfold crossW
  rw [h2, h3]
  unfold spikeW
  ring

theorem crossTiltNormRef_rows3 {ν : ℝ} (hν : 0 < ν) (τ : ℝ) {k q' M : ℕ} (x : Fin k → ℝ)
    (y : Fin q' → ℝ) (z : Fin M → ℝ) (R : ℕ → ℝ) :
    crossTiltNormRef τ (Fin.append (negPosW ν k q') (spikeW ν M))
        (Fin.append (Fin.append x y) z) (refTilt R) =
      (1 / 4) * ip (fun n => powSum τ ν x n - powSum τ ν (Fin.append y z) n - R n)
        (fun n => powSum τ ν x n - powSum τ ν (Fin.append y z) n - R n) := by
  rw [← crossTiltNormRef_append hν x (Fin.append y z) R]
  unfold crossTiltNormRef
  refine tsum_congr fun n => ?_
  rw [crossBeta_rows3]

theorem spikeNumB_eq (D : SignedData) (hν : 0 < D.ν) {k q' M : ℕ} (x : Fin k → ℝ)
    (y : Fin q' → ℝ) (z : Fin M → ℝ) :
    spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp x y z =
      D.ν ^ 2 * D.numB x (Fin.append y z) := by
  unfold spikeNumB jTwoRhs SignedData.numB SignedData.numConst SignedData.ra
  rw [crossTiltNormRef_rows3 hν]
  have h1 := sum_rows3 (fun w v => w * barrierTrialS D.a (-(realEnergyTau D.e) * v))
    (fun _ : Fin k => 1 / (2 * D.ν)) x (spikeW D.ν q') y (spikeW D.ν M) z
  have h3 := row_sum_split (fun v => barrierTrialS D.a (-D.τ * v)) y z
  unfold negPosW
  try simp only at h1 h3
  rw [h1, h3]
  unfold spikeW SignedData.τ
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_neg_distrib, mul_neg, neg_mul]
  generalize ∑ i, barrierTrialS D.a (-realEnergyTau D.e * x i) = A
  generalize ∑ i, barrierTrialS D.a (-realEnergyTau D.e * y i) = B
  generalize ∑ i, barrierTrialS D.a (-realEnergyTau D.e * z i) = C
  field_simp
  ring

/-- `barrierTrialS` of a finitely supported trial is the finite sum. -/
theorem barrierTrialS_trunc {b : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0) (x : ℝ) :
    barrierTrialS b x = ∑ i ∈ Finset.range K, b (i + 1) * x ^ (i + 1) / ((i + 1 : ℕ) : ℝ) := by
  unfold barrierTrialS
  refine tsum_eq_range fun k hk => ?_
  rw [hb (k + 1) (by omega)]
  simp

theorem denPoly_eq {b : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0) (g : ℝ) :
    denPoly b K g = 2 * barrierTrialS b (-g) := by
  rw [barrierTrialS_trunc hb]
  unfold denPoly
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem spikeDenB_eq (D : SignedData) (hν : 0 < D.ν) (hb : ∀ i, D.K < i → D.b i = 0) {q' M : ℕ}
    (y : Fin q' → ℝ) (z : Fin M → ℝ) :
    spikeDenB D.b D.sp y z = D.ν ^ 2 * D.denB (Fin.append y z) := by
  unfold spikeDenB SignedData.denB SignedData.denConst
  have h3 := row_sum_split (fun v => denPoly D.b D.K v) y z
  try simp only at h3
  rw [h3]
  have e1 : ∑' i : ℕ, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) =
      ∑ i ∈ Finset.range D.K, 2 * D.b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) :=
    tsum_eq_range fun k hk => by rw [hb (k + 1) (by omega)]; simp
  have e2 : ∑' k : ℕ, D.b (k + 1) ^ 2 = ∑ i ∈ Finset.range D.K, D.b (i + 1) ^ 2 :=
    tsum_eq_range fun k hk => by rw [hb (k + 1) (by omega)]; simp
  have e3 : ∀ j, denPoly D.b D.K j = 2 * barrierTrialS D.b (-j) := fun j => denPoly_eq hb j
  simp only [e3, e1, e2, ← Finset.mul_sum]
  field_simp
  ring

theorem numB_equiv (D : SignedData) {k n q : ℕ} (σ : Fin n ≃ Fin q) (x : Fin k → ℝ)
    (g : Fin q → ℝ) : D.numB x (fun i => g (σ i)) = D.numB x g := by
  have hp : ∀ j, powSum D.τ D.ν (fun i => g (σ i)) j = powSum D.τ D.ν g j := fun j => by
    unfold powSum
    rw [Equiv.sum_comp σ (fun p => (D.τ * g p) ^ (j + 1))]
  have hs := Equiv.sum_comp σ (fun p => barrierTrialS D.a (-D.τ * g p))
  unfold SignedData.numB
  simp only [hp]
  rw [hs]

theorem denB_equiv (D : SignedData) {n q : ℕ} (σ : Fin n ≃ Fin q) (g : Fin q → ℝ) :
    D.denB (fun i => g (σ i)) = D.denB g := by
  have hs := Equiv.sum_comp σ (fun p => denPoly D.b D.K (g p))
  unfold SignedData.denB
  rw [hs]

theorem spikeTerm_eq (D : SignedData) {q q' M : ℕ} (σ : Fin (q' + M) ≃ Fin q) (gp : Fin q → ℝ)
    (y : Fin q' → ℝ) (z : Fin M → ℝ) (hσ : ∀ i, gp (σ i) = Fin.append y z i)
    (hy : ∀ j, y j ≤ 1 - D.θ) (hz : ∀ i, 1 - D.θ < z i) :
    D.spikeTerm gp = (1 / D.ν) * ((M : ℝ) * D.cs) := by
  unfold SignedData.spikeTerm
  rw [← Equiv.sum_comp σ (fun p => D.cs * (if 1 - D.θ < gp p then (1 : ℝ) else 0))]
  have : ∀ i, D.cs * (if 1 - D.θ < gp (σ i) then (1 : ℝ) else 0) =
      (fun v => D.cs * (if 1 - D.θ < v then (1 : ℝ) else 0)) (Fin.append y z i) := fun i => by
    rw [hσ]
  rw [Finset.sum_congr rfl fun i _ => this i,
    row_sum_split (fun v => D.cs * (if 1 - D.θ < v then (1 : ℝ) else 0)) y z]
  have hy0 : ∀ j, D.cs * (if 1 - D.θ < y j then (1 : ℝ) else 0) = 0 := fun j => by
    rw [if_neg (not_lt.mpr (hy j))]; simp
  have hz0 : ∀ i, D.cs * (if 1 - D.θ < z i then (1 : ℝ) else 0) = D.cs := fun i => by
    rw [if_pos (hz i)]; simp
  simp only [hy0, hz0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_zero,
    zero_add, nsmul_eq_mul]

/-- The Heine ratio of an arbitrary positive list, in the split form of `spike_reduction_rows`. -/
theorem logRatio_eq (sp : ℕ) {k q q' M : ℕ} (σ : Fin (q' + M) ≃ Fin q) (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ) (hσ : ∀ i, gp (σ i) = Fin.append y z i) :
    logRatioZ sp xn gp = logPref xn gp +
      (Real.log (heineZ sp (fun u => (∏ b, (1 + 2 * xn b * u + xn b ^ 2)) *
          ((∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) * ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹))) -
        Real.log (heineZ sp (fun u => (∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) *
          ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹))) := by
  have hprod : ∀ u : ℝ, ∏ p, (1 + 2 * gp p * u + gp p ^ 2)⁻¹ =
      (∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) * ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹ := fun u => by
    rw [← Equiv.prod_comp σ (fun p => (1 + 2 * gp p * u + gp p ^ 2)⁻¹), Fin.prod_univ_add]
    simp only [hσ, Fin.append_left, Fin.append_right]
  have hF1 : (fun u : ℝ => (∏ b, (1 + 2 * xn b * u + xn b ^ 2)) /
      ∏ p, (1 + 2 * gp p * u + gp p ^ 2)) = fun u => (∏ b, (1 + 2 * xn b * u + xn b ^ 2)) *
        ((∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) * ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹) := by
    funext u
    rw [div_eq_mul_inv, ← Finset.prod_inv_distrib, hprod]
  have hF2 : (fun u : ℝ => 1 / ∏ p, (1 + 2 * gp p * u + gp p ^ 2)) = fun u =>
      (∏ p, (1 + 2 * y p * u + y p ^ 2)⁻¹) * ∏ p, (1 + 2 * z p * u + z p ^ 2)⁻¹ := by
    funext u
    rw [one_div, ← Finset.prod_inv_distrib, hprod]
  unfold logRatioZ
  rw [hF1, hF2]
  ring


/-! ### D. The class -/

/-- The inputs of the spike lemmas that belong to the instance `D` (not to the configuration):
the hypotheses of `spike_compare` on the trial `a`, the reference tilt `refTilt D.R` with its
Frostman sup `D.Sup`, and the finitely supported denominator trial `D.b`. -/
structure SpikeEnv (D : SignedData) where
  hν : 0 < D.ν
  he : D.e ∈ Ioo (0 : ℝ) (1 / 8)
  hsp : (D.sp : ℝ) ≤ D.ν
  hθ : D.θ ∈ Ioo (0 : ℝ) 1
  ha : Summable fun k => |D.a k|
  hr : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * refTilt D.R (k + 1) ^ 2
  hra : Summable fun k : ℕ => refTilt D.R (k + 1) * D.a (k + 1)
  Qref : ℝ → ℝ
  hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => refTilt D.R (k + 1) *
    realEnergyTau D.e ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x)
  hℓ : ∀ x ∈ Icc (-1 : ℝ) 1, Qref x - 2 * barrierTrialT D.a x ≤ D.Sup
  hbK : ∀ i, D.K < i → D.b i = 0

/-- **The concrete class.**  A witness that the configuration `(xn, gp)` is in the spike class:
the positives are split (`σ`) into the rest `y` (non-spikes, `y ≤ 1 - θ`) and the `M` spikes `z`
(`1 - θ < z`); `M = 2m` or `M + 1 = 2m` (phantom `zph` in the odd case); the negatives need NO margin (one-sided
J3, `crossLog_le_dilate`; `c'` is the margin of the non-spike positives, `c' ≤ θ`); the denominator trial `D.b` with removal scale `ρ ≤ τ² (1 - θ)` satisfies (P') with `c1 > 0`;
and `hcost` is the cost bound: the cost `spikeCost` of the (extended) spike family, together with
the change of `NumB - DenB` caused by the phantom, is at most `ν cs M` (`cs` per capped positive). -/
structure SpikeWitness (D : SignedData) (c' : ℝ) {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) where
  q' : ℕ
  M : ℕ
  m : ℕ
  y : Fin q' → ℝ
  z : Fin M → ℝ
  zph : ℝ
  σ : Fin (q' + M) ≃ Fin q
  hσ : ∀ i, gp (σ i) = Fin.append y z i
  hM : M = 2 * m ∨ M + 1 = 2 * m
  hm : m < D.sp
  hy_not_spike : ∀ j, y j ≤ 1 - D.θ
  hz_spike : ∀ i, 1 - D.θ < z i
  hzph : 1 - D.θ ≤ zph ∧ zph < 1
  ρ : ℝ
  c1 : ℝ
  hρ : |ρ| < 1
  hρd : ρ ≤ D.τ ^ 2 * (1 - D.θ)
  hc1 : 0 < c1
  hP : ∀ u ∈ Icc (-1 : ℝ) 1, ((D.sp - m : ℕ) : ℝ) * c1 ≤
    (D.sp : ℝ) * chebPs D.b u - m * chebPs (poisSeq ρ) u
  hcost :
    spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y (extFam z zph m) -
        spikeDenB D.b D.sp y (extFam z zph m) +
        spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k (extFam z zph m) ≤
      spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y z - spikeDenB D.b D.sp y z +
        D.ν * ((M : ℝ) * D.cs) + D.ν * D.kph

/-- The class predicate (a refinement of the `Cls` of the contracts). -/
def SpikeCls (D : SignedData) (c' : ℝ) {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) : Prop :=
  Nonempty (SpikeWitness D c' xn gp)

theorem SpikeCompare.mono {D : SignedData} {c' : ℝ} {k q : ℕ}
    {Cls Cls' : (Fin k → ℝ) → (Fin q → ℝ) → Prop} {LR : (Fin k → ℝ) → (Fin q → ℝ) → ℝ}
    (h : ∀ xn gp, Cls' xn gp → Cls xn gp) (hA : SpikeCompare D c' Cls LR) :
    SpikeCompare D c' Cls' LR :=
  fun xn gp hxn hgp hc => hA xn gp hxn hgp (h xn gp hc)

/-! ### E. `SpikeCompare` from the class -/

theorem spikeCompare_of_class (D : SignedData) (E : SpikeEnv D) {c' : ℝ}
    (hc' : c' ∈ Ioc (0 : ℝ) 1) (hcθ : c' ≤ D.θ) {k q : ℕ}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → ℝ} (hLR : ∀ xn gp, LR xn gp = logRatioZ D.sp xn gp) :
    SpikeCompare D c' (SpikeCls D c') LR := by
  intro xn gp hxn hgp hW
  obtain ⟨W⟩ := hW
  rw [hLR]
  have hν := E.hν
  have hθ := E.hθ
  have hmle : W.m ≤ D.sp := W.hm.le
  have hs'pos : 0 < D.sp - W.m := Nat.sub_pos_of_lt W.hm
  have hsν : ((D.sp - W.m : ℕ) : ℝ) ≤ D.ν := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans E.hsp
  have hd : 1 - D.θ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hb : Summable fun k : ℕ => |D.b (k + 1)| := by
    refine summable_of_ne_finset_zero (s := Finset.range D.K) fun k hk => ?_
    rw [E.hbK (k + 1) (by simp at hk; omega)]
    simp
  -- positions
  have hy0 : ∀ j, 0 < W.y j := fun j => by
    have := hgp (W.σ (Fin.castAdd W.M j))
    rw [W.hσ, Fin.append_left] at this
    exact this.1
  have hy1 : ∀ j, W.y j < 1 := fun j => by
    have := hgp (W.σ (Fin.castAdd W.M j))
    rw [W.hσ, Fin.append_left] at this
    exact this.2
  have hz0 : ∀ i, 0 < W.z i := fun i => by
    have := hgp (W.σ (Fin.natAdd W.q' i))
    rw [W.hσ, Fin.append_right] at this
    exact this.1
  have hz1 : ∀ i, W.z i < 1 := fun i => by
    have := hgp (W.σ (Fin.natAdd W.q' i))
    rw [W.hσ, Fin.append_right] at this
    exact this.2
  have hcard : W.q' + W.M = q := by simpa using Fintype.card_congr W.σ
  have hext : ∀ p, 1 - D.θ ≤ extFam W.z W.zph W.m p ∧ extFam W.z W.zph W.m p < 1 :=
    extFam_mem W.z W.zph (1 - D.θ) (fun i => ⟨(W.hz_spike i).le, hz1 i⟩) W.hzph
  have hy : ∀ j, |W.y j| ≤ 1 - c' := fun j =>
    abs_le.mpr ⟨by linarith [hy0 j, hc'.2], by linarith [W.hy_not_spike j, hcθ]⟩
  have hzext : ∀ p, |extFam W.z W.zph W.m p| < 1 := fun p =>
    abs_lt.mpr ⟨by linarith [(hext p).1, hθ.2], (hext p).2⟩
  have hfN : ∀ u ∈ Icc (-1 : ℝ) 1, (∏ b, (1 + 2 * xn b * u + xn b ^ 2)) *
      ∏ p, (1 + 2 * W.y p * u + W.y p ^ 2)⁻¹ =
      Real.exp (∑ i, crossLog (xn i) u - ∑ j, crossLog (W.y j) u) := by
    intro u hu
    have ex : ∀ i, Real.exp (crossLog (xn i) u) = 1 + 2 * xn i * u + xn i ^ 2 := fun i =>
      Real.exp_log (cross_pos (abs_lt.mpr ⟨(hxn i).1, by linarith [(hxn i).2]⟩) hu)
    have ey : ∀ j, Real.exp (crossLog (W.y j) u) = 1 + 2 * W.y j * u + W.y j ^ 2 := fun j =>
      Real.exp_log (cross_pos (abs_lt.mpr ⟨by linarith [hy0 j], hy1 j⟩) hu)
    rw [Real.exp_sub, Real.exp_sum, Real.exp_sum]
    simp only [ex, ey]
    rw [div_eq_mul_inv, Finset.prod_inv_distrib]
  have hfD : ∀ u ∈ Icc (-1 : ℝ) 1, ∏ p, (1 + 2 * W.y p * u + W.y p ^ 2)⁻¹ =
      Real.exp (-∑ j, crossLog (W.y j) u) := by
    intro u hu
    have ey : ∀ j, Real.exp (crossLog (W.y j) u) = 1 + 2 * W.y j * u + W.y j ^ 2 := fun j =>
      Real.exp_log (cross_pos (abs_lt.mpr ⟨by linarith [hy0 j], hy1 j⟩) hu)
    rw [Real.exp_neg, Real.exp_sum]
    simp only [ey]
    rw [Finset.prod_inv_distrib]
  have hP' : ∀ u ∈ Icc (-1 : ℝ) 1, ((D.sp - W.m : ℕ) : ℝ) * W.c1 ≤
      (((D.sp - W.m) + W.m : ℕ) : ℝ) * chebPs D.b u - W.m * chebPs (poisSeq W.ρ) u := by
    intro u hu
    rw [Nat.sub_add_cancel hmle]
    exact W.hP u hu
  have hcmp := spike_compare (s' := D.sp - W.m) (m := W.m) E.hν E.he hc' hd hs'pos hsν D.a
    (refTilt D.R) E.ha E.hr E.hra E.Qref E.hQ E.hℓ hb W.hρ W.hρd W.hc1 hP' xn W.y
    (extFam W.z W.zph W.m) (fun i => (hxn i).1) hy hzext (fun i => (hxn i).2.le) (fun j => (hy0 j).le)
    (fun p => (hext p).1)
    (fN := fun u => (∏ b, (1 + 2 * xn b * u + xn b ^ 2)) *
      ∏ p, (1 + 2 * W.y p * u + W.y p ^ 2)⁻¹)
    (fD := fun u => ∏ p, (1 + 2 * W.y p * u + W.y p ^ 2)⁻¹) hfN hfD
  rw [Nat.sub_add_cancel hmle] at hcmp
  have hred := CatalanMeasure.GenD.Signed.spike_reduction_rows (s := D.sp) (m := W.m) hmle xn
    (fun b => ⟨(hxn b).1, (hxn b).2.le⟩) W.y (fun j => ⟨by linarith [hy0 j], hy1 j⟩) W.z
    (fun i => ⟨hz0 i, hz1 i⟩) (by simpa using W.hM)
  have hlogprod : Real.log (∏ b, (1 + 2 * xn b * (-1) + xn b ^ 2)) =
      ∑ b, crossLog (xn b) (-1) := by
    rw [Real.log_prod]
    · rfl
    · intro b _
      exact (cross_pos (abs_lt.mpr ⟨(hxn b).1, by linarith [(hxn b).2]⟩)
        ⟨le_refl _, by norm_num⟩).ne'
  rw [hlogprod] at hred
  have hLRe := logRatio_eq D.sp W.σ xn gp W.y W.z W.hσ
  -- matching of the bound expressions
  have hgfun : (fun i => gp (W.σ i)) = Fin.append W.y W.z := funext W.hσ
  have hnum : D.numB xn (Fin.append W.y W.z) = D.numB xn gp := by
    rw [← hgfun]; exact numB_equiv D W.σ xn gp
  have hden : D.denB (Fin.append W.y W.z) = D.denB gp := by
    rw [← hgfun]; exact denB_equiv D W.σ gp
  have hNum := spikeNumB_eq D hν xn W.y W.z
  have hDen := spikeDenB_eq D hν E.hbK W.y W.z
  have hST := spikeTerm_eq D W.σ gp W.y W.z W.hσ W.hy_not_spike W.hz_spike
  have hcost := W.hcost
  rw [hNum, hDen, hnum, hden] at hcost
  -- the J3 term
  have hE4 : 0 ≤ 4 * D.e / c' := div_nonneg (by linarith [E.he.1]) hc'.1.le
  have hq'q : W.q' ≤ q := by omega
  have hJ : ((D.sp - W.m : ℕ) : ℝ) * (((k + W.q' : ℕ) : ℝ) * (4 * D.e / c')) / D.ν ^ 2 ≤
      (4 * D.e / c') * ((D.sp : ℝ) / D.ν) * (((k + q : ℕ) : ℝ) / D.ν) := by
    have h1 : ((D.sp - W.m : ℕ) : ℝ) * (((k + W.q' : ℕ) : ℝ) * (4 * D.e / c')) ≤
        (D.sp : ℝ) * (((k + q : ℕ) : ℝ) * (4 * D.e / c')) :=
      mul_le_mul (Nat.cast_le.mpr (Nat.sub_le _ _))
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) hE4) (by positivity)
        (Nat.cast_nonneg _)
    have h2 := div_le_div_of_nonneg_right h1 (sq_nonneg D.ν)
    refine h2.trans (le_of_eq ?_)
    field_simp
  have hErr : D.errJ3 c' (k + q) =
      (4 * D.e / c') * ((D.sp : ℝ) / D.ν) * (((k + q : ℕ) : ℝ) / D.ν) + D.kph / D.ν := rfl
  have key : logRatioZ D.sp xn gp - logPref xn gp ≤ D.ν ^ 2 * (D.numB xn gp - D.denB gp) +
      D.ν * ((W.M : ℝ) * D.cs) + D.ν * D.kph + ((D.sp - W.m : ℕ) : ℝ) *
        (((k + W.q' : ℕ) : ℝ) * (4 * D.e / c')) := by
    rw [hLRe]
    linarith [hred, hcmp, hcost]
  have hdiv := div_le_div_of_nonneg_right key (sq_nonneg D.ν)
  have hrhs : (D.ν ^ 2 * (D.numB xn gp - D.denB gp) + D.ν * ((W.M : ℝ) * D.cs) + D.ν * D.kph +
      ((D.sp - W.m : ℕ) : ℝ) * (((k + W.q' : ℕ) : ℝ) * (4 * D.e / c'))) / D.ν ^ 2 =
      (D.numB xn gp - D.denB gp) + (1 / D.ν) * ((W.M : ℝ) * D.cs) + D.kph / D.ν +
        ((D.sp - W.m : ℕ) : ℝ) * (((k + W.q' : ℕ) : ℝ) * (4 * D.e / c')) / D.ν ^ 2 := by
    field_simp
  rw [hrhs, sub_div, ← hST] at hdiv
  rw [hErr]
  linarith [hdiv, hJ]

/-! ### F. Fixed (marked) nodes -/

/-- The class for fixed nodes: the combined sign-split lists are in the spike class, and the marked
positives lie below the quadrature cap `1 - bcap` with `θ < bcap`. -/
def ClsFixed (D : SignedData) (c' bcap : ℝ) {k q m1 m2 : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) : Prop :=
  SpikeCls D c' (Fin.append xn yn) (Fin.append gp yp) ∧ D.θ < bcap ∧ ∀ p, yp p ≤ 1 - bcap

/-- With the quadrature cap `bcap > θ`, a marked positive is never a spike. -/
theorem marked_not_spike (D : SignedData) {bcap : ℝ} (h : D.θ < bcap) {m2 : ℕ} (yp : Fin m2 → ℝ)
    (hyp : ∀ p, yp p ≤ 1 - bcap) (p : Fin m2) : ¬ (1 - D.θ < yp p) := by
  have := hyp p
  intro hlt
  linarith

/-- The spike cost of the combined positive list charges only the free positives. -/
theorem spikeTerm_append_marked (D : SignedData) {bcap : ℝ} (h : D.θ < bcap) {q m2 : ℕ}
    (gp : Fin q → ℝ) (yp : Fin m2 → ℝ) (hyp : ∀ p, yp p ≤ 1 - bcap) :
    D.spikeTerm (Fin.append gp yp) = D.spikeTerm gp := by
  unfold SignedData.spikeTerm
  rw [row_sum_split (fun v => D.cs * (if 1 - D.θ < v then (1 : ℝ) else 0)) gp yp]
  have : ∀ p, D.cs * (if 1 - D.θ < yp p then (1 : ℝ) else 0) = 0 := fun p => by
    rw [if_neg (marked_not_spike D h yp hyp p)]; simp
  simp [this]

theorem spikeCompareFixed_of_class (D : SignedData) (E : SpikeEnv D) {c' bcap : ℝ}
    (hc' : c' ∈ Ioc (0 : ℝ) 1) (hcθ : c' ≤ D.θ) {k q m1 m2 : ℕ}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ}
    (hLR : ∀ xn gp yn yp, LR xn gp yn yp =
      logRatioZ D.sp (Fin.append xn yn) (Fin.append gp yp)) :
    SpikeCompareFixed D c' (ClsFixed D c' bcap) LR := by
  intro xn gp yn yp hxn hgp hyn hyp hcls
  have hxa : ∀ l, Fin.append xn yn l ∈ Ioo (-1 : ℝ) 0 :=
    fin_append_forall xn yn (fun t => t ∈ Ioo (-1 : ℝ) 0) hxn hyn
  have hga : ∀ l, Fin.append gp yp l ∈ Ioo (0 : ℝ) 1 :=
    fin_append_forall gp yp (fun t => t ∈ Ioo (0 : ℝ) 1) hgp hyp
  rw [hLR]
  exact spikeCompare_of_class D E hc' hcθ (k := k + m1) (q := q + m2)
    (LR := fun a b => logRatioZ D.sp a b) (fun _ _ => rfl) (Fin.append xn yn)
    (Fin.append gp yp) hxa hga hcls.1

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.spikeNumB_eq
#print axioms CatalanMeasure.Signed.spikeDenB_eq
#print axioms CatalanMeasure.Signed.spikeTerm_eq
#print axioms CatalanMeasure.Signed.logRatio_eq
#print axioms CatalanMeasure.Signed.spikeCompare_of_class
#print axioms CatalanMeasure.Signed.spikeCompareFixed_of_class
#print axioms CatalanMeasure.Signed.marked_not_spike
#print axioms CatalanMeasure.Signed.spikeTerm_append_marked
