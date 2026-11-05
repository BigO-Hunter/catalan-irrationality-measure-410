module

public import Submission.CatalanMeasure.GenD.Signed.Interp
public import Submission.CatalanMeasure.GenD.Signed.SpikeDischarge

/-!
# `spikeFix` from the endpoint trials (lane SE)

The field `spikeFix` of `SignedNearBounds` asks for `SpikeCompareFixed` for the interpolated trial
data `D i N α = SignedData.interp (DA i N) (DB i N) l c` (`Interp.lean`).  Here it is derived from
spike witnesses at the two endpoint trials that share one configuration (the split of the
positives into rest and spikes, the pole `ρ`, the count `m`).

* `SpikeEnv.interp`: the environment of the spike lemmas is stable under `interp`.
* `SpikePair`: two witnesses with the same configuration and separate `(c1, hP, hcost)` data.
* `SpikePair.toWitness`: a witness for `interp DA DB l c`, `l ∈ [0,1]`.  The condition `(P')` is
  affine in `b` (take `c1 = (1-l) c1A + l c1B`).  The cost condition is
  `Δ(D) := LHS - RHS ≤ 0`; the part of `Δ` that is not affine in the data is the convex
  `4 ν m e Σ|a|` and the quadratic `(2 c / s') Σ b_n² (1 - 1/n)` in `b` (note the cancellation of the
  indefinite pairing `ra` and of `numConst`/`denConst`), and `cs` is affine, so
  `Δ(interp) ≤ (1-l) Δ(DA) + l Δ(DB)`.  Hence the spike constant `cs` of the interpolated trial is
  the chord of the endpoint constants (each endpoint keeps its own constant, e.g. CSP = 11/10 at
  α = 1/16).
* `spikeFix_of_ends`: the field `spikeFix` itself.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set MeasureTheory Filter Topology OAI.InternalCatalan
open CatalanMeasure.GenD.Signed (heineZ)
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### 1. The environment is stable under `interp` -/

theorem refTilt_linSeq (l : ℝ) (R R' : ℕ → ℝ) (m : ℕ) :
    refTilt (linSeq l R R') m = (1 - l) * refTilt R m + l * refTilt R' m := by
  unfold refTilt linSeq
  ring

def SpikeEnv.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB)
    (EA : SpikeEnv DA) (EB : SpikeEnv DB) : SpikeEnv (SignedData.interp DA DB l c) where
  hν := EA.hν
  he := EA.he
  hsp := EA.hsp
  hθ := EA.hθ
  ha := summable_abs_linSeq hl0 hl1 EA.ha EB.ha
  hr := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((EA.hr.mul_left (1 - l)).add (EB.hr.mul_left l))
    show ((k + 1 : ℕ) : ℝ) * refTilt (linSeq l DA.R DB.R) (k + 1) ^ 2 ≤ _
    rw [refTilt_linSeq]
    have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ l * (1 - l) * (refTilt DA.R (k + 1) - refTilt DB.R (k + 1)) ^ 2 :=
      mul_nonneg (mul_nonneg hl0 (by linarith)) (sq_nonneg _)
    nlinarith [mul_nonneg hk h2]
  hra := by
    have hreg := SignedRegular.interp (c := c) hl0 hl1 hc rA rB
    obtain ⟨M, hM⟩ := abs_rt_le hreg.tau hreg.hR
    exact summable_mul_bdd hM (summable_abs_sh hreg.ha)
  Qref := fun x => (1 - l) * EA.Qref x + l * EB.Qref x
  hQ := by
    intro x hx
    have hB := EB.hQ x hx
    rw [hc.e] at hB
    have h := ((EA.hQ x hx).mul_left (1 - l)).add (hB.mul_left l)
    convert h using 1
    funext k
    show refTilt (linSeq l DA.R DB.R) (k + 1) * realEnergyTau DA.e ^ (k + 1) * _ = _
    rw [refTilt_linSeq]
    ring
  hℓ := by
    intro x hx
    have hx1 : |x| ≤ 1 := abs_le.mpr hx
    show (1 - l) * EA.Qref x + l * EB.Qref x - 2 * barrierTrialT (linSeq l DA.a DB.a) x ≤
      (1 - l) * DA.Sup + l * DB.Sup
    rw [barrierTrialT_linSeq EA.ha EB.ha l hx1]
    have h1 := mul_le_mul_of_nonneg_left (EA.hℓ x hx) (by linarith : 0 ≤ 1 - l)
    have h2 := mul_le_mul_of_nonneg_left (EB.hℓ x hx) hl0
    linarith
  hbK := by
    intro i hi
    have hi' : DA.K < i := hi
    have hB := EB.hbK i (by rw [hc.K]; exact hi')
    show (1 - l) * DA.b i + l * DB.b i = 0
    rw [EA.hbK i hi', hB]
    ring


/-! ### 2. The numerator and denominator differences are affine

The cost condition compares the spike family `ext` (extended by the phantom) with `z`; in the
difference of the two bounds the terms `numConst`, `denConst` (and with them the indefinite pairing
`ra`) cancel, and what remains is affine in `(a, R)` and in `b`. -/

/-- `ip (u - R) (u - R) - ip (u' - R) (u' - R)`. -/
def Ipd (u u' R : ℕ → ℝ) : ℝ :=
  ip (fun n => u n - R n) (fun n => u n - R n) - ip (fun n => u' n - R n) (fun n => u' n - R n)

theorem Ipd_eq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {u u' R : ℕ → ℝ} (hu : IsGeom τ u)
    (hu' : IsGeom τ u') (hR : IsGeom τ R) :
    Ipd u u' R = ip u u - ip u' u' - 2 * ip (fun n => u n - u' n) R := by
  have h1 := hasSum_ip hτ (hu.sub hR) (hu.sub hR)
  have h2 := hasSum_ip hτ (hu'.sub hR) (hu'.sub hR)
  have h3 := ((hasSum_ip hτ hu hu).sub (hasSum_ip hτ hu' hu')).sub
    ((hasSum_ip hτ (hu.sub hu') hR).mul_left 2)
  have h4 := h1.sub h2
  have h5 : HasSum (fun n : ℕ => (u n - R n) * (u n - R n) / ((n : ℝ) + 1) -
      (u' n - R n) * (u' n - R n) / ((n : ℝ) + 1))
      (ip u u - ip u' u' - 2 * ip (fun n => u n - u' n) R) := by
    convert h3 using 1
    funext n
    ring
  exact h4.unique h5

theorem Ipd_linSeq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {u u' R R' : ℕ → ℝ} (hu : IsGeom τ u)
    (hu' : IsGeom τ u') (hR : IsGeom τ R) (hR' : IsGeom τ R') (l : ℝ) :
    Ipd u u' (linSeq l R R') = (1 - l) * Ipd u u' R + l * Ipd u u' R' := by
  rw [Ipd_eq hτ hu hu' (isGeom_linSeq hR hR' l), Ipd_eq hτ hu hu' hR, Ipd_eq hτ hu hu' hR',
    ip_linSeq_right hτ (hu.sub hu') hR hR' l]
  ring

/-- The difference of the numerator bounds `numB` at two positive lists. -/
def numDiff (ν τ : ℝ) (a R : ℕ → ℝ) {k n n' : ℕ} (x : Fin k → ℝ) (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) : ℝ :=
  (2 / ν) * ((∑ p, barrierTrialS a (-τ * g p)) - ∑ p, barrierTrialS a (-τ * g' p)) +
    (1 / 2) * Ipd (fun j => powSum τ ν x j - powSum τ ν g j)
      (fun j => powSum τ ν x j - powSum τ ν g' j) R

theorem numB_sub (D : SignedData) {k n n' : ℕ} (x : Fin k → ℝ) (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) : D.numB x g - D.numB x g' = numDiff D.ν D.τ D.a D.R x g g' := by
  simp only [SignedData.numB, numDiff, Ipd]
  ring

theorem numDiff_linSeq {ν τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) {a a' R R' : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) (hR : IsGeom τ R)
    (hR' : IsGeom τ R') (l : ℝ) {k n n' : ℕ} (x : Fin k → ℝ) (g : Fin n → ℝ) (g' : Fin n' → ℝ)
    (hx : ∀ b, |x b| ≤ 1) (hg : ∀ p, |g p| ≤ 1) (hg' : ∀ p, |g' p| ≤ 1) :
    numDiff ν τ (linSeq l a a') (linSeq l R R') x g g' =
      (1 - l) * numDiff ν τ a R x g g' + l * numDiff ν τ a' R' x g g' := by
  have hS : ∀ {n : ℕ} (g : Fin n → ℝ), (∀ p, |g p| ≤ 1) →
      ∑ p, barrierTrialS (linSeq l a a') (-τ * g p) =
        (1 - l) * ∑ p, barrierTrialS a (-τ * g p) + l * ∑ p, barrierTrialS a' (-τ * g p) := by
    intro n g hg
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ =>
      barrierTrialS_linSeq ha ha' l (abs_neg_tau_mul_le hτ (hg p))
  have hu : IsGeom τ (fun j => powSum τ ν x j - powSum τ ν g j) :=
    (isGeom_powSum hτ.1 hν x hx).sub (isGeom_powSum hτ.1 hν g hg)
  have hu' : IsGeom τ (fun j => powSum τ ν x j - powSum τ ν g' j) :=
    (isGeom_powSum hτ.1 hν x hx).sub (isGeom_powSum hτ.1 hν g' hg')
  unfold numDiff
  rw [Ipd_linSeq hτ hu hu' hR hR' l, hS g hg, hS g' hg']
  ring

/-- The difference of the denominator bounds `spikeDenB` (the constants cancel). -/
theorem spikeDenB_sub (b : ℕ → ℝ) (s : ℕ) {q n n' : ℕ} (y : Fin q → ℝ) (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) :
    spikeDenB b s y g - spikeDenB b s y g' =
      2 * (s : ℝ) * ((∑ p, barrierTrialS b (-(g p))) - ∑ p, barrierTrialS b (-(g' p))) := by
  unfold spikeDenB
  ring

theorem denDiff_linSeq {b b' : ℕ → ℝ} (hb : Summable fun k => |b k|)
    (hb' : Summable fun k => |b' k|) (l : ℝ) (s : ℕ) {n n' : ℕ} (g : Fin n → ℝ)
    (g' : Fin n' → ℝ) (hg : ∀ p, |g p| ≤ 1) (hg' : ∀ p, |g' p| ≤ 1) :
    2 * (s : ℝ) * ((∑ p, barrierTrialS (linSeq l b b') (-(g p))) -
        ∑ p, barrierTrialS (linSeq l b b') (-(g' p))) =
      (1 - l) * (2 * (s : ℝ) * ((∑ p, barrierTrialS b (-(g p))) - ∑ p, barrierTrialS b (-(g' p)))) +
      l * (2 * (s : ℝ) * ((∑ p, barrierTrialS b' (-(g p))) - ∑ p, barrierTrialS b' (-(g' p)))) := by
  have hS : ∀ {n : ℕ} (g : Fin n → ℝ), (∀ p, |g p| ≤ 1) →
      ∑ p, barrierTrialS (linSeq l b b') (-(g p)) =
        (1 - l) * ∑ p, barrierTrialS b (-(g p)) + l * ∑ p, barrierTrialS b' (-(g p)) := by
    intro n g hg
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ =>
      barrierTrialS_linSeq hb hb' l (by rw [abs_neg]; exact hg p)
  rw [hS g hg, hS g' hg']
  ring

/-! ### 3. The spike cost is convex in the data

`spikeCost` splits into the part that depends on the configuration only, the term
`4 ν m e Σ|a|` (convex in `a`), a part affine in `b`, and the quadratic form
`(2 (s'+m) m / s') Σ_n (1 - 1/n) b_n²` in `b` (convex, as `1 - 1/n ≥ 0`). -/

def costCfg (e : ℝ) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) : ℝ :=
  2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) +
  2 * (m : ℝ) ^ 2 * (Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) - Real.log (1 - ρ ^ 2)) +
  (m : ℝ) * Real.log 2 + (2 * (m : ℝ) ^ 2 / s') * (ρ ^ 2 / (1 - ρ ^ 2))

def costA (ν e : ℝ) (m : ℕ) (a : ℕ → ℝ) : ℝ := 4 * ν * m * e * ∑' j : ℕ, |a j|

def costLin (b : ℕ → ℝ) (s' m : ℕ) (ρ : ℝ) {M : ℕ} (z : Fin M → ℝ) : ℝ :=
  2 * ((s' : ℝ) + m) * ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) -
    (4 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1)) +
    (4 * ((s' : ℝ) + m) * m / s') * barrierTrialS b (-ρ)

def costQuad (b : ℕ → ℝ) (s' m : ℕ) : ℝ :=
  -((((s' : ℝ) + m) * m / s') * (∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))) +
    (2 * ((s' : ℝ) + m) * m / s') * (∑' k : ℕ, b (k + 1) ^ 2)

theorem spikeCost_split (ν e : ℝ) (a b : ℕ → ℝ) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) {M : ℕ}
    (z : Fin M → ℝ) :
    spikeCost ν e a b s' m ρ r k z =
      costCfg e s' m ρ r k + costA ν e m a + costLin b s' m ρ z + costQuad b s' m := by
  unfold spikeCost costCfg costA costLin costQuad
  ring

theorem costA_le {ν e : ℝ} (hν : 0 ≤ ν) (he : 0 ≤ e) (m : ℕ) {a a' : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    costA ν e m (linSeq l a a') ≤ (1 - l) * costA ν e m a + l * costA ν e m a' := by
  have h1 : ∑' j, |linSeq l a a' j| ≤ (1 - l) * ∑' j, |a j| + l * ∑' j, |a' j| := by
    have hs := (ha.mul_left (1 - l)).add (ha'.mul_left l)
    calc _ ≤ ∑' j, ((1 - l) * |a j| + l * |a' j|) :=
          (summable_abs_linSeq hl0 hl1 ha ha').tsum_le_tsum
            (fun j => abs_linSeq_le l hl0 hl1 a a' j) hs
      _ = _ := by
          rw [(ha.mul_left _).tsum_add (ha'.mul_left _), tsum_mul_left, tsum_mul_left]
  unfold costA
  have hc : 0 ≤ 4 * ν * m * e := by positivity
  have := mul_le_mul_of_nonneg_left h1 hc
  linarith

theorem barrierTrialS_linSeq_fin {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) (l x : ℝ) :
    barrierTrialS (linSeq l b b') x = (1 - l) * barrierTrialS b x + l * barrierTrialS b' x := by
  have hlin : ∀ i, K < i → linSeq l b b' i = 0 := fun i hi => by
    simp [linSeq, hb i hi, hb' i hi]
  rw [barrierTrialS_trunc hlin, barrierTrialS_trunc hb, barrierTrialS_trunc hb',
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [linSeq]; ring

theorem tsum_linSeq_fin {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) (l : ℝ) (c : ℕ → ℝ) :
    ∑' k : ℕ, linSeq l b b' (k + 1) * c k =
      (1 - l) * ∑' k : ℕ, b (k + 1) * c k + l * ∑' k : ℕ, b' (k + 1) * c k := by
  rw [tsum_eq_range (K := K) (f := fun k => linSeq l b b' (k + 1) * c k) (fun k hk => by
        simp [linSeq, hb (k + 1) (by omega), hb' (k + 1) (by omega)]),
    tsum_eq_range (K := K) (f := fun k => b (k + 1) * c k) (fun k hk => by
        simp [hb (k + 1) (by omega)]),
    tsum_eq_range (K := K) (f := fun k => b' (k + 1) * c k) (fun k hk => by
        simp [hb' (k + 1) (by omega)]),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [linSeq]; ring

theorem costLin_linSeq {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) (l : ℝ) (s' m : ℕ) (ρ : ℝ) {M : ℕ} (z : Fin M → ℝ) :
    costLin (linSeq l b b') s' m ρ z = (1 - l) * costLin b s' m ρ z + l * costLin b' s' m ρ z := by
  unfold costLin
  simp only [barrierTrialS_linSeq_fin hb hb' l]
  rw [tsum_linSeq_fin hb hb' l (fun k => poisSeq ρ (k + 1))]
  have hsum : ∑ p, (((1 - l) * barrierTrialS b (-(z p)) + l * barrierTrialS b' (-(z p))) -
      ((1 - l) * barrierTrialS b (-ρ) + l * barrierTrialS b' (-ρ))) =
      (1 - l) * ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) +
        l * ∑ p, (barrierTrialS b' (-(z p)) - barrierTrialS b' (-ρ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  ring

theorem costQuad_fin {b : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0) (s' m : ℕ) :
    costQuad b s' m = (2 * ((s' : ℝ) + m) * m / s') *
      ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b (i + 1) ^ 2 := by
  unfold costQuad
  rw [tsum_eq_range (K := K) (f := fun i => 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ))
      (fun k hk => by simp [hb (k + 1) (by omega)]),
    tsum_eq_range (K := K) (f := fun k => b (k + 1) ^ 2)
      (fun k hk => by simp [hb (k + 1) (by omega)])]
  have : ∀ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b (i + 1) ^ 2 =
      b (i + 1) ^ 2 - (1 / 2) * (2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) := fun i _ => by
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem costQuad_le {b b' : ℕ → ℝ} {K : ℕ} (hb : ∀ i, K < i → b i = 0)
    (hb' : ∀ i, K < i → b' i = 0) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (s' m : ℕ) :
    costQuad (linSeq l b b') s' m ≤ (1 - l) * costQuad b s' m + l * costQuad b' s' m := by
  have hlin : ∀ i, K < i → linSeq l b b' i = 0 := fun i hi => by
    simp [linSeq, hb i hi, hb' i hi]
  rw [costQuad_fin hlin, costQuad_fin hb, costQuad_fin hb']
  set c : ℝ := 2 * ((s' : ℝ) + m) * m / s' with hcdef
  have hc : 0 ≤ c := by positivity
  have hsum : ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * linSeq l b b' (i + 1) ^ 2 ≤
      (1 - l) * ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b (i + 1) ^ 2 +
        l * ∑ i ∈ Finset.range K, (1 - 1 / ((i + 1 : ℕ) : ℝ)) * b' (i + 1) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hw : 0 ≤ 1 - 1 / ((i + 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 i
      have : 1 / ((i + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact h1
      linarith
    have h2 : 0 ≤ l * (1 - l) * (b (i + 1) - b' (i + 1)) ^ 2 :=
      mul_nonneg (mul_nonneg hl0 (by linarith)) (sq_nonneg _)
    simp only [linSeq]
    nlinarith [mul_nonneg hw h2]
  have := mul_le_mul_of_nonneg_left hsum hc
  linarith

theorem spikeCost_interp_le {ν e : ℝ} (hν : 0 ≤ ν) (he : 0 ≤ e) {a a' b b' : ℕ → ℝ}
    (ha : Summable fun k => |a k|) (ha' : Summable fun k => |a' k|) {K : ℕ}
    (hb : ∀ i, K < i → b i = 0) (hb' : ∀ i, K < i → b' i = 0) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) {M : ℕ} (z : Fin M → ℝ) :
    spikeCost ν e (linSeq l a a') (linSeq l b b') s' m ρ r k z ≤
      (1 - l) * spikeCost ν e a b s' m ρ r k z + l * spikeCost ν e a' b' s' m ρ r k z := by
  rw [spikeCost_split, spikeCost_split, spikeCost_split, costLin_linSeq hb hb' l]
  have h1 := costA_le hν he m ha ha' hl0 hl1
  have h2 := costQuad_le hb hb' hl0 hl1 s' m
  linarith

/-! ### 4. The cost condition and (P') pass to `interp` -/

/-- The cost condition `hcost` of `SpikeWitness`, as a predicate of the trial. -/
def SpikeCostOK (D : SignedData) {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ) (y : Fin q' → ℝ)
    (z : Fin M → ℝ) (zph ρ : ℝ) : Prop :=
  spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y (extFam z zph m) -
        spikeDenB D.b D.sp y (extFam z zph m) +
        spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k (extFam z zph m) ≤
      spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y z - spikeDenB D.b D.sp y z +
        D.ν * ((M : ℝ) * D.cs) + D.ν * D.kph

/-- The condition (P') of `SpikeWitness`, as a predicate of the trial. -/
def SpikeChebOK (D : SignedData) (m : ℕ) (ρ c1 : ℝ) : Prop :=
  ∀ u ∈ Icc (-1 : ℝ) 1, ((D.sp - m : ℕ) : ℝ) * c1 ≤
    (D.sp : ℝ) * chebPs D.b u - m * chebPs (poisSeq ρ) u

/-- `LHS - RHS` of the cost condition, after the cancellation of the configuration-free terms. -/
def costGap (D : SignedData) {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ) (y : Fin q' → ℝ)
    (z : Fin M → ℝ) (zph ρ : ℝ) : ℝ :=
  D.ν ^ 2 * numDiff D.ν D.τ D.a D.R xn (Fin.append y (extFam z zph m)) (Fin.append y z) -
    2 * (D.sp : ℝ) * ((∑ p, barrierTrialS D.b (-(extFam z zph m p))) -
      ∑ p, barrierTrialS D.b (-(z p))) +
    spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k (extFam z zph m) -
    D.ν * ((M : ℝ) * D.cs) - D.ν * D.kph

theorem costOK_iff (D : SignedData) (hν : 0 < D.ν) {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ)
    (y : Fin q' → ℝ) (z : Fin M → ℝ) (zph ρ : ℝ) :
    SpikeCostOK D m xn y z zph ρ ↔ costGap D m xn y z zph ρ ≤ 0 := by
  unfold SpikeCostOK costGap
  have e1 : spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y (extFam z zph m) -
      spikeNumB D.ν D.e D.a (refTilt D.R) D.Sup D.sp xn y z =
      D.ν ^ 2 * numDiff D.ν D.τ D.a D.R xn (Fin.append y (extFam z zph m)) (Fin.append y z) := by
    rw [spikeNumB_eq D hν, spikeNumB_eq D hν, ← mul_sub, numB_sub]
  have e2 := spikeDenB_sub D.b D.sp y (extFam z zph m) z
  constructor <;> intro h <;> linarith

theorem abs_extFam_le {M m : ℕ} {z : Fin M → ℝ} {zph : ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hph : |zph| ≤ 1) (p : Fin (2 * m)) : |extFam z zph m p| ≤ 1 := by
  unfold extFam
  split_ifs with h
  · exact hz _
  · exact hph

theorem costGap_interp_le {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (hν : 0 < DA.ν)
    (hbA : ∀ i, DA.K < i → DA.b i = 0) (hbB : ∀ i, DA.K < i → DB.b i = 0)
    {k q' M : ℕ} (m : ℕ) (xn : Fin k → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ) (zph ρ : ℝ)
    (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, |z i| ≤ 1) (hph : |zph| ≤ 1) :
    costGap (SignedData.interp DA DB l c) m xn y z zph ρ ≤
      (1 - l) * costGap DA m xn y z zph ρ + l * costGap DB m xn y z zph ρ := by
  have hτ := rA.tau
  have hext : ∀ p, |extFam z zph m p| ≤ 1 := abs_extFam_le hz hph
  have hge : ∀ p, |Fin.append y (extFam z zph m) p| ≤ 1 :=
    fin_append_forall y (extFam z zph m) (fun t => |t| ≤ 1) hy hext
  have hgz : ∀ p, |Fin.append y z p| ≤ 1 :=
    fin_append_forall y z (fun t => |t| ≤ 1) hy hz
  have hsA : Summable fun k => |DA.b k| :=
    summable_of_ne_finset_zero (s := Finset.range (DA.K + 1)) fun i hi =>
      by simp [hbA i (by simpa using hi)]
  have hsB : Summable fun k => |DB.b k| :=
    summable_of_ne_finset_zero (s := Finset.range (DA.K + 1)) fun i hi =>
      by simp [hbB i (by simpa using hi)]
  have hI : costGap (SignedData.interp DA DB l c) m xn y z zph ρ =
      DA.ν ^ 2 * numDiff DA.ν DA.τ (linSeq l DA.a DB.a) (linSeq l DA.R DB.R) xn
          (Fin.append y (extFam z zph m)) (Fin.append y z) -
        2 * (DA.sp : ℝ) * ((∑ p, barrierTrialS (linSeq l DA.b DB.b) (-(extFam z zph m p))) -
          ∑ p, barrierTrialS (linSeq l DA.b DB.b) (-(z p))) +
        spikeCost DA.ν DA.e (linSeq l DA.a DB.a) (linSeq l DA.b DB.b) (DA.sp - m) m ρ
          (1 - DA.θ) k (extFam z zph m) -
        DA.ν * ((M : ℝ) * ((1 - l) * DA.cs + l * DB.cs)) - DA.ν * DA.kph := rfl
  have hB : costGap DB m xn y z zph ρ =
      DA.ν ^ 2 * numDiff DA.ν DA.τ DB.a DB.R xn (Fin.append y (extFam z zph m))
          (Fin.append y z) -
        2 * (DA.sp : ℝ) * ((∑ p, barrierTrialS DB.b (-(extFam z zph m p))) -
          ∑ p, barrierTrialS DB.b (-(z p))) +
        spikeCost DA.ν DA.e DB.a DB.b (DA.sp - m) m ρ (1 - DA.θ) k (extFam z zph m) -
        DA.ν * ((M : ℝ) * DB.cs) - DA.ν * DA.kph := by
    unfold costGap
    rw [hc.ν, hc.τ, hc.e, hc.sp, hc.θ, hc.kph]
  rw [hI, hB]
  have h1 := numDiff_linSeq hτ hν rA.ha rB.ha rA.hR (rB.hRτ hc) l xn
    (Fin.append y (extFam z zph m)) (Fin.append y z) hx hge hgz
  have h2 := denDiff_linSeq hsA hsB l DA.sp (extFam z zph m) z hext hz
  have h3 := spikeCost_interp_le hν.le rA.he.1.le rA.ha rB.ha hbA
    (fun i hi => hbB i hi) hl0 hl1 (DA.sp - m) m ρ (1 - DA.θ) k (extFam z zph m)
  unfold costGap
  rw [h1, h2]
  nlinarith [h3]

theorem SpikeCostOK.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (EA : SpikeEnv DA)
    (EB : SpikeEnv DB) {k q' M : ℕ} {m : ℕ} {xn : Fin k → ℝ} {y : Fin q' → ℝ} {z : Fin M → ℝ}
    {zph ρ : ℝ} (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, |z i| ≤ 1)
    (hph : |zph| ≤ 1) (hA : SpikeCostOK DA m xn y z zph ρ) (hB : SpikeCostOK DB m xn y z zph ρ) :
    SpikeCostOK (SignedData.interp DA DB l c) m xn y z zph ρ := by
  have hνB : 0 < DB.ν := by rw [hc.ν]; exact EA.hν
  rw [costOK_iff DA EA.hν] at hA
  rw [costOK_iff DB hνB] at hB
  rw [costOK_iff (SignedData.interp DA DB l c) EA.hν]
  have h := costGap_interp_le hl0 hl1 hc rA rB EA.hν EA.hbK
    (fun i hi => EB.hbK i (by rw [hc.K]; exact hi)) m xn y z zph ρ hx hy hz hph (c := c)
  have h1 := mul_le_mul_of_nonneg_left hA (by linarith : 0 ≤ 1 - l)
  have h2 := mul_le_mul_of_nonneg_left hB hl0
  linarith

theorem SpikeChebOK.interp {DA DB : SignedData} {l c : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (EA : SpikeEnv DA) (EB : SpikeEnv DB) {m : ℕ} {ρ c1A c1B : ℝ}
    (hA : SpikeChebOK DA m ρ c1A) (hB : SpikeChebOK DB m ρ c1B) :
    SpikeChebOK (SignedData.interp DA DB l c) m ρ ((1 - l) * c1A + l * c1B) := by
  intro u hu
  have hbB : ∀ i, DA.K < i → DB.b i = 0 := fun i hi => EB.hbK i (by rw [hc.K]; exact hi)
  have hcheb : chebPs (linSeq l DA.b DB.b) u = (1 - l) * chebPs DA.b u + l * chebPs DB.b u := by
    unfold chebPs
    rw [tsum_linSeq_fin EA.hbK hbB l
      (fun k => (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval u)]
    ring
  have h1 := hA u hu
  have h2 := hB u hu
  rw [hc.sp] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 - l)
  have h2' := mul_le_mul_of_nonneg_left h2 hl0
  show (((DA.sp - m : ℕ) : ℝ)) * ((1 - l) * c1A + l * c1B) ≤
    (DA.sp : ℝ) * chebPs (linSeq l DA.b DB.b) u - m * chebPs (poisSeq ρ) u
  rw [hcheb]
  nlinarith [h1', h2']

/-! ### 5. Witness pairs and the class -/

/-- Two spike witnesses at the endpoint trials `DA`, `DB` with ONE configuration (the split of the
positives into rest and spikes, the count `m`, the phantom, the pole `ρ`).  The data that belong to
the trial are kept apart: `(P')` with its own `c1`, and the cost condition (which contains the
spike constant `cs` of the trial, so each endpoint keeps its own constant). -/
structure SpikePair (DA DB : SignedData) (c' : ℝ) {k q : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) where
  q' : ℕ
  M : ℕ
  m : ℕ
  y : Fin q' → ℝ
  z : Fin M → ℝ
  zph : ℝ
  σ : Fin (q' + M) ≃ Fin q
  hσ : ∀ i, gp (σ i) = Fin.append y z i
  hM : M = 2 * m ∨ M + 1 = 2 * m
  hm : m < DA.sp
  hy_not_spike : ∀ j, y j ≤ 1 - DA.θ
  hz_spike : ∀ i, 1 - DA.θ < z i
  hzph : 1 - DA.θ ≤ zph ∧ zph < 1
  ρ : ℝ
  c1A : ℝ
  c1B : ℝ
  hρ : |ρ| < 1
  hρd : ρ ≤ DA.τ ^ 2 * (1 - DA.θ)
  hc1A : 0 < c1A
  hc1B : 0 < c1B
  hPA : SpikeChebOK DA m ρ c1A
  hPB : SpikeChebOK DB m ρ c1B
  hcostA : SpikeCostOK DA m xn y z zph ρ
  hcostB : SpikeCostOK DB m xn y z zph ρ

/-- **The interpolated witness.**  A pair of endpoint witnesses gives a witness for every
`interp DA DB l c`, `l ∈ [0,1]`, with `c1 = (1-l) c1A + l c1B`. -/
def SpikePair.toWitness {DA DB : SignedData} {l c c' : ℝ} {k q : ℕ} {xn : Fin k → ℝ}
    {gp : Fin q → ℝ} (P : SpikePair DA DB c' xn gp) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (EA : SpikeEnv DA)
    (EB : SpikeEnv DB) (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |P.y j| ≤ 1) (hz : ∀ i, |P.z i| ≤ 1) :
    SpikeWitness (SignedData.interp DA DB l c) c' xn gp where
  q' := P.q'
  M := P.M
  m := P.m
  y := P.y
  z := P.z
  zph := P.zph
  σ := P.σ
  hσ := P.hσ
  hM := P.hM
  hm := P.hm
  hy_not_spike := P.hy_not_spike
  hz_spike := P.hz_spike
  hzph := P.hzph
  ρ := P.ρ
  c1 := (1 - l) * P.c1A + l * P.c1B
  hρ := P.hρ
  hρd := P.hρd
  hc1 := by
    have hmin : min P.c1A P.c1B ≤ (1 - l) * P.c1A + l * P.c1B := by
      have h1 := mul_le_mul_of_nonneg_left (min_le_left P.c1A P.c1B) (by linarith : 0 ≤ 1 - l)
      have h2 := mul_le_mul_of_nonneg_left (min_le_right P.c1A P.c1B) hl0
      nlinarith
    exact lt_of_lt_of_le (lt_min P.hc1A P.hc1B) hmin
  hP := SpikeChebOK.interp hl0 hl1 hc EA EB P.hPA P.hPB
  hcost := SpikeCostOK.interp hl0 hl1 hc rA rB EA EB hx hy hz
    (abs_le.mpr ⟨by linarith [EA.hθ.2, P.hzph.1], P.hzph.2.le⟩) P.hcostA P.hcostB

/-- The class of the interpolated contract: the endpoint trials are regular and compatible, their
environments exist, and the configuration is a witness pair.  Marked positives may be spikes:
they are charged by `spikeTerm` of the combined list, so no quadrature cap is needed here. -/
structure PairCls (DA DB : SignedData) (c' : ℝ) {k q m1 m2 : ℕ} (xn : Fin k → ℝ)
    (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) where
  compat : InterpCompat DA DB
  rA : SignedRegular DA
  rB : SignedRegular DB
  EA : SpikeEnv DA
  EB : SpikeEnv DB
  P : SpikePair DA DB c' (Fin.append xn yn) (Fin.append gp yp)

/-- `SpikeCompareFixed` for the interpolated trial `interp DA DB l c`, `l ∈ [0,1]`, for every
configuration whose class gives a witness pair at the endpoints. -/
theorem spikeCompareFixed_interp (DA DB : SignedData) {l c c' : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hc' : c' ∈ Ioc (0 : ℝ) 1) (hcθ : c' ≤ DA.θ) {k q m1 m2 : ℕ}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ}
    (hLR : ∀ xn gp yn yp, LR xn gp yn yp =
      logRatioZ DA.sp (Fin.append xn yn) (Fin.append gp yp))
    {Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop}
    (hCls : ∀ xn gp yn yp, Cls xn gp yn yp → Nonempty (PairCls DA DB c' xn gp yn yp)) :
    SpikeCompareFixed (SignedData.interp DA DB l c) c' Cls LR := by
  intro xn gp yn yp hxn hgp hyn hyp hcls
  obtain ⟨C⟩ := hCls xn gp yn yp hcls
  have hxa : ∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0 :=
    fin_append_forall xn yn (fun t => t ∈ Ioo (-1 : ℝ) 0) hxn hyn
  have hga : ∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1 :=
    fin_append_forall gp yp (fun t => t ∈ Ioo (0 : ℝ) 1) hgp hyp
  have hx : ∀ b, |Fin.append xn yn b| ≤ 1 := fun b =>
    abs_le.mpr ⟨(hxa b).1.le, by linarith [(hxa b).2]⟩
  have hy : ∀ j, |C.P.y j| ≤ 1 := fun j => by
    have := hga (C.P.σ (Fin.castAdd C.P.M j))
    rw [C.P.hσ, Fin.append_left] at this
    exact abs_le.mpr ⟨by linarith [this.1], this.2.le⟩
  have hz : ∀ i, |C.P.z i| ≤ 1 := fun i => by
    have := hga (C.P.σ (Fin.natAdd C.P.q' i))
    rw [C.P.hσ, Fin.append_right] at this
    exact abs_le.mpr ⟨by linarith [this.1], this.2.le⟩
  have W := C.P.toWitness (c := c) (l := l) hl0 hl1 C.compat C.rA C.rB C.EA C.EB hx hy hz
  have E := SpikeEnv.interp (c := c) hl0 hl1 C.compat C.rA C.rB C.EA C.EB
  rw [hLR]
  exact spikeCompare_of_class (SignedData.interp DA DB l c) E hc' hcθ (k := k + m1) (q := q + m2)
    (LR := fun a b => logRatioZ DA.sp a b) (fun _ _ => rfl) (Fin.append xn yn)
    (Fin.append gp yp) hxa hga ⟨W⟩

/-- The interpolated trial at a Heine count is the interpolation of the endpoint trials at that
count (the endpoints share the reference count `sp`). -/
theorem interp_withCount {DA DB : SignedData} (hsp : DB.sp = DA.sp) (l c : ℝ) (x : ℕ) :
    (SignedData.interp DA DB l c).withCount x =
      SignedData.interp (DA.withCount x) (DB.withCount x) l c := by
  unfold SignedData.withCount SignedData.interp
  simp only [SignedData.mk.injEq, true_and, and_true]
  funext k
  simp only [linSeq, hsp]
  ring

/-- **`spikeFix` of `SignedNearBounds.ofEnds`.**  For every interval `i`, all large `N` and every `α`,
the interpolated trial `interpFamily (αA i) (αB i) (DA i) (DB i) constant N α` satisfies
`SpikeCompareFixedCount` with the margin `cp i N α` and the class `Clsf`, provided the class gives
the count condition `0 < sp`, `sp + g ≤ q + m₂` and a witness pair at the endpoint trials at the
configuration's Heine count `q + m₂ - g` (same configuration, each endpoint with its own spike
constant `cs`; NOTES-ETA §5.1). -/
theorem spikeFix_of_ends {I : ℕ} (αA αB : Fin I → ℝ) (DA DB : Fin I → ℕ → SignedData)
    (constant : ℕ → ℝ → ℝ) (cp : Fin I → ℕ → ℝ → ℝ) (cp_pos : ∀ i N α, 0 < cp i N α)
    (cp_le : ∀ i N α, cp i N α ≤ 1) (cp_theta : ∀ i N α, cp i N α ≤ (DA i N).θ)
    (hsp : ∀ i N, (DB i N).sp = (DA i N).sp)
    (Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LRf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ)
    (hLR : ∀ i N k q m1 m2 xn gp yn yp, LRf N k q m1 m2 xn gp yn yp =
      logRatioZ (q + m2 - (DA i N).g) (Fin.append xn yn) (Fin.append gp yp))
    (hCls : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α k q m1 m2 xn gp yn yp,
      Clsf N k q m1 m2 xn gp yn yp →
      (0 < (DA i N).sp ∧ (DA i N).sp + (DA i N).g ≤ q + m2) ∧
      Nonempty (PairCls ((DA i N).withCount (q + m2 - (DA i N).g))
        ((DB i N).withCount (q + m2 - (DA i N).g)) (cp i N α) xn gp yn yp)) :
    ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α k q m1 m2,
      SpikeCompareFixedCount (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α) (cp i N α)
        (Clsf N k q m1 m2) (LRf N k q m1 m2) := by
  intro i
  filter_upwards [hCls i] with N hN
  intro α k q m1 m2
  refine ⟨fun xn gp yn yp h => (hN α k q m1 m2 xn gp yn yp h).1, ?_⟩
  have e : (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α).withCount
      (q + m2 - (interpFamily (αA i) (αB i) (DA i) (DB i) constant N α).g) =
      SignedData.interp ((DA i N).withCount (q + m2 - (DA i N).g))
        ((DB i N).withCount (q + m2 - (DA i N).g)) (interpL (αA i) (αB i) α) (constant N α) :=
    interp_withCount (hsp i N) _ _ _
  rw [e]
  have hθ : cp i N α ≤ ((DA i N).withCount (q + m2 - (DA i N).g)).θ := cp_theta i N α
  have hLR' : ∀ xn gp yn yp, LRf N k q m1 m2 xn gp yn yp =
      logRatioZ ((DA i N).withCount (q + m2 - (DA i N).g)).sp (Fin.append xn yn)
        (Fin.append gp yp) := fun xn gp yn yp => hLR i N k q m1 m2 xn gp yn yp
  exact spikeCompareFixed_interp ((DA i N).withCount (q + m2 - (DA i N).g))
    ((DB i N).withCount (q + m2 - (DA i N).g)) (l := interpL (αA i) (αB i) α)
    (c := constant N α) (interpL_nonneg (αA i) (αB i) α)
    (interpL_le_one (αA i) (αB i) α) ⟨cp_pos i N α, cp_le i N α⟩ hθ hLR'
    (fun xn gp yn yp h => (hN α k q m1 m2 xn gp yn yp h).2)


/-! ### 6. Building the pair from ONE single-trial witness -/

/-- No field of the pair depends on the margin any more (the negatives need no margin: one-sided
J3, `crossLog_le_dilate`), so a pair at margin `c'` is a pair at every margin. -/
def SpikePair.monoMargin {DA DB : SignedData} {c' c'' : ℝ} {k q : ℕ} {xn : Fin k → ℝ}
    {gp : Fin q → ℝ} (P : SpikePair DA DB c' xn gp) (_h : c'' ≤ c') :
    SpikePair DA DB c'' xn gp :=
  { P with }

def PairCls.monoMargin {DA DB : SignedData} {c' c'' : ℝ} {k q m1 m2 : ℕ}
    {xn : Fin k → ℝ} {gp : Fin q → ℝ} {yn : Fin m1 → ℝ} {yp : Fin m2 → ℝ}
    (C : PairCls DA DB c' xn gp yn yp) (h : c'' ≤ c') :
    PairCls DA DB c'' xn gp yn yp :=
  { C with P := C.P.monoMargin h }

/-- **The pair from one single-trial witness.**  A spike witness `WA` of the trial `DA` (the
existing class `SpikeCls`) fixes the configuration (split, `m`, phantom, pole `ρ`, margin); the
only extra data for `DB` are its own `(P')` constant `c1B` and its own cost condition for the SAME
configuration (the cost condition contains the trial's spike constant `cs`).  The margin is that of
the witness (it does not depend on the trial). -/
def SpikePair.ofWitness {DA DB : SignedData} {c' : ℝ} {k q : ℕ} {xn : Fin k → ℝ} {gp : Fin q → ℝ}
    (WA : SpikeWitness DA c' xn gp) (c1B : ℝ) (hc1B : 0 < c1B)
    (hPB : SpikeChebOK DB WA.m WA.ρ c1B)
    (hcostB : SpikeCostOK DB WA.m xn WA.y WA.z WA.zph WA.ρ) : SpikePair DA DB c' xn gp where
  q' := WA.q'
  M := WA.M
  m := WA.m
  y := WA.y
  z := WA.z
  zph := WA.zph
  σ := WA.σ
  hσ := WA.hσ
  hM := WA.hM
  hm := WA.hm
  hy_not_spike := WA.hy_not_spike
  hz_spike := WA.hz_spike
  hzph := WA.hzph
  ρ := WA.ρ
  c1A := WA.c1
  c1B := c1B
  hρ := WA.hρ
  hρd := WA.hρd
  hc1A := WA.hc1
  hc1B := hc1B
  hPA := WA.hP
  hPB := hPB
  hcostA := WA.hcost
  hcostB := hcostB

/-- `PairCls` from a single-trial witness `WA` plus the endpoint-`B` ingredients on the same
configuration, the environments and the cap. -/
def PairCls.ofWitness {DA DB : SignedData} {c' : ℝ} {k q m1 m2 : ℕ} {xn : Fin k → ℝ}
    {gq : Fin q → ℝ} {yn : Fin m1 → ℝ} {yp : Fin m2 → ℝ}
    (hc : InterpCompat DA DB) (rA : SignedRegular DA) (rB : SignedRegular DB) (EA : SpikeEnv DA)
    (EB : SpikeEnv DB) (WA : SpikeWitness DA c' (Fin.append xn yn) (Fin.append gq yp))
    (c1B : ℝ) (hc1B : 0 < c1B) (hPB : SpikeChebOK DB WA.m WA.ρ c1B)
    (hcostB : SpikeCostOK DB WA.m (Fin.append xn yn) WA.y WA.z WA.zph WA.ρ) :
    PairCls DA DB c' xn gq yn yp where
  compat := hc
  rA := rA
  rB := rB
  EA := EA
  EB := EB
  P := SpikePair.ofWitness WA c1B hc1B hPB hcostB

/-! ### 7. The cost condition for an even number of spikes -/

theorem extFam_even {m : ℕ} (z : Fin (2 * m) → ℝ) (zph : ℝ) : extFam z zph m = z := by
  funext i
  simp [extFam, i.isLt]

/-- **Even case of the cost condition.**  For `M = 2m` spikes there is no phantom
(`extFam z zph m = z`), the numerator and denominator differences cancel, and `SpikeCostOK` is
exactly the bound `spikeCost ≤ ν M cs` (the per-spike constant of the trial). -/
theorem SpikeCostOK.of_even (D : SignedData) {k q' m : ℕ} (xn : Fin k → ℝ) (y : Fin q' → ℝ)
    (z : Fin (2 * m) → ℝ) (zph ρ : ℝ)
    (h : spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k z ≤
      D.ν * (((2 * m : ℕ) : ℝ) * D.cs) + D.ν * D.kph) :
    SpikeCostOK D m xn y z zph ρ := by
  unfold SpikeCostOK
  rw [extFam_even]
  linarith


/-! ### 7. Per-trial certificates: (P') and the even-`M` cost

Both lemmas reduce the witness inequalities to inequalities in finitely many real/rational
parameters of the trial (data supplies only those), uniformly in the configuration. -/

/-- **(P') from a polynomial certificate.**  If `m ≤ κ sp` and, on `[-1,1]`,
`c1 ≤ P_b(u)` and `κ(1-ρ²) ≤ (P_b(u) - (1-κ) c1)(1 + 2ρu + ρ²)` (a polynomial inequality in `u`
for a finitely supported `b`), then `SpikeChebOK D m ρ c1`. -/
theorem spikeChebOK_of_cert {D : SignedData} {m : ℕ} {ρ c1 κ : ℝ} (hρ : |ρ| < 1)
    (hκ0 : 0 ≤ κ) (hmκ : (m : ℝ) ≤ κ * D.sp) (hm : m ≤ D.sp)
    (hb : ∀ u ∈ Icc (-1 : ℝ) 1, c1 ≤ chebPs D.b u)
    (hpoly : ∀ u ∈ Icc (-1 : ℝ) 1,
      κ * (1 - ρ ^ 2) ≤ (chebPs D.b u - (1 - κ) * c1) * (1 + 2 * ρ * u + ρ ^ 2)) :
    SpikeChebOK D m ρ c1 := by
  intro u hu
  have hρ1 := abs_lt.mp hρ
  have hd : 0 < 1 + 2 * ρ * u + ρ ^ 2 := by
    have h1 : -|ρ| ≤ ρ * u := by
      have : |ρ * u| ≤ |ρ| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨hu.1, hu.2⟩)
      linarith [neg_abs_le (ρ * u)]
    have h2 : 0 < (1 - |ρ|) ^ 2 := pow_pos (by linarith) 2
    have h3 : (1 - |ρ|) ^ 2 = 1 - 2 * |ρ| + ρ ^ 2 := by
      have := sq_abs ρ
      nlinarith [this]
    nlinarith [h2, h3]
  rw [chebPs_poisSeq hρ hu, Nat.cast_sub hm]
  set P := chebPs D.b u
  set Q := (1 - ρ ^ 2) / (1 + 2 * ρ * u + ρ ^ 2) with hQ
  have hQd : Q * (1 + 2 * ρ * u + ρ ^ 2) = 1 - ρ ^ 2 := by
    rw [hQ]; exact div_mul_cancel₀ _ hd.ne'
  have hkey : κ * (Q - c1) ≤ P - c1 := by
    have h := hpoly u hu
    have h' : κ * Q * (1 + 2 * ρ * u + ρ ^ 2) ≤ (P - (1 - κ) * c1) * (1 + 2 * ρ * u + ρ ^ 2) := by
      calc κ * Q * (1 + 2 * ρ * u + ρ ^ 2) = κ * (1 - ρ ^ 2) := by rw [mul_assoc, hQd]
        _ ≤ _ := h
    have := le_of_mul_le_mul_right h' hd
    linarith
  have hP1 := hb u hu
  have hsp : (0 : ℝ) ≤ D.sp := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rcases le_or_gt c1 Q with hq | hq
  · have h1 : (m : ℝ) * (Q - c1) ≤ κ * D.sp * (Q - c1) :=
      mul_le_mul_of_nonneg_right hmκ (by linarith)
    have h2 : κ * D.sp * (Q - c1) ≤ D.sp * (P - c1) := by
      have := mul_le_mul_of_nonneg_left hkey hsp
      nlinarith [this]
    nlinarith [h1, h2]
  · have h1 : (m : ℝ) * (Q - c1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 (by linarith)
    have h2 : 0 ≤ (D.sp : ℝ) * (P - c1) := mul_nonneg hsp (by linarith)
    nlinarith [h1, h2]

/-- The `O(m)` remainder of `spikeCost` per pinned pair (terms T5-T10 of SPIKE-CLASS §4). -/
def costRem (b : ℕ → ℝ) (s' m : ℕ) (ρ : ℝ) : ℝ :=
  Real.log 2 - (((s' : ℝ) + m) / s') * (∑' i : ℕ, 2 * b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ)) +
    (2 * ((s' : ℝ) + m) / s') * (∑' k : ℕ, b (k + 1) ^ 2) -
    (4 * ((s' : ℝ) + m) / s') * (∑' k : ℕ, b (k + 1) * poisSeq ρ (k + 1)) +
    (2 * (m : ℝ) / s') * (ρ ^ 2 / (1 - ρ ^ 2)) + (4 * ((s' : ℝ) + m) / s') * barrierTrialS b (-ρ)

/-- **The cost in the paper's terms** (field map, SPIKE-CLASS §4): `T1 + T2 + T3 + T4 + m·costRem`. -/
theorem spikeCost_eq_map (ν e : ℝ) (a b : ℕ → ℝ) (s' m : ℕ) (ρ r : ℝ) (k : ℕ) {M : ℕ}
    (z : Fin M → ℝ) :
    spikeCost ν e a b s' m ρ r k z =
      2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) +
      4 * ν * m * e * ∑' j : ℕ, |a j| +
      2 * (m : ℝ) ^ 2 * (Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) - Real.log (1 - ρ ^ 2)) +
      2 * ((s' : ℝ) + m) * ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) +
      (m : ℝ) * costRem b s' m ρ := by
  unfold spikeCost costRem
  ring

/-- **Even-`M` cost from per-trial bounds.**  With `Λ' ≤ L`, `S_b(-y) - S_b(-ρ) ≤ De2` on
`[r,1)`, the Σ gain `≤ Sg`, `Σ|a| ≤ A`, `costRem ≤ K0`: an explicit bound, linear in the
configuration counts. -/
theorem spikeCost_le_of_bounds {ν e : ℝ} (hν : 0 ≤ ν) (he : 0 ≤ e) (a b : ℕ → ℝ) (s' m : ℕ)
    {ρ r L De2 Sg A K0 : ℝ} (k : ℕ) (z : Fin (2 * m) → ℝ)
    (hL : Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) ≤ L)
    (hDe : ∀ p, barrierTrialS b (-(z p)) - barrierTrialS b (-ρ) ≤ De2)
    (hSg : Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) - Real.log (1 - ρ ^ 2) ≤ Sg)
    (hA : ∑' j : ℕ, |a j| ≤ A) (hK : costRem b s' m ρ ≤ K0) :
    spikeCost ν e a b s' m ρ r k z ≤
      2 * (m : ℝ) * (k * L + 2 * ((s' : ℝ) + m) * De2 + m * Sg + 2 * ν * e * A) +
        (m : ℝ) * K0 := by
  rw [spikeCost_eq_map]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ (s' : ℝ) + m := by positivity
  have h1 : 2 * (m : ℝ) * k * Real.log (2 / (1 + realEnergyTau e ^ 2 * r)) ≤ 2 * m * k * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h2 : 4 * ν * m * e * ∑' j : ℕ, |a j| ≤ 4 * ν * m * e * A :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have h3 : 2 * (m : ℝ) ^ 2 * (Real.log (1 - realEnergyTau e ^ 2 * r ^ 2) - Real.log (1 - ρ ^ 2))
      ≤ 2 * (m : ℝ) ^ 2 * Sg := mul_le_mul_of_nonneg_left hSg (by positivity)
  have h4 : ∑ p, (barrierTrialS b (-(z p)) - barrierTrialS b (-ρ)) ≤ 2 * (m : ℝ) * De2 := by
    calc _ ≤ ∑ _p : Fin (2 * m), De2 := Finset.sum_le_sum fun p _ => hDe p
      _ = 2 * (m : ℝ) * De2 := by simp
  have h4' := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * ((s' : ℝ) + m))
  have h5 : (m : ℝ) * costRem b s' m ρ ≤ m * K0 := mul_le_mul_of_nonneg_left hK hm
  nlinarith [h1, h2, h3, h4', h5]

/-- **`SpikeCostOK` for even `M` from the per-trial bounds** and one arithmetic inequality in the
counts (`hfin`; `cs` the trial's per-spike charge, `kph ≥ 0` its phantom charge). -/
theorem SpikeCostOK.of_even_cert (D : SignedData) {k q' m : ℕ} (xn : Fin k → ℝ) (y : Fin q' → ℝ)
    (z : Fin (2 * m) → ℝ) (zph ρ : ℝ) {L De2 Sg A K0 : ℝ} (hν : 0 ≤ D.ν) (he : 0 ≤ D.e)
    (hL : Real.log (2 / (1 + realEnergyTau D.e ^ 2 * (1 - D.θ))) ≤ L)
    (hDe : ∀ p, barrierTrialS D.b (-(z p)) - barrierTrialS D.b (-ρ) ≤ De2)
    (hSg : Real.log (1 - realEnergyTau D.e ^ 2 * (1 - D.θ) ^ 2) - Real.log (1 - ρ ^ 2) ≤ Sg)
    (hA : ∑' j : ℕ, |D.a j| ≤ A) (hK : costRem D.b (D.sp - m) m ρ ≤ K0)
    (hfin : 2 * (m : ℝ) * (k * L + 2 * (((D.sp - m : ℕ) : ℝ) + m) * De2 + m * Sg +
        2 * D.ν * D.e * A) + (m : ℝ) * K0 ≤ D.ν * (((2 * m : ℕ) : ℝ) * D.cs) + D.ν * D.kph) :
    SpikeCostOK D m xn y z zph ρ :=
  SpikeCostOK.of_even D xn y z zph ρ
    ((spikeCost_le_of_bounds hν he D.a D.b (D.sp - m) m k z hL hDe hSg hA hK).trans hfin)


/-! ### 8. Odd `M`: the phantom row at `r = 1 - θ` (SIMPLIFY-S2 §2.3), charged to `ν kph` -/

theorem sum_extFam_odd {M m : ℕ} (hM : M + 1 = 2 * m) (z : Fin M → ℝ) (zph : ℝ) (f : ℝ → ℝ) :
    ∑ p, f (extFam z zph m p) = ∑ i, f (z i) + f zph := by
  rw [← Fin.sum_congr' (fun p => f (extFam z zph m p)) hM, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [extFam, i.isLt]
  · simp [extFam]

theorem powSum_append_extFam_odd {M m q' : ℕ} (hM : M + 1 = 2 * m) (τ ν : ℝ) (y : Fin q' → ℝ)
    (z : Fin M → ℝ) (zph : ℝ) (n : ℕ) :
    powSum τ ν (Fin.append y (extFam z zph m)) n =
      powSum τ ν (Fin.append y z) n + powSum τ ν (fun _ : Fin 1 => zph) n := by
  unfold powSum
  rw [row_sum_split (fun v => (τ * v) ^ (n + 1)) y (extFam z zph m),
    row_sum_split (fun v => (τ * v) ^ (n + 1)) y z,
    sum_extFam_odd hM z zph (fun v => (τ * v) ^ (n + 1))]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  ring

/-- `|log(1 - τ² w r)| ≤ log(1/θ)` for `|w| ≤ 1`, `r = 1 - θ`, `θ ≤ 1/2`, `0 < τ ≤ 1`. -/
theorem abs_log_one_sub_le {τ w θ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hw : |w| ≤ 1)
    (hθ : θ ∈ Ioc (0 : ℝ) (1 / 2)) :
    |Real.log (1 - (τ * w) * (τ * (1 - θ)))| ≤ Real.log (1 / θ) := by
  have hτ2 : τ * τ ≤ 1 := by nlinarith [hτ.1, hτ.2]
  have hτ0 : 0 ≤ τ * τ := by nlinarith [hτ.1]
  have hw' := abs_le.mp hw
  have hprod : |(τ * w) * (τ * (1 - θ))| ≤ 1 - θ := by
    rw [show (τ * w) * (τ * (1 - θ)) = (τ * τ) * w * (1 - θ) by ring, abs_mul, abs_mul,
      abs_of_nonneg hτ0, abs_of_nonneg (by linarith [hθ.2] : (0 : ℝ) ≤ 1 - θ)]
    have : τ * τ * |w| ≤ 1 := by nlinarith [abs_nonneg w]
    nlinarith [hθ.2, abs_nonneg w]
  have hp := abs_le.mp hprod
  have hlo : θ ≤ 1 - (τ * w) * (τ * (1 - θ)) := by linarith [hp.2]
  have hhi : 1 - (τ * w) * (τ * (1 - θ)) ≤ 1 / θ := by
    have : (2 : ℝ) ≤ 1 / θ := by rw [le_div_iff₀ hθ.1]; linarith [hθ.2]
    linarith [hp.1, hθ.1]
  have hpos : 0 < 1 - (τ * w) * (τ * (1 - θ)) := lt_of_lt_of_le hθ.1 hlo
  rw [abs_le]
  constructor
  · have h1 : Real.log θ ≤ Real.log (1 - (τ * w) * (τ * (1 - θ))) := Real.log_le_log hθ.1 hlo
    have h2 : Real.log (1 / θ) = -Real.log θ := by rw [one_div, Real.log_inv]
    linarith
  · exact Real.log_le_log hpos hhi

theorem abs_sum_log_le {n : ℕ} {τ θ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hθ : θ ∈ Ioc (0 : ℝ) (1 / 2)) (w : Fin n → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    |∑ i, Real.log (1 - (τ * w i) * (τ * (1 - θ)))| ≤ n * Real.log (1 / θ) := by
  calc _ ≤ ∑ i, |Real.log (1 - (τ * w i) * (τ * (1 - θ)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, Real.log (1 / θ) :=
        Finset.sum_le_sum fun i _ => abs_log_one_sub_le hτ (hw i) hθ
    _ = _ := by simp

set_option maxHeartbeats 1600000 in
/-- **The phantom bound (odd `M`).**  With the phantom at `r = 1 - θ` and the cost of the `2m`
pinned spikes within `ν (2m) cs`, the cost condition holds as soon as the phantom row is paid by
`ν kph`:
`2ν A1 + ν BR + (k + q' + M + 1) log(1/θ) + 2 sp B1 + ν cs ≤ ν kph`, where the data supply
`|S_a(-τ r)| ≤ A1`, `|S_b(-r)| ≤ B1` and `|Σ R_n (τ r)^{n+1}/(n+1)| ≤ BR` (three evaluations of the
trial at the single point `r`).  Since `k + q' + M ≤ n` this is `kph = O(1)`, so `kph/ν → 0`. -/
theorem SpikeCostOK.of_odd_cert (D : SignedData) (hν : 0 < D.ν) (rD : SignedRegular D)
    {k q' M m : ℕ} (hM : M + 1 = 2 * m) (xn : Fin k → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ)
    (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, |z i| ≤ 1)
    (hθ : D.θ ∈ Ioc (0 : ℝ) (1 / 2)) (ρ : ℝ) {A1 B1 BR : ℝ}
    (hA1 : |barrierTrialS D.a (-D.τ * (1 - D.θ))| ≤ A1)
    (hB1 : |barrierTrialS D.b (-(1 - D.θ))| ≤ B1)
    (hBR : |∑' n : ℕ, D.R n * (D.τ * (1 - D.θ)) ^ (n + 1) / ((n : ℝ) + 1)| ≤ BR)
    (hcost : spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) k
        (extFam z (1 - D.θ) m) ≤ D.ν * (((2 * m : ℕ) : ℝ) * D.cs))
    (hph : 2 * D.ν * A1 + D.ν * BR + ((k + q' + M + 1 : ℕ) : ℝ) * Real.log (1 / D.θ) +
        2 * (D.sp : ℝ) * B1 + D.ν * D.cs ≤ D.ν * D.kph) :
    SpikeCostOK D m xn y z (1 - D.θ) ρ := by
  rw [costOK_iff D hν]
  have hτ := rD.tau
  set r := 1 - D.θ with hr
  have hr1 : |r| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  set δ := powSum D.τ D.ν (fun _ : Fin 1 => r) with hδ
  set u := fun j => powSum D.τ D.ν xn j - powSum D.τ D.ν (Fin.append y z) j with hu
  have hyz : ∀ p, |Fin.append y z p| ≤ 1 := fin_append_forall y z (fun t => |t| ≤ 1) hy hz
  have hgx := isGeom_powSum hτ.1 hν xn hx
  have hgyz := isGeom_powSum hτ.1 hν (Fin.append y z) hyz
  have hgd := isGeom_powSum hτ.1 hν (fun _ : Fin 1 => r) (fun _ => hr1)
  have hgu : IsGeom D.τ u := hgx.sub hgyz
  have hgR := rD.hR
  -- the Ipd term
  have hu' : (fun j => powSum D.τ D.ν xn j -
      powSum D.τ D.ν (Fin.append y (extFam z r m)) j) = fun j => u j - δ j := by
    funext j
    rw [powSum_append_extFam_odd hM]
    simp only [hu, hδ]
    ring
  have hIpd : Ipd (fun j => powSum D.τ D.ν xn j - powSum D.τ D.ν (Fin.append y (extFam z r m)) j)
      u D.R = ip δ δ - 2 * (ip u δ - ip D.R δ) := by
    rw [hu']
    unfold Ipd
    have h1 := hasSum_ip hτ ((hgu.sub hgd).sub hgR) ((hgu.sub hgd).sub hgR)
    have h2 := hasSum_ip hτ (hgu.sub hgR) (hgu.sub hgR)
    have h3 := ((hasSum_ip hτ hgd hgd).sub
      (((hasSum_ip hτ hgu hgd).sub (hasSum_ip hτ hgR hgd)).mul_left 2))
    have h4 := h1.sub h2
    refine h4.unique ?_
    convert h3 using 1
    funext n
    ring
  -- pair sums
  have hτx : ∀ i, |D.τ * xn i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1]; exact lt_of_le_of_lt (mul_le_of_le_one_right hτ.1.le (hx i)) hτ.2
  have hτyz : ∀ i, |D.τ * Fin.append y z i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1]; exact lt_of_le_of_lt (mul_le_of_le_one_right hτ.1.le (hyz i)) hτ.2
  have hτr : ∀ _i : Fin 1, |D.τ * r| < 1 := fun _ => by
    rw [abs_mul, abs_of_pos hτ.1]; exact lt_of_le_of_lt (mul_le_of_le_one_right hτ.1.le hr1) hτ.2
  have hpx := hasSum_pair_powSum hν hτx hτr
  have hpyz := hasSum_pair_powSum hν hτyz hτr
  have hpd := hasSum_pair_powSum hν hτr hτr
  have hipx : ip (powSum D.τ D.ν xn) δ =
      -(∑ i, ∑ _j : Fin 1, Real.log (1 - (D.τ * xn i) * (D.τ * r))) / D.ν ^ 2 :=
    (hasSum_ip hτ hgx hgd).unique hpx
  have hipyz : ip (powSum D.τ D.ν (Fin.append y z)) δ =
      -(∑ i, ∑ _j : Fin 1, Real.log (1 - (D.τ * Fin.append y z i) * (D.τ * r))) / D.ν ^ 2 :=
    (hasSum_ip hτ hgyz hgd).unique hpyz
  have hipd : ip δ δ =
      -(∑ _i : Fin 1, ∑ _j : Fin 1, Real.log (1 - (D.τ * r) * (D.τ * r))) / D.ν ^ 2 :=
    (hasSum_ip hτ hgd hgd).unique hpd
  have hipu : ip u δ = ip (powSum D.τ D.ν xn) δ - ip (powSum D.τ D.ν (Fin.append y z)) δ :=
    ((hasSum_ip hτ hgu hgd).unique (by
      convert (hasSum_ip hτ hgx hgd).sub (hasSum_ip hτ hgyz hgd) using 1
      funext n; simp only [hu]; ring))
  have hipR : ip D.R δ = (1 / D.ν) * ∑' n : ℕ, D.R n * (D.τ * r) ^ (n + 1) / ((n : ℝ) + 1) := by
    unfold ip
    rw [← tsum_mul_left]
    congr 1; funext n
    simp only [hδ, powSum, Finset.univ_unique, Finset.sum_singleton]
    field_simp
  -- bounds on the logs
  have hLx := abs_sum_log_le hτ hθ xn hx
  have hLyz := abs_sum_log_le hτ hθ (Fin.append y z) hyz
  have hLr : |Real.log (1 - (D.τ * r) * (D.τ * r))| ≤ Real.log (1 / D.θ) :=
    abs_log_one_sub_le hτ hr1 hθ
  simp only [Finset.univ_unique, Finset.sum_singleton] at hipx hipyz hipd
  -- the S_a and S_b parts
  have hSa : (∑ p, barrierTrialS D.a (-D.τ * Fin.append y (extFam z r m) p)) -
      ∑ p, barrierTrialS D.a (-D.τ * Fin.append y z p) = barrierTrialS D.a (-D.τ * r) := by
    rw [row_sum_split (fun v => barrierTrialS D.a (-D.τ * v)) y (extFam z r m),
      row_sum_split (fun v => barrierTrialS D.a (-D.τ * v)) y z,
      sum_extFam_odd hM z r (fun v => barrierTrialS D.a (-D.τ * v))]
    ring
  have hSb : (∑ p, barrierTrialS D.b (-(extFam z r m p))) - ∑ p, barrierTrialS D.b (-(z p)) =
      barrierTrialS D.b (-r) := by
    rw [sum_extFam_odd hM z r (fun v => barrierTrialS D.b (-v))]
    ring
  -- assemble
  unfold costGap numDiff
  rw [hSa, hSb, hIpd, hipu, hipR, hipx, hipyz, hipd]
  have hν2 : 0 < D.ν ^ 2 := by positivity
  have hcard : ((k + q' + M + 1 : ℕ) : ℝ) = (k : ℝ) + ((q' + M : ℕ) : ℝ) + 1 := by push_cast; ring
  have hMm : (((2 * m : ℕ) : ℝ)) = (M : ℝ) + 1 := by exact_mod_cast hM.symm
  rw [hMm] at hcost
  rw [hcard] at hph
  have hlogθ : 0 ≤ Real.log (1 / D.θ) := Real.log_nonneg (by
    rw [le_div_iff₀ hθ.1]; linarith [hθ.2])
  have eA := abs_le.mp hA1
  have eB := abs_le.mp hB1
  have eR := abs_le.mp hBR
  have ex := abs_le.mp hLx
  have eyz := abs_le.mp hLyz
  have er := abs_le.mp hLr
  have hspB : 2 * (D.sp : ℝ) * (-(barrierTrialS D.b (-r))) ≤ 2 * (D.sp : ℝ) * B1 :=
    mul_le_mul_of_nonneg_left (by linarith [eB.1]) (by positivity)
  have hνA : D.ν * barrierTrialS D.a (-D.τ * r) ≤ D.ν * A1 :=
    mul_le_mul_of_nonneg_left eA.2 hν.le
  have hνR : D.ν * ∑' n : ℕ, D.R n * (D.τ * r) ^ (n + 1) / ((n : ℝ) + 1) ≤ D.ν * BR :=
    mul_le_mul_of_nonneg_left eR.2 hν.le
  have e2 : D.ν ^ 2 * ((2 / D.ν) * barrierTrialS D.a (-D.τ * r) + (1 / 2) *
      (-Real.log (1 - D.τ * r * (D.τ * r)) / D.ν ^ 2 - 2 *
        (-(∑ i, Real.log (1 - D.τ * xn i * (D.τ * r))) / D.ν ^ 2 -
          -(∑ i, Real.log (1 - D.τ * Fin.append y z i * (D.τ * r))) / D.ν ^ 2 -
          1 / D.ν * ∑' n : ℕ, D.R n * (D.τ * r) ^ (n + 1) / ((n : ℝ) + 1)))) =
      2 * (D.ν * barrierTrialS D.a (-D.τ * r)) - (1 / 2) * Real.log (1 - D.τ * r * (D.τ * r)) +
        (∑ i, Real.log (1 - D.τ * xn i * (D.τ * r))) -
        (∑ i, Real.log (1 - D.τ * Fin.append y z i * (D.τ * r))) +
        D.ν * ∑' n : ℕ, D.R n * (D.τ * r) ^ (n + 1) / ((n : ℝ) + 1) := by
    field_simp
    ring
  rw [e2]
  have hcq : ((q' + M : ℕ) : ℝ) * Real.log (1 / D.θ) ≥ 0 := by positivity
  nlinarith [hcost, hph, hspB, hνA, hνR, ex.1, eyz.2, er.1, hlogθ]

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.refTilt_linSeq
#print axioms CatalanMeasure.Signed.SpikeEnv.interp
#print axioms CatalanMeasure.Signed.Ipd_eq
#print axioms CatalanMeasure.Signed.Ipd_linSeq
#print axioms CatalanMeasure.Signed.numB_sub
#print axioms CatalanMeasure.Signed.numDiff_linSeq
#print axioms CatalanMeasure.Signed.spikeDenB_sub
#print axioms CatalanMeasure.Signed.denDiff_linSeq
#print axioms CatalanMeasure.Signed.spikeCost_split
#print axioms CatalanMeasure.Signed.costA_le
#print axioms CatalanMeasure.Signed.costLin_linSeq
#print axioms CatalanMeasure.Signed.costQuad_fin
#print axioms CatalanMeasure.Signed.costQuad_le
#print axioms CatalanMeasure.Signed.spikeCost_interp_le
#print axioms CatalanMeasure.Signed.costOK_iff
#print axioms CatalanMeasure.Signed.costGap_interp_le
#print axioms CatalanMeasure.Signed.SpikeCostOK.interp
#print axioms CatalanMeasure.Signed.SpikeChebOK.interp
#print axioms CatalanMeasure.Signed.SpikePair.toWitness
#print axioms CatalanMeasure.Signed.spikeCompareFixed_interp
#print axioms CatalanMeasure.Signed.spikeFix_of_ends
#print axioms CatalanMeasure.Signed.SpikePair.monoMargin
#print axioms CatalanMeasure.Signed.PairCls.ofWitness
#print axioms CatalanMeasure.Signed.SpikeCostOK.of_even
#print axioms CatalanMeasure.Signed.spikeChebOK_of_cert
#print axioms CatalanMeasure.Signed.spikeCost_le_of_bounds
#print axioms CatalanMeasure.Signed.SpikeCostOK.of_even_cert
#print axioms CatalanMeasure.Signed.SpikeCostOK.of_odd_cert
