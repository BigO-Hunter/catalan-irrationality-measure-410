module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMom

@[expose] public section

/-!
# The curvature lower bound `hκ` (Theorem A, lane E1b, item 18)

`curvQ DA DB p = AA − AB − BA + BB` (`curvQ_blocks`), where each `curvBlock` is the bilinear form of `restQ`.  The
trial sequences of the two endpoint trials share the pole tails of `v` and `p`, so the combination is the
quadratic form of the DIFFERENCE of the data (`curvQ_eq`):

  `curvQ = ½‖Δv‖² + 2‖Δa‖² + (1−η)·RB + 2η‖Δp‖² − 2·RA + Σ w_i Δb_i² + ½ ip(ΔR,ΔR) − ½ ip(Δmpos,Δmpos)`,

with `RB = refBil(A,A) − refBil(A,B) − refBil(B,A) + refBil(B,B)` (four `refBil_enc`, `enc4`),
`RA = raBil(A,A) − raBil(A,B) − raBil(B,A) + raBil(B,B)` (finite sums), the `t`-terms cancelling (`Spec.ht`).  The norms and
`ip(ΔR,ΔR)` are `≥ 0` (a lower bound `0` is admissible; `EvalNorm` gives exact values of the finite differences),
`ip(Δmpos,Δmpos)` is bounded above by `EvalRefMom.ip_mposDiff_le`.  `curvQ_ge` combines the bounds into `κc ≤ curvQ`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open OAI.InternalCatalan
open CatalanMeasure.Signed CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.LogEval (Enc)
open MeasureTheory Set Filter Topology

noncomputable section

/-! ### 1. Bilinear expansions of the four blocks -/

theorem nsq4_eq {u v : ℕ → ℝ} (hu : Summable fun k => |u k|) (hv : Summable fun k => |v k|) :
    nsqBil u u - nsqBil u v - nsqBil v u + nsqBil v v = barrierTrialNormSq (fun k => u k - v k) := by
  have s11 := summable_mul_bdd (abs_wsh_le hu) (summable_abs_sh hu)
  have s12 := summable_mul_bdd (abs_wsh_le hu) (summable_abs_sh hv)
  have s21 := summable_mul_bdd (abs_wsh_le hv) (summable_abs_sh hu)
  have s22 := summable_mul_bdd (abs_wsh_le hv) (summable_abs_sh hv)
  have h := ((s11.hasSum.sub s12.hasSum).sub s21.hasSum).add s22.hasSum
  have h2 : HasSum (fun n => wsh (fun k => u k - v k) n * sh (fun k => u k - v k) n)
      (∑' n, wsh u n * sh u n - ∑' n, wsh u n * sh v n - ∑' n, wsh v n * sh u n +
        ∑' n, wsh v n * sh v n) := by
    convert h using 1
    funext n
    simp only [wsh, sh]
    ring
  rw [nsq_eq_tsum]
  unfold nsqBil
  exact h2.tsum_eq.symm

theorem ip4_eq {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c c' : ℕ → ℝ} (hc : IsGeom τ c)
    (hc' : IsGeom τ c') :
    ip c c - ip c c' - ip c' c + ip c' c' = ip (fun n => c n - c' n) (fun n => c n - c' n) := by
  have h := (((hasSum_ip hτ hc hc).sub (hasSum_ip hτ hc hc')).sub (hasSum_ip hτ hc' hc)).add
    (hasSum_ip hτ hc' hc')
  have h' := hasSum_ip hτ (hc.sub hc') (hc.sub hc')
  have h2 : HasSum (fun n : ℕ => (c n - c' n) * (c n - c' n) / ((n : ℝ) + 1))
      (ip c c - ip c c' - ip c' c + ip c' c') := by
    convert h using 1
    funext n
    ring
  exact h2.unique h'

theorem sumBil4_eq (w : ℕ → ℝ) (K : ℕ) (b b' : ℕ → ℝ) :
    sumBil w K b b - sumBil w K b b' - sumBil w K b' b + sumBil w K b' b' =
      ∑ i ∈ Finset.range K, w i * (b (i + 1) - b' (i + 1)) ^ 2 := by
  unfold sumBil
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem denW_nonneg (D : SignedData) (i : ℕ) : 0 ≤ denW D i := by
  unfold denW
  positivity

/-- **The curvature as the quadratic form of the difference.** -/
theorem curvQ_eq (DA DB : SignedData) (p : ℕ) (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (htA : DA.t = mneg DA.μ DA.τ) (htB : DB.t = mneg DB.μ DB.τ) :
    curvQ DA DB p =
      (1 / 2) * barrierTrialNormSq (fun k => DA.v k - DB.v k) +
      2 * barrierTrialNormSq (fun k => DA.a k - DB.a k) +
      (1 - DA.η) * (refBil DA.μ DA.μ - refBil DA.μ DB.μ - refBil DB.μ DA.μ + refBil DB.μ DB.μ) +
      2 * DA.η * barrierTrialNormSq (fun k => DA.p k - DB.p k) -
      2 * (raBil DA.R DA.a - raBil DA.R DB.a - raBil DB.R DA.a + raBil DB.R DB.a) +
      (∑ i ∈ Finset.range DA.K, denW DA i * (DA.b (i + 1) - DB.b (i + 1)) ^ 2) +
      (1 / 2) * ip (fun n => DA.R n - DB.R n) (fun n => DA.R n - DB.R n) -
      (1 / 2) * ip (fun n => mpos DA.μ DA.τ n - mpos DB.μ DA.τ n)
        (fun n => mpos DA.μ DA.τ n - mpos DB.μ DA.τ n) := by
  have hτ := rA.tau
  have n1 := nsq4_eq rA.hv rB.hv
  have n2 := nsq4_eq rA.ha rB.ha
  have n3 := nsq4_eq rA.hp rB.hp
  have gR := SignedRegular.hRτ hc rB
  have i1 := ip4_eq hτ rA.hR gR
  have gA := isGeom_mpos rA.hμ hτ.1
  have gB := isGeom_mpos rB.hμ hτ.1
  have i2 := ip4_eq hτ gA gB
  have s1 := sumBil4_eq (denW DA) DA.K DA.b DB.b
  rw [curvQ_blocks hc rA rB p]
  simp only [curvBlock]
  rw [htA, htB, hc.τ]
  linear_combination (1 / 2) * n1 + 2 * n2 + (2 * DA.η) * n3 + (1 / 2) * i1 - (1 / 2) * i2 + s1

/-! ### 2. The lower bound -/

/-- **`κc ≤ curvQ`** from bounds on the five difference quantities.  `lbV, lbA, lbP, lbRR` are lower bounds of
`‖Δv‖²`, `‖Δa‖²`, `‖Δp‖²`, `ip(ΔR,ΔR)` (`0` is admissible), `lbRB` of the `refBil` combination (`enc4`), `ubRa` an
upper bound of the `raBil` combination, `ubIM` of `ip(Δmpos, Δmpos)` (`ip_mposDiff_le`). -/
theorem curvQ_ge (DA DB : SignedData) (p : ℕ) (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (htA : DA.t = mneg DA.μ DA.τ) (htB : DB.t = mneg DB.μ DB.τ)
    (hη1 : DA.η ≤ 1) (lbV lbA lbP lbRR lbRB lbB ubRa ubIM : ℝ)
    (hV : lbV ≤ barrierTrialNormSq (fun k => DA.v k - DB.v k))
    (hA : lbA ≤ barrierTrialNormSq (fun k => DA.a k - DB.a k))
    (hP : lbP ≤ barrierTrialNormSq (fun k => DA.p k - DB.p k))
    (hRR : lbRR ≤ ip (fun n => DA.R n - DB.R n) (fun n => DA.R n - DB.R n))
    (hRB : lbRB ≤ refBil DA.μ DA.μ - refBil DA.μ DB.μ - refBil DB.μ DA.μ + refBil DB.μ DB.μ)
    (hBb : lbB ≤ ∑ i ∈ Finset.range DA.K, denW DA i * (DA.b (i + 1) - DB.b (i + 1)) ^ 2)
    (hRa : raBil DA.R DA.a - raBil DA.R DB.a - raBil DB.R DA.a + raBil DB.R DB.a ≤ ubRa)
    (hIM : ip (fun n => mpos DA.μ DA.τ n - mpos DB.μ DA.τ n)
        (fun n => mpos DA.μ DA.τ n - mpos DB.μ DA.τ n) ≤ ubIM) :
    (1 / 2) * lbV + 2 * lbA + (1 - DA.η) * lbRB + 2 * DA.η * lbP - 2 * ubRa + lbB + (1 / 2) * lbRR -
        (1 / 2) * ubIM ≤ curvQ DA DB p := by
  rw [curvQ_eq DA DB p hc rA rB htA htB]
  have hη0 : 0 ≤ DA.η := rA.hη0
  have m1 := mul_le_mul_of_nonneg_left hRB (show 0 ≤ 1 - DA.η by linarith)
  have m2 := mul_le_mul_of_nonneg_left hP hη0
  nlinarith [m1, m2, hV, hA, hRR, hRa, hIM, hBb]

/-- The four-term combination of enclosures (`refBil_enc` for the pairs `AA, AB, BA, BB`). -/
theorem enc4 {x1 x2 x3 x4 : ℝ} {p1 p2 p3 p4 : ℚ × ℚ} (h1 : Enc x1 p1) (h2 : Enc x2 p2)
    (h3 : Enc x3 p3) (h4 : Enc x4 p4) :
    Enc (x1 - x2 - x3 + x4) (p1.1 - p2.1 - p3.1 + p4.1, p1.2 + p2.2 + p3.2 + p4.2) :=
  ((h1.sub h2).sub h3).add h4

/-- `hκ` from `κc ≤ curvQ` eventually (`IntervalEnds.regA/regB` hold eventually; `curvQ DA DB p` is independent
of `p`).  The consumer: `Phase2Contract.hκ`, `Interp.SignedNearBounds.ofEnds` (`hκ`). -/
theorem hκ_of_ge {DA DB : ℕ → SignedData} {n : ℕ → ℕ} {κc : ℝ}
    (h : ∀ᶠ N : ℕ in atTop, κc ≤ curvQ (DA N) (DB N) (n N)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, κc - ε ≤ curvQ (DA N) (DB N) (n N) :=
  fun ε hε => h.mono (fun N hN => by linarith)

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.curvQ_eq
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.curvQ_ge
