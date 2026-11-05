module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RConst
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefCurv
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefSym

@[expose] public section

/-!
# 410 assembly: `κc ≤ curvQ` for the family (T9, second half)

The curvature `curvQ (famD X N) (famD Y N) p` is bounded below by rational quantities
(`EvalRefCurv.curvQ_ge`), with
* `lbNorm`: partial sums `Σ_{k<K} (Δ_k)² / (k+1)` of the squared differences of two trial sequences
  (nonnegative terms of a summable series: a lower bound of `barrierTrialNormSq`; screen
  `phase2-data/consts/kappac_screen.py`: `K = 1000` captures 98 % of `‖Δa‖²` in interval 0, 99.9999 % in interval 1,
  and all of `‖Δv‖², ‖Δp‖²` since the common tails cancel);
* `lbRRQ`, `lbBQ`, `rbQ`: exact finite sums (`R`, `b`, `ra` combinations).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

noncomputable section

theorem summable_sq_of_abs {u : ℕ → ℝ} (h : Summable fun k => |u k|) : Summable fun k => u k ^ 2 := by
  obtain ⟨M, hM⟩ := h.tendsto_atTop_zero.bddAbove_range
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (h.mul_left M)
  have h1 : |u k| ≤ M := hM ⟨k, rfl⟩
  nlinarith [abs_nonneg (u k), sq_abs (u k)]

/-- Partial sums of the norm series are lower bounds. -/
theorem norm_ge_partial {u : ℕ → ℝ} (h : Summable fun k => |u k|) (K : ℕ) :
    ∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) ≤ barrierTrialNormSq u := by
  have h1 : Summable fun k => |u (k + 1)| := (summable_nat_add_iff 1).mpr h
  have h2 : Summable fun k => u (k + 1) ^ 2 := summable_sq_of_abs h1
  have h3 : Summable fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) := by
    refine Summable.of_nonneg_of_le (fun k => div_nonneg (sq_nonneg _) (by positivity))
      (fun k => ?_) h2
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact div_le_self (sq_nonneg _) this
  unfold barrierTrialNormSq
  exact Summable.sum_le_tsum _ (fun k _ => div_nonneg (sq_nonneg _) (by positivity)) h3

def sqQ (s : SeqQ) (k : ℕ) : ℚ := s.f.getD k 0 + tailValQ s.tail (k + 1)

theorem seq_succ (s : SeqQ) (k : ℕ) :
    tseq (fQ s.f) (s.tail.map TailQ.toC) (k + 1) = ((sqQ s k : ℚ) : ℝ) := by
  unfold tseq sqQ
  rw [if_neg (Nat.succ_ne_zero k), fQ_succ, ← tailValQ_spec]
  push_cast
  rfl

def lbNorm (s t : SeqQ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (sqQ s k - sqQ t k) ^ 2 / ((k : ℚ) + 1)

theorem lbNorm_le (s t : SeqQ)
    (hs : Summable fun j => |tseq (fQ s.f) (s.tail.map TailQ.toC) j|)
    (ht : Summable fun j => |tseq (fQ t.f) (t.tail.map TailQ.toC) j|) (K : ℕ) :
    ((lbNorm s t K : ℚ) : ℝ) ≤ barrierTrialNormSq
      (fun k => tseq (fQ s.f) (s.tail.map TailQ.toC) k - tseq (fQ t.f) (t.tail.map TailQ.toC) k) := by
  have hd : Summable fun k => |tseq (fQ s.f) (s.tail.map TailQ.toC) k -
      tseq (fQ t.f) (t.tail.map TailQ.toC) k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => abs_sub _ _) (hs.add ht)
  refine le_trans (le_of_eq ?_) (norm_ge_partial hd K)
  unfold lbNorm
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [seq_succ, seq_succ]

/-- Exact `ip (ΔR, ΔR)` for finite references. -/
def lbRRQ (X Y : FamPar) : ℚ :=
  ∑ n ∈ Finset.range (max X.T.R.f.length Y.T.R.f.length),
    (X.T.R.f.getD n 0 - Y.T.R.f.getD n 0) ^ 2 / ((n : ℚ) + 1)

theorem famD_ipRR (X Y : FamPar) (N : ℕ) :
    ip (fun n => (famD X N).R n - (famD Y N).R n) (fun n => (famD X N).R n - (famD Y N).R n) =
      ((lbRRQ X Y : ℚ) : ℝ) := by
  unfold ip lbRRQ
  rw [tsum_eq_sum (s := Finset.range (max X.T.R.f.length Y.T.R.f.length))]
  · push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [famD_R, famD_R]
    push_cast
    ring
  · intro n hn
    have hn' : max X.T.R.f.length Y.T.R.f.length ≤ n := by simpa using hn
    simp only [famD_R_zero X N n (le_trans (le_max_left _ _) hn'), famD_R_zero Y N n (le_trans (le_max_right _ _) hn')]
    simp

/-- The `b`-part of the curvature: `denW ≥ (sp/ν)² · 2/(i+1)` with `sp/ν = 20/58`. -/
def lbBQ (X Y : FamPar) : ℚ :=
  ∑ i ∈ Finset.range X.bs.length,
    (20 / 58 : ℚ) ^ 2 * (2 / ((i : ℚ) + 1)) * (X.bs.getD i 0 - Y.bs.getD i 0) ^ 2

theorem famD_lbB (X Y : FamPar) (N : ℕ) (hN : 0 < N) :
    ((lbBQ X Y : ℚ) : ℝ) ≤ ∑ i ∈ Finset.range (famD X N).K,
      denW (famD X N) i * ((famD X N).b (i + 1) - (famD Y N).b (i + 1)) ^ 2 := by
  unfold lbBQ
  show _ ≤ ∑ i ∈ Finset.range X.bs.length, denW (famD X N) i * (bSeq X.bs (i + 1) - bSeq Y.bs (i + 1)) ^ 2
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  have hν : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : bSeq X.bs (i + 1) = ((X.bs.getD i 0 : ℚ) : ℝ) := by unfold bSeq; rw [if_neg (Nat.succ_ne_zero i)]; simp
  have e2 : bSeq Y.bs (i + 1) = ((Y.bs.getD i 0 : ℚ) : ℝ) := by unfold bSeq; rw [if_neg (Nat.succ_ne_zero i)]; simp
  rw [e1, e2]
  have hw : (20 / 58 : ℝ) ^ 2 * (2 / ((i : ℝ) + 1)) ≤ denW (famD X N) i := by
    unfold denW
    show _ ≤ (((20 * N : ℕ) : ℝ) ^ 2 / (58 * (N : ℝ)) ^ 2) * (2 / ((i + 1 : ℕ) : ℝ)) +
      2 * ((20 * N : ℕ) : ℝ) / (58 * (N : ℝ)) ^ 2
    push_cast
    have hN0 : (N : ℝ) ≠ 0 := hν.ne'
    have : ((20 : ℝ) * N) ^ 2 / (58 * (N : ℝ)) ^ 2 = (20 / 58) ^ 2 := by field_simp
    rw [this]
    have : 0 ≤ 2 * (20 * (N : ℝ)) / (58 * (N : ℝ)) ^ 2 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

/-- `raBil (famD X).R (famD Y).a`, exact. -/
def rbQ (X Y : FamPar) : ℚ :=
  ∑ n ∈ Finset.range X.T.R.f.length,
    (-(-1 : ℚ) ^ (n + 1) * (X.T.R.f.getD n 0) / ((n : ℚ) + 1)) * sqQ Y.T.a n

theorem famD_raBil (X Y : FamPar) (N : ℕ) :
    raBil (famD X N).R (famD Y N).a = ((rbQ X Y : ℚ) : ℝ) := by
  unfold raBil rbQ
  rw [tsum_eq_sum (s := Finset.range X.T.R.f.length)]
  · push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold rt sh refTilt
    rw [Nat.add_sub_cancel, famD_R]
    have : (famD Y N).a (n + 1) = ((sqQ Y.T.a n : ℚ) : ℝ) := seq_succ Y.T.a n
    rw [this]
    push_cast
    ring
  · intro n hn
    have hn' : X.T.R.f.length ≤ n := by simpa using hn
    unfold rt sh refTilt
    rw [Nat.add_sub_cancel, famD_R_zero X N n hn']
    simp

/-- The combination `raBil(A,A) - raBil(A,B) - raBil(B,A) + raBil(B,B)` is the rational `ubRaQ`. -/
def ubRaQ (X Y : FamPar) : ℚ := rbQ X X - rbQ X Y - rbQ Y X + rbQ Y Y

theorem famD_ubRa (X Y : FamPar) (N : ℕ) :
    raBil (famD X N).R (famD X N).a - raBil (famD X N).R (famD Y N).a -
      raBil (famD Y N).R (famD X N).a + raBil (famD Y N).R (famD Y N).a = ((ubRaQ X Y : ℚ) : ℝ) := by
  unfold ubRaQ
  rw [famD_raBil, famD_raBil, famD_raBil, famD_raBil]
  push_cast
  ring

theorem srefOK_mono {μ : SRef} {C C' : ℝ} (h : μ.OK C) (hC : C ≤ C') : μ.OK C' :=
  ⟨fun τ => CatalanMeasure.Signed.BD_mono (h.hP τ) hC, fun τ => CatalanMeasure.Signed.BD_mono (h.hN τ) hC, h.hNm⟩

theorem famD_v_eq (X : FamPar) (N : ℕ) :
    (famD X N).v = tseq (fQ X.T.v.f) (X.T.v.tail.map TailQ.toC) := rfl

theorem famD_lbV (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (K N : ℕ) :
    ((lbNorm X.T.v Y.T.v K : ℚ) : ℝ) ≤ barrierTrialNormSq (fun k => (famD X N).v k - (famD Y N).v k) := by
  have hX := Glue410.Spec_summable_v (famD_spec X hokX N)
  have hY := Glue410.Spec_summable_v (famD_spec Y hokY N)
  rw [famD_v_eq] at hX ⊢
  rw [famD_v_eq] at hY ⊢
  exact lbNorm_le X.T.v Y.T.v hX hY K

theorem famD_a_eq (X : FamPar) (N : ℕ) :
    (famD X N).a = tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC) := rfl

theorem famD_lbA (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (K N : ℕ) :
    ((lbNorm X.T.a Y.T.a K : ℚ) : ℝ) ≤ barrierTrialNormSq (fun k => (famD X N).a k - (famD Y N).a k) := by
  have hX := Glue410.Spec_summable_a (famD_spec X hokX N)
  have hY := Glue410.Spec_summable_a (famD_spec Y hokY N)
  rw [famD_a_eq] at hX ⊢
  rw [famD_a_eq] at hY ⊢
  exact lbNorm_le X.T.a Y.T.a hX hY K

theorem famD_p_eq (X : FamPar) (N : ℕ) :
    (famD X N).p = tseq (fQ X.T.p.f) (X.T.p.tail.map TailQ.toC) := rfl

theorem famD_lbP (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (K N : ℕ) :
    ((lbNorm X.T.p Y.T.p K : ℚ) : ℝ) ≤ barrierTrialNormSq (fun k => (famD X N).p k - (famD Y N).p k) := by
  have hX := Glue410.Spec_summable_p (famD_spec X hokX N)
  have hY := Glue410.Spec_summable_p (famD_spec Y hokY N)
  rw [famD_p_eq] at hX ⊢
  rw [famD_p_eq] at hY ⊢
  exact lbNorm_le X.T.p Y.T.p hX hY K

/-- **`κc ≤ curvQ`** for two trials of the family. -/
theorem famD_curv (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (hCX : (0 : ℝ) ≤ X.Cb) (hCY : (0 : ℝ) ≤ Y.Cb)
    (hK : X.bs.length = Y.bs.length) (hη : (X.T.η : ℝ) = Y.T.η) (hη1 : (X.T.η : ℝ) ≤ 1)
    (K : ℕ) (lbRB : ℚ)
    (hRB : (lbRB : ℝ) ≤ refBil (famMu X) (famMu X) - refBil (famMu X) (famMu Y) -
      refBil (famMu Y) (famMu X) + refBil (famMu Y) (famMu Y))
    (ubIM : ℝ)
    (hIM : ∀ N : ℕ, ip (fun n => mpos (famMu X) (famD X N).τ n - mpos (famMu Y) (famD X N).τ n)
        (fun n => mpos (famMu X) (famD X N).τ n - mpos (famMu Y) (famD X N).τ n) ≤ ubIM) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 2) * ((lbNorm X.T.v Y.T.v K : ℚ) : ℝ) + 2 * ((lbNorm X.T.a Y.T.a K : ℚ) : ℝ) +
        (1 - (X.T.η : ℝ)) * (lbRB : ℝ) + 2 * (X.T.η : ℝ) * ((lbNorm X.T.p Y.T.p K : ℚ) : ℝ) -
        2 * ((ubRaQ X Y : ℚ) : ℝ) + ((lbBQ X Y : ℚ) : ℝ) + (1 / 2) * ((lbRRQ X Y : ℚ) : ℝ) -
        (1 / 2) * ubIM ≤ curvQ (famD X N) (famD Y N) (58 * N) := by
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hc := famD_compat X Y hK hη N
  have hrA := famD_regular X hokX hCX N
  have hrB := famD_regular Y hokY hCY N
  have hX := famD_spec X hokX N
  have hY := famD_spec Y hokY N
  have hV : ((lbNorm X.T.v Y.T.v K : ℚ) : ℝ) ≤
      barrierTrialNormSq (fun k => (famD X N).v k - (famD Y N).v k) :=
    famD_lbV X Y hokX hokY K N
  have hA : ((lbNorm X.T.a Y.T.a K : ℚ) : ℝ) ≤
      barrierTrialNormSq (fun k => (famD X N).a k - (famD Y N).a k) :=
    famD_lbA X Y hokX hokY K N
  have hP : ((lbNorm X.T.p Y.T.p K : ℚ) : ℝ) ≤
      barrierTrialNormSq (fun k => (famD X N).p k - (famD Y N).p k) :=
    famD_lbP X Y hokX hokY K N
  have hRR : ((lbRRQ X Y : ℚ) : ℝ) ≤
      ip (fun n => (famD X N).R n - (famD Y N).R n) (fun n => (famD X N).R n - (famD Y N).R n) :=
    (famD_ipRR X Y N).ge
  have hRB' : (lbRB : ℝ) ≤ refBil (famD X N).μ (famD X N).μ - refBil (famD X N).μ (famD Y N).μ -
      refBil (famD Y N).μ (famD X N).μ + refBil (famD Y N).μ (famD Y N).μ := hRB
  have hBb := famD_lbB X Y N hN
  have hRa : raBil (famD X N).R (famD X N).a - raBil (famD X N).R (famD Y N).a -
      raBil (famD Y N).R (famD X N).a + raBil (famD Y N).R (famD Y N).a ≤ ((ubRaQ X Y : ℚ) : ℝ) :=
    (famD_ubRa X Y N).le
  have hIM' : ip (fun n => mpos (famD X N).μ (famD X N).τ n - mpos (famD Y N).μ (famD X N).τ n)
      (fun n => mpos (famD X N).μ (famD X N).τ n - mpos (famD Y N).μ (famD X N).τ n) ≤ ubIM := hIM N
  have hη1' : (famD X N).η ≤ 1 := hη1
  exact curvQ_ge (famD X N) (famD Y N) (58 * N) hc hrA hrB hX.ht hY.ht hη1' _ _ _ _ _ _ _ _
    hV hA hP hRR hRB' hBb hRa hIM'

/-- `Σ_{n<K} (Δ mposQ_n)² / (n+1)` of two trial references. -/
def ipDiffQ (X Y : FamPar) (K : ℕ) : ℚ :=
  ∑ n ∈ Finset.range K, (mposQ (ofTrial X.T) n - mposQ (ofTrial Y.T) n) ^ 2 / ((n : ℚ) + 1)

theorem famD_IM (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) (hCX : (0 : ℝ) ≤ X.Cb) (K : ℕ) (N : ℕ) :
    ip (fun n => mpos (famMu X) (famD X N).τ n - mpos (famMu Y) (famD X N).τ n)
        (fun n => mpos (famMu X) (famD X N).τ n - mpos (famMu Y) (famD X N).τ n) ≤
      ((ipDiffQ X Y K : ℚ) : ℝ) + (2 * max (X.Cb : ℝ) (Y.Cb : ℝ)) ^ 2 / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
  have hX := famD_spec X hokX N
  have hY := famD_spec Y hokY N
  have h := ip_mposDiff_le (famMu X) (famMu Y) (ofTrial X.T) (ofTrial Y.T) ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩ (ofTrial_OK (hokX _ le_rfl)) (ofTrial_OK (hokY _ le_rfl))
    (C := max (X.Cb : ℝ) (Y.Cb : ℝ)) (srefOK_mono hX.bd (le_max_left _ _))
    (srefOK_mono hY.bd (le_max_right _ _)) (le_trans hCX (le_max_left _ _)) (famD_tau_mem X N) K
  exact h

/-- `hRB`: the curvature block of the references from the one-shot enclosures. -/
theorem famD_RB (X Y : FamPar) (hokX : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C)
    (hokY : ∀ C : ℝ, (Y.Cb : ℝ) ≤ C → Y.T.DataOK C) {LA LB UAB : ℚ}
    (hA : (LA : ℝ) ≤ refEnergy (famMu X)) (hB : (LB : ℝ) ≤ refEnergy (famMu Y))
    (hAB : refBil (famMu X) (famMu Y) ≤ (UAB : ℝ)) :
    ((LA + LB - 2 * UAB : ℚ) : ℝ) ≤ refBil (famMu X) (famMu X) - refBil (famMu X) (famMu Y) -
      refBil (famMu Y) (famMu X) + refBil (famMu Y) (famMu Y) := by
  have hsym := refBil_symm (famMu X) (famMu Y) (ofTrial X.T) (ofTrial Y.T) ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩ (ofTrial_OK (hokX _ le_rfl)) (ofTrial_OK (hokY _ le_rfl))
  rw [← hsym]
  rw [refEnergy_eq_refBil] at hA hB
  push_cast
  linarith

end

end CatalanMeasure.GenD.Signed.Data.Assembly
