module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Family
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefConst
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMom
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefInst
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.MeanEval

@[expose] public section

/-!
# 410 assembly: `hrA` / `hrB` for the family `famD X` (T9, first half)

* finite-sum evaluators for the three sums that are not norms: `ra` (`raQ`), `ip R R` (`iRRQ`) and
  `Σ 2 b² / (i+1)` (`bQ`), for a reference with finite moments (`R.tail = []`);
* `famD_const`: `constTotal (58 N) - constant ≤ rLim … + ε` eventually, for `famD X`, from rational bounds of
  the norms (`EvalNormT`), the energy (`EvalRefE*`) and these sums.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.Consts OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Cert
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

noncomputable section

/-- The rational `ra` of a trial with finite reference moments. -/
def raQ (X : FamPar) : ℚ :=
  ∑ n ∈ Finset.range X.T.R.f.length,
    (-(-1 : ℚ) ^ (n + 1) * (X.T.R.f.getD n 0) / ((n : ℚ) + 1)) *
      ((X.T.a.f.getD n 0) + tailValQ X.T.a.tail (n + 1))

def iRRQ (X : FamPar) : ℚ :=
  ∑ n ∈ Finset.range X.T.R.f.length, (X.T.R.f.getD n 0) ^ 2 / ((n : ℚ) + 1)

def bQ (X : FamPar) : ℚ :=
  ∑ i ∈ Finset.range X.bs.length, 2 * (X.bs.getD i 0) ^ 2 / ((i : ℚ) + 1)

theorem famD_R (X : FamPar) (N : ℕ) (n : ℕ) :
    (famD X N).R n = ((X.T.R.f.getD n 0 : ℚ) : ℝ) := by
  show fQ X.T.R.f (n + 1) = _
  exact fQ_succ _ _

theorem famD_R_zero (X : FamPar) (N n : ℕ) (hn : X.T.R.f.length ≤ n) : (famD X N).R n = 0 := by
  rw [famD_R, List.getD_eq_default _ _ hn]; simp

theorem famD_a_succ (X : FamPar) (N n : ℕ) :
    (famD X N).a (n + 1) = (((X.T.a.f.getD n 0) + tailValQ X.T.a.tail (n + 1) : ℚ) : ℝ) := by
  show tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC) (n + 1) = _
  unfold tseq
  rw [if_neg (Nat.succ_ne_zero n), fQ_succ, ← tailValQ_spec]
  push_cast
  rfl

theorem famD_ra (X : FamPar) (N : ℕ) : (famD X N).ra = ((raQ X : ℚ) : ℝ) := by
  unfold SignedData.ra raQ
  rw [tsum_eq_sum (s := Finset.range X.T.R.f.length)]
  · push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold refTilt
    rw [famD_a_succ]
    have : (famD X N).R (n + 1 - 1) = (famD X N).R n := rfl
    rw [Nat.add_sub_cancel, famD_R]
    push_cast
    ring
  · intro n hn
    have hn' : X.T.R.f.length ≤ n := by simpa using hn
    unfold refTilt
    rw [Nat.add_sub_cancel, famD_R_zero X N n hn']
    simp

theorem famD_iRR (X : FamPar) (N : ℕ) : ip (famD X N).R (famD X N).R = ((iRRQ X : ℚ) : ℝ) := by
  unfold ip iRRQ
  rw [tsum_eq_sum (s := Finset.range X.T.R.f.length)]
  · push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [famD_R]; ring
  · intro n hn
    have hn' : X.T.R.f.length ≤ n := by simpa using hn
    rw [famD_R_zero X N n hn']
    simp

theorem famD_B (X : FamPar) (N : ℕ) :
    ∑ i ∈ Finset.range (famD X N).K, 2 * (famD X N).b (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) =
      ((bQ X : ℚ) : ℝ) := by
  unfold bQ
  show ∑ i ∈ Finset.range X.bs.length, 2 * bSeq X.bs (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) = _
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bSeq
  rw [if_neg (Nat.succ_ne_zero i)]
  simp

/-- **`hrA` / `hrB` of the family** (eventually in `N`, at `p = 58 N`). -/
theorem famD_const (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (K : ℕ)
    (l2 Vq Pq Rq Aq : ℝ) (hl2 : l2 ≤ Real.log 2)
    (hV : barrierTrialNormSq (tseq (fQ X.T.v.f) (X.T.v.tail.map TailQ.toC)) ≤ Vq)
    (hP : barrierTrialNormSq (tseq (fQ X.T.p.f) (X.T.p.tail.map TailQ.toC)) ≤ Pq)
    (hA : barrierTrialNormSq (tseq (fQ X.T.a.f) (X.T.a.tail.map TailQ.toC)) ≤ Aq)
    (hRef : refEnergy (famMu X) ≤ Rq) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (famD X N).constTotal (58 * N) - (famD X N).constant ≤
        rLim (X.T.η : ℝ) l2 Vq Pq Rq Aq ((raQ X : ℚ) : ℝ) ((iRRQ X : ℚ) : ℝ)
          ((ipPartQ (ofTrial X.T) K : ℚ) : ℝ) (5 / 58) (X.T.Sup : ℝ) (20 / 58) ((bQ X : ℚ) : ℝ) + ε := by
  have hf := famD_family X hok
  have hR : (ofTrial X.T).OK := ofTrial_OK (hok _ le_rfl)
  exact constTotal_sub_constant_le hf (fun N => 58 * N) (fun N => by push_cast; rfl)
    (20 / 58) (5 / 58) (X.Cb : ℝ)
    (fun N => by show ((20 * N : ℕ) : ℝ) = _; rw [show (famD X N).ν = 58 * (N : ℝ) from rfl]; push_cast; ring)
    (fun N => by show ((5 * N : ℕ) : ℝ) = _; rw [show (famD X N).ν = 58 * (N : ℝ) from rfl]; push_cast; ring)
    (fun N => rfl) (bSeq X.bs) X.bs.length (fun N => rfl) (fun N => rfl)
    l2 Vq Pq Rq Aq ((raQ X : ℚ) : ℝ) ((iRRQ X : ℚ) : ℝ) ((ipPartQ (ofTrial X.T) K : ℚ) : ℝ)
    ((bQ X : ℚ) : ℝ) hl2 (fun N => hV) (fun N => hP) (fun N => hA) (fun N => hRef)
    (fun N => (famD_ra X N).ge) (fun N => (famD_iRR X N).le)
    (famD_B X 0).le
    (hM_of_family hf (ofTrial X.T) hR (fun N => ⟨rfl, rfl, rfl, rfl⟩) K)

end

end CatalanMeasure.GenD.Signed.Data.Assembly
